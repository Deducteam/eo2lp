(* syntax_eo.ml
   Eunoia AST definitions and core operations *)

open Literal

module S = String
module M = Map.Make(S)

module L = struct
  include List
  let chop xs =
    let n = List.length xs in
    (take (n - 1) xs, nth xs (n - 1))
end

(* Core AST *)

type term =
  | Symbol  of string
  | Literal of literal
  | Apply   of string * term list
  | Bind    of string * var list * term

and var  = string * term
and case = term * term

type attr =
  (* constant attributes *)
  | RightAssocNil    of term
  | LeftAssocNil     of term
  | LeftAssocNilNSN  of term
  | RightAssocNilNSN of term
  | RightAssocNSN    of term
  | LeftAssocNSN     of term
  | RightAssoc
  | LeftAssoc
  | ArgList    of string
  | Chainable  of string
  | Pairwise   of string
  | Binder     of string
  | LetBinder  of term
  (* parameter attributes *)
  | Implicit
  | Opaque
  | List
  | Syntax   of term
  | Restrict of term

and premises =
  | Simple      of term list
  | PremiseList of term * term

and conclusion =
  | Conclusion         of term
  | ConclusionExplicit of term

and rule_dec = {
  assm : term option;
  prem : premises option;
  args : term list;
  reqs : case list;
  conc : conclusion;
}

and sorry = Sorry
and path  = string list

type param = string * term * attr list

type symbol =
  | Decl of param list * term * attr option
  | Defn of param list * term * term option  (* params, body, optional :type *)
  | Ltrl of lit_category * term
  | Prog of param list * term list * term * case list
  | Rule of param list * term * term list
         * term list * case list * term
  | Assume of term                            (* formula being assumed *)
  | Step of string * term list * term list * term option
         (* rule_name, premises, args, optional conclusion *)

type signature = (string * symbol) list
type context   = signature * param list

(* Builtins *)

let is_builtin s =
  s = "->" || s = "Type" || s = "_" || s = "as"
  || (S.starts_with ~prefix:"eo::" s
      && s <> "eo::List::cons"
      && s <> "eo::List::nil")

(* Parameter queries *)

let is_name (s, _, _) s' = s = s'
let is_attr (_, _, pas) pa = List.mem pa pas
let is_typ  (_, ty, _) ty' = ty = ty'

let prm_find s = L.find_opt (fun p -> is_name p s)
let prm_mem  s = L.exists   (fun p -> is_name p s)

let prm_typ s ty =
  L.exists (fun p -> is_name p s && is_typ p ty)

let prm_has_attr s pa =
  L.exists (fun p -> is_name p s && is_attr p pa)

(* Term operations *)

let app_ho t t' = Apply ("_", [t; t'])

let app_ho_list t ts = L.fold_left app_ho t ts

let app_raw t ts =
  match t, ts with
  | Symbol s, []   -> Symbol s
  | Symbol s, ts   -> Apply (s, ts)
  | Apply (s, ts), ts' -> Apply (s, L.append ts ts')
  | _ -> app_ho_list t ts

let rec subst t s t' =
  match t with
  | Literal _ -> t
  | Symbol s' ->
    if s = s' then t' else t
  | Apply (s', ts) ->
    let ts' = L.map (fun u -> subst u s t') ts in
    if s = s' then app_ho_list t' ts'
    else Apply (s', ts')
  | Bind (b, xs, body) ->
    let ys =
      L.map (fun (x, tx) -> (x, subst tx s t')) xs
    in
    Bind (b, ys, subst body s t')

(* Free parameters *)

let rec free_params ps = function
  | Symbol s ->
    (match prm_find s ps with
     | Some p -> [p]
     | None   -> [])
  | Literal _ -> []
  | Apply (_, ts) -> L.concat_map (free_params ps) ts
  | Bind (_, xs, body) ->
    let bound = L.map fst xs in
    let body_fvs = free_params ps body in
    L.filter (fun (s, _, _) -> not (L.mem s bound)) body_fvs

module P = struct
  type t = param
  let compare = compare
end

let free_params_many ps ts =
  L.concat_map (free_params ps) ts
  |> L.sort_uniq P.compare

let rec splice (ps, t, ts) =
  match ps, ts with
  | [], _ | _, [] -> (ps, t, ts)
  | (s, _, atts) :: ps', ts when List.mem Implicit atts ->
    splice (ps', t, ts)
  | (s, _, _) :: ps', t' :: ts' ->
    splice (ps', subst t s t', ts')

let rec is_kind = function
  | Symbol "Type"   -> true
  | Apply ("->", ts) -> L.exists is_kind ts
  | _ -> false

(* Free variables *)

module Set = Set.Make(String)

let rec params_in ps = function
  | Literal _ -> Set.empty
  | Symbol s ->
    if prm_mem s ps then Set.singleton s
    else Set.empty
  | Apply (s, ts) ->
    let xs =
      L.fold_left
        (fun acc t -> Set.union acc (params_in ps t))
        Set.empty ts
    in
    if prm_mem s ps then Set.union (Set.singleton s) xs
    else xs
  | Bind (_, vs, t) ->
    let xs =
      L.fold_left
        (fun acc (_, t) -> Set.union acc (params_in ps t))
        Set.empty vs
    in
    Set.union xs (params_in ps t)

let rec is_free s = function
  | Symbol s' -> s = s'
  | Apply (s', ts) -> s = s' || L.exists (is_free s) ts
  | Literal _ -> false
  | Bind (_, vs, t) ->
    let b1 = List.exists (fun (_, ty) -> is_free s ty) vs in
    let b2 = is_free s t in
    b1 || b2

(* Program helpers *)

let prog_ty (doms, ran) =
  Apply ("->", List.append doms [ran])

let rec returns_type = function
  | Symbol "Type" -> true
  | Apply ("->", ts) when ts <> [] ->
    returns_type (L.hd (L.rev ts))
  | _ -> false

let prog_ty_params t ps =
  let type_params =
    L.filter (fun (_, ty, _) -> ty = Symbol "Type") ps
  in
  let free_type_params term =
    let free = params_in type_params term in
    L.filter (fun (s, _, _) -> Set.mem s free) type_params
  in
  let sig_params =
    let free = params_in ps t in
    L.filter (fun (s, _, _) -> Set.mem s free) ps
  in
  let collected =
    L.fold_left (fun acc (s, ty, _) ->
      if ty = Symbol "Type" then Set.add s acc
      else
        let deps = free_type_params ty in
        L.fold_left
          (fun a (s', _, _) -> Set.add s' a)
          acc deps)
    Set.empty sig_params
  in
  type_params
  |> L.filter (fun (s, _, _) -> Set.mem s collected)
  |> L.map (fun (s, ty, atts) ->
       if L.mem Implicit atts then (s, ty, atts)
       else (s, ty, [Implicit]))

let prog_cs_params cs =
  let f ((s, ty, _) as p) =
    let g (t, t') = is_free s t || is_free s t' in
    if L.exists g cs || ty = Symbol "Type"
    then Some p
    else None
  in
  L.filter_map f

(* Literal types *)

let lit_cat_of = function
  | Numeral _     -> NUM
  | Decimal _     -> DEC
  | Rational _    -> RAT
  | Binary _      -> BIN
  | Hexadecimal _ -> HEX
  | String _      -> STR

let lit_type_table : (lit_category, string) Hashtbl.t =
  Hashtbl.create 8

let clear_lit_types () = Hashtbl.clear lit_type_table
let set_lit_type cat ty = Hashtbl.replace lit_type_table cat ty
let get_lit_type cat = Hashtbl.find_opt lit_type_table cat
let type_of_literal l = get_lit_type (lit_cat_of l)

(* Pretty printing *)

let opt_newline f = function
  | Some x -> Printf.sprintf "  %s\n" (f x)
  | None   -> ""

let opt_str f = Option.fold ~none:"" ~some:f

let opt_suffix_str f =
  Option.fold ~none:"" ~some:(fun x -> " " ^ f x)

let list_str f xs =
  String.concat " " (List.map f xs)

let list_suffix_str f = function
  | [] -> ""
  | ys -> " " ^ list_str f ys

let rec var_str (str, t) =
  Printf.sprintf "(%s %s)" str (term_str t)

and symbol_attr_str = function
  | RightAssoc -> ":right-assoc"
  | LeftAssoc  -> ":left-assoc"
  | RightAssocNil t ->
    Printf.sprintf ":right-assoc-nil %s" (term_str t)
  | LeftAssocNil t ->
    Printf.sprintf ":left-assoc-nil %s" (term_str t)
  | RightAssocNilNSN t ->
    Printf.sprintf
      ":right-assoc-nil-non-singleton-nil %s"
      (term_str t)
  | LeftAssocNilNSN t ->
    Printf.sprintf
      ":left-assoc-nil-non-singleton-nil %s"
      (term_str t)
  | RightAssocNSN t ->
    Printf.sprintf
      ":right-assoc-non-singleton-nil %s"
      (term_str t)
  | LeftAssocNSN t ->
    Printf.sprintf
      ":left-assoc-non-singleton-nil %s"
      (term_str t)
  | Chainable s  -> Printf.sprintf ":chainable %s" s
  | Binder s     -> Printf.sprintf ":binder %s" s
  | Pairwise s   -> Printf.sprintf ":pairwise %s" s
  | ArgList s    -> Printf.sprintf ":arg-list %s" s
  | LetBinder t  ->
    Printf.sprintf ":let-binder %s" (term_str t)
  | Implicit     -> ":implicit"
  | Opaque       -> ":opaque"
  | List         -> ":list"
  | Syntax t     ->
    Printf.sprintf ":syntax %s" (term_str t)
  | Restrict t   ->
    Printf.sprintf ":restrict %s" (term_str t)

and term_str = function
  | Symbol str  -> str
  | Literal l   -> literal_str l
  | Bind (str, xs, t) ->
    let xs' = List.map var_str xs in
    Printf.sprintf "(%s (%s) %s)"
      str (String.concat ", " xs') (term_str t)
  | Apply (s, ts) ->
    Printf.sprintf "(%s %s)"
      s (String.concat " " (List.map term_str ts))

and term_list_str ts =
  String.concat " " (List.map term_str ts)

let param_str (s, t, atts) =
  Printf.sprintf "(%s %s%s)"
    s (term_str t)
    (list_suffix_str symbol_attr_str atts)

let case_str (t, t') =
  Printf.sprintf "(%s %s)" (term_str t) (term_str t')

let case_list_str = list_str case_str

let premises_str = function
  | Simple ts ->
    Printf.sprintf ":premises %s" (term_list_str ts)
  | PremiseList (t, t') ->
    Printf.sprintf ":premise-list %s %s"
      (term_str t) (term_str t')

and assumption_str t =
  Printf.sprintf ":assumption %s" (term_str t)

and arguments_str ts =
  Printf.sprintf ":args %s" (term_list_str ts)

and reqs_str cs =
  Printf.sprintf ":requires (%s)" (case_list_str cs)

and conclusion_str = function
  | Conclusion t ->
    Printf.sprintf ":conclusion %s" (term_str t)
  | ConclusionExplicit t ->
    Printf.sprintf ":conclusion-explicit %s" (term_str t)

let rule_dec_str { assm; prem; args; reqs; conc } =
  Printf.sprintf "%s%s%s%s%s"
    (opt_newline assumption_str assm)
    (opt_newline premises_str prem)
    (opt_newline arguments_str (Some args))
    (opt_newline reqs_str (Some reqs))
    (opt_newline conclusion_str (Some conc))

let symbol_str = function
  | s, Decl (ps, t, ao) ->
    Printf.sprintf "(decl %s (%s) %s (%s))"
      s (list_str param_str ps)
      (term_str t) (opt_str symbol_attr_str ao)
  | s, Defn (ps, t, ty_opt) ->
    Printf.sprintf "(defn %s (%s) %s%s)"
      s (list_str param_str ps) (term_str t)
      (match ty_opt with None -> "" | Some ty -> " :type " ^ term_str ty)
  | s, Ltrl (cat, t) ->
    Printf.sprintf "(declare-consts %s %s)"
      (Literal.lit_category_str cat) (term_str t)
  | s, Prog (ps, doms, ran, cs) ->
    Printf.sprintf "(prog %s ((%s) :signature (%s) %s) (%s))"
      s (list_str param_str ps)
      (term_list_str doms) (term_str ran)
      (case_list_str cs)
  | s, Rule _ ->
    Printf.sprintf "(rule %s ...)" s

let sig_str sgn =
  S.concat "\n" (L.map symbol_str sgn)

(* Datatype declarations *)

type sort_dec = SortDec of string * int

and sel_dec  = SelDec  of string * term
and cons_dec = ConsDec of string * sel_dec list
and dt_dec   = DatatypeDec of cons_dec list

let sort_dec_str = function
  | SortDec (s, n) -> Printf.sprintf "(%s %d)" s n

and sel_dec_str = function
  | SelDec (s, t) ->
    Printf.sprintf "(%s %s)" s (term_str t)

let cons_dec_str = function
  | ConsDec (s, xs) ->
    Printf.sprintf "(%s %s)"
      s (String.concat " " (List.map sel_dec_str xs))

let dt_dec_str = function
  | DatatypeDec xs ->
    Printf.sprintf "(%s)"
      (String.concat " " (List.map cons_dec_str xs))

(* Commands *)

type common_command =
  | DeclareConst     of string * term * attr option
  | DeclareDatatype  of string * dt_dec
  | DeclareDatatypes of sort_dec list * dt_dec list
  | Echo             of string option
  | Exit
  | Reset
  | SetOption        of string

type command =
  | Assume            of string * term
  | AssumePush        of string * term
  | DeclareConsts     of lit_category * term
  | DeclareParamConst of string * param list
                      * term * attr option
  | DeclareRule       of string * param list
                      * rule_dec * sorry option
  | Define            of string * param list
                      * term * term option
  | Include           of path
  | Program           of string
                      * (param list * term)
                      * (param list * case list)
  | Reference         of string * string option
  | Step              of string * term * string
                      * term list * term list
  | StepPop           of string * term * string
                      * term list * term list
  | Common            of common_command

let common_command_str = function
  | DeclareConst (s, t, att) ->
    Printf.sprintf "(declare-const %s %s %s)"
      s (term_str t) (opt_suffix_str symbol_attr_str att)
  | DeclareDatatype (s, dt) ->
    Printf.sprintf "(declare-datatype %s %s)"
      s (dt_dec_str dt)
  | DeclareDatatypes (xs, ys) ->
    Printf.sprintf "(declare-datatypes (%s) (%s))"
      (String.concat "" (List.map sort_dec_str xs))
      (String.concat "" (List.map dt_dec_str ys))
  | Echo str_opt ->
    Printf.sprintf "(echo%s)"
      (opt_suffix_str (fun x -> x) str_opt)
  | Reset -> "(reset)"
  | SetOption x -> Printf.sprintf "(set-option %s)" x
  | Exit -> "(exit)"

let command_str = function
  | Assume (s, t) ->
    Printf.sprintf "(assume %s %s)" s (term_str t)
  | AssumePush (s, t) ->
    Printf.sprintf "(assume-push %s %s)" s (term_str t)
  | DeclareConsts (lc, t) ->
    Printf.sprintf "(declare-consts %s %s)"
      (lit_category_str lc) (term_str t)
  | DeclareParamConst (s, ps, t, att_opt) ->
    Printf.sprintf "(declare-parameterized-const %s (%s) %s%s)"
      s (list_str param_str ps)
      (term_str t) (opt_suffix_str symbol_attr_str att_opt)
  | DeclareRule (s, xs, rdec, sorry_opt) ->
    Printf.sprintf "(declare-rule %s (%s)\n%s\n%s)"
      s (list_str param_str xs)
      (rule_dec_str rdec)
      (opt_newline (fun _ -> ":sorry") sorry_opt)
  | Define (s, xs, t, t_opt) ->
    Printf.sprintf "(define %s (%s) %s%s)"
      s (list_str param_str xs)
      (term_str t) (opt_suffix_str term_str t_opt)
  | Include p ->
    Printf.sprintf "(include %s)" (String.concat "." p)
  | Program (s, (ps, ty), (qs, cs)) ->
    Printf.sprintf "(program %s\n:type (%s) %s\n:cases (%s) (%s))"
      s (list_str param_str ps) (term_str ty)
      (list_str param_str qs) (case_list_str cs)
  | Reference (str, s_opt) ->
    Printf.sprintf "(reference %s %s)"
      str (opt_str (fun x -> x) s_opt)
  | Step (s, t_opt, s', ts, ts') ->
    Printf.sprintf "(step %s %s %s%s%s)"
      s (term_str t_opt) s'
      (list_suffix_str term_str ts)
      (list_suffix_str term_str ts')
  | StepPop (s, t_opt, s', ts, ts') ->
    Printf.sprintf "(step-pop %s %s %s%s%s)"
      s (term_str t_opt) s'
      (list_suffix_str term_str ts)
      (list_suffix_str term_str ts')
  | Common c -> common_command_str c

(* ============================================================
   Symbol Graph - Primary data structure
   ============================================================ *)

module PathMap = Map.Make(struct
  type t = path
  let compare = compare
end)

(* Symbol identifier: module path + symbol name *)
type symbol_id = {
  sid_module : path;   (* e.g., ["theories"; "Arith"] *)
  sid_name   : string; (* e.g., "+" *)
}

module SymbolId = struct
  type t = symbol_id
  let compare a b =
    match compare a.sid_module b.sid_module with
    | 0 -> String.compare a.sid_name b.sid_name
    | n -> n
  let equal a b = compare a b = 0
  let hash a = Hashtbl.hash (a.sid_module, a.sid_name)
  let to_string a = String.concat "." a.sid_module ^ "." ^ a.sid_name
end

module SymbolMap = Map.Make(SymbolId)
module SymbolSet = Stdlib.Set.Make(SymbolId)

(* A node in the symbol graph *)
type symbol_node = {
  sn_id   : symbol_id;
  sn_def  : symbol;
  sn_deps : SymbolSet.t;  (* direct dependencies - edges in the graph *)
}

(* The symbol graph: the primary data structure
   Maps symbol_id -> symbol_node *)
type symbol_graph = {
  sg_nodes   : symbol_node SymbolMap.t;
  sg_by_name : symbol_id list M.t;  (* for resolving unqualified names *)
}

let empty_graph : symbol_graph = {
  sg_nodes = SymbolMap.empty;
  sg_by_name = M.empty;
}

let graph_add (node : symbol_node) (g : symbol_graph) : symbol_graph =
  let name = node.sn_id.sid_name in
  let existing = Option.value ~default:[] (M.find_opt name g.sg_by_name) in
  {
    sg_nodes = SymbolMap.add node.sn_id node g.sg_nodes;
    sg_by_name = M.add name (node.sn_id :: existing) g.sg_by_name;
  }

let graph_find (g : symbol_graph) (sid : symbol_id) : symbol_node option =
  SymbolMap.find_opt sid g.sg_nodes

let graph_find_by_name (g : symbol_graph) (name : string) : symbol_id list =
  Option.value ~default:[] (M.find_opt name g.sg_by_name)

let graph_mem (g : symbol_graph) (sid : symbol_id) : bool =
  SymbolMap.mem sid g.sg_nodes

let graph_fold f (g : symbol_graph) acc =
  SymbolMap.fold (fun _ node acc -> f node acc) g.sg_nodes acc

let graph_cardinal (g : symbol_graph) : int =
  SymbolMap.cardinal g.sg_nodes

(* Resolve an unqualified symbol name, preferring the given module context *)
let graph_resolve (g : symbol_graph) (context : path) (name : string) : symbol_id option =
  match graph_find_by_name g name with
  | [] -> None
  | [single] -> Some single
  | multiple ->
    (* Prefer symbol from same module *)
    match L.find_opt (fun sid -> sid.sid_module = context) multiple with
    | Some found -> Some found
    | None -> Some (L.hd multiple)

(* Compute transitive closure of symbol dependencies *)
let graph_closure (g : symbol_graph) (seeds : SymbolSet.t) : SymbolSet.t =
  let rec go visited frontier =
    if SymbolSet.is_empty frontier then visited
    else
      let new_visited = SymbolSet.union visited frontier in
      let new_deps =
        SymbolSet.fold (fun sid acc ->
          match graph_find g sid with
          | Some node -> SymbolSet.union acc node.sn_deps
          | None -> acc
        ) frontier SymbolSet.empty
      in
      let new_frontier = SymbolSet.diff new_deps new_visited in
      go new_visited new_frontier
  in
  go SymbolSet.empty seeds

(* Filter graph to only include symbols in the given set *)
let graph_filter (g : symbol_graph) (keep : SymbolSet.t) : symbol_graph =
  SymbolMap.fold (fun sid node acc ->
    if SymbolSet.mem sid keep then graph_add node acc else acc
  ) g.sg_nodes empty_graph

(* Group symbols by module path *)
let graph_group_by_module (g : symbol_graph) : (path * (string * symbol) list) list =
  let by_module = SymbolMap.fold (fun sid node acc ->
    let existing = Option.value ~default:[] (PathMap.find_opt sid.sid_module acc) in
    PathMap.add sid.sid_module ((sid.sid_name, node.sn_def) :: existing) acc
  ) g.sg_nodes PathMap.empty in
  PathMap.bindings by_module

(* Get all modules in the graph *)
let graph_modules (g : symbol_graph) : path list =
  SymbolMap.fold (fun sid _ acc ->
    if L.mem sid.sid_module acc then acc else sid.sid_module :: acc
  ) g.sg_nodes []

(* Merge two graphs *)
let graph_union (g1 : symbol_graph) (g2 : symbol_graph) : symbol_graph =
  SymbolMap.fold (fun _ node acc -> graph_add node acc) g2.sg_nodes g1

(* ============================================================
   Legacy types (for gradual migration)
   ============================================================ *)

type sig_node = {
  node_path     : path;
  node_file     : string;
  node_includes : path list;
  node_sig      : signature;
}

type sig_graph_legacy = sig_node PathMap.t

type file_parse_result = {
  fpr_path     : path;
  fpr_file     : string;
  fpr_includes : path list;
  fpr_sig      : signature;
}

(* Alias for backwards compatibility during migration *)
type sig_graph = sig_graph_legacy

(* Legacy symbol types - to be removed *)
type symbol_entry = {
  se_id   : symbol_id;
  se_def  : symbol;
  se_deps : SymbolSet.t;
}

type symbol_index = {
  si_by_name : symbol_id list M.t;
  si_by_id : symbol_entry SymbolMap.t;
}

let empty_symbol_index = {
  si_by_name = M.empty;
  si_by_id = SymbolMap.empty;
}

let add_symbol_entry (idx : symbol_index) (entry : symbol_entry) : symbol_index =
  let name = entry.se_id.sid_name in
  let existing = Option.value ~default:[] (M.find_opt name idx.si_by_name) in
  {
    si_by_name = M.add name (entry.se_id :: existing) idx.si_by_name;
    si_by_id = SymbolMap.add entry.se_id entry idx.si_by_id;
  }

let find_symbol_by_id (idx : symbol_index) (sid : symbol_id) : symbol_entry option =
  SymbolMap.find_opt sid idx.si_by_id

let find_symbols_by_name (idx : symbol_index) (name : string) : symbol_id list =
  Option.value ~default:[] (M.find_opt name idx.si_by_name)

(* Resolve a symbol name to a symbol_id, preferring the given module context *)
let resolve_symbol_name (idx : symbol_index) (context : path) (name : string) : symbol_id option =
  match find_symbols_by_name idx name with
  | [] -> None  (* unknown symbol *)
  | [single] -> Some single  (* unique *)
  | multiple ->
    (* Prefer symbol from same module *)
    match L.find_opt (fun sid -> sid.sid_module = context) multiple with
    | Some found -> Some found
    | None -> Some (L.hd multiple)  (* fallback to first *)

let sig_node_str n =
  Printf.sprintf
    "{ path: %s\n  file: %s\n  includes: [%s]\n  symbols: %d }"
    (S.concat "." n.node_path)
    n.node_file
    (S.concat ", " (L.map (S.concat ".") n.node_includes))
    (L.length n.node_sig)

let path_str : path -> string = S.concat "."

let topo_sort graph =
  let visited =
    Hashtbl.create (PathMap.cardinal graph)
  in
  let result = ref [] in
  let rec visit path =
    if Hashtbl.mem visited path then ()
    else begin
      Hashtbl.add visited path ();
      match PathMap.find_opt path graph with
      | None -> ()
      | Some node ->
        L.iter visit node.node_includes;
        result := path :: !result
    end
  in
  PathMap.iter (fun path _ -> visit path) graph;
  L.rev !result

let flatten_graph graph =
  let paths = topo_sort graph in
  L.concat_map (fun p ->
    match PathMap.find_opt p graph with
    | Some node -> node.node_sig
    | None -> [])
  paths

(* Core prelude *)

let core_prelude : signature ref = ref []

let set_core_prelude sig_ = core_prelude := sig_

let core_eo_source = {|
(declare-const eo::Bool Type)
(declare-const eo::true eo::Bool)
(declare-const eo::false eo::Bool)

(declare-const eo::String Type)
(declare-const eo::Z Type)
(declare-const eo::Q Type)

(declare-parameterized-const eo::as
  ((T Type :implicit))
  (-> T Type T)
)

(declare-parameterized-const eo::is_ok
  ((T Type :implicit))
  (-> T eo::Bool)
)
(declare-parameterized-const eo::ite
  ((T Type :implicit))
  (-> eo::Bool T T T)
)
(declare-parameterized-const eo::eq
  ((U Type :implicit))
  (-> U U eo::Bool)
)
(declare-parameterized-const eo::is_eq
    ((T Type :implicit) (S Type :implicit))
    (-> T S eo::Bool)
)
(declare-parameterized-const eo::requires
  ((T Type :implicit) (U Type :implicit) (V Type :implicit))
  (-> T U V V)
)
(declare-parameterized-const eo::hash
    ((T Type :implicit))
    (-> T eo::Z)
)
(declare-parameterized-const eo::typeof
  ((T Type :implicit))
  (-> T Type)
)
(declare-parameterized-const eo::nameof
    ((T Type :implicit))
    (-> T eo::String)
)
(declare-parameterized-const eo::var
    ((T Type :implicit))
    (-> eo::String T T)
)
(declare-parameterized-const eo::cmp
  ((T Type :implicit) (U Type :implicit))
  (-> T U eo::Bool)
)
(declare-parameterized-const eo::is_var
  ((T Type :implicit))
  (-> T eo::Bool)
)
(declare-parameterized-const eo::is_z
  ((T Type :implicit))
  (-> T eo::Bool)
)

(declare-const eo::and (-> eo::Bool eo::Bool eo::Bool))
(declare-const eo::or (-> eo::Bool eo::Bool eo::Bool))
(declare-const eo::xor (-> eo::Bool eo::Bool eo::Bool))
(declare-const eo::not (-> eo::Bool eo::Bool))

(declare-parameterized-const eo::add
    ((T Type :implicit))
    (-> T T T)
)
(declare-parameterized-const eo::mul
    ((T Type :implicit))
    (-> T T T)
)
(declare-parameterized-const eo::neg
    ((T Type :implicit))
    (-> T T)
)
(declare-parameterized-const eo::qdiv
    ((T Type :implicit))
    (-> T T T)
)
(declare-parameterized-const eo::zdiv
    ((T Type :implicit))
    (-> T T T)
)
(declare-parameterized-const eo::zmod
    ((T Type :implicit))
    (-> T T T)
)
(declare-parameterized-const eo::is_neg
    ((T Type :implicit))
    (-> T eo::Bool)
)
(declare-parameterized-const eo::gt
    ((T Type :implicit) (U Type :implicit))
    (-> T U eo::Bool)
)

(declare-parameterized-const eo::len
    ((T Type :implicit))
    (-> T eo::Z)
)
(declare-parameterized-const eo::concat
    ((T Type :implicit))
    (-> T T T)
)
(declare-parameterized-const eo::extract
    ((T Type :implicit))
    (-> T eo::Z eo::Z T)
)
(declare-const eo::find (-> eo::String eo::String eo::Z))

(declare-parameterized-const eo::to_z
    ((T Type :implicit))
    (-> T eo::Z)
)
(declare-parameterized-const eo::to_q
    ((T Type :implicit))
    (-> T eo::Q)
)
(declare-parameterized-const eo::to_bin
    ((T Type :implicit))
    (-> eo::Z T T)
)
(declare-parameterized-const eo::to_str
    ((T Type :implicit))
    (-> T eo::String)
)

(declare-parameterized-const eo::nil
  ((U Type :implicit) (T Type :implicit))
  (-> (-> U T T) Type T)
)
(declare-parameterized-const eo::cons
  ((U Type :implicit) (T Type :implicit))
  (-> (-> U T T) U T T)
)
(declare-parameterized-const eo::list_concat
  ((U Type :implicit) (T Type :implicit))
  (-> (-> U T T) T T T)
)
(declare-parameterized-const eo::list_len
  ((F Type :implicit) (T Type :implicit))
  (-> F T eo::Z)
)
(declare-parameterized-const eo::list_nth
  ((F Type :implicit) (T Type :implicit))
  (-> F T eo::Z T)
)
(declare-parameterized-const eo::list_find
  ((F Type :implicit) (T Type :implicit))
  (-> F T T eo::Z)
)
(declare-parameterized-const eo::list_rev
  ((F Type :implicit) (T Type :implicit))
  (-> F T T)
)
(declare-parameterized-const eo::list_erase
  ((F Type :implicit) (T Type :implicit))
  (-> F T T T)
)
(declare-parameterized-const eo::list_erase_all
  ((F Type :implicit) (T Type :implicit))
  (-> F T T T)
)
(declare-parameterized-const eo::list_setof
  ((F Type :implicit) (T Type :implicit))
  (-> F T T)
)
(declare-parameterized-const eo::list_minclude
  ((F Type :implicit) (T Type :implicit))
  (-> F T T eo::Bool)
)
(declare-parameterized-const eo::list_meq
  ((F Type :implicit) (T Type :implicit))
  (-> F T T eo::Bool)
)
(declare-parameterized-const eo::list_diff
  ((F Type :implicit) (T Type :implicit))
  (-> F T T T)
)
(declare-parameterized-const eo::list_inter
  ((F Type :implicit) (T Type :implicit))
  (-> F T T T)
)
(declare-parameterized-const eo::list_singleton_elim
  ((F Type :implicit) (T Type :implicit))
  (-> F T T)
)

(declare-const eo::List Type)
(declare-const eo::List::nil eo::List)
(declare-parameterized-const eo::List::cons
  ((T Type :implicit))
  (-> T eo::List eo::List)
  :right-assoc-nil eo::List::nil
)
|}

let full_sig_at graph path =
  let visited = Hashtbl.create 16 in
  let rec collect p =
    if Hashtbl.mem visited p then []
    else begin
      Hashtbl.add visited p ();
      match PathMap.find_opt p graph with
      | None -> []
      | Some node ->
        let deps = L.concat_map collect node.node_includes in
        deps @ node.node_sig
    end
  in
  !core_prelude @ collect path

(* Get the full signature for all modules in a graph (for proof mode) *)
let full_sig graph =
  let all_sigs =
    PathMap.fold (fun _ node acc -> node.node_sig @ acc) graph []
  in
  !core_prelude @ all_sigs

(* ============================================================
   Symbol dependency analysis for minimal CPC generation
   ============================================================ *)

(* Extract all symbol references from a term *)
let rec symbols_in_term acc = function
  | Symbol s -> Set.add s acc
  | Literal _ -> acc
  | Apply (s, ts) ->
    let acc = Set.add s acc in
    L.fold_left symbols_in_term acc ts
  | Bind (b, vs, body) ->
    let acc = Set.add b acc in
    let acc = L.fold_left (fun a (_, ty) -> symbols_in_term a ty) acc vs in
    symbols_in_term acc body

(* Extract all symbol references from a list of terms *)
let symbols_in_terms ts =
  L.fold_left symbols_in_term Set.empty ts

(* Extract all symbol references from a case *)
let symbols_in_case (lhs, rhs) =
  Set.union (symbols_in_term Set.empty lhs) (symbols_in_term Set.empty rhs)

(* Extract all symbol references from params *)
let symbols_in_params ps =
  L.fold_left (fun acc (_, ty, _) -> symbols_in_term acc ty) Set.empty ps

(* Extract all symbol references from a rule_dec *)
let symbols_in_rule_dec rd =
  let acc = Set.empty in
  let acc = match rd.assm with Some t -> symbols_in_term acc t | None -> acc in
  let acc = match rd.prem with
    | Some (Simple ts) -> L.fold_left symbols_in_term acc ts
    | Some (PremiseList (t1, t2)) ->
      symbols_in_term (symbols_in_term acc t1) t2
    | None -> acc
  in
  let acc = L.fold_left symbols_in_term acc rd.args in
  let acc = L.fold_left (fun a c -> Set.union a (symbols_in_case c)) acc rd.reqs in
  match rd.conc with
  | Conclusion t | ConclusionExplicit t -> symbols_in_term acc t

(* Extract all symbol references from attr *)
let symbols_in_attr = function
  | RightAssocNil t | LeftAssocNil t
  | LeftAssocNilNSN t | RightAssocNilNSN t
  | RightAssocNSN t | LeftAssocNSN t
  | Syntax t | Restrict t | LetBinder t -> symbols_in_term Set.empty t
  | ArgList s | Chainable s | Pairwise s | Binder s -> Set.singleton s
  | _ -> Set.empty

(* Extract all symbol dependencies from a symbol definition *)
let symbols_in_symbol = function
  | Decl (ps, ty, attr_opt) ->
    let acc = symbols_in_params ps in
    let acc = symbols_in_term acc ty in
    (match attr_opt with
     | Some attr -> Set.union acc (symbols_in_attr attr)
     | None -> acc)
  | Defn (ps, body, ty_opt) ->
    let acc = symbols_in_params ps in
    let acc = symbols_in_term acc body in
    (match ty_opt with
     | Some ty -> symbols_in_term acc ty
     | None -> acc)
  | Ltrl (_, ty) -> symbols_in_term Set.empty ty
  | Prog (ps, sig_tys, ret_ty, cases) ->
    let acc = symbols_in_params ps in
    let acc = L.fold_left symbols_in_term acc sig_tys in
    let acc = symbols_in_term acc ret_ty in
    L.fold_left (fun a c -> Set.union a (symbols_in_case c)) acc cases
  | Rule (ps, assm, prems, args, reqs, conc) ->
    let acc = symbols_in_params ps in
    let acc = symbols_in_term acc assm in
    let acc = L.fold_left symbols_in_term acc prems in
    let acc = L.fold_left symbols_in_term acc args in
    let acc = L.fold_left (fun a c -> Set.union a (symbols_in_case c)) acc reqs in
    symbols_in_term acc conc
  | Assume t -> symbols_in_term Set.empty t
  | Step (rule_name, prems, args, conc_opt) ->
    let acc = Set.singleton rule_name in
    let acc = L.fold_left symbols_in_term acc prems in
    let acc = L.fold_left symbols_in_term acc args in
    (match conc_opt with
     | Some conc -> symbols_in_term acc conc
     | None -> acc)

(* Build a symbol graph from parsed modules.
   Takes a list of (module_path, symbols) pairs.
   Dependencies are resolved in two passes:
   1. Add all symbols with empty deps
   2. Resolve deps using the complete graph *)
let build_graph (modules : (path * (string * symbol) list) list) : symbol_graph =
  (* Pass 1: add all symbols with empty deps *)
  let g = L.fold_left (fun g (mod_path, syms) ->
    L.fold_left (fun g (name, def) ->
      let node = {
        sn_id = { sid_module = mod_path; sid_name = name };
        sn_def = def;
        sn_deps = SymbolSet.empty;
      } in
      graph_add node g
    ) g syms
  ) empty_graph modules in

  (* Pass 2: resolve dependencies *)
  let resolve_deps (node : symbol_node) : symbol_node =
    let string_deps = symbols_in_symbol node.sn_def in
    let resolved_deps = Set.fold (fun name acc ->
      (* Skip self-reference *)
      if name = node.sn_id.sid_name then acc
      else match graph_resolve g node.sn_id.sid_module name with
        | Some sid -> SymbolSet.add sid acc
        | None -> acc  (* unresolved - builtin or unknown *)
    ) string_deps SymbolSet.empty in
    { node with sn_deps = resolved_deps }
  in

  SymbolMap.fold (fun _sid node acc ->
    graph_add (resolve_deps node) acc
  ) g.sg_nodes empty_graph

(* Build a map from symbol name to its dependencies *)
let build_dependency_map (sig_ : signature) : Set.t M.t =
  L.fold_left (fun map (name, sym) ->
    let deps = symbols_in_symbol sym in
    (* Remove self-reference *)
    let deps = Set.remove name deps in
    M.add name deps map
  ) M.empty sig_

(* Compute transitive closure of dependencies from a set of seed symbols *)
let transitive_closure (dep_map : Set.t M.t) (seeds : Set.t) : Set.t =
  let rec go visited frontier =
    if Set.is_empty frontier then visited
    else
      let new_visited = Set.union visited frontier in
      let new_deps =
        Set.fold (fun sym acc ->
          match M.find_opt sym dep_map with
          | Some deps -> Set.union acc deps
          | None -> acc
        ) frontier Set.empty
      in
      let new_frontier = Set.diff new_deps new_visited in
      go new_visited new_frontier
  in
  go Set.empty seeds

(* Filter a signature to only include symbols in the given set *)
let filter_signature (sig_ : signature) (keep : Set.t) : signature =
  L.filter (fun (name, _) -> Set.mem name keep) sig_

(* Given a signature and a set of seed symbol names, compute the minimal
   signature containing only those symbols and their transitive dependencies *)
let minimal_signature (sig_ : signature) (seeds : string list) : signature =
  let seed_set = Set.of_list seeds in
  let dep_map = build_dependency_map sig_ in
  let closure = transitive_closure dep_map seed_set in
  filter_signature sig_ closure

(* Extract all rule names used in a proof signature (from Step commands) *)
let rules_in_signature (sig_ : signature) : Set.t =
  L.fold_left (fun acc (_, (c : symbol)) ->
    match c with
    | Step (rule_name, _, _, _) -> Set.add rule_name acc
    | _ -> acc
  ) Set.empty sig_

(* ============================================================
   Symbol-level dependency analysis (using symbol_id)
   ============================================================ *)

(* Build a symbol index from a module graph *)
let build_symbol_index (modules : sig_node PathMap.t) : symbol_index =
  PathMap.fold (fun mod_path node idx ->
    L.fold_left (fun idx (name, def) ->
      let sid = { sid_module = mod_path; sid_name = name } in
      (* For now, store empty deps - we'll compute them in a second pass *)
      let entry = { se_id = sid; se_def = def; se_deps = SymbolSet.empty } in
      add_symbol_entry idx entry
    ) idx node.node_sig
  ) modules empty_symbol_index

(* Resolve symbol references in a term to symbol_ids *)
let rec resolve_symbols_in_term (idx : symbol_index) (context : path) (acc : SymbolSet.t) = function
  | Symbol s ->
    (match resolve_symbol_name idx context s with
     | Some sid -> SymbolSet.add sid acc
     | None -> acc)  (* unresolved - might be builtin or parameter *)
  | Literal _ -> acc
  | Apply (s, ts) ->
    let acc = match resolve_symbol_name idx context s with
      | Some sid -> SymbolSet.add sid acc
      | None -> acc
    in
    L.fold_left (resolve_symbols_in_term idx context) acc ts
  | Bind (b, vs, body) ->
    let acc = match resolve_symbol_name idx context b with
      | Some sid -> SymbolSet.add sid acc
      | None -> acc
    in
    let acc = L.fold_left (fun a (_, ty) -> resolve_symbols_in_term idx context a ty) acc vs in
    resolve_symbols_in_term idx context acc body

(* Resolve all symbol references in a symbol definition *)
let resolve_symbols_in_def (idx : symbol_index) (context : path) (def : symbol) : SymbolSet.t =
  let resolve = resolve_symbols_in_term idx context in
  let resolve_params ps =
    L.fold_left (fun acc (_, ty, _) -> resolve acc ty) SymbolSet.empty ps
  in
  let resolve_case acc (lhs, rhs) =
    SymbolSet.union (resolve acc lhs) (resolve SymbolSet.empty rhs)
  in
  match def with
  | Decl (ps, ty, _) ->
    SymbolSet.union (resolve_params ps) (resolve SymbolSet.empty ty)
  | Defn (ps, body, ty_opt) ->
    let acc = SymbolSet.union (resolve_params ps) (resolve SymbolSet.empty body) in
    (match ty_opt with Some ty -> resolve acc ty | None -> acc)
  | Ltrl (_, ty) -> resolve SymbolSet.empty ty
  | Prog (ps, sig_tys, ret_ty, cases) ->
    let acc = resolve_params ps in
    let acc = L.fold_left resolve acc sig_tys in
    let acc = resolve acc ret_ty in
    L.fold_left resolve_case acc cases
  | Rule (ps, assm, prems, args, reqs, conc) ->
    let acc = resolve_params ps in
    let acc = resolve acc assm in
    let acc = L.fold_left resolve acc prems in
    let acc = L.fold_left resolve acc args in
    let acc = L.fold_left resolve_case acc reqs in
    resolve acc conc
  | Assume t -> resolve SymbolSet.empty t
  | Step (rule_name, prems, args, conc_opt) ->
    let acc = match resolve_symbol_name idx context rule_name with
      | Some sid -> SymbolSet.singleton sid
      | None -> SymbolSet.empty
    in
    let acc = L.fold_left resolve acc prems in
    let acc = L.fold_left resolve acc args in
    (match conc_opt with Some t -> resolve acc t | None -> acc)

(* Compute dependencies for all symbols in the index *)
let compute_symbol_deps (modules : sig_node PathMap.t) (idx : symbol_index) : symbol_index =
  SymbolMap.fold (fun sid entry new_idx ->
    let deps = resolve_symbols_in_def idx sid.sid_module entry.se_def in
    (* Remove self-reference *)
    let deps = SymbolSet.remove sid deps in
    let new_entry = { entry with se_deps = deps } in
    { new_idx with si_by_id = SymbolMap.add sid new_entry new_idx.si_by_id }
  ) idx.si_by_id idx

(* Compute transitive closure from seed symbol_ids *)
let transitive_closure_ids (idx : symbol_index) (seeds : SymbolSet.t) : SymbolSet.t =
  let rec go visited frontier =
    if SymbolSet.is_empty frontier then visited
    else
      let new_visited = SymbolSet.union visited frontier in
      let new_deps =
        SymbolSet.fold (fun sid acc ->
          match find_symbol_by_id idx sid with
          | Some entry -> SymbolSet.union acc entry.se_deps
          | None -> acc
        ) frontier SymbolSet.empty
      in
      let new_frontier = SymbolSet.diff new_deps new_visited in
      go new_visited new_frontier
  in
  go SymbolSet.empty seeds

(* Filter a module graph to only include symbols in the closure *)
let filter_graph_by_symbols (modules : sig_node PathMap.t) (keep : SymbolSet.t) : sig_node PathMap.t =
  PathMap.map (fun node ->
    let filtered_sig = L.filter (fun (name, _) ->
      let sid = { sid_module = node.node_path; sid_name = name } in
      SymbolSet.mem sid keep
    ) node.node_sig in
    { node with node_sig = filtered_sig }
  ) modules
  |> PathMap.filter (fun _ node -> node.node_sig <> [])

(* Build complete symbol index with dependencies from a module graph *)
let build_complete_symbol_index (modules : sig_node PathMap.t) : symbol_index =
  let idx = build_symbol_index modules in
  compute_symbol_deps modules idx

(* Combined module graph with symbol index *)
type indexed_graph = {
  ig_modules : sig_node PathMap.t;
  ig_symbols : symbol_index;
}

(* Build an indexed graph from a module graph *)
let index_graph (modules : sig_node PathMap.t) : indexed_graph = {
  ig_modules = modules;
  ig_symbols = build_complete_symbol_index modules;
}

(* Given an indexed graph and seed symbol names, compute minimal graph *)
let minimal_indexed_graph (ig : indexed_graph) (seed_names : string list) : indexed_graph =
  (* Resolve seed names to symbol_ids *)
  let seeds = L.filter_map (fun name ->
    match find_symbols_by_name ig.ig_symbols name with
    | [] -> None
    | sids -> Some (L.hd sids)  (* take first if multiple *)
  ) seed_names in
  let seed_set = SymbolSet.of_list seeds in

  (* Compute transitive closure *)
  let closure = transitive_closure_ids ig.ig_symbols seed_set in

  (* Filter modules *)
  let filtered_modules = filter_graph_by_symbols ig.ig_modules closure in

  (* Rebuild symbol index for filtered graph *)
  let filtered_symbols = build_complete_symbol_index filtered_modules in

  { ig_modules = filtered_modules; ig_symbols = filtered_symbols }

(* ============================================================
   Job specification for benchmarking
   ============================================================ *)

(* Source of proof files *)
type proof_source =
  | ProofDir of string        (* directory containing .eo files *)
  | ProofFiles of string list (* explicit list of files *)

(* Job specification *)
type job = {
  job_name   : string;
  job_logic  : string;        (* path to logic source directory *)
  job_proofs : proof_source;
}

let job_str j =
  let proofs_str = match j.job_proofs with
    | ProofDir d -> Printf.sprintf "(dir %s)" d
    | ProofFiles fs -> Printf.sprintf "(files %s)" (String.concat " " fs)
  in
  Printf.sprintf "(job\n  (name %s)\n  (logic %s)\n  (proofs %s))"
    j.job_name j.job_logic proofs_str
