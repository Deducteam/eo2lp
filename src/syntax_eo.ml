open Literal

module S = String
module M = Map.Make(S)

module L = struct
  include List
  let chop (xs : 'a list) : ('a list * 'a) =
    let n = List.length xs in
    (take (n-1) xs, nth xs (n-1))
end

(* ---------------------------------------------- *)
type term =
  | Symbol of string
  | Literal of literal
  | Apply of string * (term list)
  | Bind of string * (var list) * term
and var = (string * term)
and case = (term * term)

type attr =
  (* constant attributes *)
  | RightAssocNil of term | LeftAssocNil of term
  | LeftAssocNilNSN of term | RightAssocNilNSN of term
  | RightAssocNSN of term | LeftAssocNSN of term
  | RightAssoc | LeftAssoc
  | ArgList of string
  | Chainable of string
  | Pairwise of string
  | Binder of string
  | LetBinder of term
  (* parameter attributes *)
  | Implicit | Opaque | List
  | Syntax of term | Restrict of term

and premises =
  | Simple of term list
  | PremiseList of term * term
and conclusion =
  | Conclusion of term
  | ConclusionExplicit of term
and rule_dec =
  {
    assm : term option;
    prem : premises option;
    args : term list;
    reqs : case list;
    conc : conclusion;
  }
and sorry = Sorry (* `:sorry` attribute for `declare-rule`.*)
and path = string list (* type of paths for `include`. *)

type param = string * term * (attr list)
type const =
  | Decl of param list * term * attr option
  | Defn of param list * term
  | Prog of (param list * term) * (param list * case list)
  | Rule of param list * term * term list * term list * case list * term
  (* Rule (ps,assm,prems,args,reqs,conc)  *)
type signature = (string * const) list
type context = signature * param list
(* ---------------------------------------------- *)

(* ---- contexts: `param list` and `signature`. ---- *)
(* Note: eo::List::cons and eo::List::nil are NOT builtins because they need
   n-ary expansion via :right-assoc-nil during elaboration *)
let is_builtin (s : string) : bool =
  s = "->" || s = "Type" || s = "_" || s = "as"
  || (S.starts_with ~prefix:"eo::" s
      && s <> "eo::List::cons"
      && s <> "eo::List::nil")

let is_name (s,_,_ : param) (s' : string) =
  (s = s')
let is_attr (_,_,pas : param) (pa : attr) =
  List.mem pa pas
let is_typ (_,ty,_ : param) (ty' : term) =
  ty = ty'

let prm_find (s : string) =
  L.find_opt (fun p -> is_name p s)
let prm_mem (s : string) =
  L.exists (fun p -> is_name p s)
let prm_typ (s : string) (ty : term) =
  L.exists (fun p -> is_name p s && is_typ p ty)
let prm_has_attr (s : string) (pa : attr) =
  L.exists (fun p -> is_name p s && is_attr p pa)


(* ---------------------------------------------- *)

(* ---- terms: application, substitution. ---- *)
let app_ho : term -> term -> term =
  fun t t' -> Apply ("_", [t;t'])

let app_ho_list : term -> term list -> term =
  fun t ts -> L.fold_left app_ho t ts

let app_raw : term -> term list -> term =
  fun t ts ->
    match t,ts with
    | (Symbol s, []) -> Symbol s
    | (Symbol s, ts) -> Apply (s, ts)
    | (Apply (s,ts), ts') -> Apply (s, L.append ts ts')
    | _ -> app_ho_list t ts

let rec subst : term -> string -> term -> term =
  fun t s t' ->
    match t with
    | Literal _ -> t
    | Symbol s' -> if (s = s') then t' else t
    | Apply (s', ts) ->
      let ts' = L.map (fun u -> subst u s t') ts in
      if (s = s')
        then app_ho_list t' ts'
        else Apply (s', ts')
    | Bind (b,xs,body) ->
      let ys = L.map (fun (x,tx) -> (x, subst tx s t')) xs in
      Bind (b,ys, subst body s t')

let rec splice (ps,t,ts : param list * term * term list)
  : (param list * term * term list) =
  match ps, ts with
  | (([],_)|(_,[])) -> (ps, t, ts)
  | ((s,_, atts) :: ps, ts) when List.mem Implicit atts ->
      splice (ps, t, ts)
  | ((s,_,_) :: ps, t' :: ts) ->
      splice (ps, subst t s t', ts)

let rec is_kind : term -> bool =
  function
  | Symbol "Type" -> true
  | Apply ("->", ts) -> L.exists is_kind ts
  | _ -> false
(* ---------------------------------------------- *)

(* ---- free variables ---- *)
module Set = Set.Make(String)
let rec params_in (ps : param list) : term -> Set.t =
  function
  | Literal _ -> Set.empty
  | Symbol s ->
    if prm_mem s ps then Set.singleton s else Set.empty
  | Apply (s,ts) ->
    let xs =
      L.fold_left
        (fun acc t -> Set.union acc (params_in ps t))
        Set.empty ts
    in
      if prm_mem s ps
        then Set.union (Set.singleton s) xs
        else xs
  | Bind (_, vs, t) ->
    let xs =
      L.fold_left
        (fun acc (_,t) -> Set.union acc (params_in ps t))
        Set.empty vs
    in
      Set.union xs (params_in ps t)

let rec is_free (s : string) : term -> bool =
  function
  | Symbol s' -> s = s'
  | Apply (s',ts) -> (s = s') || L.exists (is_free s) ts
  | Literal _ -> false
  | Bind (s, vs, t) ->
    let b1 = List.exists (fun (_,ty) -> is_free s ty) vs
    and b2 = is_free s t in (b1 || b2)
(* ---------------------------------------------- *)

(* ---- handling programs ---- *)
let prog_ty
  (doms,ran : term list * term) : term
=
  Apply ("->", List.append doms [ran])

let prog_ty_params (t : term)
  : param list -> param list =
  let f (s,ty,_) =
    if is_free s t then
      Some (s, ty, [Implicit])
    else
      None
  in
    L.filter_map f

let prog_cs_params (cs : case list)
  : param list -> param list =
  let f ((s,ty,_) as p) =
    let g (t,t') = is_free s t || is_free s t' in
    (* Include param if:
       1. It's free in the case terms, OR
       2. It has type Type (it's a type variable used to type other params) *)
    if L.exists g cs || ty = Symbol "Type" then (Some p) else None
  in
    L.filter_map f

(* ---------------------------------------------- *)


(* map a literal to its category *)
let lit_cat_of : literal -> lit_category =
  function
  | Numeral _  -> NUM
  | Decimal _  -> DEC
  | Rational _ -> RAT
  | Binary _   -> BIN
  | Hexadecimal _ -> HEX
  | String _      -> STR

(* ------------------------------------------------*)

(* ---- pretty printing -------- *)
let opt_newline (f : 'a -> string) (x_opt : 'a option) =
  match x_opt with
  | Some x -> Printf.sprintf "  %s\n" (f x)
  | None -> ""

let opt_str (f : 'a -> string) =
  Option.fold ~none:"" ~some:f

let opt_suffix_str (f : 'a -> string) =
  Option.fold ~none:"" ~some:(fun x -> " " ^ (f x))



let list_str (f : 'a -> string) =
  fun xs -> (String.concat " " (List.map f xs))

let list_suffix_str (f : 'a -> string) =
  function
  | [] -> ""
  | ys -> " " ^ (list_str f ys)

let rec
  var_str = fun (str,t) ->
    Printf.sprintf "(%s %s)"
      str (term_str t)
and
  const_attr_str = function
  | RightAssoc -> ":right-assoc"
  | LeftAssoc  -> ":left-assoc"
  | RightAssocNil t ->
      Printf.sprintf ":right-assoc-nil %s" (term_str t)
  | LeftAssocNil t ->
      Printf.sprintf ":left-assoc-nil %s" (term_str t)
  | RightAssocNilNSN t ->
      Printf.sprintf ":right-assoc-nil-non-singleton-nil %s" (term_str t)
  | LeftAssocNilNSN t ->
      Printf.sprintf ":left-assoc-nil-non-singleton-nil %s" (term_str t)
  | RightAssocNSN t ->
      Printf.sprintf ":right-assoc-non-singleton-nil %s" (term_str t)
  | LeftAssocNSN t ->
      Printf.sprintf ":left-assoc-non-singleton-nil %s" (term_str t)
  | Chainable s ->
      Printf.sprintf ":chainable %s" s
  | Binder s ->
      Printf.sprintf ":binder %s" s
  | Pairwise s ->
      Printf.sprintf ":pairwise %s" s
  | ArgList s ->
      Printf.sprintf ":arg-list %s" s
  | LetBinder t ->
      Printf.sprintf ":let-binder %s" (term_str t)
  | Implicit -> ":implicit"
  | Opaque -> ":opaque"
  | List -> ":list"
  | Syntax t -> Printf.sprintf ":syntax %s" (term_str t)
  | Restrict t -> Printf.sprintf ":restrict %s" (term_str t)
and
  term_str = function
  | Symbol str  -> str
  | Literal l   -> literal_str l
  | Bind (str, xs, t) ->
      let xs' = List.map var_str xs in
      Printf.sprintf "(%s (%s) %s)"
        str (String.concat ", " xs')
        (term_str t)
  | Apply (s, ts) ->
      Printf.sprintf "(%s %s)"
        s (String.concat " " (List.map term_str ts))
and term_list_str = fun ts ->
  String.concat " " (List.map term_str ts)

let param_str (s,t,atts) =
  Printf.sprintf "(%s %s%s)"
    s (term_str t)
    (list_suffix_str const_attr_str atts)

let case_str (t,t') =
  Printf.sprintf "(%s %s)"
    (term_str t)
    (term_str t')

let case_list_str : case list -> string =
  list_str case_str

let premises_str = function
  | Simple ts ->
      Printf.sprintf ":premises %s"
      (term_list_str ts)
  | PremiseList (t, t') ->
      Printf.sprintf ":premsie-list %s %s"
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

let rule_dec_str ({assm; prem; args; reqs; conc} : rule_dec) : string =
  Printf.sprintf "%s%s%s%s%s"
    (opt_newline assumption_str assm)
    (opt_newline premises_str prem)
    (opt_newline arguments_str (Some args))
    (opt_newline reqs_str (Some reqs))
    (opt_newline conclusion_str (Some conc))

let const_str : (string * const) -> string =
  function
  | s, Decl (ps,t,ao) ->
    Printf.sprintf "(decl %s (%s) %s (%s))"
      s (list_str param_str ps)
      (term_str t)
      (opt_str const_attr_str ao)
  | s, Defn (ps,t) ->
    Printf.sprintf "(defn %s (%s) %s)"
      s (list_str param_str ps)
      (term_str t)
  | s, Prog ((ps,t), (qs,cs)) ->
    Printf.sprintf "(prog %s ((%s) %s) (..))"
      s (list_str param_str ps)
      (term_str t)
      (* (list_str param_str qs) *)
      (* (case_list_str cs) *)

 let sig_str : signature -> string =
   fun sgn -> S.concat "\n" (L.map const_str sgn)

(* ------------------------------------------------------ *)
type sort_dec =
  | SortDec of string * int
and sel_dec =
  | SelDec of string * term
and cons_dec =
  | ConsDec of string * (sel_dec list)
and dt_dec =
  | DatatypeDec of cons_dec list

let sort_dec_str = function
  | SortDec (s,n) ->
      Printf.sprintf "(%s %d)" s n
and sel_dec_str = function
  | SelDec (s,t) ->
      Printf.sprintf "(%s %s)" s (term_str t)
let cons_dec_str = function
  | ConsDec (s, xs) ->
      Printf.sprintf "(%s %s)"
        s
        (String.concat " " (List.map sel_dec_str xs))
let dt_dec_str = function
  | DatatypeDec xs ->
      Printf.sprintf "(%s)"
        (String.concat " " (List.map cons_dec_str xs))

(* ------------------------------------------------------ *)
type common_command =
  | DeclareConst     of string * term * (attr option)
  | DeclareDatatype  of string * dt_dec
  | DeclareDatatypes of (sort_dec list) * (dt_dec list)
  | Echo             of string option
  | Exit
  | Reset
  | SetOption        of string

type command =
  | Assume            of string * term
  | AssumePush        of string * term
  | DeclareConsts     of lit_category * term
  | DeclareParamConst of string * param list * term * (attr option)
  | DeclareRule       of string * param list * rule_dec * (sorry option)
  | Define            of string * param list * term * (term option)
  | Include           of path
  | Program           of string
                       * (param list * term)
                       * (param list * case list)
  | Reference         of string * string option
  | Step              of string * term * string * term list * term list
  | StepPop           of string * term * string * term list * term list
  | Common            of common_command


let common_command_str = function
  | DeclareConst (s,t,att) ->
      Printf.sprintf "(declare-const %s %s %s)"
        s (term_str t)
        (opt_suffix_str const_attr_str att)
  | DeclareDatatype (s,dt) ->
      Printf.sprintf "(declare-datatype %s %s)"
        s (dt_dec_str dt)
  | DeclareDatatypes (xs,ys) ->
      Printf.sprintf "(declare-datatypes (%s) (%s))"
        (String.concat "" (List.map sort_dec_str xs))
        (String.concat "" (List.map dt_dec_str ys))
  | Echo (str_opt) ->
      Printf.sprintf "(echo%s)"
        (opt_suffix_str (fun x -> x) str_opt)
  | Reset -> "(reset)"
  | SetOption x ->
      Printf.sprintf "(set-option %s)" (x)
  | Exit -> "(exit)"

let command_str = function
  | Assume (s,t) ->
      Printf.sprintf "(assume %s %s)"
        s (term_str t)
  | AssumePush (s,t) ->
      Printf.sprintf "(assume-push %s %s)"
        s (term_str t)
  | DeclareConsts (lc,t) ->
      Printf.sprintf "(declare-consts %s %s)"
        (lit_category_str lc)
        (term_str t)
  | DeclareParamConst (s,ps,t,att_opt) ->
      Printf.sprintf
        "(declare-parameterized-const %s (%s) %s%s)"
        s (list_str param_str ps)
        (term_str t)
        (opt_suffix_str const_attr_str att_opt)
  | DeclareRule (s,xs,rdec,sorry_opt) ->
      Printf.sprintf "(declare-rule %s (%s)\n%s\n%s)"
        s (list_str param_str xs)
        (rule_dec_str rdec)
        (opt_newline (fun _ -> ":sorry") sorry_opt)
  | Define (s,xs,t,t_opt) ->
      Printf.sprintf "(define %s (%s) %s%s)"
        s (list_str param_str xs)
        (term_str t)
        (opt_suffix_str term_str t_opt)
  | Include p ->
      Printf.sprintf "(include %s)" (String.concat "." p)
  | Program (s,(ps,ty),(qs,cs)) ->
      Printf.sprintf
        "(program %s\n:type (%s) %s\n:cases (%s) (%s))"
        s (list_str param_str ps) (term_str ty)
          (list_str param_str qs) (case_list_str cs)
  | Reference (str, s_opt) ->
      Printf.sprintf "(reference %s %s)"
        str (opt_str (fun x -> x) s_opt)
  | Step (s,t_opt,s',ts,ts') ->
      Printf.sprintf "(step %s %s %s%s%s)"
        s (term_str t_opt) s'
        (list_suffix_str term_str ts)
        (list_suffix_str term_str ts')
  | StepPop (s,t_opt,s',ts,ts') ->
      Printf.sprintf "(step-pop %s %s %s%s%s)"
        s (term_str t_opt) s'
        (list_suffix_str term_str ts)
        (list_suffix_str term_str ts')
  | Common c ->
      common_command_str c

(*
let mk_proof (t : term) : term =
  Apply("Proof", [t])

let is_builtin (str : string) : bool =
  String.starts_with ~prefix:"eo::" str

let is_prog (str : string) : bool =
  not (str = "eo::List::cons" || str = "eo::List::nil")
  &&
  (is_builtin str || String.starts_with ~prefix:"$" str)

let mk_aux_str (str : string) : string =
  (str ^ "_aux")

let mk_reqs_tm ((t1,t2) : term * term) (t3 : term) : term =
  Apply ("eo::requires", [t1;t2;t3])

let mk_reqs_list_tm (cs : case list) (t : term) : term =
  List.fold_left (fun acc c -> mk_reqs_tm c acc) t cs

let mk_conc_tm (cs : case list) : conclusion -> term =
  function
  | Conclusion t ->
      mk_reqs_list_tm cs t
  | ConclusionExplicit t ->
      Printf.printf "WARNING! --- :conclusion-explicit\n";
      mk_reqs_list_tm cs t

let mk_arg_vars (arg_tys : term list) : (string * term) list =
  let arg_sym =
    (fun i t -> (("α" ^ string_of_int i), t))
  in
    List.mapi arg_sym arg_tys *)

(* ============================================================
   Signature Graph (DAG) for managing file dependencies
   ============================================================ *)

module PathMap = Map.Make(struct
  type t = path
  let compare = compare
end)

(* A node in the signature graph represents a single .eo file *)
type sig_node = {
  node_path : path;           (* logical path, e.g., ["theories"; "Builtin"] *)
  node_file : string;         (* absolute file path *)
  node_includes : path list;  (* direct dependencies (include statements) *)
  node_sig : signature;       (* symbols defined in THIS file only *)
}

(* The signature graph: a DAG of sig_nodes keyed by path *)
type sig_graph = sig_node PathMap.t

(* Result of parsing a single file (before graph construction) *)
type file_parse_result = {
  fpr_path : path;
  fpr_file : string;
  fpr_includes : path list;
  fpr_sig : signature;
}

(* Pretty printing for sig_node *)
let sig_node_str (n : sig_node) : string =
  Printf.sprintf "{ path: %s\n  file: %s\n  includes: [%s]\n  symbols: %d }"
    (S.concat "." n.node_path)
    n.node_file
    (S.concat ", " (L.map (S.concat ".") n.node_includes))
    (L.length n.node_sig)

let path_str : path -> string = S.concat "."

(* Get all paths in topological order (dependencies first) *)
let topo_sort (graph : sig_graph) : path list =
  let visited = Hashtbl.create (PathMap.cardinal graph) in
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

(* Flatten a graph into a single signature (topological order) *)
let flatten_graph (graph : sig_graph) : signature =
  let paths = topo_sort graph in
  L.concat_map (fun p ->
    match PathMap.find_opt p graph with
    | Some node -> node.node_sig
    | None -> []
  ) paths

(* Core/prelude signature - symbols that are always available *)
let core_prelude : signature ref = ref []

let set_core_prelude (sig_ : signature) : unit =
  core_prelude := sig_

(* Embedded Core.eo source - always available.
   All symbols are prefixed with eo:: to match usage in Eunoia files. *)
let core_eo_source = {|
(declare-const eo::Bool Type)
(declare-const eo::true eo::Bool)
(declare-const eo::false eo::Bool)

(declare-const eo::String Type)
(declare-const eo::Z Type)
(declare-const eo::Q Type)

; Core operators
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

; Boolean operators
(declare-const eo::and (-> eo::Bool eo::Bool eo::Bool))
(declare-const eo::or (-> eo::Bool eo::Bool eo::Bool))
(declare-const eo::xor (-> eo::Bool eo::Bool eo::Bool))
(declare-const eo::not (-> eo::Bool eo::Bool))

; Arithmetic operators
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

; String operators
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

; Conversion operators
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


; List operators
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

(* Get the full signature visible at a node (includes + local) *)
let full_sig_at (graph : sig_graph) (path : path) : signature =
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
  (* Include core prelude + collected signatures *)
  !core_prelude @ collect path
