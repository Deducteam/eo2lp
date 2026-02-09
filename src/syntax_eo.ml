(* syntax_eo.ml
   Eunoia AST definitions and core operations *)

open Literal

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
  | Rule of param list * rule_dec
  | Assume of term                            (* formula being assumed *)
  | AssumePush of term                        (* push assumption onto scope stack *)
  | Step of string * term list * term list * term option
         (* rule_name, premises, args, optional conclusion *)
  | StepPop of string * term list * term list * term option
         (* like Step but pops one assumption from scope stack *)

(* Builtin constants *)

module Builtin = struct
  let ty_type   = "Type"
  let ty_arrow  = "->"
  let ty_app    = "_"
  let ty_as     = "as"
  let eo_and    = "eo::and"
  let eo_or     = "eo::or"
  let eo_xor    = "eo::xor"
  let eo_add    = "eo::add"
  let eo_mul    = "eo::mul"
  let eo_define = "eo::define"
  let eo_typeof = "eo::typeof"
  let eo_var    = "eo::var"
  let eo_as     = "eo::as"
  let eo_quote  = "eo::quote"
  let eo_requires = "eo::requires"
  let eo_list_cons   = "eo::List::cons"
  let eo_list_nil    = "eo::List::nil"
  let eo_list_concat = "eo::List::concat"
  let eo_list_concat_old = "eo::list_concat"
  let eo_nil            = "eo::nil"
  let eo_nil_assumption = "eo::nil_assumption"
  let eo_premise_list   = "eo::premise_list"
  let eo_int  = "eo::Int"
  let eo_real = "eo::Real"
end

let is_builtin s =
  s = Builtin.ty_arrow || s = Builtin.ty_type
  || s = Builtin.ty_app || s = Builtin.ty_as
  || String.starts_with ~prefix:"eo::" s

(* Parameter queries *)

let is_name (s, _, _) s' = s = s'
let is_attr (_, _, pas) pa = List.mem pa pas
let is_typ  (_, ty, _) ty' = ty = ty'

let prm_find s = List.find_opt (fun p -> is_name p s)
let prm_mem  s = List.exists   (fun p -> is_name p s)

let prm_typ s ty =
  List.exists (fun p -> is_name p s && is_typ p ty)

let prm_has_attr s pa =
  List.exists (fun p -> is_name p s && is_attr p pa)

(* Term operations *)

let app_ho t t' = Apply (Builtin.ty_app, [t; t'])

let app_ho_list t ts = List.fold_left app_ho t ts

let rec subst t s t' =
  match t with
  | Literal _ -> t
  | Symbol s' ->
    if s = s' then t' else t
  | Apply (s', ts) ->
    let ts' = List.map (fun u -> subst u s t') ts in
    if s = s' then app_ho_list t' ts'
    else Apply (s', ts')
  | Bind (b, xs, body) ->
    let ys =
      List.map (fun (x, tx) -> (x, subst tx s t')) xs
    in
    Bind (b, ys, subst body s t')

module Set = Set.Make(String)

(* Program helpers *)

let rec returns_type = function
  | Symbol s when s = Builtin.ty_type -> true
  | Apply (s, ts) when s = Builtin.ty_arrow && ts <> [] ->
    returns_type (List.hd (List.rev ts))
  | _ -> false

(* Placeholder name → concrete type, populated by declare-consts *)
let lit_alias_table : (string, term) Hashtbl.t = Hashtbl.create 4

let placeholder_of_cat = function
  | Literal.NUM -> Builtin.eo_int
  | Literal.RAT -> Builtin.eo_real
  | Literal.STR -> "eo::String"
  | _           -> failwith "placeholder_of_cat: unsupported"

let register_lit_alias cat ty =
  Hashtbl.replace lit_alias_table (placeholder_of_cat cat) ty

(* Substitute placeholder type names in an Eunoia term *)
let rec subst_lit_aliases = function
  | Symbol s as t ->
    (match Hashtbl.find_opt lit_alias_table s with
     | Some replacement -> replacement
     | None -> t)
  | Apply (s, ts) -> Apply (s, List.map subst_lit_aliases ts)
  | Bind (b, vs, body) -> Bind (b, vs, subst_lit_aliases body)
  | t -> t

(* Datatype declarations *)

type sort_dec = SortDec of string * int

and sel_dec  = SelDec  of string * term
and cons_dec = ConsDec of string * sel_dec list
and dt_dec   = DatatypeDec of cons_dec list

(* ============================================================
   Signature and Module Graph
   ============================================================ *)

(* Simple flat signature: association list of name -> symbol *)
type signature = (string * symbol) list

(* Context for elaboration: full signature + local parameters *)
type context = signature * param list

(* Module graph for tracking file structure and includes *)
module PathMap = Map.Make(struct
  type t = path
  let compare = compare
end)

type sig_node = {
  node_path     : path;
  node_file     : string;
  node_includes : path list;
  node_sig      : signature;
}

type sig_graph = sig_node PathMap.t

let path_str : path -> string = String.concat "."

(* Core prelude - symbols available in all modules *)
let core_prelude : signature ref = ref []

let set_core_prelude sig_ = core_prelude := sig_

(* Get full signature at a path by collecting transitive includes *)
let full_sig_at graph path =
  let visited = Hashtbl.create 16 in
  let rec collect_rev p acc =
    if Hashtbl.mem visited p then acc
    else begin
      Hashtbl.add visited p ();
      match PathMap.find_opt p graph with
      | None ->
        Printf.eprintf "warning: missing dependency %s (included from %s)\n%!"
          (path_str p) (path_str path);
        acc
      | Some node ->
        let acc = List.fold_left (fun acc dep -> collect_rev dep acc) acc node.node_includes in
        List.fold_left (fun acc sym -> sym :: acc) acc node.node_sig
    end
  in
  !core_prelude @ List.rev (collect_rev path [])

(* Topological sort of modules in the graph *)
let topo_sort_graph (graph : sig_graph) : path list =
  let visiting = Hashtbl.create (PathMap.cardinal graph) in
  let visited = Hashtbl.create (PathMap.cardinal graph) in
  let result = ref [] in

  let rec visit path =
    if Hashtbl.mem visited path then ()
    else if Hashtbl.mem visiting path then ()  (* cycle - skip *)
    else begin
      Hashtbl.add visiting path ();
      (match PathMap.find_opt path graph with
       | Some node -> List.iter visit node.node_includes
       | None -> ());
      Hashtbl.remove visiting path;
      Hashtbl.add visited path ();
      (* Only emit paths that are actually in the graph *)
      if PathMap.mem path graph then
        result := path :: !result
    end
  in
  PathMap.iter (fun path _ -> visit path) graph;
  List.rev !result

(* ============================================================
   Job files for proof processing
   ============================================================ *)

type proof_source =
  | ProofDir of string
  | ProofFiles of string list

type job = {
  job_name   : string;
  job_logic  : string;
  job_proofs : proof_source;
}

(* ============================================================
   Symbol dependency analysis for minimal CPC generation
   ============================================================ *)

(* Extract all symbol references from a term *)
let rec symbols_in_term acc = function
  | Symbol s -> Set.add s acc
  | Literal _ -> acc
  | Apply (s, ts) ->
    let acc = Set.add s acc in
    List.fold_left symbols_in_term acc ts
  | Bind (b, vs, body) ->
    let acc = Set.add b acc in
    let acc = List.fold_left (fun a (_, ty) -> symbols_in_term a ty) acc vs in
    symbols_in_term acc body

(* Extract all symbol references from a list of terms *)
let symbols_in_terms ts =
  List.fold_left symbols_in_term Set.empty ts

let term_contains_symbol name t =
  Set.mem name (symbols_in_term Set.empty t)
