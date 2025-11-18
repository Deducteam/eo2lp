open Syntax_eo

type defn =
  | Term of term
  | Cases of cases

type judgement =
  | LitJ  of lit_category * term
  | TypeJ of symbol * param list * term
  | DefnJ of symbol * param list * defn
  | AttrJ of symbol * param list * attr

module SMap = Map.Make(String)
type eo_sig = judgement SMap.t

module Judgement = struct
  type t = judgement
  let compare = compare
end

module Jset = Set.Make(Judgement)
type jset = Jset.t

let mk_atts_jset : symbol -> param list -> attr list -> jset =
  fun s xs ys ->
  Jset.of_list
    (List.map (fun y -> AttrJ (s, xs, y)) ys)

let proc_common_command : common_command -> jset =
  function
  | DeclareConst (s,t,xs)  ->
    Jset.add (TypeJ (s,[],t)) (mk_atts_jset s [] xs)
  | DeclareDatatype  (s,dt)    -> Jset.empty
  | DeclareDatatypes (sts,dts) -> Jset.empty
  | Echo             (str_opt) -> Jset.empty
  | Exit                       -> Jset.empty
  | Reset                      -> Jset.empty
  | SetOption        (a)       -> Jset.empty

let arrow_sym       : symbol = (Symbol "->")
let proof_sym       : symbol = (Symbol "Proof")
let eo_requires_sym : symbol = (Symbol "eo::requires")

let bool_tm : term = Sym (Symbol "Bool")

let mk_proof_tm : term -> term =
  fun t -> Apply (proof_sym, [t])

(* TODO. actually implement *)
let ty_of : term -> term =
  fun t -> Sym (Symbol (term_str t ^ "_ty"))

let mk_arrow_tm : term list -> term -> term =
  fun ts t -> Apply (arrow_sym, List.append ts [t])

let mk_aux_sym : symbol -> symbol =
  fun (Symbol str) -> (Symbol (str ^ "_aux"))

let mk_reqs_tm : (term * term) -> term -> term =
  fun (t1,t2) t3 -> Apply (eo_requires_sym, [t1;t2;t3])

let mk_reqs_list_tm : cases -> term -> term =
  fun cs t ->
    List.fold_left (fun acc c -> mk_reqs_tm c acc) t cs

let mk_conc_tm (cs : cases) : conclusion -> term =
  function
  | Conclusion t ->
      mk_reqs_list_tm cs t
  | ConclusionExplicit t ->
      Printf.printf "WARNING! --- :conclusion-explicit\n";
      mk_reqs_list_tm cs t

let mk_aux_jset
  (s : symbol) (ps : params)
  (arg_tms : term list) (arg_tys : term list)
  (conc_tm : term) : jset
=
  let s' = mk_aux_sym s in
  let aux_ty = mk_arrow_tm arg_tys bool_tm in
  let aux_cs = [(Apply (s',arg_tms), conc_tm)] in
  Jset.of_list [
    TypeJ (s', ps, aux_ty);
    DefnJ (s', ps, Cases aux_cs)
  ]

let arg_sym : int -> term -> (symbol * term) =
  fun i t -> (Symbol ("α" ^ string_of_int i), t)

let mk_arg_vars (arg_tys : term list) =
  List.mapi arg_sym arg_tys

let proc_eo_command : eo_command -> jset =
  function
  | Assume (s,t) ->
    Jset.singleton (TypeJ (s, [], t))
  | AssumePush (s,t) ->
    Jset.empty
  | DeclareConsts (lc,t) ->
    Jset.singleton (LitJ (lc, t))
  | DeclareParamConst (s,xs,t,ys) ->
    Jset.add (TypeJ (s, xs, t)) (mk_atts_jset s xs ys)
  | DeclareRule (s,ps,rdec,ys) ->
    let
      RuleDec
        (_, prems_opt, args_opt, reqs_opt, conc) = rdec
    in

    (* if there are requirements, wrap the conclusion. *)
    let conc_tm =
      match reqs_opt with
      | Some (Requires cs) -> mk_conc_tm cs conc
      | None               -> mk_conc_tm [] conc
    in

    (* if there are arguments, gen aux judgements and fresh vars *)
    let (aux_jset, arg_vars) =
      match args_opt with
      | Some (Args ts) ->
        let arg_tys = List.map ty_of ts in
        (mk_aux_jset s ps ts arg_tys conc_tm,
         mk_arg_vars arg_tys)
      | None           -> (Jset.empty, [])
    in

    (* if there are premises, create rule ty accordingly *)
    let prem_tys =
      match prems_opt with
      | Some (Simple (Premises ts)) ->
        List.map mk_proof_tm ts
      | Some (PremiseList (_,_)) ->
        Printf.printf "WARNING! --- :premise-list\n"; []
      | None -> []
    in

    (* if aux gen, then generate conc ty accordingly. *)
    let conc_ty =
      if aux_jset = Jset.empty then
        mk_proof_tm conc_tm
      else
        let arg_var_tms =
          List.map (fun (s, _) -> Sym s) arg_vars
        in
          mk_proof_tm (Apply (mk_aux_sym s, arg_var_tms))
    in

    let main_ty =
      match prem_tys with
      | [] -> conc_ty
      | ts -> mk_arrow_tm ts conc_ty
    in

    let main_jset =
      let arg_ps =
        List.map (fun (s,t) -> Param (s,t,[])) arg_vars
      in let ps' =
        List.append ps arg_ps
      in
        Jset.add
        (TypeJ (s, ps', main_ty))
        (mk_atts_jset s ps' ys)
    in

      Jset.union aux_jset main_jset

  | Define (s,xs,t,t_opt) -> Jset.empty
  | Include s -> Jset.empty
  | Program (s,xs,(ts,t),tps) -> Jset.empty
  | Reference (str, s_opt) -> Jset.empty
  | Step (s,t_opt,s',sp_opt,args_opt) -> Jset.empty
  | StepPop (s,t_opt,s',sp_opt,args_opt) -> Jset.empty
  | Common c -> Jset.empty
