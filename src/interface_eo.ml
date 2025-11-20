open Syntax_eo

type defn =
  | Term of term
  | Cases of cases

let defn_str (d : defn) =
  match d with
  | Term t   -> term_str t
  | Cases cs -> Printf.sprintf "CASES[%s]" (cases_str cs)

type judgement =
  | LitJ  of lit_category * term
  | TypeJ of symbol * param list * term
  | DefnJ of symbol * param list * defn
  | AttrJ of symbol * param list * attr


let params_str (ps : params) : string =
  (if ps = [] then "⋅" else (list_str param_str ps))

let judgement_str (j : judgement) =
  match j with
  | LitJ (lc, t) ->
    Printf.sprintf "(%s : %s)"
      (lit_category_str lc)
      (term_str t)
  | TypeJ (s, ps, t) ->
    Printf.sprintf "(%s[%s] : %s)"
      (symbol_str s)
      (params_str ps)
      (term_str t)
  | DefnJ (s, ps, d) ->
    Printf.sprintf "(%s[%s] ≔ %s)"
      (symbol_str s)
      (params_str ps)
      (defn_str d)
  | AttrJ (s, ps, att) ->
    Printf.sprintf "(%s[%s] ⋈ %s)"
      (symbol_str s)
      (params_str ps)
      (attr_str att)

type jlist = judgement list

let jlist_str js =
  let js_str = String.concat "\n  " (List.map judgement_str js) in
  Printf.sprintf "[\n  %s\n]" js_str

let mk_atts_jlist : symbol -> params -> atts -> jlist =
  fun s xs ys ->
    (List.map (fun y -> AttrJ (s, xs, y)) ys)

let proc_common_command : common_command -> jlist =
  function
  | DeclareConst (s,t,xs)  ->
    (TypeJ (s,[],t)) :: (mk_atts_jlist s [] xs)
  | DeclareDatatype  (_s,_dt)    -> []
  | DeclareDatatypes (_sts,_dts) -> []
  | Echo             (_str_opt) -> []
  | Exit                       -> []
  | Reset                      -> []
  | SetOption        (_a)       -> []

let arrow_sym       : symbol = (Symbol "->")
let proof_sym       : symbol = (Symbol "Proof")
let eo_requires_sym : symbol = (Symbol "eo::requires")
let bool_sym        : symbol = (Symbol "Bool")

let mk_proof_tm (t : term) : term =
  Apply (proof_sym, [t])

(* TODO. actually implement *)
let ty_of (t : term) : term =
  Sym (Symbol ("TY[" ^  term_str t ^ "]"))

let mk_arrow_ty (ts : term list) (t : term) : term =
  Apply (arrow_sym, List.append ts [t])

let mk_aux_sym (Symbol str : symbol) : symbol =
  Symbol (str ^ "_aux")

let mk_reqs_tm ((t1,t2) : term * term) (t3 : term) : term =
  Apply (eo_requires_sym, [t1;t2;t3])

let mk_reqs_list_tm (cs : cases) (t : term) : term =
  List.fold_left (fun acc c -> mk_reqs_tm c acc) t cs

let mk_conc_tm (cs : cases) : conclusion -> term =
  function
  | Conclusion t ->
      mk_reqs_list_tm cs t
  | ConclusionExplicit t ->
      Printf.printf "WARNING! --- :conclusion-explicit\n";
      mk_reqs_list_tm cs t

let mk_aux_jlist
  (s : symbol) (ps : params)
  (arg_tms : term list) (arg_tys : term list)
  (conc_tm : term) : jlist
=
  let s'     = mk_aux_sym s in
  let aux_ty = mk_arrow_ty arg_tys (Sym bool_sym) in
  let aux_cs = [(Apply (s',arg_tms), conc_tm)] in
  [
    TypeJ (s', ps, aux_ty);
    DefnJ (s', ps, Cases aux_cs)
  ]

let mk_arg_vars (arg_tys : term list) =
  let arg_sym =
    (fun i t -> (Symbol ("α" ^ string_of_int i), t))
  in
    List.mapi arg_sym arg_tys

let proc_eo_command (cmd : eo_command) : jlist =
  match cmd with
  | Assume (s,t)          -> [TypeJ (s, [], t)]
  | AssumePush (_,_)      -> []
  | DeclareConsts (lc,t)  -> [LitJ (lc, t)]
  | DeclareParamConst (s,xs,t,ys) ->
     (TypeJ (s, xs, t)) :: (mk_atts_jlist s xs ys)
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
        (
          mk_aux_jlist s ps ts arg_tys conc_tm,
          mk_arg_vars arg_tys
        )
      | None -> ([], [])
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
      if aux_jset = [] then
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
      | ts -> mk_arrow_ty ts conc_ty
    in

    let main_jset =
      let arg_ps =
        List.map (fun (s,t) -> Param (s,t,[])) arg_vars
      in let ps' =
        List.append ps arg_ps
      in
        (TypeJ (s, ps', main_ty))
        :: (mk_atts_jlist s ps' ys)
    in
      List.append aux_jset main_jset

  | Define (s,xs,t,t_opt) ->
    let tj =
      match t_opt with
      | Some t -> [TypeJ (s, xs, t)]
      | None   -> []
    in
      List.append tj [DefnJ (s, xs, Term t)]

  | Include s -> []

  | Program (s,xs,(ts,t),cs) ->
    [
      TypeJ (s, xs, mk_arrow_ty ts t);
      DefnJ (s, xs, Cases cs)
    ]

  | Reference (_, _) -> []
  | Step (s, t_opt, s', prems_opt, args_opt) ->
    let tj =
      match t_opt with
      | Some t -> [TypeJ (s, [], t)]
      | None   -> []
    in
    let prem_ts =
      match prems_opt with
      | Some (Premises ts) -> ts
      | None               -> []
    in
    let args_ts =
      match args_opt with
      | Some (Args ts) -> ts
      | None           -> []
    in
    let def = Apply (s', List.append args_ts prem_ts) in
    List.append tj [DefnJ (s, [], Term def)]
  | StepPop (_,_,_,_,_) -> []
  | Common c -> proc_common_command c


module Symbol = struct
  type t = symbol
  let compare = compare
end

module SMap = Map.Make(Symbol)
type 'a smap = 'a SMap.t
