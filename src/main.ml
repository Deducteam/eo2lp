
module EO = struct
  include Syntax_eo
  include Parse_eo
end

module Elab = Elaborate

let cpc_root  = "../cvc5/proofs/eo/cpc"
let cpc_mini  =
  let con fp = Filename.concat cpc_root fp in
  let fps = ["programs/Utils.eo"] in
  List.map con fps
(*
let cpc_eos : EO.command list =
  List.concat_map EO.parse_eo_file cpc_mini *)

let test_eo : EO.command list =
  EO.parse_eo_file "src/test.eo"

let cpc_elab : Elab.command list =
  let f eo =
    Printf.printf
      "Elaborating:\n%s\n"
      (EO.command_str eo);

    let eo' = Option.map Elab.bind_mvars (Elab.elaborate_cmd eo) in
    if Option.is_some eo' then
      Printf.printf
        "Done:\n%s\n\n"
        (Elab.command_str (Option.get eo'));
    eo'
  in
    List.filter_map f test_eo

let tctx = (!Elab._sig, [])
let tt : EO.term =
  Apply ("@Pair", [Symbol "Bool"; Symbol "Bool"])
(*
let proc_eo_file (fp : string) : (Elab.command list) =
  let eos = Parse_eo.parse_eo_file fp in
  let (_sig', eos') = Elab.elab_eo_file !EO._sig eos in
  eos'

let proc_cpc_mini : Elab.command list =
  List.concat_map proc_eo_file cpc_mini *)


(* let builtin_tys =
  let tm = Parse_eo.parse_eo_term in
  [
    ("eo::List", tm "Type");
    ("eo::List::cons", tm "(-> T eo::List eo::List)")
  ]
(* open Elaborate *)
let _sig : signature =
  {
    prm = M.empty;
    typ = M.of_list builtin_tys;
    def = M.empty;
    att = M.empty;
    lit = [];
  } *)


(* let gen_const (sgn : signature)
    (s : string) (ps : EO.param list) (ty : EO.term)
  : LP.command =
  let (s', ps', ty') =
    (
      translate_symbol s,
      translate_params (map (elab_param sgn) ps),
      translate_ty (elab_tm (sgn,ps) ty)
    )
  in
    Symbol (Some Constant, s', ps', Some ty', None)

(* ?TODO? split into gen_prog_sym and gen_prog_rule. *)
let gen_prog (sgn : signature)
    (s : string) (ps : EO.param list) (ty : EO.term)
    (cs : EO.cases) : LP.command list
=
  let (eps, ety) =
    (
      map (elab_param sgn) ps,
      elab_tm (sgn,ps) ty
    )
  in

  let vs = free_params eps ety in
  let vs' = List.map (fun (s,t) -> (s,t, Implicit)) vs in
  Printf.printf "ty params for %s with type %s are [%s].\n"
    s (eterm_str ety) (String.concat " " (List.map fst vs));

  let (s', ty_ps, ty', rl_ps, cs') =
    (
      translate_symbol s,
      translate_params vs',
      translate_ty ety,
      translate_params eps,
      translate_cases (elab_cases (sgn,ps) cs)
    )
  in
    List.append
      [LP.Symbol (Some Sequential, s', ty_ps, Some ty', None)]
      (if cs' = [] then [] else [LP.Rule (bind_pvars_cases rl_ps cs')])

let gen_defn (sgn : signature)
    (s : string) (ps : EO.param list)
    (def : EO.term) (ty_opt : EO.term option)
  : LP.command
=
  let (s', ps', def') =
    (
      translate_symbol s,
      translate_params (map (elab_param sgn) ps),
      translate_tm (elab_tm (sgn,ps) def)
    )
  in
  let ty_opt' = match ty_opt with
    | Some ty -> Some (translate_ty (elab_tm (sgn,ps) ty))
    | None -> None
  in
    Symbol (None, s', ps', ty_opt', Some def')

let gen_rdec (sgn : signature)
    (s : string) (ps : EO.param list)
      (prems_opt : EO.premises option)
      (args_opt : EO.arguments option)
      (reqs_opt : EO.reqs option)
      (conc : EO.conclusion)
  : ((LP.command * LP.command) option * LP.command)
=
  let (s', ps') =
    (
      translate_symbol s,
      translate_params (map (elab_param sgn) ps)
    )
  in
  (* if there are requirements, wrap the conclusion. *)
  let conc_tm =
    match reqs_opt with
    | Some (Requires cs) -> EO.mk_conc_tm cs conc
    | None               -> EO.mk_conc_tm [] conc
  in

  (* if there are arguments, gen aux judgements and fresh vars *)
  let (aux_cmds_opt, aux_vars, conc_ty) =
    match args_opt with
    | Some (Args ts) ->
      let arg_tys = List.map EO.ty_of ts in
      let s_aux   = "$" ^ s ^ "_aux" in
      let aux_ty  = EO.mk_arrow_ty arg_tys (Symbol "Bool") in
      let (s',ty') =
        (
          translate_symbol s_aux,
          translate_ty (elab_tm (sgn,ps) aux_ty)
        )
      in

      let cs  = [(EO.Apply (s_aux, ts), conc_tm)] in
      let cs' = translate_cases (elab_cases (sgn,ps) cs) in

      let aux_cmds =
        (
          LP.Symbol (None, s', [], Some ty', None),
          LP.Rule (bind_pvars_cases ps' cs')
        )
      in

      let vs = mk_aux_vars arg_tys in
      let ws = List.map (fun (s,_) -> EO.Symbol s) vs in
      let conc = EO.proof_of (EO.Apply (s_aux, ws)) in

      (Some aux_cmds, vs, conc)

    | None -> (None, [], EO.proof_of conc_tm)
    in

    (* build type of symbol for declared rule. *)
    let ty =
      match prems_opt with
      | Some (Simple (Premises ts)) ->
          let ts' = List.map EO.proof_of ts in
          EO.mk_arrow_ty ts' conc_ty
      | Some (PremiseList (_,_)) ->
          Printf.printf "WARNING! --- :premise-list\n";
          conc_ty
      | None -> conc_ty
    in

    let ty' = translate_ty (elab_tm (sgn,ps) ty) in
    let ty_cmd =
      LP.Symbol (None, s', ps', Some ty', None)
    in
      (aux_cmds_opt, ty_cmd)
 *)
