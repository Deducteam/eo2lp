
module EO = struct
  include Syntax_eo
  include Parse_eo
end

module LP = struct
  include Syntax_lp
  include Translate
end
module Elab = Elaborate
module M = EO.M

let elaborate (env : EO.environment) (cs : EO.command list)
  : Elab.command list =
  let f eo =
    Printf.printf
      "Elaborating:\n%s\n"
      (EO.command_str eo);

    let eo' = Elab.elaborate_cmd env eo in
    if eo' != [] then
      Printf.printf
        "Done:\n%s\n\n"
        (List.map Elab.command_str eo' |> String.concat "\n");
    eo'
  in
    List.concat_map f cs

let translate (eos : Elab.command list) : LP.command list =
  List.concat_map (fun eo ->
    Printf.printf
      "Translating:\n%s\n"
      (Elab.command_str eo);

    let lps = LP.translate_command eo in
    Printf.printf
      "Done:\n%s\n\n"
      (String.concat "\n" (List.map LP.lp_command_str lps));
    lps
) eos

let write (lps : LP.command list) : unit =
  let ch = open_out "lp/out.lp" in
  output_string ch
    (String.concat "\n" [
    "require Stdlib.Bool as B;";
     "symbol Bool ≔ B.bool;";
     "symbol true ≔ B.true;";
     "symbol false ≔ B.false;\n\n";
    ]);
  output_string ch "require open Stdlib.HOL;\n";
  output_string ch "require eo2lp.Core as eo;\n";
  output_string ch "symbol ▫ [x y] ≔  eo.app [x] [y];\n";
  output_string ch "notation ▫ infix left 5;\n\n";

  let f lp =
    output_string ch (LP.lp_command_str lp);
    output_char ch '\n'
  in
    List.iter f lps;
    close_out ch

let proc (env : EO.environment) (p : EO.path) : LP.command list =
  match List.assoc_opt p env with
  | Some eos -> translate (elaborate env eos)
  | None -> failwith "Can't find path in environment."

let core : Elab.command list =
  let eos =
    EO.parse_eo_file (Sys.getcwd (), "./eo/Core.eo")
  in
    (elaborate [] eos)

let env : EO.environment =
  Parse_eo.parse_eo_dir "./cpc-mini"

let main () =
  let lps = proc env ["theories";"Arith"] in
  write lps


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
