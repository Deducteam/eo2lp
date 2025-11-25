module EO = struct
  include Syntax_eo
end

module LP = struct
  include Syntax_lp
end

open Context_eo
(* open Elaborate *)

let _sig : signature =
  {
    atts = M.of_list [];
    typs = M.of_list [];
    defs = M.of_list [];
    prgs = M.of_list [];
  }

(* find eo files in dir *)
let find_eo_files (dir : string) : string list =
  Array.fold_left
    (fun acc name ->
      if Filename.check_suffix name ".eo" then
        (Filename.concat dir name) :: acc
      else
        acc
    )
    [] (Sys.readdir dir)


(* let atts_zip
  (s : string) (ps : EO.params) (xs : EO.attr list)
  : (EO.param list * EO.attr)
=
  List.map (fun x -> (s, (ps,x))) xs *)

let proc_common_command : EO.common_command -> unit =
  function
  | DeclareConst (s,t,xs)  ->
    _sig.typs <- M.add s ([],t) _sig.typs;
    (* if `xs : attr list` is non-empty, add the first attribute.*)
    if xs != [] then
      _sig.atts <- M.add s ([], List.hd xs) _sig.atts;

  | DeclareDatatype  (_s,_dt)    -> ()
  | DeclareDatatypes (_sts,_dts) -> ()
  | Echo             (_str_opt)  -> ()
  | Exit                         -> ()
  | Reset                        -> ()
  | SetOption        (_a)        -> ()

let mk_aux_vars (tys : EO.term list) =
  List.mapi
    (fun i ty -> (("α" ^ string_of_int i), ty))
    tys

let proc_ruledec
  (s : string) (ps : EO.params)
  : EO.rule_dec -> unit
=
  function
  | RuleDec (_, prems_opt, args_opt, reqs_opt, conc) ->

    (* if there are requirements, wrap the conclusion. *)
    let conc_tm =
      match reqs_opt with
      | Some (Requires cs) -> EO.mk_conc_tm cs conc
      | None               -> EO.mk_conc_tm [] conc
    in

    (* if there are arguments, gen aux judgements and fresh vars *)
    let (aux_vars, conc_ty) =
      match args_opt with
      | Some (Args ts) ->
        let arg_tys = List.map EO.ty_of ts in
        let s_aux   = "$" ^ s ^ "_aux" in
        let aux_ty  = EO.mk_arrow_ty arg_tys (Symbol "Bool") in
        let aux_cs  = [(EO.Apply (s_aux, ts), conc_tm)] in
        _sig.typs <- M.add s_aux ([], aux_ty) _sig.typs;
        _sig.prgs <- M.add s_aux ([], aux_cs) _sig.prgs;

        let vs = mk_aux_vars arg_tys in
        let ws = List.map (fun (s,_) -> EO.Symbol s) vs in
        let aux_app = EO.Apply (s_aux, ws) in
        (vs, EO.mk_proof_tm aux_app)

      | None -> ([], EO.mk_proof_tm conc_tm)
    in

    (* build type of symbol for declared rule. *)
    let main_ty =
      match prems_opt with
      | Some (Simple (Premises ts)) ->
        let ts' = List.map EO.mk_proof_tm ts in
        EO.mk_arrow_ty ts' conc_ty
      | Some (PremiseList (_,_)) ->
        Printf.printf "WARNING! --- :premise-list\n";
        conc_ty
      | None -> conc_ty
    in

    _sig.typs <- M.add s ([], main_ty) _sig.typs
    (* _sig.atts <-  *)


(* TODO. deprecate by just doing this at parse-time *)
let mk_step_def (s : string)
  (prems_opt : EO.simple_premises option)
  (args_opt : EO.arguments option)
: EO.term
=
  let prem_ts =
    match prems_opt with
    | Some (Premises ts) -> ts
    | None               -> []
  in

  let arg_ts =
    match args_opt with
    | Some (Args ts) -> ts
    | None           -> []
  in
  EO.Apply (s, List.append arg_ts prem_ts)


let proc_command : EO.command -> unit =
  function
  | Assume (s,t)          ->
    let t_prf = EO.mk_proof_tm t in
    _sig.typs <- M.add s ([], t_prf) _sig.typs

  | AssumePush (_,_)      -> ()
  | DeclareConsts (lc,t)  -> ()
(*  *)
  | DeclareParamConst (s,ps,t,xs) ->
      _sig.typs <- M.add s ([], t) _sig.typs;

      if xs != [] then
      _sig.atts <- M.add s ([], List.hd xs) _sig.atts;

  | DeclareRule (s,ps,rdec,_) -> proc_ruledec s ps rdec
  | Define (s, ps, t_def, ty_opt) ->
    _sig.defs <- M.add s (ps, t_def) _sig.defs;
    (match ty_opt with
    | Some t ->
      _sig.typs <- M.add s (ps, t) _sig.typs;
    | None -> ())

  | Include s -> ()

  | Program (s,ps,(ts,t),cs) ->
    let ty = EO.mk_arrow_ty ts t in
    _sig.typs <- M.add s (ps, ty) _sig.typs;
    _sig.prgs <- M.add s (ps, cs) _sig.prgs;


  | Reference (_, _) -> ()
  | Step (s, t_opt, s', prems_opt, args_opt) ->

    (match t_opt with
    | Some t ->
      _sig.typs <- M.add s ([], t) _sig.typs
    | None   -> ());

    let t_def = mk_step_def s' prems_opt args_opt in
    _sig.defs <- M.add s' ([], t_def) _sig.defs;

  | StepPop (_,_,_,_,_) -> ()
  | Common c -> proc_common_command c


let proc_eo_file (fp : string) : unit =
  List.iter
    (fun cmd ->
      Printf.printf "Processing:\n%s\n" (EO.command_str cmd);
      proc_command cmd
    )
    (Parse_eo.parse_eo_file fp)
