open Elaborate
open Translate
open Context_eo

module EO = struct
  include Syntax_eo
end

module LP = struct
  include Syntax_lp
end

(* open Elaborate *)
let _sig : signature =
  {
    atts = M.of_list [];
    typs = M.of_list [];
    defs = M.of_list [];
    (* prgs = M.of_list []; *)
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

let gen_const (sgn : signature)
    (s : string) (ps : EO.params) (ty : EO.term)
  : LP.command =
  let (s', ps', ty') =
    (
      translate_symbol s,
      translate_params (elab_params sgn ps),
      translate_ty (elab sgn ps ty)
    )
  in
    Symbol (Some Constant, s', ps', Some ty', None)

let gen_prog (sgn : signature)
    (s : string) (ps : EO.params) (ty : EO.term)
    (cs : EO.cases) : LP.command list
=
  let (s', ps', ty', cs') =
    (
      translate_symbol s,
      translate_params (elab_params sgn ps),
      translate_ty (elab sgn ps ty),
      translate_cases (elab_cases sgn ps cs)
    )
  in
    List.append
      [LP.Symbol (Some Sequential, s', [], Some ty', None)]
      (if cs' = [] then [] else [LP.Rule (bind_pvars_cases ps' cs')])

let gen_defn (sgn : signature)
    (s : string) (ps : EO.params)
    (def : EO.term) (ty_opt : EO.term option)
  : LP.command
=
  let (s', ps', def') =
    (
      translate_symbol s,
      translate_params (elab_params sgn ps),
      translate_tm (elab sgn ps def)
    )
  in
  let ty_opt' = match ty_opt with
    | Some ty -> Some (translate_ty (elab sgn ps ty))
    | None -> None
  in
    Symbol (None, s', ps', ty_opt', Some def')

let mk_aux_vars (tys : EO.term list) =
  List.mapi
    (fun i ty -> (("α" ^ string_of_int i), ty))
    tys

let gen_rdec (sgn : signature)
    (s : string) (ps : EO.params)
      (prems_opt : EO.premises option)
      (args_opt : EO.arguments option)
      (reqs_opt : EO.reqs option)
      (conc : EO.conclusion)
  : ((LP.command * LP.command) option * LP.command)
=
  let (s', ps') =
    (
      translate_symbol s,
      translate_params (elab_params sgn ps)
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
          translate_ty (elab sgn ps aux_ty)
        )
      in

      let cs  = [(EO.Apply (s_aux, ts), conc_tm)] in
      let cs' = translate_cases (elab_cases sgn ps cs) in

      let aux_cmds =
        (
          LP.Symbol (None, s', [], Some ty', None),
          LP.Rule (bind_pvars_cases ps' cs')
        )
      in

      let vs = mk_aux_vars arg_tys in
      let ws = List.map (fun (s,_) -> EO.Symbol s) vs in
      let conc = EO.mk_proof_tm (EO.Apply (s_aux, ws)) in

      (Some aux_cmds, vs, conc)

    | None -> (None, [], EO.mk_proof_tm conc_tm)
    in

    (* build type of symbol for declared rule. *)
    let ty =
      match prems_opt with
      | Some (Simple (Premises ts)) ->
          let ts' = List.map EO.mk_proof_tm ts in
          EO.mk_arrow_ty ts' conc_ty
      | Some (PremiseList (_,_)) ->
          Printf.printf "WARNING! --- :premise-list\n";
          conc_ty
      | None -> conc_ty
    in

    let ty' = translate_ty (elab sgn ps ty) in
    let ty_cmd =
      LP.Symbol (None, s', ps', Some ty', None)
    in
      (aux_cmds_opt, ty_cmd)

(* TODO. deprecate by just doing this at parse-time *)
let mk_step_defn (s : string)
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



let proc_common_command : EO.common_command -> LP.command list =
  function
  | DeclareConst (s,t,xs)  ->
    (* FIXME. if `xs : attr list` is non-empty, add the first attribute.*)
    if xs != [] then
      _sig.atts <- M.add s ([], List.hd xs) _sig.atts;
    [ gen_const _sig s [] t ]
  | DeclareDatatype  (_s,_dt)    -> []
  | DeclareDatatypes (_sts,_dts) -> []
  | Echo             (_str_opt)  -> []
  | Exit                         -> []
  | Reset                        -> []
  | SetOption        (_a)        -> []

let proc_command : EO.command -> LP.command list =
  function
  (* ---------------- *)
  | Assume (s,t)          ->
      let t_prf = EO.mk_proof_tm t in
      [ gen_const _sig s [] t_prf ]
  (* ---------------- *)
  | AssumePush (_,_)      -> []
  (* ---------------- *)
  | DeclareConsts (lc,t)  -> []
  (* ---------------- *)
  | DeclareParamConst (s,ps,t,xs) ->
      if xs != [] then
        _sig.atts <- M.add s ([], List.hd xs) _sig.atts;
      [ gen_const _sig s ps t ]
  (* ---------------- *)
  | DeclareRule (s,ps,
      RuleDec (_, prm_opt, arg_opt, req_opt, conc), _
    ) ->
    (
      match
        gen_rdec _sig s ps prm_opt arg_opt req_opt conc
      with
        | (Some (x,y), z) -> [x;y;z]
        | (None, z) -> [z]
    )
  (* ---------------- *)
  | Define (s, ps, t_def, ty_opt) ->
    (* register definition in signature *)
    _sig.defs <- M.add s (ps, t_def) _sig.defs;
    [gen_defn _sig s ps t_def ty_opt]
  (* ---------------- *)
  | Include s -> []
  (* ---------------- *)
  | Program (s, ps, (ts,t), cs) ->
    let ty = EO.mk_arrow_ty ts t
    in gen_prog _sig s ps ty cs
  (* ---------------- *)
  | Reference (_, _) -> []
  | Step (s, conc_opt, s', prems_opt, args_opt) ->
    let t_def = mk_step_defn s' prems_opt args_opt in
    let ty_opt = Option.map EO.mk_proof_tm conc_opt in

    _sig.defs <- M.add s' ([], t_def) _sig.defs;
    [ gen_defn _sig s [] t_def ty_opt ]

  | StepPop (_,_,_,_,_) -> []
  | Common c -> proc_common_command c


let proc_eo_file (fp : string) : (LP.command list) list =
  let eos = Parse_eo.parse_eo_file fp in
  let f eo =
    Printf.printf "Processing:\n  %s\n"
      (EO.command_str eo);

    let lps = proc_command eo in
    let lps_str =
      (String.concat "\n" (List.map LP.lp_command_str lps))
    in
    Printf.printf "Done!:\n  %s\n\n" lps_str; lps
  in
    List.map f eos

(* let proc_signature : EO.signature -> LP.command : *)
