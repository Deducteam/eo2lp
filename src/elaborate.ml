open Desugar
open Resolve

(* let rec elaborate_cmd (sgn : EO.signature)
  : EO.command -> command option =
  function
  (* ---------------- *)
  | Assume (s,t) ->
    let (t', _) = resolve (sgn, []) ()
    Some (Decl (s, [], desugar (sgn, []) t))
  (* ---------------- *)
  | AssumePush (_,_)      -> None
  (* ---------------- *)
  | DeclareConsts (lc,t)  -> None
  (* ---------------- *)
  | DeclareParamConst (s,ps,t,_) ->
    let ps' = List.map (desugar_param sgn) ps
    and t'  = desugar (sgn, []) t in
    Some (Decl (s, ps', t'))
  (* ---------------- *)
  | DeclareRule (s,ps,r) ->
    let ps' = List.map (desugar_param sgn) ps
    and r'  = desugar_rdec (sgn, []) r in
    Some (Rule (s, ps', r'))
  (* ---------------- *)
  | Define (s, ps, def, ty_opt) ->
    let ps' = List.map (desugar_param sgn) ps
    and def'   = desugar (sgn, ps) def
    and ty_opt' = Option.map (desugar (sgn,ps)) ty_opt in
    Some (Defn (s, ps', def', ty_opt'))
  (* ---------------- *)
  | Include s -> None
  (* ---------------- *)
  | Program (s, ps, (ts,t), cs) ->
    (* TODO. contemplate handling of program parameters. *)
    let ps' = List.map (desugar_param sgn) ps in
    let ty' = desugar (sgn, ps) (EO.mk_arrow_ty ts t) in
    let cs' = List.map (desugar_case (sgn,ps)) cs in
    Some (Prog (s, ps', ty', cs'))
    (* ---------------- *)
  | Reference (_, _) -> None
  (* ---------------- *)
  | Step (s, _, _, _, _) ->
    let (_,_, Some typ, Some def) = M.find s sgn in
    let def' = desugar (sgn,[]) def in
    let typ' = desugar (sgn,[]) def in
    Some (Defn (s, [], def', Some typ'))
  (* ---------------- *)
  | StepPop (_,_,_,_,_) -> None
  (* ---------------- *)
  | Common c -> desugar_common sgn c
and
  desugar_common (sgn : EO.signature)
  : EO.common_command -> command option =
  function
  | DeclareConst (s,t,_)  ->
    Some (Decl (s, [], desugar (sgn,[]) t))
  | DeclareDatatype  (_s,_dt)    -> None
  | DeclareDatatypes (_sts,_dts) -> None
  | Echo             (_str_opt)  -> None
  | Exit                         -> None
  | Reset                        -> None
  | SetOption        (_a)        -> None

 *)

 (* let elaborate_eo_file
  (sgn : EO.signature)
  (eos : EO.command list) : (signature * command list)
=
  let f eo =
    Printf.printf "desugaring:\n  %s\n"
      (EO.command_str eo);

    let eo' = desugar_cmd sgn eo in
    if Option.is_some eo' then
      Printf.printf "Done!:\n  %s\n\n"
      (command_str (Option.get eo')); eo'
  in
    (desugar_signature sgn, List.filter_map f eos)  *)
