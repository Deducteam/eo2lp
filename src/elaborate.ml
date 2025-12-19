open Desugar
open Resolve

(* post-elaboration command structure.  *)
type command =
  | Decl of string * param list * term
  | Prog of string * param list * term * case list
  | Defn of string * param list * term * term option
  | Rule of string * param list * rule_dec

let command_str : command -> string =
  function
  | Decl (s, ps, t) ->
    Printf.sprintf
      "declare %s⟨%s⟩ : %s"
      s (param_list_str ps) (term_str t)
  | Prog (s,ps,t,_) ->
    Printf.sprintf
      "program %s⟨%s⟩ : %s := (...)"
      s (param_list_str ps) (term_str t)
  | Defn (s,ps,def,ty_opt) ->
    let ty_opt_str =
      match ty_opt with
      | Some ty -> " : " ^ (term_str ty)
      | None -> ""
    in
      Printf.sprintf
        "define %s⟨%s⟩%s := %s"
        s (param_list_str ps) ty_opt_str (term_str def)
  | Rule (s,_,_) ->
    Printf.sprintf "WARNING: rule %s not printed" s


let elab (ctx : context) (t : EO.term) : term * term =
  resolve ctx (desugar ctx t)


(* ?TODO?.
  should param elaboration be part of main term elaboration
  procedure? are there situations where constraints
  generated during param elaboration may be relevant
  to the body? *)
let elab_params (sgn : signature)
  (qs : EO.param list) : param list
=
  let f q =
    let (s,ty,att) = desugar_param (sgn,[]) q in
    let (ty',_)    = resolve (sgn, []) ty in
    (s,ty',att)
  in
    List.map f qs

let _sig : signature ref = ref M.empty

let rec elaborate_cmd : EO.command -> command option =
  function
  (* ---------------- *)
  | Assume (s,p) ->
    let (ty, _) = elab (!_sig, []) (EO.mk_proof p) in
    _sig := M.add s
      { prm = []; typ = ty; def = None; att = None; }
      !_sig;
    Some (Decl (s, [], ty))
  (* ---------------- *)
  | AssumePush (_,_)      -> None
  (* ---------------- *)
  | DeclareConsts (lc,t)  -> None
  (* ---------------- *)
  | DeclareParamConst (s,ps,ty,att) ->
    let qs = elab_params !_sig ps in
    let att' = Option.map (desugar_cattr !_sig) att in
    let (ty',_) = elab (!_sig, qs) ty in

    _sig := M.add s
      { prm = qs; typ = ty';
        def = None ; att = att'; } !_sig;
    Some (Decl (s, qs, ty'))
  (* ---------------- *)
  | DeclareRule (s,ps,rd) ->
    let qs = elab_params !_sig ps in
    let r'  = desugar_rdec (!_sig, qs) rd in
    Printf.printf
      "WARNING: rule declaration resolution not implemented.\n";

    _sig := M.add s
      { prm = qs; typ = mk_var "NONE";
        def = None; att = None } !_sig;
    Some (Rule (s, qs, r'))
  (* ---------------- *)
  | Define (s, ps, def, _) ->
    let qs = elab_params !_sig ps in
    let (def', ty) = elab (!_sig, qs) def in

    _sig := M.add s
      { prm = qs; typ = ty;
        def = Some def'; att = None } !_sig;
    Some (Defn (s, qs, def', Some ty))
  (* ---------------- *)
  | Include s -> None
  (* ---------------- *)
  | Program (s, ps, (ts,t), cs) ->
    (* TODO. contemplate handling of program parameters. *)
    let qs = elab_params !_sig ps in
    let (ty, _) = elab (!_sig, qs) (EO.mk_arrow_ty ts t) in
    let ds = List.map (desugar_case (!_sig,qs)) cs in
    Printf.printf
      "WARNING: resolution on cases not defined.\n";

    _sig := M.add s
      { prm = qs; typ = ty; def = None; att = None } !_sig;
    Some (Prog (s, qs, ty, ds))
    (* ---------------- *)
  | Reference (_, _) -> None
  (* ---------------- *)
  | Step (s_step, conc_opt, s_rule, t_args, t_prems) ->
    None
  (* ---------------- *)
  | StepPop (_,_,_,_,_) -> None
  (* ---------------- *)
  | Common c -> elab_common c
and
  elab_common : EO.common_command -> command option =
  function
  | DeclareConst (s,ty,att)  ->
    let (ty',_) = elab (!_sig, []) ty in
    _sig := M.add s
      { prm = []; typ = ty'; def = None; att = None } !_sig;
    Some (Decl (s, [], ty'))
  | DeclareDatatype  (_s,_dt)    -> None
  | DeclareDatatypes (_sts,_dts) -> None
  | Echo             (_str_opt)  -> None
  | Exit                         -> None
  | Reset                        -> None
  | SetOption        (_a)        -> None

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
