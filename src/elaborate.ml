open Desugar
open Resolve

(* post-elaboration command structure.  *)
type command =
  | Decl of string * param list * term
  | Prog of string * (param list * term) * (param list * case list)
  | Defn of string * param list * term * term option
  | Rule of string * param list * rule_dec

let const_str (str : string) : param list -> string =
  function
    | [] -> str
    | ps  -> Printf.sprintf "%s⟨%s⟩" str (param_list_str ps)

let command_str : command -> string =
  function
  | Decl (s, ps, t) ->
    Printf.sprintf
      "declare %s : %s"
      (const_str s ps) (term_str t)
  | Prog (s,(ps,t),(qs, cs)) ->
    let cs_str = String.concat "\n" (List.map
      (fun (l,r) -> term_str l ^ " ↪ " ^ term_str r) cs)
    in
      Printf.sprintf
        "program %s : %s :=\n%s"
        (const_str s ps) (term_str t) cs_str

  | Defn (s,ps,def,ty_opt) ->
    let ty_opt_str =
      match ty_opt with
      | Some ty -> " : " ^ (term_str ty)
      | None -> ""
    in
      Printf.sprintf
        "define %s%s := %s"
        (const_str s ps) ty_opt_str (term_str def)
  | Rule (s,_,_) ->
    Printf.sprintf "WARNING: rule %s not printed" s
(* ----------------------------------------------------- *)

let elab_param (ctx : context)
  (p : EO.param) : param =
  let (s,ty,att) = desugar_param ctx p in
  let (ty',_)    = resolve ctx ty in
  (s,ty',att)

let elab_param_list (sgn : signature)
  : EO.param list -> param list
=
  let rec aux sgn ps =
    function
    | [] -> []
    | (q :: qs) ->
      let q' = elab_param (sgn, ps) q in
      q' :: (aux sgn (q' :: ps) qs)
  in
    aux sgn []

let elab (ctx : context) (t : EO.term) : term * term =
  resolve ctx (desugar_term ctx t)

let elab_cases (ctx : context) : EO.case list -> case list =
  List.map (fun c -> resolve_case ctx (desugar_case ctx c))

let elab_rdec
  (sgn,ps as ctx : context)
  (rd : EO.rule_dec) : rule_dec
=
  let e t = fst (elab ctx t) in
  {
    assm =
      begin match rd.assm with
      | Some t -> Some (e t)
      | None -> None
      end;
    prem =
      begin match rd.prem with
      | Some (Simple ts) ->
          Some (Simple (List.map e ts))
      | Some (PremiseList (t,t')) ->
          Some (PremiseList (e t, e t'))
      | None ->
          None
      end;
    args = List.map e rd.args;
    reqs = List.map (desugar_case ctx) rd.reqs;
    conc =
      begin match rd.conc with
      | Conclusion t ->
          Conclusion (e t)
      | ConclusionExplicit t ->
          ConclusionExplicit (e t)
      end;
  }

let _sig : signature ref = ref M.empty

let mvars_in_params (ps : param list) : S.t =
  List.fold_left
    (fun x (s,t,att) -> S.union x (mvars_in t))
    S.empty ps

let prog_params (ps : param list) (t : term) : param list =
  let f (s,ty,_) =
    if free s t then
      Some (s, ty, Implicit)
    else
      None
  in
    List.filter_map f ps

let rec elaborate_cmd : EO.command -> command option =
  function
  (* ---------------- *)
  | Assume (s,p) ->
    let (ty, _) = elab (!_sig, []) (EO.mk_proof p) in

    _sig := M.add s
      { prm = []; typ = Some ty;
        def = None; att = None; }
      !_sig;

    Some (Decl (s, [], ty))
  (* ---------------- *)
  | AssumePush (_,_)      -> None
  (* ---------------- *)
  | DeclareConsts (lc,t)  -> None
  (* ---------------- *)
  | DeclareParamConst (s,ps,ty,att) ->
    let qs = elab_param_list !_sig ps in
    let att' = Option.map (desugar_cattr !_sig) att in
    let (ty',_) = elab (!_sig, qs) ty in

    _sig := M.add s
      { prm = qs; typ = Some ty';
        def = None ; att = att'; } !_sig;

    Some (Decl (s, qs, ty'))
  (* ---------------- *)
  | DeclareRule (s,ps,rd) ->
    let qs = elab_param_list !_sig ps in
    let r' = elab_rdec (!_sig, qs) rd in

    _sig := M.add s
      { prm = qs; typ = None;
        def = None; att = None } !_sig;

    Some (Rule (s, qs, r'))
  (* ---------------- *)
  (* Define just binds `s` to an `EO.term`.
    occurences unfolded during desugaring. *)
  | Define (s, ps, def, _) ->
    let qs = elab_param_list !_sig ps in

    _sig := M.add s
      { prm = qs; typ = None;
        def = Some def; att = None } !_sig;

    None;
    (* Some (Defn (s, List.append rs qs, def'', Some ty')) *)
  (* ---------------- *)
  | Include s -> None
  (* ---------------- *)
  | Program (s, ps, (ts,t), cs) ->
    let ps' = elab_param_list !_sig ps in
    let (ty, _) = elab (!_sig, ps') (EO.mk_arrow_ty ts t) in
    let qs = prog_params ps' ty in

    _sig := M.add s
      { prm = qs; typ = Some ty;
        def = None; att = None }
      !_sig;

    let cs' = elab_cases (!_sig, ps') cs in
    Some (Prog (s, (qs,ty), (ps', cs')))
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
      { prm = []; typ = Some ty';
        def = None; att = None }
      !_sig;
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
