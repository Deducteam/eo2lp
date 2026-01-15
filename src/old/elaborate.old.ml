open Desugar
open Resolve

module L = List

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
    let cs_str = String.concat "\n" (L.map
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
  : EO.param list -> param list =
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
  L.map (fun c -> resolve_case ctx (desugar_case ctx c))

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
          Some (Simple (L.map e ts))
      | Some (PremiseList (t,t')) ->
          Some (PremiseList (e t, e t'))
      | None ->
          None
      end;
    args = L.map e rd.args;
    reqs = L.map (desugar_case ctx) rd.reqs;
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
  L.fold_left
    (fun x (s,t,att) -> S.union x (mvars_in t))
    S.empty ps

let bind_mvars (ps, t : param list * term)
  : param list * term =
  (* ---- *)
  let bind =
    fun i ((_,ty,_), j) ->
    let rec
      s = "x" ^ string_of_int i and
      q = (s,ty,Implicit) and
      tq = Leaf (Var s)
    in
      Some (q, (j, tq))
  in
  (* ---- *)
  let (qs, mvm) = mvars_in t
    |> S.to_list
    |> L.mapi bind
    |> L.filter_map (fun x -> x)
    |> L.split
  in
  (* ---- *)
  let
    ps' = ps |> L.map (map_param (mv_subst mvm)) and
    t' = mv_subst mvm t
  in
    (List.append qs ps', t')



let prog_params (ps : param list) (t : term) : param list =
  let f (s,ty,_) =
    if free s t then
      Some (s, ty, Implicit)
    else
      None
  in
    L.filter_map f ps

(* (cwd,env : string * EO.environment) *)
let rec elaborate_cmd (env : EO.environment)
  : EO.command -> command list =
  function
  (* ---------------- *)
  | Assume (s,p) ->
    let (ty, _) = elab (!_sig, []) (EO.mk_proof p) in

    _sig := M.add s
      { prm = []; typ = Some ty;
        def = None; att = None; }
      !_sig;

    [ Decl (s, [], ty) ]
  (* ---------------- *)
  | AssumePush (_,_)      -> []
  (* ---------------- *)
  | DeclareConsts (lc,t)  ->
    let (ty,_) = elab (!_sig, []) t in
    _sig := M.add (EO.lit_category_str lc)
      { prm = []; typ = Some ty;
        def = None ; att = None; } !_sig;
    let ds =
      match lc with
      (* -- *)
      | NUM ->
        let ty' =
          Arrow (O, [Leaf (Const ("eo::int", [])); ty])
        in
          [ Decl ("_Z", [], ty') ]
      (* -- *)
      | RAT ->
        let ty' =
          Arrow (O, [Leaf (Const ("eo::rat", [])); ty])
        in
          [ Decl ("_Q", [], ty') ]
      (* -- *)
      | STR ->
        let ty' =
          Arrow (O, [Leaf (Const ("eo::string", [])); ty])
        in
          [ Decl ("_S", [], ty') ]
    in
      ds
  (* ---------------- *)
  | DeclareParamConst (s,ps,ty,att) ->
    let qs = elab_param_list !_sig ps in
    let att' = Option.map (desugar_cattr !_sig) att in
    let (ty',_) = elab (!_sig, qs) ty in

    _sig := M.add s
      { prm = qs; typ = Some ty';
        def = None ; att = att'; } !_sig;

    [ Decl (s, qs, ty') ]
  (* ---------------- *)
  | DeclareRule (s,ps,rd,_) ->
    let qs = elab_param_list !_sig ps in
    let r' = elab_rdec (!_sig, qs) rd in

    _sig := M.add s
      { prm = qs; typ = None;
        def = None; att = None } !_sig;

    [ Rule (s, qs, r') ]
  (* ---------------- *)
  (* Define just binds `s` to an `EO.term`.
    occurences unfolded during desugaring. *)
  | Define (s, ps, def, _) ->
    let qs = elab_param_list !_sig ps in

    _sig := M.add s
      { prm = qs; typ = None;
        def = Some def; att = None } !_sig;

    []
  (* ---------------- *)
  | Include p ->
    begin match L.assoc_opt p env with
    | Some eos -> L.concat_map (elaborate_cmd env) eos
    | None -> Printf.printf
      "WARNING: %s not in environment.\n"
      (String.concat "." p); []
    end
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
    [ Prog (s, (qs,ty), (ps', cs')) ]
    (* ---------------- *)
  | Reference (_, _) -> []
  (* ---------------- *)
  | Step (s_step, conc_opt, s_rule, t_args, t_prems) -> []
  (* ---------------- *)
  | StepPop (_,_,_,_,_) -> []
  (* ---------------- *)
  | Common c -> elab_common c
and
  elab_common : EO.common_command -> command list =
  function
  | DeclareConst (s,ty,att)  ->
    let (ty',_) = elab (!_sig, []) ty in
    _sig := M.add s
      { prm = [];   typ = Some ty';
        def = None; att = None }
      !_sig;

    [ Decl (s, [], ty') ]

  | DeclareDatatype  (_s,_dt)    -> []
  | DeclareDatatypes (_sts,_dts) -> []
  | Echo             (_str_opt)  -> []
  | Exit                         -> []
  | Reset                        -> []
  | SetOption        (_a)        -> []

 (* let elaborate_eo_file
  (sgn : EO.signature) (fp : EO.command list)
  : (signature * command list)
=
  let f eo =
    Printf.printf "desugaring:\n  %s\n"
      (EO.command_str eo);

    let eo' = des sgn eo in
    if Option.is_some eo' then
      Printf.printf "Done!:\n  %s\n\n"
      (command_str (Option.get eo')); eo'
  in
    (desugar_signature sgn, L.filter_map f eos)  *)
