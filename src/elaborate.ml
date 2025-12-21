open Desugar
open Resolve

(* post-elaboration command structure.  *)
type command =
  | Decl of string * param list * term
  | Prog of string * param list * term * case list
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
  | Prog (s,ps,t,_) ->
    Printf.sprintf
      "program %s : %s := (...)"
      (const_str s ps) (term_str t)
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

let elab_param (ctx : context) (p : EO.param) : param =
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
  resolve ctx (desugar ctx t)

let _sig : signature ref = ref M.empty

let mvars_in_params (ps : param list) : S.t =
  List.fold_left
    (fun x (s,t,att) -> S.union x (mvars_in t))
    S.empty ps

(* our 'goal' is to generate a list of parameters that
  will be used in place of the the lingering mvars.
  generate mvmap and param list, then substitute.
*)
let bind_nulls_pmap (pm : pmap) : param list * mvmap =
  let f = function
    | ((_,ty,_), Null (s,i)) ->
      let s' = s ^ string_of_int i in
      Some (
        (s', ty, Implicit),
        ((s,i), Leaf (Var s'))
      )
    | (p, This t) -> None
  in
    List.split (List.filter_map f pm)

(* for a term `t`, generate a list of parameters `ps`
   and a metavariable map `mv` such that `mv` assigns
   every null parameter in `t` to some parameter in `ps`.

   e.g., if `t == bar<U -> ?U0, T -> Bool>`,
   then we obtain `ps == [(U0, Type, Explicit)]`
   and `[(MVar ?U0, Var U0)].
*)
let rec bind_nulls_term : term -> param list * mvmap =
  function
  | Leaf (Const (s, pm)) -> bind_nulls_pmap pm
  | Leaf l -> ([],[])
  | App (lv,t1,t2) ->
    let (ps, mv1) = bind_nulls_term t1 in
    let (qs, mv2) = bind_nulls_term t2 in
    (List.append ps qs, List.append mv1 mv2)
  | Arrow (lv,ts) ->
    let (pss, mvms) =
      List.split (List.map bind_nulls_term ts)
    in
      (List.concat pss, List.concat mvms)
  | Let ((s,def), t) ->
    let (ps, mvm1) = bind_nulls_term def in
    let (qs, mvm2) = bind_nulls_term t in
    (List.append ps qs, List.append mvm1 mvm2)

let bind_mvars : command -> command =
  function
  | Decl (s,ps,t) ->
    let (qs, mvm) = bind_nulls_term t in
    Decl (s, List.append qs ps, mvmap_subst mvm t)
  | Defn (s,ps,def,ty_opt) ->
    let (qs, mvm) = bind_nulls_term def in
    Defn (s,
      List.append qs ps,
      mvmap_subst mvm def,
      Option.map (mvmap_subst mvm) ty_opt
    )
  | _ as cmd -> cmd

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
    let qs = elab_param_list !_sig ps in
    let att' = Option.map (desugar_cattr !_sig) att in
    let (ty',_) = elab (!_sig, qs) ty in

    _sig := M.add s
      { prm = qs; typ = ty';
        def = None ; att = att'; } !_sig;
    Some (Decl (s, qs, ty'))
  (* ---------------- *)
  | DeclareRule (s,ps,rd) ->
    let qs = elab_param_list !_sig ps in
    let r' = desugar_rdec (!_sig, qs) rd in
    Printf.printf
      "WARNING: rule declaration resolution not implemented.\n";

    _sig := M.add s
      { prm = qs; typ = mk_var "NONE";
        def = None; att = None } !_sig;
    Some (Rule (s, qs, r'))
  (* ---------------- *)
  | Define (s, ps, def, _) ->
    let qs = elab_param_list !_sig ps in
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
    let qs = elab_param_list !_sig ps in
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
