open Elaborate
open Translate
open Context_eo
open List

module EO = struct
  include Syntax_eo
end

module LP = struct
  include Syntax_lp
end


let builtin_tys =
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

let mk_aux_vars (tys : EO.term list) =
  List.mapi
    (fun i ty -> (("α" ^ string_of_int i), ty))
    tys

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

(* find the first constant attribute in `xs` *)
let proc_atts (s : string) (xs : EO.attr list) : unit =
  match List.find_opt EO.is_const_attr xs with
    | Some x -> _sig.att <- M.add s x _sig.att
    | None -> ()

let proc_common_command : EO.common_command -> LP.command list =
  function
  | DeclareConst (s,t,xs)  ->
      _sig.prm <- M.add s [] _sig.prm;
      _sig.typ <- M.add s t  _sig.typ;
      proc_atts s xs; [ gen_const _sig s [] t ]
  | DeclareDatatype  (_s,_dt)    -> []
  | DeclareDatatypes (_sts,_dts) -> []
  | Echo             (_str_opt)  -> []
  | Exit                         -> []
  | Reset                        -> []
  | SetOption        (_a)        -> []

let proc_command : EO.command -> LP.command list =
  function
  (* ---------------- *)
  | Assume (s,t) ->
      _sig.prm <- M.add s [] _sig.prm;
      _sig.typ <- M.add s t  _sig.typ;
      [ gen_const _sig s [] (EO.proof_of t) ]
  (* ---------------- *)
  | AssumePush (_,_)      -> []
  (* ---------------- *)
  | DeclareConsts (lc,t)  -> []
  (* ---------------- *)
  | DeclareParamConst (s,ps,t,xs) ->
    _sig.prm <- M.add s ps _sig.prm;
    _sig.typ <- M.add s t _sig.typ;
    proc_atts s xs; [ gen_const _sig s ps t ]
  (* ---------------- *)
  | DeclareRule (s,ps,
    (* TODO. refactor `RuleDec` parsing and refactor `gen_rdec` *)
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
    _sig.prm <- M.add s ps    _sig.prm;
    _sig.def <- M.add s t_def _sig.def;
    (match ty_opt with
      | Some t -> _sig.typ <- M.add s t _sig.typ
      | None -> ()
    ); [ gen_defn _sig s ps t_def ty_opt ]
  (* ---------------- *)
  (*  recursively generate signature DAG from `include`? *)
  | Include s -> []
  (* ---------------- *)
  | Program (s, ps, (ts,t), cs) ->
    (* TODO. contemplate handling of program parameters. *)
    let ty = EO.mk_arrow_ty ts t in
    _sig.prm <- M.add s ps _sig.prm;
    _sig.typ <- M.add s ty _sig.typ;
    gen_prog _sig s ps ty cs
  (* ---------------- *)
  | Reference (_, _) -> []
  (* ---------------- *)
  | Step (s, conc_opt, s', prems_opt, args_opt) ->
    let t_def = mk_step_defn s' prems_opt args_opt in
    _sig.def <- M.add s t_def _sig.def;

    let ty_opt =
      match conc_opt with
      | Some t ->
          _sig.typ <- M.add s t _sig.typ;
          Some (EO.proof_of t)
      | None -> None
    in
      [ gen_defn _sig s [] t_def ty_opt ]
  (* ---------------- *)
  | StepPop (_,_,_,_,_) -> []
  (* ---------------- *)
  | Common c -> proc_common_command c


let proc_eo_file (fp : string) : (LP.command list) list =
  let eos = Parse_eo.parse_eo_file fp in
  let f eo =
    Printf.printf "Processing:\n  %s\n" (EO.command_str eo);
    proc_command eo
  in
    List.map f eos

(* let proc_signature : EO.signature -> LP.command : *)
