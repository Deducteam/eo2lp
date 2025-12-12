open List

module EO = struct
  include Syntax_eo
  include Context_eo
end

module M = EO.M

let split_last (xs : 'a list) : ('a list * 'a) =
  let ys = List.rev xs in
  (List.rev (List.tl ys), List.hd ys)

(* post-elaboration terms *)
type param_attr =
  | Implicit
  | Explicit
  | Opaque
type term =
  | Literal of EO.literal
  | Const of string * pmap
  | MVar of string * int
  | Var of string
  | App of term * term
  | Meta of term * term
  | Let of var list * term
and param =
  string * term * param_attr
and pmap =
  PMap of (string * term) list
and var =
  string * term
and case =
  term * term

let mk_app (t : term) (ts : term list) : term =
  fold_left (fun t_acc t' -> App (t_acc, t')) t ts

let mk_app_bin =
  fun f t1 t2 -> App (App (f, t1), t2)

let mk_arrow_app (ts : term list) =
  let (xs,x) = split_last ts in
  let arr = Const ("->", PMap []) in
  fold_right (fun t_acc t' -> mk_app_bin arr t_acc t') xs x

(* let mk_app_binop_right (cons, nil : term * term) (ts : term list) =
  let app_bin f t1 t2 = App (App (f, t1), t2) in
  fold_right (fun t_acc t' -> app_bin cons t_acc t') ts nil *)

let mk_meta_app (t : term) (ts : term list) : term =
  fold_left (fun t_acc t' -> Meta (t_acc, t')) t ts

let mk_eo_list_concat
  (f,t1,t2 : term * term * term) : term =
  mk_meta_app (Var "eo::list_concat") [f;t1;t2]

(* auxillary function used in elaboration of f-lists. *)
let glue (ps : EO.param list)
  (f,t1,t2 : term * term * term) : term
=
  match t1 with
  | Var s when EO.is_list_param s ps ->
    mk_eo_list_concat (f,t1,t2)
  | _ -> mk_app f [t1;t2]

(* fresh metavariable names should have the name of
   the parameter as prefix, followed by an index.

   so our ref for this should be a map from strings to index.
*)
let _ids : int M.t ref = ref M.empty
let gen_id (s : string) : int =
  let f = function
    | Some i -> Some (i + 1)
    | None   -> Some (0)
  in
    _ids := M.update s f !_ids;
    M.find s !_ids

let rec elab_tm
  (sgn, ps as ctx : EO.signature * EO.param list)
  (t : EO.term) : term
=
  match t with
  (* ------------------------ *)
  | Literal l -> Literal l
  (* ------------------------ *)
  | Symbol s ->
    (
      (* is `s` registered in the signature? *)
      match M.find_opt s sgn with
      (* if so, initialize parameters as metavariables. *)
      | Some (ps,_,_,_) ->
        let f (s,_,_) =
          (s, MVar (s, gen_id s))
        in
          Const (s, PMap (List.map f ps))
      | None -> Var s
    )
  (* ------------------------ *)
  | Bind (s, vs, t) ->
    if s = "eo::define" then
      Let (map (elab_var ctx) vs, elab_tm ctx t)
    else
      elab_binder_app ctx (s,vs,t)
  (* ------------------------ *)
  | Apply (s, ts) ->
    if EO.is_builtin s || EO.is_program s || EO.is_def s sgn then
      let c = elab_tm ctx (Symbol s) in
      mk_meta_app c (map (elab_tm ctx) ts)
    else
      elab_const_app ctx s ts
and
  elab_const_app
    (sgn,ps as ctx : EO.signature * EO.param list)
    (s : string) (ts : EO.term list) : term
  =
    let c = elab_tm ctx (Symbol s) in
    let
      ts' = map (elab_tm ctx) ts and
      g x y = glue ps (c, x, y)  and
      h y x = glue ps (c, y, x)
    in
      match EO.get_attr s sgn with
      | Some (RightAssocNil t_nil) ->
        fold_right g ts' (elab_tm ctx t_nil)
      | Some (LeftAssocNil t_nil) ->
        fold_left h (elab_tm ctx t_nil) ts'
      | Some (RightAssoc) ->
        let (xs, x) = split_last ts' in
        List.fold_right g xs x
      | Some (LeftAssoc) ->
        List.fold_left h (List.hd ts') (List.tl ts')
      | Some (att) ->
        Printf.printf
          "WARNING: naive app: constant %s, attribute %s.\n"
          s (EO.const_attr_str att);
        mk_app c ts'
      | None ->
        if s = "->" then
          mk_arrow_app ts'
        else
          mk_app c ts'
and
  elab_binder_app
    (sgn,ps as ctx : EO.signature * EO.param list)
    (s,vs,t : string * EO.var list * EO.term) : term
  =
    match EO.get_attr s sgn with
    | Some (Binder t_cons) ->
      let c = elab_tm ctx (Symbol s) in
      let xs = map EO.mk_eo_var vs in
      let xs' = elab_tm ctx (Apply (t_cons, xs)) in
      let t'  = elab_tm ctx t in
      App (App (c, xs'), t')
    | _ -> Printf.ksprintf failwith
      "ERROR: unregistered binder %s." s
and
  elab_param
    (sgn : EO.signature) (s,t,att_opt : EO.param) : param
  =
    let t' = elab_tm (sgn,[]) t in
    let att' =
      match att_opt with
      | Some (Implicit) -> Implicit
      | Some (Opaque) -> Opaque
      | _ -> Explicit
    in
      (s,t',att')
and
  elab_var (ctx : EO.signature * EO.param list)
    (s,t : EO.var) : var = (s, elab_tm ctx t)

let elab_case (ctx : EO.signature * EO.param list)
  (t,t' : EO.case) : case
=
  (elab_tm ctx t, elab_tm ctx t')


(* post-elaboration signature *)
type signature =
  (param list * term option * term option) M.t

let elab_signature (sgn : EO.signature) =
  let f (ps, _, ty_opt, def_opt) =
    (
      List.map (elab_param sgn) ps,
      Option.map (elab_tm (sgn, ps)) ty_opt,
      Option.map (elab_tm (sgn, ps)) def_opt
    )
  in
    M.map f sgn

(* post-elaboration rule declaration *)
type premises =
  | Simple of term list
  | PremiseList of term * term
and conclusion =
  | Conclusion of term
  | ConclusionExplicit of term
and rule_dec =
  {
    assm : term option;
    prem : premises option;
    args : term list;
    reqs : case list;
    conc : conclusion;
  }

type command =
  | Decl of string * param list * term
  | Prog  of string * param list * term * case list
  | Defn  of string * param list * term * term option
  | Rule  of string * param list * rule_dec

let elab_common_command (sgn : EO.signature)
  : EO.common_command -> command option =
  function
  | DeclareConst (s,t,_)  ->
    Some (Decl (s, [], elab_tm (sgn,[]) t))
  | DeclareDatatype  (_s,_dt)    -> None
  | DeclareDatatypes (_sts,_dts) -> None
  | Echo             (_str_opt)  -> None
  | Exit                         -> None
  | Reset                        -> None
  | SetOption        (_a)        -> None


let elab_rdec
  (sgn,ps as ctx : EO.signature * EO.param list)
  (rd : EO.rule_dec) : rule_dec
=
  let e = elab_tm ctx in
  {
    assm = Option.map e rd.assm;
    prem =
      begin match rd.prem with
      | Some (Simple ts) ->
        Some (Simple (List.map e ts))
      | Some (PremiseList (t,t')) ->
        Some (PremiseList (e t, e t'))
      end;
    args = List.map e rd.args;
    reqs = List.map (elab_case ctx) rd.reqs;
    conc =
      begin match rd.conc with
      | Conclusion t -> Conclusion (e t)
      | ConclusionExplicit t -> ConclusionExplicit (e t)
      end;
  }

let elab_command (sgn : EO.signature)
  : EO.command -> command option =
  function
  (* ---------------- *)
  | Assume (s,t) ->
    Some (Decl (s, [], elab_tm (sgn, []) t))
  (* ---------------- *)
  | AssumePush (_,_)      -> None
  (* ---------------- *)
  | DeclareConsts (lc,t)  -> None
  (* ---------------- *)
  | DeclareParamConst (s,ps,t,_) ->
    let ps' = List.map (elab_param sgn) ps
    and t'  = elab_tm (sgn, []) t in
    Some (Decl (s, ps', t'))
  (* ---------------- *)
  | DeclareRule (s,ps,r) ->
    let ps' = List.map (elab_param sgn) ps
    and r'  = elab_rdec (sgn, []) r in
    Some (Rule (s, ps', r'))
  (* ---------------- *)
  | Define (s, ps, def, ty_opt) ->
    let ps' = List.map (elab_param sgn) ps
    and def'   = elab_tm (sgn, ps) def
    and ty_opt' = Option.map (elab_tm (sgn,ps)) ty_opt in
    Some (Defn (s, ps', def', ty_opt'))
  (* ---------------- *)
  | Include s -> None
  (* ---------------- *)
  | Program (s, ps, (ts,t), cs) ->
    (* TODO. contemplate handling of program parameters. *)
    let ps' = List.map (elab_param sgn) ps in
    let ty' = elab_tm (sgn, ps) (EO.mk_arrow_ty ts t) in
    let cs' = List.map (elab_case (sgn,ps)) cs in
    Some (Prog (s, ps', ty', cs'))
    (* ---------------- *)
  | Reference (_, _) -> None
  (* ---------------- *)
  | Step (s, _, _, _, _) ->
    let (_,_, Some typ, Some def) = M.find s sgn in
    let def' = elab_tm (sgn,[]) def in
    let typ' = elab_tm (sgn,[]) def in
    Some (Defn (s, [], def', Some typ'))
  (* ---------------- *)
  | StepPop (_,_,_,_,_) -> None
  (* ---------------- *)
  | Common c -> elab_common_command sgn c

(* --------- pretty printing ---------- *)
let rec term_str : term -> string =
  function
  | MVar (s,id) ->
    Printf.sprintf "?%s%s"
      s (string_of_int id)
  | Var s -> s
  | Const (s, pm) ->
    Printf.sprintf "%s⟨%s⟩" s (pmap_str pm)
  | Literal l -> EO.literal_str l
  | App (t1,t2) ->
    Printf.sprintf "(%s ⋅ %s)"
      (term_str t1)
      (term_str t2)
  | Meta (t1,t2) ->
    Printf.sprintf "(%s %s)"
      (term_str t1) (term_str t2)
  | Let (xs, t) ->
    let xs_str = EO.list_str var_str xs in
    Printf.sprintf
      "(eo::define (%s) %s)"
      xs_str (term_str t)
and pmap_str (PMap pm : pmap) : string =
  let f (s,t) = s ^ " ↦ " ^ term_str t in
  String.concat ", " (List.map f pm)
and var_str (s,t : string * term) : string =
  Printf.sprintf "(%s %s)" s (term_str t)

let param_str (s,t,att : param) : string =
  match att with
  | Explicit ->
      Printf.sprintf "(%s : %s)" s (term_str t)
  | Implicit ->
      Printf.sprintf "[%s : %s]" s (term_str t)
  | Opaque ->
      Printf.sprintf "⟬%s : %s⟭" s (term_str t)

let param_list_str (ps : param list) : string =
  String.concat ", " (List.map param_str ps)


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

let lcat_of : EO.literal -> EO.lit_category =
  function
  | Numeral _  -> NUM
  | Decimal _  -> DEC
  | Rational _ -> RAT
  | Binary _   -> BIN
  | Hexadecimal _ -> HEX
  | String _      -> STR

(* let rec free_in (t : term) (s : string) =
  match t with
  | Const (_,_) -> false
  | Var s' -> s = s'
  | Literal l -> false
  | App (t1,t2)   -> free_in t1 s || free_in t2 s
  | Meta (s', ts) -> List.exists (fun t' -> free_in t' s) ts
  | Let (xs, t') ->
      let b = List.exists
        (fun (s',t') ->
          if s = s' then failwith "error: variable capture in eo::define"
          else free_in t' s
        ) xs
      in
        b || free_in t' s

let free_params (ps : eparam list) (t : term) : (string * term) list =
  let f (s,ty,flg) =
    if free_in t s then Some (s,ty) else None
  in
    List.filter_map f ps *)
    (* let rec subst ((s,t) : string * term) =
  let f = subst (s,t) in
  function
  | Symbol s' -> if s = s' then t else Symbol s'
  | Literal l -> Literal l
  | App (t1,t2) -> App (f t1, f t2)
  | Let (xs, t') ->
      let ys =
        List.map (fun (x,d) -> (x, f d)) xs
      in
        Let (ys, f t')
  | Meta (s, ts) -> Meta (s,List.map f ts)

let rec splice (t : term)
  (ps : params) (ts : term list) : term
=
  match ps with
  | [] -> t
  | Param (s, _, xs) :: ps' ->
    if List.mem (Attr ("implicit", None)) xs then
      splice t ps' ts
    else
      let t' = subst (s, List.hd ts) t in
      splice t' ps' (List.tl ts) *)

(* let esig : EO.signature =
  {
    prm = M.of_list [
      ("Int", []);
      ("Bool", []);
      ("or", []);
      ("true", []);
      ("false", []);
      ("0", []);
      ("=", [("U", EO.Symbol "Type", Some EO.Implicit)])
    ];
    typ = M.empty;
    def = M.empty;
    att = M.of_list [
      ("or", EO.RightAssocNil (EO.Symbol "false"))]
  }

let eps : EO.param list =
  [ ("x", Symbol "Bool", None); ("y", Symbol "Int", None) ]

let eterm : EO.term =
  Apply ("or",
    [
      Apply ("=", [Symbol "true"; Symbol "false"]);
      Symbol "x";
      Apply ("=", [Symbol "0"; Symbol "y"]);
    ]
  ) *)
