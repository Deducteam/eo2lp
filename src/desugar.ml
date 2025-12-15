open List

module EO = Syntax_eo
module M = EO.M

let split_last (xs : 'a list) : ('a list * 'a) =
  let ys = List.rev xs in
  (List.rev (List.tl ys), List.hd ys)

(* post-desugaroration terms *)
type param_attr =
  | Implicit
  | Explicit
  | Opaque
type term =
  | Literal of EO.literal
  | Const of string * pmap
  | Var of string
  | MVar of string * int
  | App of term * term
  | Meta of term * term
  | TArr of term * term
  | KArr of term * term
  | Let of var list * term
and pmap =
  PMap of (string * term) list
and var =
  string * term

type case = term * term
type param = string * term * param_attr


let mk_app (t : term) (ts : term list) : term =
  fold_left (fun t_acc t' -> App (t_acc, t')) t ts

let mk_app_bin =
  fun f t1 t2 -> App (App (f, t1), t2)

let mk_arrow_app (ts : term list) =
  let (xs,x) = split_last ts in
  let arr = Const ("->", PMap []) in
  fold_right (fun t_acc t' -> mk_app_bin arr t_acc t') xs x

let mk_meta_app (t : term) (ts : term list) : term =
  fold_left (fun t_acc t' -> Meta (t_acc, t')) t ts

let mk_eo_list_concat
  (f,t1,t2 : term * term * term) : term =
  mk_meta_app (Var "eo::list_concat") [f;t1;t2]

(* auxillary function used in desugaroration of f-lists. *)
let glue (ps : EO.param list)
  (f,t1,t2 : term * term * term) : term
=
  match t1 with
  | Var s when EO.is_list_param s ps ->
    mk_eo_list_concat (f,t1,t2)
  | _ -> mk_app f [t1;t2]

let _ids : int M.t ref = ref M.empty
let gen_id (s : string) : int =
  let f = function
    | Some i -> Some (i + 1)
    | None   -> Some (0)
  in
    _ids := M.update s f !_ids;
    M.find s !_ids

let rec desugar (sgn, ps as ctx) : EO.term -> term =
  function
  (* ------------------------ *)
  | Literal l -> Literal l
  (* ------------------------ *)
  | Symbol s ->
    (* is `s` registered in the signature? *)
    begin match M.find_opt s sgn with
    (* if so, initialize parameters as metavariables. *)
    | Some info ->
      let f (s,_,_) =
        (s, MVar (s, gen_id s))
      in
        Const (s, PMap (List.map f info.EO.prm))
    (* otherwise, s is a variable. *)
    | None -> Var s
    end
  (* ------------------------ *)
  | Bind (s, vs, t) ->
    if s = "eo::define" then
      Let (map (desugar_var ctx) vs, desugar ctx t)
    else
      desugar_binder_app ctx (s,vs,t)
  (* ------------------------ *)
  | Apply (s, ts) ->
    if s = "->" then
      desugar_arrow_tm ctx ts
    else if
      EO.is_builtin s || EO.is_program s || EO.is_def s sgn
    then
      let c = desugar ctx (Symbol s) in
      mk_meta_app c (map (desugar ctx) ts)
    else
      desugar_const_app ctx s ts
and desugar_arrow_tm
  (sgn,ps as ctx : EO.signature * EO.param list)
  (ts : EO.term list) : term
=
  let ts' = List.map (desugar ctx) ts in
  let (xs, x) = split_last ts' in
  if List.mem (EO.Symbol "Type") ts then
    fold_right (fun acc ty -> KArr (acc, ty)) xs x
  else
    fold_right (fun acc ty -> TArr (acc, ty)) xs x
and
  desugar_const_app
    (sgn,ps as ctx : EO.signature * EO.param list)
    (s : string) (ts : EO.term list) : term
  =
    let c = desugar ctx (Symbol s) in
    let
      ts' = map (desugar ctx) ts and
      g x y = glue ps (c, x, y)  and
      h y x = glue ps (c, y, x)
    in
      match EO.get_attr s sgn with
      | Some (RightAssocNil t_nil) ->
        fold_right g ts' (desugar ctx t_nil)
      | Some (LeftAssocNil t_nil) ->
        fold_left h (desugar ctx t_nil) ts'
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
  desugar_binder_app
    (sgn,ps as ctx : EO.signature * EO.param list)
    (s,vs,t : string * EO.var list * EO.term) : term
  =
    match EO.get_attr s sgn with
    | Some (Binder t_cons) ->
      let c = desugar ctx (Symbol s) in
      let xs = map EO.mk_eo_var vs in
      let xs' = desugar ctx (Apply (t_cons, xs)) in
      let t'  = desugar ctx t in
      App (App (c, xs'), t')
    | _ -> Printf.ksprintf failwith
      "ERROR: unregistered binder %s." s
and
  desugar_param
    (sgn : EO.signature) (s,t,att_opt : EO.param) : param
  =
    let t' = desugar (sgn,[]) t in
    let att' =
      match att_opt with
      | Some (Implicit) -> Implicit
      | Some (Opaque) -> Opaque
      | _ -> Explicit
    in
      (s,t',att')
and
  desugar_var (ctx : EO.signature * EO.param list)
    (s,t : EO.var) : var = (s, desugar ctx t)

let desugar_case ctx (t,t') : case
  = (desugar ctx t, desugar ctx t')

(* post-desugaroration rule declaration *)
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


let desugar_rdec
  (sgn,ps as ctx : EO.signature * EO.param list)
  (rd : EO.rule_dec) : rule_dec
=
  let e = desugar ctx in
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
    reqs = List.map (desugar_case ctx) rd.reqs;
    conc =
      begin match rd.conc with
      | Conclusion t -> Conclusion (e t)
      | ConclusionExplicit t -> ConclusionExplicit (e t)
      end;
  }





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
  | TArr (t1,t2) ->
    Printf.sprintf "(%s ~> %s)"
      (term_str t1) (term_str t2)
  | KArr (t1,t2) ->
    Printf.sprintf "(%s -> %s)"
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
  String.concat ";" (List.map param_str ps)

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
