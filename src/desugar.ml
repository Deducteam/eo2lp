
module EO = Syntax_eo
module M = EO.M

(* --------- types ---------- *)
type literal = EO.literal

type leaf =
  | Type | Kind
  | Literal of literal
  | Const of string * pmap
  | Var of string
  | SVar of string * int
and term =
  | Leaf of leaf
  | App of level * term * term
  | Arrow of level * term list
  | Let of var * term
and level = O | M
and var = (string * term)
and pmap = (string * term) list

(* post-elab attributes *)
type const_attr =
  | RightAssocNil of term
  | RightAssocNilNSN of term
  | LeftAssocNil of term
  | LeftAssocNilNSN of term
  | RightAssoc
  | LeftAssoc
  | ArgList of string
  | Chainable of string
  | Pairwise of string
  | Binder of string
type param_attr =
  | Explicit
  | Implicit
  | Opaque
  | List

type case = term * term
type param = string * term * param_attr

(* post-elab rule declaration *)
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


(* post elaboration signature. *)
type info = {
    prm : param list;
    typ : term;
    def : term option;
    att : const_attr option;
  }
type signature = info M.t
type context = signature * param list


(* --------- pretty printing ---------- *)
let rec term_str : term -> string =
  function
  | Leaf (Type) -> "TYPE"
  | Leaf (Kind) -> "KIND"
  | Leaf (SVar (s,id)) ->
    Printf.sprintf "?%s%s"
      s (string_of_int id)
  | Leaf (Var s) -> s
  | Leaf (Const (s, xs)) ->
    Printf.sprintf "%s⟨%s⟩" s (pmap_str xs)
  | Leaf (Literal l) -> EO.literal_str l
  | App (O, t1,t2) ->
    Printf.sprintf "(%s ⋅ %s)"
      (term_str t1)
      (term_str t2)
  | App (M, t1,t2) ->
    Printf.sprintf "(%s %s)"
      (term_str t1) (term_str t2)
  | Arrow (lv, ts) ->
    Printf.sprintf "(%s %s)"
      (if lv = O then "~>" else "->")
      (String.concat " " (List.map term_str ts))
  | Let ((s,t), t') ->
    Printf.sprintf
      "let (%s := %s) in %s"
      s (term_str t) (term_str t')
and pmap_str (xs : pmap) : string =
  let f (s,t) = s ^ " ↦ " ^ term_str t in
  String.concat ", " (List.map f xs)

let param_attr_str = function
  | Implicit -> ":implicit"
  | Opaque -> ":opaque"
  | List -> ":list"

let const_attr_str = function
  | RightAssoc -> ":right-assoc"
  | LeftAssoc  -> ":left-assoc"
  | RightAssocNil t ->
      Printf.sprintf ":right-assoc-nil %s" (term_str t)
  | LeftAssocNil t ->
      Printf.sprintf ":left-assoc-nil %s" (term_str t)
  | RightAssocNilNSN t ->
      Printf.sprintf ":right-assoc-nil-non-singleton-nil %s" (term_str t)
  | LeftAssocNilNSN t ->
      Printf.sprintf ":left-assoc-nil-non-singleton-nil %s" (term_str t)
  | Chainable s ->
      Printf.sprintf ":chainable %s" s
  | Binder s ->
      Printf.sprintf ":binder %s" s
  | Pairwise s ->
      Printf.sprintf ":pairwise %s" s
  | ArgList s ->
      Printf.sprintf ":arg-list %s" s

let param_str (s,t,att : param) : string =
  match att with
  | Explicit ->
      Printf.sprintf "(%s ⦂ %s)" s (term_str t)
  | _ ->
      Printf.sprintf "(%s ⦂ (%s, %s))"
        s (term_str t) (param_attr_str att)

let param_list_str (ps : param list) : string =
  String.concat ";" (List.map param_str ps)

(* -------- auxilliary functions -------- *)
let split_last (xs : 'a list) : ('a list * 'a) =
  let ys = List.rev xs in
  (List.rev (List.tl ys), List.hd ys)

let mk_var (str : string) : term = Leaf (Var str)

let mk_app (lv : level) (t : term) (ts : term list) : term =
  List.fold_left (fun t_acc t' -> App (lv, t_acc, t')) t ts

let mk_binop_app (f,t1,t2 : term * term * term) : term =
  App (O, App (O, f, t1), t2)

let is_list_param (s : string) (ps : param list) =
  let f (s',_,att_opt) =
    (s = s' && att_opt = List)
  in
    List.exists f ps

(* ref for unique metavariable names.  *)
let _ids : int M.t ref = ref M.empty

let gen_id (s : string) : int =
  let f = function
    | Some i -> Some (i + 1)
    | None   -> Some (0)
  in
    _ids := M.update s f !_ids;
    M.find s !_ids

let mk_const (str : string) (ps : param list) =
  let f (s,_,_) = (s, Leaf (SVar (s, gen_id s))) in
  let xs = List.map f ps in
  Leaf (Const (str, xs))

(* used for desugaring 'f-lists'. *)
let glue (ps : param list)
  (f,t1,t2 : term * term * term) : term
=
  match t1 with
  | Leaf (Var s) when is_list_param s ps ->
    mk_app M (mk_var "eo::list_concat") [f;t1;t2]
  | _ -> mk_binop_app (f,t1,t2)

let mk_const_app
  (f, att_opt : term * const_attr option)
  (ts, ps : term list * param list) : term
=
  let
    g x y = glue ps (f, x, y)  and
    h y x = glue ps (f, y, x)
  in
    begin match att_opt with
    | None -> mk_app O f ts
    | Some (RightAssocNil t_nil) ->
      List.fold_right g ts t_nil
    | Some (LeftAssocNil t_nil) ->
      List.fold_left h t_nil ts
    | Some (RightAssoc) ->
      let (xs, x) = split_last ts in
      List.fold_right g xs x
    | Some (LeftAssoc) ->
      List.fold_left h (List.hd ts) (List.tl ts)
    | Some (att) ->
      Printf.printf
        "WARNING: naive app; constant %s, attribute %s.\n"
        (term_str f) (const_attr_str att);
      mk_app O f ts
    end

let mk_let (ws : var list) (t : term) =
  List.fold_right (fun v t_acc -> Let (v, t_acc)) ws t

let rec desugar (sgn,ps as ctx : context)
  : EO.term -> term =
  function
  (* ------------------------ *)
  | Literal l -> Leaf (Literal l)
  (* ------------------------ *)
  | Symbol s ->
    if s = "Type" then
      Leaf (Type)
    else
      begin match M.find_opt s sgn with
      | Some info -> mk_const s info.prm
      | None -> Leaf (Var s)
      end
  (* ------------------------ *)
  | Bind ("eo::define", vs, t) ->
    let ws =
      List.map (fun (s,t') -> (s, desugar ctx t')) vs
    in
      mk_let ws (desugar ctx t)
  (* ------------------------ *)
  | Bind (s, vs, t) ->
    begin match M.find_opt s sgn with
    | Some info ->
      let f = mk_const s info.prm in
      let ws = List.map EO.mk_eo_var vs in
      let t' = desugar ctx t in
      begin match info.att with
      | Some (Binder t_cons) ->
        let ws_tm = desugar ctx (Apply (t_cons, ws)) in
        mk_binop_app (f, ws_tm, t')
      | None -> Printf.ksprintf failwith
        "ERROR: symbol `%s` used as binder without :binder attribute." s
      end

    | None -> Printf.ksprintf failwith
      "ERROR: unregistered symbol `%s` used as binder." s
    end
  (* ------------------------ *)
  | Apply ("->", ts) ->
    let ts' = List.map (desugar ctx) ts in
    if List.mem (Leaf Type) ts' then
      Arrow (M, ts')
    else
      Arrow (O, ts')
  (* ------------------------ *)
  | Apply (s, ts) ->
    let ts' = List.map (desugar ctx) ts in
    begin match M.find_opt s sgn with
    | Some info ->
      let f = mk_const s info.prm in
      if EO.is_prog s || Option.is_some info.def then
        mk_app O f ts'
      else
        mk_const_app (f, info.att) (ts', ps)
    | None -> mk_app O (mk_var s) ts'
    end

let desugar_param
  (ctx : context)
  (s,t,att_opt : EO.param) : param
=
  let att' =
    match att_opt with
    | Some (Implicit) -> Implicit
    | Some (Opaque)   -> Opaque
    | Some (List)     -> List
    | _               -> Explicit
  in
    (s, desugar ctx t, att')

let desugar_case (ctx : context) (t,t' : EO.case) : case =
  (desugar ctx t, desugar ctx t')

let desugar_rdec
  (sgn,ps as ctx : context)
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

let desugar_cattr (sgn : signature) :
  EO.const_attr -> const_attr =
  function
  | RightAssocNil t ->
    RightAssocNil (desugar (sgn,[]) t)
  | RightAssocNilNSN t ->
    RightAssocNilNSN (desugar (sgn,[]) t)
  | LeftAssocNil t ->
    LeftAssocNil (desugar (sgn,[]) t)
  | LeftAssocNilNSN t ->
    LeftAssocNilNSN (desugar (sgn,[]) t)
  | RightAssoc -> RightAssoc
  | LeftAssoc -> LeftAssoc
  | ArgList s -> ArgList s
  | Chainable s -> Chainable s
  | Pairwise s -> Pairwise s
  | Binder s -> Binder s

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
