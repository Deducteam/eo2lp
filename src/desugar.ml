
module EO = Syntax_eo
module M = EO.M

(* --------- types ---------- *)
type literal = EO.literal

type leaf =
  | Type | Kind
  | Literal of literal
  | Const of string * pmap
  | Var of string
  | MVar of int
and term =
  | Leaf of leaf
  | App of level * term * term
  | Arrow of level * term list
  | Let of var * term
and level = O | M
and var = (string * term)
and param = string * term * param_attr
and pmap = (param * inst) list
and inst =
  | Null of int
  | This of term
and param_attr =
  | Explicit
  | Implicit
  | Opaque
  | List

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

type case = term * term

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
let mvar_str : string * int -> string =
  function
    | (s,0) -> s
    | (s,i) -> s ^ (string_of_int i)

let rec term_str : term -> string =
  function
  | Leaf (Literal l) -> EO.literal_str l
  | Leaf (Type) -> "TYPE"
  | Leaf (Kind) -> "KIND"
  | Leaf (MVar i) -> Printf.sprintf "?%d" i
  | Leaf (Var s) -> s
  | Leaf (Const (s, xs)) ->
    if xs = [] then s else
    Printf.sprintf "%s⟨%s⟩" s (pmap_str xs)
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
and inst_str : inst -> string =
  function
  | Null i -> term_str (Leaf (MVar i))
  | This t -> term_str t
and pmap_str (xs : pmap) : string =
  let f ((s,_,_),i) = inst_str i in
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
  | Implicit ->
      Printf.sprintf "[%s ⦂ %s]" s (term_str t)
  | Opaque ->
      Printf.sprintf "{%s ⦂ %s}" s (term_str t)
  | List ->
      Printf.sprintf "|%s ⦂ %s|" s (term_str t)

let param_list_str (ps : param list) : string =
  String.concat "; " (List.map param_str ps)

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

let mk_const
  (str : string) (ps : param list)
  (iref : int ref)
=
  let f ((s,_,_) as p) =
    incr iref;
    (p, Null !iref)
  in
    Leaf (Const (str, List.map f ps))

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

let rec desugar (sgn,ps as ctx : context) (iref : int ref)
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
      | Some info -> mk_const s info.prm iref
      | None -> Leaf (Var s)
      end
  (* ------------------------ *)
  | Bind ("eo::define", vs, t) ->
    let ws =
      List.map (fun (s,t') -> (s, desugar ctx iref t')) vs
    in
      mk_let ws (desugar ctx iref t)
  (* ------------------------ *)
  | Bind (s, vs, t) ->
    begin match M.find_opt s sgn with
    | Some info ->
      let f = mk_const s info.prm iref in
      let ws = List.map EO.mk_eo_var vs in
      let t' = desugar ctx iref t in
      begin match info.att with
      | Some (Binder t_cons) ->
        let ws_tm = desugar ctx iref (Apply (t_cons, ws)) in
        mk_binop_app (f, ws_tm, t')
      | None -> Printf.ksprintf failwith
        "ERROR: symbol `%s` used as binder without :binder attribute." s
      end

    | None -> Printf.ksprintf failwith
      "ERROR: unregistered symbol `%s` used as binder." s
    end
  (* ------------------------ *)
  | Apply ("->", ts) ->
    let ts' = List.map (desugar ctx iref) ts in
    if List.mem (Leaf Type) ts' then
      Arrow (M, ts')
    else
      Arrow (O, ts')
  (* ------------------------ *)
  | Apply (s, ts) ->
    let ts' = List.map (desugar ctx iref) ts in
    begin match M.find_opt s sgn with
    | Some info ->
      let f = mk_const s info.prm iref in
      if EO.is_prog s || Option.is_some info.def then
        mk_app M f ts'
      else
        mk_const_app (f, info.att) (ts', ps)
    | None -> mk_app O (mk_var s) ts'
    end

let desugar_term (ctx : context) (t : EO.term) =
  let mvs = ref 0 in
  desugar ctx mvs t

let desugar_param
  (ctx : context)
  (s,t,att_opt : EO.param) : param
=
  let mvs = ref 0 in
  let att' =
    match att_opt with
    | Some (Implicit) -> Implicit
    | Some (Opaque)   -> Opaque
    | Some (List)     -> List
    | _               -> Explicit
  in
    (s, desugar ctx mvs t, att')

let desugar_case (ctx : context)
  (t,t' : EO.case) : case =
  let mvs = ref 0 in
  (desugar ctx mvs t, desugar ctx mvs t')

let desugar_rdec
  (sgn,ps as ctx : context)
  (rd : EO.rule_dec) : rule_dec
=
  let e = desugar_term ctx in
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

let desugar_cattr (sgn : signature) (att : EO.const_attr)
  : const_attr
=
  let mvs = ref 0 in
  match att with
  | RightAssocNil t ->
    RightAssocNil (desugar (sgn,[]) mvs t)
  | RightAssocNilNSN t ->
    RightAssocNilNSN (desugar (sgn,[]) mvs t)
  | LeftAssocNil t ->
    LeftAssocNil (desugar (sgn,[]) mvs t)
  | LeftAssocNilNSN t ->
    LeftAssocNilNSN (desugar (sgn,[]) mvs t)
  | RightAssoc -> RightAssoc
  | LeftAssoc -> LeftAssoc
  | ArgList s -> ArgList s
  | Chainable s -> Chainable s
  | Pairwise s -> Pairwise s
  | Binder s -> Binder s
