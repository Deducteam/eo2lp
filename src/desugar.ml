
module EO = Syntax_eo
module M = EO.M

(* --------- types ---------- *)
type literal = EO.literal

type leaf =
  | Type | Kind
  | Literal of literal
  | Prog of string * pmap
  | Const of string * pmap
  | Var of string
  | MVar of int
and term =
  | Leaf of leaf
  | App of level * term * term
  | Arrow of level * term list
  | Let of string * term * term
and level = O | M

and param = string * term * param_attr
and pmap = (param * term) list
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
    typ : term option;
    def : EO.term option;
    att : const_attr option;
  }
type signature = info M.t
type context = signature * param list


(* --------- pretty printing ---------- *)
let is_leaf : term -> bool =
  function
  | Leaf l -> true
  | _ -> false

let rec term_str : term -> string =
  function
  | Leaf (Literal l) -> EO.literal_str l
  | Leaf (Type) -> "TYPE"
  | Leaf (Kind) -> "KIND"
  | Leaf (MVar i) -> Printf.sprintf "?%d" i
  | Leaf (Var s) -> s
  | Leaf (Prog (s,xs)) | Leaf (Const (s, xs)) ->
    if xs = [] then s else
    Printf.sprintf "%s⟨%s⟩" s (pmap_str xs)
  | App (lv,t1,t2) ->
    if is_leaf t2 then
      Printf.sprintf "%s%s%s"
        (term_str t1)
        (if lv = O then " ⋅ " else " ")
        (term_str t2)
    else
      Printf.sprintf "%s%s(%s)"
        (term_str t1)
        (if lv = O then " ⋅ " else " ")
        (term_str t2)
  | Arrow (lv, ts) ->
  let f t =
    if is_leaf t then term_str t
    else  "(" ^ term_str t ^ ")"
  in
    Printf.sprintf "(%s %s)"
      (if lv = O then "~>" else "->")
      (String.concat " " (List.map f ts))
  | Let (s,t,t') ->
    Printf.sprintf
      "let (%s := %s) in %s"
      s (term_str t) (term_str t')
and pmap_str (xs : pmap) : string =
  let f ((s,_,_),t) = term_str t in
  String.concat ", " (List.map f xs)

let param_attr_str = function
  | Explicit -> ""
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

let rec map_leaves (f : leaf -> term) : term -> term =
  function
  | Leaf l -> f l
  | App (lv,t,t') ->
    App (lv, map_leaves f t, map_leaves f t')
  | Arrow (lv,ts) ->
    Arrow (lv, List.map (map_leaves f) ts)
  | Let (s,t,t') ->
    Let (s, map_leaves f t, map_leaves f t')

let is_list_param (s : string) (ps : param list) =
  let f (s',_,att_opt) =
    (s = s' && att_opt = List)
  in
    List.exists f ps

let mk_const
  (str : string) (ps : param list)
  (mvs : int ref)
=
  let f ((s,_,_) as p) =
    incr mvs; (p, Leaf (MVar !mvs))
  in
    if EO.is_meta str then
      Leaf (Prog (str, List.map f ps))
    else
      Leaf (Const (str, List.map f ps))


let app_opaques (f : term) (ts : term list)
  : (term * term list) =
  let rec aux pm ts =
    begin match (pm,ts) with
    | (_,[]) -> (pm,[])
    | ([],_) -> ([],ts)
    | (((_,_,Opaque) as p, _) :: qm, t :: ts) ->
      let (qm', ts') = aux qm ts in
      ((p, t) :: qm', ts')
    end
  in
    begin match f with
    | Leaf Const (s,pm) ->
      let (pm',ts') = aux pm ts in
      (Leaf (Const (s, pm')), ts')
    | _ -> (f,ts)
    end

let mk_let (ws : (string * term) list) (t : term) =
  List.fold_right (fun (s,def) t_acc -> Let (s,def,t_acc)) ws t

let find_typ_opt (s : string) (sgn : signature)
  : term option =
  begin match M.find_opt s sgn with
  | Some info -> info.typ
  | None -> None
  end

let find_def_opt (s : string) (sgn : signature)
  : EO.term option =
  begin match M.find_opt s sgn with
  | Some info -> info.def
  | None -> None
  end

let find_att_opt (s : string) (sgn : signature)
  : const_attr option =
  begin match M.find_opt s sgn with
  | Some info -> info.att
  | None -> None
  end

let pmap_find_opt
  (s : string) : pmap -> (param * term) option =
  List.find_opt (fun ((s',_,_),_) -> s = s')

let map_param (f : term -> term) : param -> param =
  fun (s,ty,att) -> (s, f ty, att)

let map_pmap (f : term -> term) (pm : pmap) : pmap =
  let g (p, t) = (map_param f p, f t) in
  List.map g pm

let rec pmap_subst (pm : pmap) (t : term) : term =
  let f : leaf -> term =
    function
    | Var s ->
      begin match pmap_find_opt s pm with
      | Some (p, t) -> t
      | None -> Leaf (Var s)
      end
    | Const (s, qm) ->
      Leaf (Const (s, map_pmap (pmap_subst pm) qm))
    | Prog (s, qm) ->
      Leaf (Prog (s, map_pmap (pmap_subst pm) qm))
    | _ as l -> Leaf l
  in
    map_leaves f t

let is_kind : term -> bool =
  function
  | Leaf Type -> true
  | Arrow (M, ts) -> true
  | _ -> false

let rec desugar (sgn,ps as ctx : context) (mvs : int ref)
  : EO.term -> term =
  begin function
  (* ------------------------ *)
  | Literal l -> Leaf (Literal l)
  (* ------------------------ *)
  | Symbol s ->
    if s = "Type" then
      Leaf (Type)
    else
      begin match M.find_opt s sgn with
      (* ---- *)
      | Some info ->
        begin match info.def with
        | Some t -> desugar ctx mvs t
        | None -> mk_const s info.prm mvs
        end
      (* ---- *)
      | None -> Leaf (Var s)
      end
  (* ------------------------ *)
  | Bind ("eo::define", vs, t) ->
    let ws =
      List.map (fun (s,t') -> (s, desugar ctx mvs t')) vs
    in
      mk_let ws (desugar ctx mvs t)
  (* ------------------------ *)
  | Bind (s, vs, t) ->
    begin match M.find_opt s sgn with
    | Some info ->
      let f = mk_const s info.prm mvs in
      let ws = List.map EO.mk_eo_var vs in
      let t' = desugar ctx mvs t in
      begin match info.att with
      | Some (Binder t_cons) ->
        let ws_tm = desugar ctx mvs (Apply (t_cons, ws)) in
        mk_binop_app (f, ws_tm, t')
      | _ -> Printf.ksprintf failwith "ERROR:
        symbol `%s` doesn't have :binder attribute." s
      end
    | None -> Printf.ksprintf failwith
      "ERROR: symbol `%s` not in signature." s
    end
  (* ------------------------ *)
  | Apply ("->", ts) ->
    let ts' = List.map (desugar ctx mvs) ts in
    if List.mem (Leaf Type) ts' then
      Arrow (M, ts')
    else
      Arrow (O, ts')
  (* ------------------------ *)
  | Apply (s, ts) ->
    let ts' = List.map (desugar ctx mvs) ts in
    (* is `s` registered in the signature? *)
    begin match M.find_opt s sgn with
    | Some info ->
      (* is `s` a defined symbol? *)
      begin match info.def with
      | Some t ->
        (* if so, desugar body and subst. *)
        let t' = desugar ctx mvs t in
        (* get non-implicit params. *)
        let qs = List.drop_while
          (fun (_,_,att) -> att = Implicit)
          info.prm
        in
        (* get terms to be substituted. *)
        let vs = List.take (List.length qs) ts' in
        let pm = List.combine qs vs in
        (* perform substitution, get rest of the terms. *)
        let f' = pmap_subst pm t' in
        let ws = List.drop (List.length qs) ts' in
        (* continue desugaring. *)
        mk_list_app ctx mvs f' ws
      (* ----- *)
      | None ->
        (* if not, make constant and gen n-ary application.*)
        let f = mk_const s info.prm mvs in
        let (f', ts'') = app_opaques f ts' in
        mk_list_app ctx mvs f ts''
      end
    (* ---- *)
    | None -> mk_app O (mk_var s) ts'
    end
  end
and
  glue
    (sgn, ps as ctx : context) (mvs : int ref)
    (f,t1,t2 : term * term * term) : term
=
  match t1 with
  | Leaf (Var s) when is_list_param s ps ->
    let con =
      desugar ctx mvs (Symbol "eo::list_concat")
    in
      mk_app M con [f;t1;t2]
  | _ -> mk_binop_app (f,t1,t2)
and
  mk_list_app
  (sgn, ps as ctx : context) (mvs : int ref)
  (f : term) (ts : term list) : term
=
  begin match f with
  | Leaf (Prog (s, _)) -> mk_app M f ts
  | Leaf (Const (s, pm)) ->
    begin match find_typ_opt s sgn with
    | Some t when is_kind t -> mk_app M f ts
    | Some _ ->
      begin match find_att_opt s sgn with
      | None -> mk_app O f ts
      | Some att ->
        let g x y = glue ctx mvs (f, x, y) in
        let h y x = glue ctx mvs (f, y, x) in
        begin match att with
        (* ---- *)
        | RightAssocNil t_nil ->
          begin match ts with
          | [t1; Leaf Var xs] when is_list_param xs ps ->
            mk_binop_app (f,t1,Leaf(Var xs))
          | _ ->
            List.fold_right g ts t_nil
          end
        (* ---- *)
        | LeftAssocNil t_nil ->
          begin match ts with
          | [t1; Leaf Var xs] when is_list_param xs ps ->
            mk_binop_app (f,t1,Leaf(Var xs))
          | _ ->
            List.fold_left h t_nil ts
          end
        (* ---- *)
        | RightAssoc ->
          let (xs, x) = split_last ts in
          List.fold_right g xs x
        (* ---- *)
        | LeftAssoc ->
          List.fold_left h (List.hd ts) (List.tl ts)
        (* ---- *)
        | Chainable op ->
          let f' = desugar ctx mvs (Symbol op) in
          let rec aux = function
            | v :: w :: vs -> mk_app O f [v;w] :: aux vs
            | _ -> []
          in
            mk_list_app ctx mvs f' (aux ts)
        (* ---- *)
        | Pairwise op ->
          let f' = desugar ctx mvs (Symbol op) in
          let rec aux = function
            | v :: vs ->
              List.append
                (List.map (fun w -> mk_app O f [v;w]) vs)
                (aux vs)
            | [] -> []
          in
            mk_list_app ctx mvs f' (aux ts)
        (* ---- *)
        | RightAssocNilNSN _
        | LeftAssocNilNSN _
        | ArgList _ | Binder _ ->
          failwith "unimplemented strategy"
        (* ---- *)
        end
      end
    | None -> Printf.ksprintf failwith
      "ERROR: unregistered constant %s" s
    end
  | _ -> mk_app O f ts
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

let desugar_case
  (ctx : context)
  (t,t' : EO.case) : case =
  let mvs = ref 0 in
  (desugar ctx mvs t, desugar ctx mvs t')

let desugar_cattr
  (sgn : signature) (att : EO.const_attr)
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
