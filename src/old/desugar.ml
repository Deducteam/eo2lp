module EO = Syntax_eo
module M = EO.M
module L = List

(* --------- types ---------- *)
type literal = EO.literal

type leaf =
  | Type | Kind
  | Literal of literal
  | Const of const
  | Var of param
  | MVar of int * term
and term =
  | Leaf of leaf
  | App of level * term * term list
  | Arrow of level * term list
  | Let of string * term * term
and level = O | M
and const_attr =
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
  | Regular

and const = string * pmap * term * const_attr
and param = string * term * param_attr

and pmap = (param * term option) list
and param_attr =
  | Explicit
  | Implicit
  | Opaque
  | List

(* post-elab attributes *)


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

(* overloaded symbols have more than one type.*)
type const_spec = param list * term * const_attr
type info =
  | Consts of const_spec list
  | Macro of (EO.param list * EO.term)
type signature = info M.t
type context = signature * param list

let find_param_opt (s : string) (ps : param list) : param option =
  List.find_opt (fun (s',_,_) -> s = s') ps

let find_first_att_opt (s : string) (sgn :  signature) : const_attr option =
  match M.find_opt s sgn with
  | Some (Macro _) -> None
  | Some (Consts ((_,_,att) :: _)) -> Some att

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
  | Leaf (MVar (i,_)) -> Printf.sprintf "?%d" i
  | Leaf (Var (s,_,_)) -> s
  | Leaf (Const (s, pm, _, _)) ->
    Printf.sprintf "%s[%s]" s (pmap_str pm)
  | App (lv,t,ts) ->
    let ss = String.concat
      (if lv = O then " ⋅ " else " ")
      (L.map term_str (t :: ts)) in
    Printf.sprintf "(%s)" ss
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
  let f = function
    | ((s,_,_), Some t) -> term_str t
    | ((s,_,_), None)   -> "_"
  in
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

let rec map_leaves (f : leaf -> term) : term -> term =
  function
  | Leaf l -> f l
  | App (lv,t,ts) ->
    let (t',ts') =
      (map_leaves f t, L.map (map_leaves f) ts) in
    App (lv, t', ts')
  | Arrow (lv,ts) ->
    Arrow (lv, List.map (map_leaves f) ts)
  | Let (s,t,t') ->
    Let (s, map_leaves f t, map_leaves f t')

let rec map_catt (f : term -> term) : const_attr -> const_attr =
  function
  | (RightAssoc | LeftAssoc) as att -> att
  | RightAssocNil t ->
    RightAssocNil (map_leaves (fun l -> f (Leaf l)) t)
  | LeftAssocNil t ->
    LeftAssocNil (map_leaves (fun l -> f (Leaf l)) t)
  | RightAssocNilNSN t ->
    RightAssocNilNSN (map_leaves (fun l -> f (Leaf l)) t)
  | LeftAssocNilNSN t ->
    LeftAssocNilNSN (map_leaves (fun l -> f (Leaf l)) t)
  | Chainable s ->
    Chainable s
  | Binder s -> Binder s
  | Pairwise s -> Pairwise s
  | ArgList s -> ArgList s

let pmap_find_opt
  (s : string) : pmap -> (param * term option) option =
  List.find_opt (fun ((s',_,_),_) -> s = s')

let map_param (f : term -> term) : param -> param =
  fun (s,ty,att) -> (s, f ty, att)

let map_pmap (f : term -> term) (pm : pmap) : pmap =
  let g (p, t_opt) = (map_param f p, Option.map f t_opt) in
  List.map g pm

let find_pmap_opt (p : param) (pm : pmap) : term option =
  Option.join (List.assoc_opt p pm)

let rec subst_pmap (sub : pmap) (t : term) : term =
  let f : leaf -> term =
    function
    | Var p ->
      begin match find_pmap_opt p sub with
      | Some t' -> t'
      | None -> Leaf (Var p)
      end
    | Const (s,pm,t,att) ->
      let (pm',t',att') =
        (map_pmap (subst_pmap sub) pm,
         map_leaves (fun l -> subst_pmap sub (Leaf l)) t,
         map_catt (subst_pmap sub) att)
      in
        Leaf (Const (s, pm',t',att'))
    | _ as l -> Leaf l
  in
    map_leaves f t

let is_list_param (s : string) (ps : param list) =
  let f (s',_,att_opt) =
    (s = s' && att_opt = List)
  in
    List.exists f ps


let mk_const (s : string) (ps,ty,att : const_spec) : const =
  let pm : pmap = L.map (fun p -> (p, None)) ps in
  (s,pm,ty,att)

let init_const (k : const_spec) : const
=
  let rec aux (ps : param list) (ts : term list)
    : pmap * term list =
    begin match (ps,ts) with
    | (_,[]) -> (ps,[])
    | ([],_) -> ([],ts)
    | (((_,ty',Implicit) as q) :: qs, _) ->
      incr mvs; let q' = (q, Leaf (MVar (!mvs, ty'))) in
      let (qs', ts') = aux qs ts in
      (q' :: qs', ts)
    | (((_,_,Opaque) as q) :: qs, t :: ts) ->
      let (qm', ts') = aux qs ts in
      ((p, t) :: qm', ts')

    | (p :: ps,_) -> (ps,ts)
    end
  in
    begin match f with
    | Leaf Const (s,pm) ->
      let (pm',ts') = aux pm ts in
      (Leaf (Const (s, pm')), ts')
    | _ -> (f,ts)
    end

let mk_let (ws : (string * term) list) (t : term) =
  let f = (fun (s,def) t_acc -> Let (s,def,t_acc)) in
  List.fold_right f ws t

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
  | Symbol "Type" -> Leaf Type
  (* ------------------------ *)
  | Symbol s ->
    begin match M.find_opt s sgn with
    (* ---- *)
    (* if `s` is a macro with no params, desugar. *)
    | Some (Macro (qs,t)) ->  desugar ctx mvs t
    (* ---- *)
    (* if `s` is a constant, initialize to the first spec.*)
    | Some (Const ks) ->
      let k = List.hd ks in
      Leaf (Const (init_const mvs s k))
    (* ---- *)
    (* if `s` is in the parameter list, create variable.*)
    | None ->
      begin match find_param_opt s ps with
      | Some p -> Leaf (Var p)
      | None -> Printf.ksprintf failwith
        "Symbol %s not found in signature or params." s
      end
    (* ---- *)
    end
  (* ------------------------ *)
  | Bind ("eo::define", vs, t) ->
    let f (s,t') = (s, desugar ctx mvs t') in
    let ws = L.map f vs in
    mk_let ws (desugar ctx mvs t)
  (* ------------------------ *)
  | Bind (s, vs, t) ->
    begin match M.find_opt s sgn with
    (* ---- *)
    (* if `s` is a macro, fail. *)
    | Some (Macro _) -> failwith "using macro symbol as binder?"
    (* ---- *)
    (* if `s` is a constant: initialize, create var list, apply. *)
    | Some (Const ((k) :: _)) ->
      let (_,_,att) as f = init_const mvs s k in
      let t' = desugar ctx mvs t in
      let ws = List.map EO.mk_eo_var vs in
      begin match att with
      | Binder t_cons ->
        let w = desugar ctx mvs (Apply (t_cons, ws)) in
        App (O, Leaf (Const f), [w; t'])
      | _ ->
        Printf.ksprintf failwith "ERROR:
        symbol `%s` doesn't have :binder attribute." s
      end
    | None -> Printf.ksprintf failwith
      "ERROR: symbol `%s` not in signature." s
    end
  (* ------------------------ *)
  | Apply ("->", ts) ->
    let ts' = L.map (desugar ctx mvs) ts in
    if L.mem (Leaf Type) ts' then
      Arrow (M, ts')
    else
      Arrow (O, ts')
  (* ------------------------ *)
  | Apply (s, ts) ->
    let ts' = List.map (desugar ctx mvs) ts in
    (* is `s` registered in the signature? *)
    begin match M.find_opt s sgn with
    (* ---- *)
    (* if `s` is a macro:
        desugar body and params, splice some vars. . *)
    | Some (Macro (qs,def)) ->
      let def' = desugar ctx mvs def in
      let qs' = qs
        |> L.map (desugar_param ctx)
        |> L.drop_while (fun (_,_,att_opt) -> att_opt = Implicit)
      in
      (* take some number of terms from `ts'`. *)
      let vs = List.take (List.length qs') ts' in
      let ws = List.drop (List.length qs) ts' in
      (* perform substitution, get rest of the terms. *)
      let pm = List.combine qs' vs in
      begin match subst_pmap pm def' with
      (* if we get a constant, make constant app.  *)
      | Leaf Const k -> mk_const_app ctx mvs k ws
      | _ as f -> App (O, f, ws)
      end
    (* ----- *)
    (* if `s` is a regular constant, make const app. *)
    | Some (Const ks) ->
      let f = init_const mvs s (List.hd ks) in
      let (f', ts'') = app_opaques f ts' in
      mk_const_app ctx mvs (f',att) ts''
    (* ---- *)
    | None -> App (O, Leaf (Var s), ts')
    end
  end
and
  mk_const_app
  (sgn,ps as ctx : context) (mvs : int ref)
  (s,ty,att as k : const) (ts : term list) : term
=
  let f = Leaf (Const k) in
  let g x y = glue ctx mvs (f, x, y) in
  let h y x = glue ctx mvs (f, y, x) in
  begin match att with
  | None -> App (O, f, ts)
  (* ---- *)
  | RightAssocNil t_nil ->
    begin match ts with
    | [t1; Leaf Var xs] when is_list_param xs ps ->
      App (O, f, [t1; Leaf(Var xs)])
    | _ ->
      List.fold_right g ts t_nil
    end
  (* ---- *)
  | LeftAssocNil t_nil ->
    begin match ts with
    | [t1; Leaf Var xs] when is_list_param xs ps ->
      App (O, f, [t1; Leaf(Var xs)])
    | _ ->
      List.fold_left h t_nil ts
    end
  (* ---- *)
  | Some RightAssoc ->
    let (xs, x) = split_last ts in
    List.fold_right g xs x
  (* ---- *)
  | Some LeftAssoc ->
    List.fold_left h (List.hd ts) (List.tl ts)
  (* ---- *)
  | Some Chainable op ->
    let f' = desugar ctx mvs (Symbol op) in
    let rec aux = function
      | v :: w :: vs -> (App (O,f,[v;w])) :: aux vs
      | _ -> []
    in
      mk_const_app ctx mvs f' (aux ts)
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
        App (M,con,[f;t1;t2])
    | _ -> App (O,f,[t1;t2])
and desugar_param
  (ctx : context)
  (s,t,att_opt : EO.param) : param =
  let mvs = ref 0 in
  let att' =
    match att_opt with
    | Some (Implicit) -> Implicit
    | Some (Opaque)   -> Opaque
    | Some (List)     -> List
    | _               -> Explicit
  in
    (s, desugar ctx mvs t, att')

let desugar_term (ctx : context) (t : EO.term) =
  let mvs = ref 0 in
  desugar ctx mvs t


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
  | RightAssocNil t -> RightAssocNil (desugar (sgn,[]) mvs t)
  | RightAssocNilNSN t -> RightAssocNilNSN (desugar (sgn,[]) mvs t)
  | LeftAssocNil t -> LeftAssocNil (desugar (sgn,[]) mvs t)
  | LeftAssocNilNSN t -> LeftAssocNilNSN (desugar (sgn,[]) mvs t)
  | RightAssoc -> RightAssoc
  | LeftAssoc -> LeftAssoc
  | ArgList s -> ArgList s
  | Chainable s -> Chainable s
  | Pairwise s -> Pairwise s
  | Binder s -> Binder s
