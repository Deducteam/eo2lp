open List

open Syntax_eo
open Context_eo

(*
definition:
  a symbol `s` is a type constructor iff:
  (a). `s` is a declared constant with range `Type`,
  (b). or `s` is a defined constant whose definiens `Ap`

hypothesis:


*)



let split_last (xs : 'a list) : ('a list * 'a) =
  let ys = List.rev xs in
  (List.rev (List.tl ys), List.hd ys)


let mk_eo_var ((s,t) : string * term) : term =
  Apply ("eo::var", [Literal (String s); t])

(* post-elaboration terms *)
type flag =
  | Explicit
  | Implicit
  | Opaque

type eterm =
  | Literal of literal
  | Var of string
  | Const of (string * eparam list)
  | App of eterm * eterm
  | Meta of string * eterm list
  | Let of evar list * eterm
and eparam =
  string * eterm * flag
and evar =
  string * eterm
and ecases =
  (eterm * eterm) list

let app_list (t : eterm) (ts : eterm list) : eterm =
  List.fold_left (fun t_acc t' -> App (t_acc, t')) t ts

(* auxillary function used in elaboration of f-lists. *)
let glue (ps : param list) (f : eterm)
  (t1 : eterm) (t2 : eterm) : eterm
=
  match t1 with
  | Var s when is_list ps s ->
      Meta ("eo::list_concat",[f;t1;t2])
  | _ -> App (App (f,t1), t2)

let rec elab_tm
  (sgn, ps as ctx : signature * param list)
  (t : term) : eterm
=
  match t with
  (* ------------------------ *)
  | Literal l -> Literal l
  (* ------------------------ *)
  | Symbol s ->
    (
      match M.find_opt s sgn.prm with
      | Some ps -> Const (s, map (elab_param sgn) ps)
      | None -> Var s
    )
  (* ------------------------ *)
  | Bind (s, vs, t) ->
    if s = "eo::define" then
      Let (map (elab_var ctx) vs, elab_tm ctx t)
    else
      elab_binder ctx (s,vs,t)
  (* ------------------------ *)
  | Apply (s, ts) ->
    let ts' = map (elab_tm ctx) ts in
    if is_builtin s || is_program s then
      Meta (s, ts')
    else (* has `s` been registered in the signature?*)
      if is_tycon sgn s then
        Meta (s, ts')
      else
      match M.find_opt s sgn.prm with
      | Some ps ->
        elab_const ctx (s, ps, M.find_opt s sgn.att) ts
      | None ->
        app_list (Var s) ts'
and
  elab_const
    (sgn,ps as ctx : signature * param list)
    (s,qs,att : string * param list * attr option)
    (ts : term list) : eterm
  =
    let
      c = Const (s, map (elab_param sgn) qs) and
      ts' = map (elab_tm ctx) ts
    in
    let
      g  x y = glue ps c x y  and
      g' y x = glue ps c y x
    in
      match att with
      | Some (Attr ("right-assoc-nil", Some t_nil)) ->
        List.fold_right g ts' (elab_tm ctx t_nil)
      | Some (Attr ("left-assoc-nil", Some t_nil)) ->
        List.fold_left g' (elab_tm ctx t_nil) ts'
      | Some (Attr ("right-assoc", None)) ->
        let (xs, x) = split_last ts' in
        List.fold_right g xs x
      | Some (Attr ("left-assoc", None)) ->
        List.fold_left g' (List.hd ts') (List.tl ts')
      | _ -> app_list c ts'
and
  elab_binder
    (sgn,ps as ctx : signature * param list)
    : string * var list * term -> eterm
  =
    fun (s,vs,t) ->
    match M.find_opt s sgn.att with
    | Some (Attr ("binder", Some (Symbol t_cons))) ->
      let ts = map mk_eo_var vs in
      let ts' = elab_tm ctx (Apply (t_cons, ts)) in
      (* TODO. lookup params of binder symbol? *)
      let c = Const (s,[]) in
      App (App (c, ts'), elab_tm ctx t)
    | _ -> failwith "error: unregistered binder."
and
  elab_param (sgn : signature)
    : param -> eparam
  =
    fun (s,t,xs) ->
    let t' = elab_tm (sgn,[]) t in
    let fl =
      if List.mem (Attr ("implicit", None)) xs then
        Implicit
      else if List.mem (Attr ("opaque", None)) xs then
        Opaque
      else
        Explicit
    in
      (s,t',fl)
and
  elab_var (ctx : signature * param list)
    : var -> evar
  =
    fun (s,t) -> (s, elab_tm ctx t)

let elab_cases (ctx : signature * param list)
  : cases -> ecases
=
  fun cs ->
    let f (t,t') = (elab_tm ctx t, elab_tm ctx t') in
    List.map f cs

let rec free_in (t : eterm) (s : string) =
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

let free_params (ps : eparam list) (t : eterm) : (string * eterm) list =
  let f (s,ty,flg) =
    if free_in t s then Some (s,ty) else None
  in
    List.filter_map f ps

(* --------- pretty printing ---------- *)
let rec eterm_str : eterm -> string =
  function
  | Const (s,qs) ->
      let qs_str = String.concat " " (map eparam_str qs) in
      Printf.sprintf "%s⟦%s⟧" s qs_str
  | Var s -> s
  | Literal l -> literal_str l
  | App (t1,t2) ->
    Printf.sprintf "(_ %s %s)"
      (eterm_str t1)
      (eterm_str t2)
  | Let (xs, t) ->
    let xs_str = String.concat " " (List.map evar_str xs) in
    Printf.sprintf "(eo::define (%s) %s)" xs_str (eterm_str t)
  | Meta (s, ts) ->
    let ts_str = String.concat " " (List.map eterm_str ts) in
    Printf.sprintf "(%s %s)" s ts_str
and evar_str : (string * eterm) -> string =
  fun (s,t) ->
    Printf.sprintf "(%s %s)" s (eterm_str t)
and eparam_str : eparam -> string =
  fun (s,t,flag) ->
    match flag with
    | Explicit ->
        Printf.sprintf "(%s : %s)" s (eterm_str t)
    | Implicit ->
        Printf.sprintf "[%s : %s]" s (eterm_str t)
    | Opaque ->
        Printf.sprintf "⟬%s : %s⟭" s (eterm_str t)


    (* let rec subst ((s,t) : string * eterm) =
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

let rec splice (t : eterm)
  (ps : params) (ts : eterm list) : eterm
=
  match ps with
  | [] -> t
  | Param (s, _, xs) :: ps' ->
    if List.mem (Attr ("implicit", None)) xs then
      splice t ps' ts
    else
      let t' = subst (s, List.hd ts) t in
      splice t' ps' (List.tl ts) *)
