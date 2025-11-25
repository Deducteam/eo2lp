open Syntax_eo
open Context_eo

let split_last (xs : 'a list) : ('a list * 'a) =
  let ys = List.rev xs in
  (List.rev (List.tl ys), List.hd ys)

(* post-elaboration terms *)
type eterm =
  | Symbol of string
  | Literal of literal
  | App of eterm * eterm
  | Let of (string * eterm) list * eterm
  | Meta of string * eterm list
and eparam =
  | Explicit of string * eterm
  | Implicit of string * eterm


let app_list (t : eterm) (ts : eterm list) : eterm =
  List.fold_left (fun t_acc t' -> App (t_acc, t')) t ts

let mk_eo_var ((s,t) : string * term) : term =
  Apply ("eo::var", [Literal (String s); t])

(* auxillary function used in elaboration of f-lists. *)
let glue (ctx : context) (f : eterm)
  (t1 : eterm) (t2 : eterm) : eterm
=
  match t1 with
  | Symbol s when is_list ctx s ->
    Meta ("eo::list_concat",[f;t1;t2])
  | _ -> App (App (f,t1), t2)

(* elaboration *)
let rec elab (sgn : signature) (ctx : context)
  : term -> eterm
=
  function
  (* ------------------------ *)
  | Symbol s -> Symbol s
  (* ------------------------ *)
  | Literal l -> Literal l
  (* ------------------------ *)
  | Bind ("eo::define", xs, t) ->
    let xs' = elab_vars sgn ctx xs in
    Let (xs', elab sgn ctx t)
  (* ------------------------ *)
  | Bind (s, xs, t) ->
    elab_binder sgn ctx (s,xs,t)
  (* ------------------------ *)
  | Apply (s, ts) ->
    let g  = glue ctx (Symbol s) in
    let g' = fun x y -> g y x in
    let ts' = List.map (elab sgn ctx) ts in
    match M.find_opt s sgn.atts with
    | Some (_, Attr ("right-assoc-nil", Some t_nil)) ->
      List.fold_right g ts' (elab sgn ctx t_nil)
    | Some (_, Attr ("left-assoc-nil", Some t_nil)) ->
      List.fold_left g' (elab sgn ctx t_nil) ts'
    | Some (_, Attr ("right-assoc", None)) ->
      let (xs, x) = split_last ts' in
      List.fold_right g xs x
    | Some (_, Attr ("left-assoc", None)) ->
      List.fold_left g' (List.hd ts') (List.tl ts')
    | _ ->
      if is_builtin s || is_program s || s = "->" then
        Meta (s, ts')
      else
        app_list (Symbol s) ts'
and
  elab_vars = fun sgn ctx xs ->
    List.map (fun (s,t) -> (s, elab sgn ctx t)) xs
and
  elab_binder = fun sgn ctx (s,xs,t) ->
    match M.find_opt s sgn.atts with
    | Some (_, Attr ("binder", Some (Symbol cons))) ->
      let vs = List.map mk_eo_var xs in
      let vs_tm = elab sgn ctx (Apply (cons, vs)) in
      App (
        App (Symbol s, vs_tm),
        elab sgn ctx t
      )
    | _ -> failwith (Printf.sprintf
      "Symbol %s not a valid :binder." s)
and
  elab_param = fun sgn ctx ->
    let implicit_attr =
      Attr ("is_implicit", None)
    in function
    | Param (s,t,xs) ->
      let t' = elab sgn ctx t in
      if List.mem implicit_attr xs then
        Implicit (s, t')
      else
        Explicit (s, t')




(* --------- pretty printing ---------- *)
let rec eterm_str : eterm -> string =
  function
  | Symbol s -> s
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
