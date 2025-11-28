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
  | TyApp of string * eterm list
and eparam =
  | Explicit of string * eterm
  | Implicit of string * eterm
and ecases = (eterm * eterm) list

let app_list (t : eterm) (ts : eterm list) : eterm =
  List.fold_left (fun t_acc t' -> App (t_acc, t')) t ts

let mk_eo_var ((s,t) : string * term) : term =
  Apply ("eo::var", [Literal (String s); t])

(* auxillary function used in elaboration of f-lists. *)
let glue (ps : params) (f : eterm)
  (t1 : eterm) (t2 : eterm) : eterm
=
  match t1 with
  | Symbol s when is_list ps s ->
    Meta ("eo::list_concat",[f;t1;t2])
  | _ -> App (App (f,t1), t2)

let rec elab_tm (sgn : signature) (ps : params)
  : term -> eterm
=
  function
  (* ------------------------ *)
  | Symbol s -> Symbol s
  (* ------------------------ *)
  | Literal l -> Literal l
  (* ------------------------ *)
  | Bind ("eo::define", xs, t) ->
    let xs' = elab_vars sgn ps xs in
    Let (xs', elab_tm sgn ps t)
  (* ------------------------ *)
  | Bind (s, xs, t) ->
    elab_binder sgn ps (s,xs,t)
  (* ------------------------ *)
  | Apply (s, ts) ->
    let
      ts' = List.map (elab_tm sgn ps) ts
    in
      let g  = glue ps (Symbol s) in
      let g' = fun x y -> g y x in
      (
        match M.find_opt s sgn.atts with
        | Some (_, Attr ("right-assoc-nil", Some t_nil)) ->
          List.fold_right g ts' (elab_tm sgn ps t_nil)
        | Some (_, Attr ("left-assoc-nil", Some t_nil)) ->
          List.fold_left g' (elab_tm sgn ps t_nil) ts'
        | Some (_, Attr ("right-assoc", None)) ->
          let (xs, x) = split_last ts' in
          List.fold_right g xs x
        | Some (_, Attr ("left-assoc", None)) ->
          List.fold_left g' (List.hd ts') (List.tl ts')
        | _ ->
          if is_builtin s || is_program s then
            Meta (s,ts')
          else if s = "->" then
            TyApp ("->", ts')
          else
            app_list (Symbol s) ts'
      )
    | Bang (t,xs)-> elab_tm sgn ps t
and
  elab_vars = fun sgn ps xs ->
    List.map (fun (s,t) -> (s, elab_tm sgn ps t)) xs
and
  elab_binder = fun sgn ps (s,xs,t) ->
    match M.find_opt s sgn.atts with
    | Some (_, Attr ("binder", Some (Symbol cons))) ->
      let vs = List.map mk_eo_var xs in
      let vs_tm = elab_tm sgn ps (Apply (cons, vs)) in
      App (
        App (Symbol s, vs_tm),
        elab_tm sgn ps t
      )
    | _ -> failwith (Printf.sprintf
      "Symbol %s not a valid :binder." s)
and
  elab_param = fun sgn ->
    function
    | Param (s,t,xs) ->
      let t' = elab_ty sgn [] t in
      if List.mem (Attr ("implicit", None)) xs then
        Implicit (s, t')
      else
        Explicit (s, t')
  and elab_ty (sgn : signature) (ps : params) : term -> eterm =
  function
    | Symbol s -> Symbol s
    | Literal l -> Literal l
    | Bind ("eo::define", xs, t) ->
        let xs' = elab_vars sgn ps xs in
        Let (xs', elab_ty sgn ps t)
    | Bind (s, xs, t) ->
        failwith "ERROR. :binder in type?"
    | Apply (s,ts) ->
      let ts' = List.map (elab_ty sgn ps) ts in
      if is_builtin s || is_program s then
        Meta (s, ts')
      else
        TyApp (s, ts')
    | Bang (t,_) -> elab_ty sgn ps t


let elab_params (sgn : signature) =
  List.map (elab_param sgn)

let elab_cases (sgn : signature)
  (ps : params) (cs : cases) : ecases
=
  let e = elab_tm sgn ps in
  let f = (fun (t,t') -> (e t, e t')) in
  List.map f cs

let rec free_in (t : eterm) (s : string) =
  match t with
  | Symbol s' -> s = s'
  | Literal l -> false
  | App (t1,t2) -> free_in t1 s || free_in t2 s
  | Meta (s', ts) -> List.exists (fun t' -> free_in t' s) ts
  | TyApp (s', ts) -> List.exists (fun t' -> free_in t' s) ts
  | Let (xs, t') ->
      let b =
        List.exists (fun (s',t') ->
          if s = s' then failwith "variable capture"
          else free_in t' s) xs
      in
        b || free_in t' s

let free_params (ps : eparam list) (t : eterm) : (string * eterm) list =
  let f (Explicit (s, ty) | Implicit (s, ty)) =
    if free_in t s then Some (s,ty) else None
  in
    List.filter_map f ps

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
  | TyApp (s, ts) | Meta (s, ts) ->
    let ts_str = String.concat " " (List.map eterm_str ts) in
    Printf.sprintf "(%s %s)" s ts_str
and evar_str : (string * eterm) -> string =
  fun (s,t) ->
    Printf.sprintf "(%s %s)" s (eterm_str t)

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
