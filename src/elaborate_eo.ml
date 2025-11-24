module EO = struct
  include Syntax_eo
  include Interface_eo
end

type term = EO.term
type literal = EO.literal
type param = EO.param
type judgement = EO.judgement

(* post-elaboration terms *)
type eterm =
  | Symbol of string
  | Literal of literal
  | App of eterm * eterm
  | Let of (string * eterm) list * eterm
  | Meta of string * eterm list

type eparam =
  | Explicit of string * eterm
  | Implicit of string * eterm

let rec eterm_str : eterm -> string =
  function
  | Symbol s -> s
  | Literal l -> EO.literal_str l
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

let glue (ps : param list) (f : eterm)
  : eterm -> eterm -> eterm
=
  fun t1 t2 ->
    match t1 with
    | Symbol s when
        EO.var_has_attr ps s (Attr ("list", None))
      -> Meta ("eo::list_concat",[f;t1;t2])
    | _ -> App (App (f,t1), t2)

let split_last (xs : 'a list) : ('a list * 'a) =
  let ys = List.rev xs in
  (List.rev (List.tl ys), List.hd ys)

let app_list (t : eterm) (ts : eterm list) : eterm =
  List.fold_left (fun t_acc t' -> App (t_acc, t')) t ts

let mk_eo_var ((s,t) : string * term) : term =
  Apply ("eo::var", [Literal (String s); t])

let rec elab (js : judgement list) (ps : param list)
  : term -> eterm
=
  function
  | Symbol s -> Symbol s
  | Literal l -> Literal l
  | Bind ("eo::define", xs, t) ->
    let xs' =
      List.map (fun (s,t) -> (s, elab js ps t)) xs
    in
      Let (xs', elab js ps t)
  | Bind (s, xs, t) ->
    (
      match EO.const_get_attr js s with
      | Some (Attr ("binder", Some (Symbol cons))) ->
        let vs = List.map mk_eo_var xs in
        let vs_tm = elab js ps (EO.Apply (cons, vs)) in
        App (App (Symbol s, vs_tm), elab js ps t)
      | None -> failwith (Printf.sprintf
          "Symbol %s not declared as :binder." s)
    )
  | Apply (s, ts) ->
    let g  = glue ps (Symbol s) in
    let g' = fun x y -> g y x in
    let ts' = List.map (elab js ps) ts in
    match EO.const_get_attr js s with
    | Some (Attr ("right-assoc-nil", Some t_nil)) ->
      List.fold_right g ts' (elab js ps t_nil)
    | Some (Attr ("left-assoc-nil", Some t_nil)) ->
      List.fold_left g' (elab js ps t_nil) ts'
    | Some (Attr ("right-assoc", None)) ->
      let (xs, x) = split_last ts' in
      List.fold_right g xs x
    | Some (Attr ("left-assoc", None)) ->
      List.fold_left g' (List.hd ts') (List.tl ts')
    | None ->
      if EO.is_builtin s || EO.is_program s || s = "->" then
        Meta (s, ts')
      else
        app_list (Symbol s) ts'

let implicit_attr : EO.attr = Attr ("implicit", None)

let elab_param (js : judgement list) : param -> eparam =
  function
  | Param (s,t,xs) ->
    if List.mem implicit_attr xs then
      Implicit (s, elab js [] t)
    else
      Explicit (s, elab js [] t)
