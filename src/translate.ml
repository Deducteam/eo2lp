(* importing Eunoia stuff. *)
module EO = struct
  include Syntax_eo
  include Elaborate
end

(* importing LambdaPi stuff. *)
module LP = Syntax_lp

let is_forbidden (s : string) : bool =
  (
    String.contains s '$'
  ||
    String.contains s '@'
  ||
    String.contains s ':'
  )

let translate_symbol (s : string) : string =
  if is_forbidden s then
    Printf.sprintf "{|%s|}" s
  else
    s

let mk_set_arrow_typ (ts : LP.term list) : LP.term =
  List.fold_left
    (fun t_acc t -> LP.App (LP.App (LP.Var "⤳", t_acc), t))
    (List.hd ts) (List.tl ts)

let app_list (t : LP.term) (ts : LP.term list) : LP.term =
  List.fold_left
    (fun t_acc t -> LP.App (t_acc, t))
    t ts

let mk_arrow_typ ((t,t') : LP.term * LP.term) : LP.term =
  Bind (Pi, [Explicit ("_",t)], t')

let mk_arrow_typ_list (ts : LP.term list) : LP.term =
  let (init, last) = EO.split_last ts in
  List.fold_right
    (fun t_acc t -> mk_arrow_typ (t_acc, t))
    init last


let rec translate_tm : EO.eterm ->  LP.term =
  function
  | Symbol s ->
      if s = "->" then
        (Var "⤳")
      else
        Var (translate_symbol s)
  | Literal l -> Var (EO.literal_str l)
  | Let (xs, t') -> (
      match xs with
      | [] -> translate_tm t'
      | (s,t) :: ys ->
        Let (
          (translate_symbol s, translate_tm t),
          translate_tm (Let (ys, t'))
        )
    )
  | App (t1,t2) ->
    App (
      App (Var "▫", translate_tm t1),
      translate_tm t2
    )
  | Meta (s, ts) ->
    let s' = translate_symbol s in
    let ts' = List.map translate_tm ts in
    app_list (Var s') ts'

let rec translate_ty : EO.eterm -> LP.term =
  function
  | Symbol s ->
    if s = "Type" then
      (Var "Set")
    else
      App (Var "El", Var (translate_symbol s))
  | Meta ("->", ts) ->
    let ts' = List.map translate_ty ts in
    mk_arrow_typ_list ts'
  | _ as t ->
    App (Var "El", translate_tm t)

let translate_param : EO.eparam -> LP.param =
  function
  | Explicit (s,t) ->
      Explicit (translate_symbol s, translate_ty t)
  | Implicit (s,t) ->
    Implicit (translate_symbol s, translate_ty t)

let rec bind_pvars (xs : LP.param list) : LP.term -> LP.term =
  function
  | PVar s -> Printf.printf
      "WARNING: Pattern variables already present in term.";
      PVar s
  | Var s ->
      if LP.in_params s xs then (PVar s) else (Var s)
  | App (t,t') ->
      App (bind_pvars xs t, bind_pvars xs t')
  | Bind (b, ys, t) ->
      let ys' = List.map (function
        | LP.Explicit (s,t) -> LP.Explicit (s, bind_pvars xs t)
        | LP.Implicit (s,t) -> LP.Implicit (s, bind_pvars xs t)
      ) ys
      in
        Bind (b, ys', bind_pvars xs t)
  | Let ((s,t), t') ->
      Let ((s, bind_pvars xs t), bind_pvars xs t')

let bind_pvars_cases (xs : LP.param list) (cs : LP.cases) : LP.cases =
  let f (t,t') = (bind_pvars xs t, bind_pvars xs t') in
  List.map f cs

let translate_params (ps : EO.eparam list) : LP.param list =
  List.map translate_param ps

let translate_cases (cs : EO.ecases) : LP.cases =
  let
    f (t,t') = (translate_tm t, translate_tm t')
  in
    List.map f cs
