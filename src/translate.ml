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

let mk_set_arrow_typ ((t,t') : LP.term * LP.term) : LP.term =
  App (App (Var "⤳", t), t')

let mk_set_arrow_typ_list (ts : LP.term list) : LP.term =
  let (init, last) = EO.split_last ts in
  List.fold_right
    (fun t_acc t -> mk_set_arrow_typ (t_acc, t))
    init last

(* TODO. review translation function wrt. elaboration.
  in particular, are we properly handling arrows?*)
let rec translate_tm : EO.eterm ->  LP.term =
  function
  | Const (s,qs) ->
    (* TODO. contemplate insertion of implicit parameters. *)
    let f = function
      | (s,_,EO.Implicit) -> Some (LP.Wrap (Var s))
      | _ -> None
    in
    app_list (Var (translate_symbol s)) (List.filter_map f qs)
  (* ------------ *)
  | Var s -> Var (translate_symbol s)
  (* ------------ *)
  | Literal l -> Var (EO.literal_str l)
  (* ------------ *)
  | Let (xs, t') -> (
      match xs with
      | [] -> translate_tm t'
      | (s,t) :: ys ->
        Let (
          (translate_symbol s, translate_tm t),
          translate_tm (Let (ys, t'))
        )
    )
  (* ------------ *)
  | App (t1,t2) ->
    App (
      App (Var "▫", translate_tm t1),
      translate_tm t2
    )
  (* ------------ *)
  | Meta (s, ts) ->
    let s' = translate_symbol s in
    let ts' = List.map translate_tm ts in
    if s = "->" then
      mk_set_arrow_typ_list ts'
    else
      app_list (Var s') ts'

let rec translate_ty : EO.eterm -> LP.term =
  function
  (* ------------ *)
  | Var s ->
    if s = "Type" then
      (Var "Set")
    else
      App (Var "El", Var (translate_symbol s))
  (* ------------ *)
  | Meta (s, ts) ->
    let s' = translate_symbol s in
    let ts' = List.map translate_ty ts in
    if s = "->" then
      mk_arrow_typ_list ts'
    else
      app_list (Var s') ts'
  (* ------------ *)
  | _ as t -> App (Var "El", translate_tm t)

let translate_param (s,t,flag : EO.eparam) : LP.param =
  let (s',t') = (translate_symbol s, translate_ty t) in
  match flag with
  | Explicit -> Explicit (s',t')
  | Implicit -> Implicit (s',t')
  | Opaque   ->
      Printf.printf "WARNING: unhandled :opaque attribute";
      Explicit (s',t')

(* TODO. refactor to a special case of a map_lp_tm function?. *)
(* i.e., translate_cases : eparam list -> ecases -> LP.cases *)
let rec bind_pvars (xs : LP.param list) : LP.term -> LP.term =
  function
  | PVar s ->
      Printf.printf
      "WARNING: Pattern variables already present in term.";
      PVar s
  | Var s ->
      if LP.in_params s xs then (PVar s) else (Var s)
  | App (t,t') ->
      App (bind_pvars xs t, bind_pvars xs t')
  | Bind (b, ys, t) ->
      (* TODO. refactor lambdapi parameters? *)
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
