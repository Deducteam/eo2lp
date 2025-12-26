(* importing Eunoia stuff. *)
module EO = struct
  include Desugar
  include Elaborate
end

open Syntax_lp

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

let app_list (t : term) (ts : term list) : term =
  List.fold_left
    (fun t_acc t -> App (t_acc, t))
    t ts

let mk_arrow_typ ((t,t') : term * term) : term =
  Bind (Pi, [Explicit ("_",t)], t')

let mk_arrow_typ_list (ts : term list) : term =
  let (init, last) = EO.split_last ts in
  List.fold_right
    (fun t_acc t -> mk_arrow_typ (t_acc, t))
    init last

let mk_set_arrow_typ ((t,t') : term * term) : term =
  App (App (Leaf (Const "⤳"), t), t')

let mk_set_arrow_typ_list (ts : term list) : term =
  let (init, last) = EO.split_last ts in
  List.fold_right
    (fun t_acc t -> mk_set_arrow_typ (t_acc, t))
    init last

let mk_sqapp (t,t' : term * term) : term =
  App (App (Leaf (Const "▫"), t),t')

let rec translate_term : EO.term -> term =
  begin function
  | Leaf l ->
    translate_leaf l
  (* ------------ *)
  | App (O, t,t') ->
    mk_sqapp (translate_term t, translate_term t')
  (* ------------ *)
  | App (M,t,t') ->
    App (translate_term t, translate_term t')
  (* ------------ *)
  | Arrow (O, ts) ->
    let ts' = List.map translate_term ts in
    mk_set_arrow_typ_list ts'
  | Arrow (M,ts) ->
    failwith "Type level arrow found at term level."
  | Let ((s,t), t') ->
    Let (
      (translate_symbol s, translate_term t),
      translate_term t'
    )
  end
and translate_leaf : EO.leaf -> term =
  begin function
  | Literal l ->
    failwith "literal translation not yet implemented."
  | MVar i ->
    failwith "can't translate a term with an mvar."
  | Type ->
    failwith "can't translate TYPE at term level."
  | Kind ->
    failwith "can't translate KIND at term level."
  | Const (s,qs) ->
    let f = Leaf (Const (translate_symbol s)) in
    let ts = List.map
      (fun (_, EO.This t) -> Wrap (translate_term t)) qs in
    app_list f ts
  | Var s -> Leaf (Var (translate_symbol s))
  end
and translate_type : EO.term -> term =
  begin function
  | Leaf Kind -> Leaf Type
  | Leaf Type -> Leaf (Const "Set")
  | Arrow (M, ts) ->
    let ts' = List.map translate_type ts in
    mk_arrow_typ_list ts'
  | Let ((s,t),t') ->
    failwith "Can't translate Let as a type."
  | _ as t -> App (Leaf (Const "El"), translate_term t)
  end

let translate_param (s,t,att : EO.param) : param =
  let (s',t') = (translate_symbol s, translate_type t) in
  match att with
  | Explicit -> Explicit (s',t')
  | Implicit -> Implicit (s',t')
  | Opaque   ->
      Printf.printf "WARNING: unhandled :opaque attribute";
      Explicit (s',t')

let translate_params (ps : EO.param list) : param list =
  List.map translate_param ps

let translate_cases (cs : EO.case list) : case list =
  let
    f (t,t') = (translate_term t, translate_term t')
  in
    List.map f cs

let translate_command : EO.command -> command list =
  function
  | Decl (s,ps,t) ->
    [
      Symbol (
        Some Constant,
        translate_symbol s,
        translate_params ps,
        Some (translate_type t),
        None
      )
    ]
  | Prog (s,ps,t,cs) ->
    [
      Symbol (
        Some Sequential,
        translate_symbol s,
        translate_params ps,
        Some (translate_type t),
        None
      );
      Rule (translate_cases cs)
    ]
  | Defn _ -> failwith "can't translate definition."
  | Rule _ -> failwith "can't translate rule declaration."

(* TODO.
  insertion of implicits needs to happen on the lhs and rhs
  of declarations for definitions and programs.
  this needs to be done after translation.

  for the rhs: we need to apply [..] to constants with
  implicit parameters that are 'waiting'.

  for the lhs: we need to find all of 'free parameters' on the rhs.

  alternatively, we can insert during elaboration.
  but we have no good way of knowing which parameters
  need to have 'wrapped' applications.

  if the constant is not applied to anything,
  then we know we need all of them.

  if the constant is fully applied, then we don't need any.

  if it's partially applied, then it depends on where the
  implicit parameters appear in the type of the symbol.

  maybe this is fine, but it wouldn't surprise me if
  there are many cases were programs/builtins are
  partially applied.

  the general case obviously requires type inference with
  ho-unification. better to do this pre or post elaboration?

  probably pre-elaboration. then we can easily check if
  symbols are type constructors.
*)

(* TODO. refactor to a special case of a map_lp_tm function?. *)
(* i.e., translate_cases : eparam list -> ecases -> cases *)
(* let rec bind_pvars (xs : param list) : term -> term =
  function
  | PVar s ->
      Printf.printf
      "WARNING: Pattern variables already present in term.";
      PVar s
  | Var s ->
      if in_params s xs then (PVar s) else (Var s)
  | App (t,t') ->
      App (bind_pvars xs t, bind_pvars xs t')
  | Bind (b, ys, t) ->
      (* TODO. refactor lambdapi parameters? *)
      let ys' = List.map (function
        | Explicit (s,t) -> Explicit (s, bind_pvars xs t)
        | Implicit (s,t) -> Implicit (s, bind_pvars xs t)
      ) ys
      in
        Bind (b, ys', bind_pvars xs t)
  | Let ((s,t), t') ->
      Let ((s, bind_pvars xs t), bind_pvars xs t')

let bind_pvars_cases (xs : param list) (cs : cases) : cases =
  let f (t,t') = (bind_pvars xs t, bind_pvars xs t') in
  List.map f cs *)
