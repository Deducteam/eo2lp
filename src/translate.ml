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
  ||
    String.contains s '.'
  )

let app_list (lv : level) (t,ts : term * term list) : term =
  List.fold_left
    (fun t_acc t -> App (lv, t_acc, t))
    t ts

let splice (c, s : char * string) (str : string) : string =
  let xs = String.split_on_char c str in
  String.concat s xs

let strip_prefix (str : string) (pre : string) : string =
  let n = String.length pre in
  let m = String.length str in
  (String.sub str n (m - n))

  let rec translate_symbol : string -> string =
  function
  | s when String.starts_with ~prefix:"$" s ->
    "!" ^ translate_symbol (strip_prefix s "$")
  | s when String.starts_with ~prefix:"@@" s ->
    "_" ^ translate_symbol (strip_prefix s "@@")
  | s when String.starts_with ~prefix:"eo::" s ->
    "eo." ^
    translate_symbol (strip_prefix s "eo::")
  | s ->
    let s' = s |> splice ('.',"⋅") |> splice (':', "⋅") in
    if is_forbidden s' then
      Printf.sprintf "{|%s|}" s
    else
      s'


let rec translate_term (exp : bool) : EO.term -> term =
  begin function
  | Leaf l -> translate_leaf exp l
  (* ------------ *)
  | App (O,t,t') ->
    App (O, translate_term exp t, translate_term exp t')
  (* ------------ *)
  | App (M,t,t') ->
    App (M, translate_term exp t, translate_term exp t')
  (* ------------ *)
  | Arrow (_, ts) ->
    let ts' = List.map (translate_term exp) ts in
    Arrow (O, ts')
  | Let (s,t,t') ->
    Let (
      translate_symbol s,
      translate_term exp t,
      translate_term exp t'
    )
  end
and translate_leaf (exp : bool) : EO.leaf -> term =
  begin function
  | Literal l ->
    failwith "literal translation not implemented yet."
  | MVar i -> failwith "can't translate Eunoia metavariable."
  | Type -> failwith "can't translate TYPE at term level."
  | Kind -> failwith "can't translate KIND at term level."
  | Const ("eo::requires", p :: (_, Leaf Type) :: pm) ->
    translate_leaf exp (Const ("eo::requires_type_out", pm))
  | Const ("eo::requires", (_, Leaf Type) :: pm) ->
    translate_leaf exp (Const ("eo::requires_type_in", pm))
  | Const (s,pm) -> (
      Leaf (Const (translate_symbol s)),
      if exp then translate_pmap pm else []
    ) |> app_list M
  | Var s -> Leaf (Var (translate_symbol s))
  end
and translate_pmap (pm : EO.pmap) : term list =
  List.map (fun (_, t) -> Wrap (translate_term true t)) pm
and translate_type : EO.term -> term =
  begin function
  | Leaf Kind -> Leaf Type
  | Leaf Type -> Leaf Set
  | Arrow (M, ts) ->
    let ts' = List.map (translate_type) ts in
    Arrow (M, ts')
  | _ as t -> El (translate_term true t)
  end

let translate_param (s,t,att : EO.param) : param =
  let (s',t') = (translate_symbol s, translate_type t) in
  match att with
  | Explicit -> (s', t', Explicit)
  | Implicit -> (s', t', Implicit)
  | Opaque ->
    Printf.printf "WARNING: unhandled :opaque attribute\n";
    (s', t', Explicit)
  | List ->
    Printf.printf "WARNING: unhandled :list attribute\n";
    (s', t', Explicit)

let translate_params (ps : EO.param list) : param list =
  List.map translate_param ps

let bind_pvars (ps : param list) : term -> term =
  let f : leaf -> term =
    function
    | Var s ->
      if in_params s ps then
        Leaf (PVar s)
      else
        Leaf (Var s)
    | _ as l -> Leaf l
  in
    map_leaves f

let translate_cases
  (ps : EO.param list) (cs : EO.case list) : case list =
  let f (t,t') =
    (translate_term true t, translate_term false t')
  in
  let ds = List.map f cs in
  let qs = List.map translate_param ps in
  map_cases (bind_pvars qs) ds

let translate_command : EO.command -> command list =
  function
  | Decl (s,ps,t) ->
    let (qs,t') = EO.bind_mvars (ps,t) in
    [
      Symbol (
        Some Constant,
        translate_symbol s,
        translate_params qs,
        Some (translate_type t'),
        None
      )
    ]
  | Prog (s,(ps,t),(qs,cs)) ->
    List.append
    [
      Symbol (
        Some Sequential,
        translate_symbol s,
        translate_params ps,
        Some (translate_type t),
        None
      );
    ]
    (if cs = [] then [] else [Rule (translate_cases qs cs)])
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
