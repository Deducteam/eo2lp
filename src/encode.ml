module EO = Syntax_eo
open Syntax_lp

let encode_hook = ref (fun _ f -> f ())

let wrangle = fun s -> s
  |> replace ('.',"_")
  |> replace (':', "_")
  |> replace ('$', "!")
  |> replace ('@', "")
  |> replace ('/', "div")

(* LambdaPi reserved keywords that need renaming *)
let reserved_keywords = ["as"; "in"; "let"; "open"; "require"; "rule"; "symbol"; "with"]

let eo_name : string -> string =
  function
  (* qualify `Type`.  *)
  | "Type" -> "eo.Type"
  (* `as` maps to the Prelude's _as function *)
  | "as" -> "eo._as"
  (* qualify `eo::` operators. *)
  | s when S.starts_with ~prefix:"eo::" s ->
    "eo." ^ wrangle ((strip_prefix "eo::" s))
  (* `@X` is shorthand for `eo::X`, but only for single @ (not @@) *)
  | s when S.starts_with ~prefix:"@" s && not (S.starts_with ~prefix:"@@" s) ->
    "" ^ wrangle ((strip_prefix "@" s))
  (* rename other reserved keywords *)
  | s when L.mem s reserved_keywords -> s ^ "_"
  (* otherwise, replace forbidden chars. *)
  | s -> wrangle s

let rec eo_tm : EO.term -> term =
  function
  (* return `var [s]`.*)
  | Symbol s -> Var (eo_name s)

  (* return `lit l`*)
  | Literal l -> Lit l

  (* dispatch. *)
  | Apply (s,ts) ->
    begin match s,ts with
    | ("_") as s, [t1;t2] ->
      app_binop (Var "⋅") (eo_tm t1, eo_tm t2)

    | "->", _ ->
      app_arr (L.map eo_tm ts)

    | _  ->
      app_list (Var (eo_name s)) (L.map eo_tm ts)
    end

  (*  *)
  | Bind ("eo::define",xs,t) ->
    (* match. *)
    begin match xs with
    | [] -> eo_tm t
    | (x,tx) :: ys ->
      let t' = EO.Bind ("eo::define",ys,t) in
      Let (eo_name x, eo_tm tx, eo_tm t')
    end

  | _ as t -> Printf.ksprintf failwith
    "Term not fully elaborated: %s" (EO.term_str t)


let eo_att (atts : EO.attr list) : attr =
  if L.mem EO.Implicit atts
  then Implicit else Explicit

let eo_prm (ps : EO.param list) : param list =
  L.map (fun (s,t,atts) ->
    (eo_name s, tau_of (eo_tm t), eo_att atts)) ps

(* Get the type of a pattern variable from the program's pattern params *)
let get_pvar_type (qs : EO.param list) (s : string) : EO.term option =
  match L.find_opt (fun (s',_,_) -> s = s') qs with
  | Some (_, ty, _) -> Some ty
  | None -> None

(* Extract type params that are Types from the program's type params *)
let get_type_params (ps : EO.param list) : string list =
  L.filter_map (fun (s, ty, _) ->
    match ty with
    | EO.Symbol "Type" -> Some s
    | _ -> None
  ) ps

(* Insert explicit type args into pattern LHS.
   - For the program symbol itself, add type params as explicit args
   - For eo::List::cons, infer the type from the first argument

   The term structure uses ⋅ for higher-order application, so:
   - (f ⋅ x ⋅ y) is represented as App(App(Var "⋅", App(App(Var "⋅", f), x)), y)
   - We need to find the "real" head symbol by looking through ⋅ applications
*)
let rec insert_explicits_lhs
    (ps : EO.param list)  (* program's type params *)
    (qs : EO.param list)  (* program's pattern params *)
    (prog_sym : string)   (* the program symbol name *)
    (t : term)
  : term =
  (* Type params use BracketApp for [T] syntax in patterns *)
  let bracket_app_list head args =
    L.fold_left (fun acc arg -> BracketApp (acc, arg)) head args
  in
  let type_pvars = L.map (fun s -> PVar (eo_name s)) (get_type_params ps) in

  (* Flatten App structure into (head, args) *)
  let rec flatten_app acc = function
    | App (f, arg) -> flatten_app (arg :: acc) f
    | t -> (t, acc)
  in

  (* Check if this is a ⋅ application and extract the real head and args *)
  let rec extract_ho_app t =
    let (head, args) = flatten_app [] t in
    match head, args with
    | Var "⋅", [lhs; rhs] ->
      (* This is (lhs ⋅ rhs), recurse on lhs *)
      let (real_head, lhs_args) = extract_ho_app lhs in
      (real_head, lhs_args @ [rhs])
    | _ -> (head, args)
  in

  (* Rebuild the ⋅ application chain *)
  let rebuild_ho_app head args =
    match args with
    | [] -> head
    | _ -> L.fold_left (fun acc arg -> App (App (Var "⋅", acc), arg)) head args
  in

  match t with
  | App _ ->
    let (real_head, ho_args) = extract_ho_app t in
    begin match real_head with
    | Var s when s = eo_name prog_sym ->
      (* This is the program symbol - insert type params after it *)
      let args' = L.map (insert_explicits_lhs ps qs prog_sym) ho_args in
      (* Type params use BracketApp for [T] syntax, then regular args *)
      let head_with_types = bracket_app_list real_head type_pvars in
      app_list head_with_types args'
    | Var s when s = "eo.List__cons" ->
      (* eo::List::cons - infer type from first argument *)
      let args' = L.map (insert_explicits_lhs ps qs prog_sym) ho_args in
      begin match args' with
      | first_arg :: rest ->
        (* Try to get the type of the first argument *)
        let type_arg = infer_type_arg_with_ps ps qs first_arg in
        (* Type arg uses BracketApp for [T] syntax, then regular args with ⋅ *)
        let head_with_type = bracket_app_list real_head type_arg in
        rebuild_ho_app head_with_type args'
      | [] -> rebuild_ho_app real_head args'
      end
    | _ ->
      (* Other applications - recurse on args *)
      let args' = L.map (insert_explicits_lhs ps qs prog_sym) ho_args in
      rebuild_ho_app real_head args'
    end
  | _ -> t

(* Try to infer the type argument for a pattern term based on pattern params.
   ps is the program's type params - if the inferred type is one of these,
   we use PVar (pattern variable), otherwise Var (concrete type).
   Also, type variables from qs (pattern params with type Type) should be PVars. *)
and infer_type_arg_with_ps (ps : EO.param list) (qs : EO.param list) (t : term) : term list =
  let type_param_names = get_type_params ps in
  (* Also get type params from qs - pattern variables that have type Type *)
  let qs_type_param_names = get_type_params qs in
  let all_type_params = type_param_names @ qs_type_param_names in
  match t with
  | PVar s ->
    (* Look up the pattern variable's type in qs *)
    let s_unmangled =
      (* Undo the eo_name mangling for lookup *)
      if S.starts_with ~prefix:"!" s then "$" ^ S.sub s 1 (S.length s - 1)
      else s
    in
    begin match get_pvar_type qs s_unmangled with
    | Some (EO.Symbol ty_name) ->
      (* If ty_name is a type parameter (from ps or qs), use PVar; else Var *)
      if L.mem ty_name all_type_params then
        [PVar (eo_name ty_name)]
      else
        [Var (eo_name ty_name)]
    | _ -> []
    end
  | _ -> []

(* Symbols that have implicit type parameters when used as values *)
let symbols_needing_type_param = ["eo::List::cons"; "List::cons"]

(* Check if a term contains any symbol that needs a type parameter when used as a value.
   Returns a list of (symbol_name, fresh_param_name) pairs. *)
let find_unapplied_poly_symbols (t : EO.term) : (string * string) list =
  let counter = ref 0 in
  let fresh_name () =
    let n = !counter in
    counter := n + 1;
    Printf.sprintf "v%d" n
  in
  let rec aux t =
    match t with
    | EO.Symbol s when L.exists (fun prefix -> S.ends_with ~suffix:prefix s) symbols_needing_type_param ->
      (* This symbol is used as a value without being applied - needs type param *)
      [(s, fresh_name ())]
    | EO.Symbol _ -> []
    | EO.Literal _ -> []
    | EO.Apply (_, ts) -> L.concat_map aux ts
    | EO.Bind (_, xs, t') ->
      let from_xs = L.concat_map (fun (_, t'') -> aux t'') xs in
      from_xs @ aux t'
  in
  aux t

(* Transform a term to apply fresh type parameters to symbols that need them.
   param_map is a list of (symbol_name, param_name) pairs. *)
let rec apply_fresh_type_params (param_map : (string * string) list) (t : term) : term =
  match t with
  | Var s ->
    (* Check if this symbol needs a type param *)
    begin match L.find_opt (fun (sym, _) -> eo_name sym = s) param_map with
    | Some (_, param_name) -> BracketApp (Var s, Var param_name)
    | None -> t
    end
  | App (f, arg) -> App (apply_fresh_type_params param_map f, apply_fresh_type_params param_map arg)
  | BracketApp (f, arg) -> BracketApp (apply_fresh_type_params param_map f, apply_fresh_type_params param_map arg)
  | Bind (b, ps, body) ->
    let ps' = L.map (fun (x, ty, attr) -> (x, apply_fresh_type_params param_map ty, attr)) ps in
    Bind (b, ps', apply_fresh_type_params param_map body)
  | Let (x, e, body) -> Let (x, apply_fresh_type_params param_map e, apply_fresh_type_params param_map body)
  | Arrow (t1, t2) -> Arrow (apply_fresh_type_params param_map t1, apply_fresh_type_params param_map t2)
  | _ -> t

(* Types that should be aliased to Prelude/Stdlib types instead of being fresh constants *)
let type_aliases = [
  ("Int", "eo.Z");   (* Int -> Z (which is int from Stdlib) *)
  ("Real", "eo.Q");  (* Real -> Q (rationals) *)
]

let eo_const (s,k : string * EO.const) : command list =
  !encode_hook s (fun () ->
    match k with
    | Decl (ps, EO.Symbol "Type", _) when L.mem_assoc s type_aliases ->
    (* This is a type declaration that should be an alias *)
    let alias_target = L.assoc s type_aliases in
    [
      Symbol (
        None, eo_name s,
        [],
        Some (Var "Set"),
        Some (Var alias_target)
      )
    ]

    | Decl (ps,ty,_) ->
    (* Check if the type contains symbols that need fresh type parameters *)
    let poly_symbols = find_unapplied_poly_symbols ty in
    let fresh_params = L.map (fun (_, name) -> (name, Var "Set", Implicit)) poly_symbols in
    let ty_encoded = eo_tm ty in
    let ty_with_params = apply_fresh_type_params poly_symbols ty_encoded in
    [
      Symbol (
        Some Constant, eo_name s,
        fresh_params @ eo_prm ps,
        Some (tau_of ty_with_params),
        None
      )
    ]

    | Prog ((ps,ty),(qs,cs)) ->
    let sym = Symbol (
        Some Sequential, eo_name s,
        eo_prm ps,
        Some (tau_of @@ eo_tm ty),
        None
      )
    in
    if cs = [] then
      (* Forward declaration with no cases - just emit the symbol *)
      [sym]
    else
      (* Encode LHS with explicit type params, RHS without *)
      let encode_lhs t =
        let t' = bind_pvars qs (eo_tm t) in
        insert_explicits_lhs ps qs s t'
      in
      let encode_rhs t = bind_pvars qs (eo_tm t) in
      [sym; Rule (L.map (fun (lhs, rhs) -> (encode_lhs lhs, encode_rhs rhs)) cs)]

    | Defn ([], EO.Symbol _) ->
    (* Skip encoding macro-like definitions: (define @foo () @@foo)
       These are expanded during elaboration and should not appear in LambdaPi. *)
    []

    | Defn (ps,t) ->
    [
      Symbol (None, eo_name s,
        eo_prm ps, None,
        Some (eo_tm t))
    ]

    | Rule _ -> []
  )

let eo_sig : EO.signature -> signature =
  L.concat_map eo_const
