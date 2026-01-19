module EO = Syntax_eo
open Syntax_lp

let encode_hook = ref (fun _ f -> f ())

(* Track overloaded symbol counts for name mangling.
   Maps base name -> count of declarations seen so far.
   First occurrence gets no suffix, second gets ', third gets '', etc. *)
let overload_counts : (string, int) Hashtbl.t = Hashtbl.create 32

let reset_overload_counts () = Hashtbl.clear overload_counts

(* Get the mangled name for an overloaded symbol.
   Returns the name with appropriate number of ' suffixes. *)
let get_overloaded_name (base_name : string) : string =
  let count = match Hashtbl.find_opt overload_counts base_name with
    | Some n -> n
    | None -> 0
  in
  Hashtbl.replace overload_counts base_name (count + 1);
  if count = 0 then base_name
  else base_name ^ String.make count '\''

(* Lookup table for resolving overloaded symbols during elaboration.
   Maps (base_name, index) -> mangled_name, where index is 0-based. *)
let overload_table : (string * int, string) Hashtbl.t = Hashtbl.create 32

let clear_overload_table () = Hashtbl.clear overload_table

let add_overload_entry (base_name : string) (index : int) (mangled_name : string) : unit =
  Hashtbl.add overload_table (base_name, index) mangled_name

let get_overload_entry (base_name : string) (index : int) : string option =
  Hashtbl.find_opt overload_table (base_name, index)

let wrangle = fun s -> s
  |> replace ('.',"_")
  |> replace (':', "_")
  |> replace ('$', "!")
  |> replace ('@', "")
  |> replace ('/', "div")

let is_nary_binop s = match s with
  | "eo::and" | "eo::or" | "eo::xor" | "eo::add" | "eo::mul" | "eo::concat" -> true
  | _ -> false

(* LambdaPi reserved keywords that need renaming *)
let reserved_keywords = ["as"; "in"; "plet"; "open"; "require"; "rule"; "symbol"; "with"]

let eo_name : string -> string =
  function
  (* qualify `Type`.  *)
  | "Type" -> "eo.Type"
  | "Set" -> "eo_Set"
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

(* Parameter context for looking up types of quoted symbols *)
let param_ctx : EO.param list ref = ref []

let lookup_param_type (s : string) : EO.term option =
  match L.find_opt (fun (s', _, _) -> s = s') !param_ctx with
  | Some (_, ty, _) -> Some ty
  | None -> None

let rec eo_tm : EO.term -> term =
  function
  (* return `var [s]`.*)
  | Symbol s -> Var (eo_name s)

  (* return `lit l`*)
  | Literal l -> Lit l

  (* dispatch. *)
  | Apply (s,ts) ->
    begin match s,ts with
    | s, ts when is_nary_binop s ->
        if List.length ts < 2 then
            failwith ("n-ary operator " ^ s ^ " needs at least 2 arguments")
        else
            let ts' = L.map eo_tm ts in
            app_binop_list (Var (eo_name s)) ts'
    | ("_") as s, [t1;t2] ->
      app_binop (Var "⋅") (eo_tm t1, eo_tm t2)
    (* | ("eo::requires", ([t1;t2;t3] as ts)) ->
      app_list (Var "??") (L.map eo_tm ts) *)
    | ("as"|"eo::as") as s, [t1;t2] ->
      (* swap arguments! *)
      app_binop (Var "eo._as") (eo_tm t2, eo_tm t1)

    | "->", ts ->
      eo_arrow ts

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

and eo_arrow (ts: EO.term list) : term =
  match ts with
  | [] -> Var "eo.Type"
  | [t] -> eo_tm t
  | EO.Apply ("eo::quote", [EO.Symbol s]) :: rest ->
    (* Dependent type: (-> (eo::quote f) T2) where f has type T1
       becomes: T1 ⤳d (λ f, T2) *)
    let param_ty = match lookup_param_type s with
      | Some ty -> eo_tm ty
      | None -> failwith (Printf.sprintf "Could not find type for quoted param: %s" s)
    in
    let f_body = eo_arrow rest in
    let f = Bind (Lambda, [(eo_name s, tau_of param_ty, Explicit)], f_body) in
    app_binop (Var "⤳d") (param_ty, f)
  | t :: rest ->
    app_binop (Var "⤳") (eo_tm t, eo_arrow rest)

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

(* Set of type constructor symbols (symbols whose type returns Type).
   This is populated during encoding and used to determine whether
   to use regular application or HO application in patterns. *)
let type_constructors : (string, unit) Hashtbl.t = Hashtbl.create 32

let is_type_constructor (s : string) : bool =
  Hashtbl.mem type_constructors s

let add_type_constructor (s : string) : unit =
  Hashtbl.add type_constructors s ()

let clear_type_constructors () : unit =
  Hashtbl.clear type_constructors

(* Insert explicit type args into pattern LHS.
   - For the program symbol itself, add type params as explicit args
   - For eo::List::cons, infer the type from the first argument

   The term structure uses ⋅ for higher-order application, so:
   - (f ⋅ x ⋅ y) is represented as App(App(Var "⋅", App(App(Var "⋅", f), x)), y)
   - We need to find the "real" head symbol by looking through ⋅ applications
   - Type constructors use regular application (no ⋅)
*)
let rec insert_explicits_lhs
    (ps : EO.param list)  (* program's type params *)
    (qs : EO.param list)  (* program's pattern params *)
    (prog_sym : string)   (* the program symbol name *)
    (t : term)
  : term =
  (* Type params use BracketApp for [T] syntax in patterns *)
  let bracket_app_list head args =
    L.fold_left (fun acc arg -> Exp (acc, arg)) head args
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
    | Var s when is_type_constructor s ->
      (* Type constructor - use regular application, not HO application *)
      let args' = L.map (insert_explicits_lhs ps qs prog_sym) ho_args in
      app_list real_head args'
    | _ ->
      (* Other applications - recurse on args using HO application *)
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
    | Some (_, param_name) -> Exp (Var s, Var param_name)
    | None -> t
    end
  | App (f, arg) -> App (apply_fresh_type_params param_map f, apply_fresh_type_params param_map arg)
  | Exp (f, arg) -> Exp (apply_fresh_type_params param_map f, apply_fresh_type_params param_map arg)
  | Bind (b, ps, body) ->
    let ps' = L.map (fun (x, ty, attr) -> (x, apply_fresh_type_params param_map ty, attr)) ps in
    Bind (b, ps', apply_fresh_type_params param_map body)
  | Let (x, e, body) -> Let (x, apply_fresh_type_params param_map e, apply_fresh_type_params param_map body)
  | Arrow (t1, t2) -> Arrow (apply_fresh_type_params param_map t1, apply_fresh_type_params param_map t2)
  | _ -> t

(* Mapping from literal categories to their Prelude type names *)
let prelude_type_of_lit_category : Literal.lit_category -> string =
  function
  | Literal.NUM -> "eo.<int>"    (* numerals are integers *)
  | Literal.RAT -> "eo.<rat>"    (* rationals *)
  | Literal.DEC -> "eo.<rat>"    (* decimals are rationals *)
  | Literal.STR -> "eo.<str>"  (* strings *)
  | Literal.BIN -> "eo.<bin>"    (* binary literals - TODO: proper BitVec support *)
  | Literal.HEX -> "eo.<hex>"    (* hex literals - TODO: proper BitVec support *)

(* Get the Prelude type alias for a user-defined type name, if it was
   declared via `(declare-consts <category> <type>)`.
   For example, if we have `(declare-consts <numeral> Int)`, then
   `get_type_alias "Int"` returns `Some "eo.Z"`. *)
let get_type_alias (type_name : string) : string option =
  (* Check each literal category to see if this type was declared for it *)
  let categories = [Literal.NUM; Literal.RAT; Literal.DEC; Literal.STR; Literal.BIN; Literal.HEX] in
  L.find_map (fun cat ->
    match EO.get_lit_type cat with
    | Some declared_type when declared_type = type_name ->
        Some (prelude_type_of_lit_category cat)
    | _ -> None
  ) categories

(* Check if a type name should be aliased to a Prelude type *)
let is_type_alias (type_name : string) : bool =
  get_type_alias type_name <> None

(* Check if a type returns Type (i.e., is a type constructor) *)
let rec eo_returns_type : EO.term -> bool = function
  | EO.Symbol "Type" -> true
  | EO.Apply ("->", ts) when ts <> [] -> eo_returns_type (L.hd (L.rev ts))
  | _ -> false

(* Encode a single constant, returning the mangled name used *)
let eo_const_with_name (s,k : string * EO.const) : (string * command list) =
  !encode_hook s (fun () ->
    match k with
    | Decl ([], EO.Symbol "Type", _) when is_type_alias s ->
    (* This is a type declaration that should be an alias based on declare-consts *)
    let alias_target = Option.get (get_type_alias s) in
    let mangled = get_overloaded_name (eo_name s) in
    (* Generate ⊍ (type union) rules for numeric type aliases.
       This is needed because ⊍ rules match syntactically, so Int ⊍ Int
       won't reduce unless we add explicit rules for Int. *)
    let union_rules =
      if false then
        (* Helper to build T1 ⊍ T2 *)
        let union t1 t2 = App (App (Var "eo.⊍", t1), t2) in
        (* Add rules: T ⊍ T ↪ T, and cross-rules with Z/Q if needed *)
        let t = Var mangled in
        let base_rules = [
          (union t t, t);  (* T ⊍ T ↪ T *)
        ] in
        (* Add cross-rules with the base type and the other numeric type *)
        let z = Var "eo.Z" in
        let q = Var "eo.Q" in
        let cross_rules =
          if alias_target = "eo.Z" then [
            (union t z, t);   (* T ⊍ Z ↪ T (since T = Z) *)
            (union z t, t);   (* Z ⊍ T ↪ T *)
            (union t q, q);   (* T ⊍ Q ↪ Q *)
            (union q t, q);   (* Q ⊍ T ↪ Q *)
          ]
          else (* alias_target = "eo.Q" *) [
            (union t q, t);   (* T ⊍ Q ↪ T (since T = Q) *)
            (union q t, t);   (* Q ⊍ T ↪ T *)
            (union t z, t);   (* T ⊍ Z ↪ T *)
            (union z t, t);   (* Z ⊍ T ↪ T *)
          ]
        in
        [Rule (base_rules @ cross_rules)]
      else
        []
    in
    (mangled, [
      Symbol (
        None, mangled,
        [],
        Some (Var "Set"),
        Some (Var alias_target),
        None
      )
    ] @ union_rules)

    | Decl (ps,ty,_) ->
    (* Register type constructors (symbols whose type returns Type) *)
    if eo_returns_type ty then add_type_constructor (eo_name s);
    (* Check if the type contains symbols that need fresh type parameters *)
    let poly_symbols = find_unapplied_poly_symbols ty in
    let fresh_params = L.map (fun (_, name) -> (name, Var "Set", Implicit)) poly_symbols in
    let ty_encoded = eo_tm ty in
    let ty_with_params = apply_fresh_type_params poly_symbols ty_encoded in
    let mangled = get_overloaded_name (eo_name s) in
    (mangled, [
      Symbol (
        Some Constant, mangled,
        fresh_params @ eo_prm ps,
        Some (tau_of ty_with_params),
        None,
        None
      )
    ])

    | Prog ((ps,ty),(qs,cs),all_ps) ->
    (* Set param context for looking up types of quoted symbols.
       Use all_ps (full original params) since it has all value params like f, x, n. *)
    param_ctx := all_ps;
    let mangled = get_overloaded_name (eo_name s) in
    let sym = Symbol (
        Some Sequential, mangled,
        eo_prm ps,
        Some (tau_of @@ eo_tm ty),
        None,
        None
      )
    in
    if cs = [] then
      (* Forward declaration with no cases - just emit the symbol *)
      (mangled, [sym])
    else
      (* Encode LHS with explicit type params, RHS without *)
      let encode_lhs t =
        let t' = bind_pvars qs (eo_tm t) in
        insert_explicits_lhs ps qs s t'
      in
      let encode_rhs t = bind_pvars qs (eo_tm t) in
      (mangled, [sym; Rule (L.map (fun (lhs, rhs) -> (encode_lhs lhs, encode_rhs rhs)) cs)])

    | Defn ([], EO.Symbol _) ->
    (* Skip encoding macro-like definitions: (define @foo () @@foo)
       These are expanded during elaboration and should not appear in LambdaPi. *)
    ("", [])

    | Defn ([], _) when is_type_alias s ->
    (* Type definition that should be aliased to a Prelude type based on declare-consts *)
    let alias_target = Option.get (get_type_alias s) in
    let mangled = get_overloaded_name (eo_name s) in
    (* Generate ⊍ (type union) rules for numeric type aliases.
       This is needed because ⊍ rules match syntactically, so Int ⊍ Int
       won't reduce unless we add explicit rules for Int. *)
    let union_rules =
      if false then
        (* Helper to build T1 ⊍ T2 *)
        let union t1 t2 = App (App (Var "eo.⊍", t1), t2) in
        (* Add rules: T ⊍ T ↪ T, and cross-rules with Z/Q if needed *)
        let t = Var mangled in
        let base_rules = [
          (union t t, t);  (* T ⊍ T ↪ T *)
        ] in
        (* Add cross-rules with the base type and the other numeric type *)
        let z = Var "eo.Z" in
        let q = Var "eo.Q" in
        let cross_rules =
          if alias_target = "eo.Z" then [
            (union t z, t);   (* T ⊍ Z ↪ T (since T = Z) *)
            (union z t, t);   (* Z ⊍ T ↪ T *)
            (union t q, q);   (* T ⊍ Q ↪ Q *)
            (union q t, q);   (* Q ⊍ T ↪ Q *)
          ]
          else (* alias_target = "eo.Q" *) [
            (union t q, t);   (* T ⊍ Q ↪ T (since T = Q) *)
            (union q t, t);   (* Q ⊍ T ↪ T *)
            (union t z, t);   (* T ⊍ Z ↪ T *)
            (union z t, t);   (* Z ⊍ T ↪ T *)
          ]
        in
        [Rule (base_rules @ cross_rules)]
      else
        []
    in
    (mangled, [
      Symbol (None, mangled,
        [],
        Some (Var "Set"),
        Some (Var alias_target),
        None)
    ] @ union_rules)

    | Defn (ps,t) ->
    let mangled = get_overloaded_name (eo_name s) in
    (mangled, [
      Symbol (None, mangled,
        eo_prm ps, None,
        Some (eo_tm t),
        None)
    ])

    | Rule _ -> ("", [])
  )

let eo_const (s,k : string * EO.const) : command list =
  let (_, cmds) = eo_const_with_name (s, k) in cmds

let eo_sig : EO.signature -> signature =
  L.concat_map eo_const

(* Encode a signature while building the overload table.
   Returns the encoded signature and populates the overload_table. *)
let eo_sig_with_overloads (sgn : EO.signature) : signature =
  reset_overload_counts ();
  clear_overload_table ();
  clear_type_constructors ();
  (* Group symbols by base name to track overload indices *)
  let name_indices : (string, int) Hashtbl.t = Hashtbl.create 32 in
  let get_index name =
    let idx = match Hashtbl.find_opt name_indices name with
      | Some n -> n
      | None -> 0
    in
    Hashtbl.replace name_indices name (idx + 1);
    idx
  in
  L.concat_map (fun (s, k) ->
    let base_name = eo_name s in
    let idx = get_index s in  (* Use original name for index tracking *)
    let (mangled, cmds) = eo_const_with_name (s, k) in
    if mangled <> "" then
      add_overload_entry base_name idx mangled;
    cmds
  ) sgn

(* Get all mangled names for a given base symbol name *)
let get_all_overloads (base_name : string) : string list =
  let rec collect idx acc =
    match get_overload_entry base_name idx with
    | Some mangled -> collect (idx + 1) (mangled :: acc)
    | None -> L.rev acc
  in
  collect 0 []

(* Get the number of overloads for a symbol *)
let get_overload_count (base_name : string) : int =
  let rec count idx =
    match get_overload_entry base_name idx with
    | Some _ -> count (idx + 1)
    | None -> idx
  in
  count 0
