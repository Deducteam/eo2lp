(* encode.ml
   Eunoia to LambdaPi encoding *)

module EO = Syntax_eo
open Api_lp

(* Overload management *)
let overload_counts : (string, int) Hashtbl.t =
  Hashtbl.create 32

let reset_overloads () =
  Hashtbl.clear overload_counts;
  reset_symbol_storage ()

(* Get a unique name for potentially overloaded symbols *)
let unique_name name =
  let escaped = esc name in
  match Hashtbl.find_opt overload_counts escaped with
  | None ->
    Hashtbl.add overload_counts escaped 1;
    escaped
  | Some n ->
    Hashtbl.replace overload_counts escaped (n + 1);
    Printf.sprintf "%s_%d" escaped n

let reset () =
  Api_lp.reset ();
  reset_overloads ()

(* ============================================================
   Eunoia signature access (for elaboration during encoding)
   ============================================================ *)

let global_sig : EO.signature ref = ref []
let set_signature s = global_sig := s

let lookup_eo_symbol name : EO.symbol option =
  List.assoc_opt name !global_sig

let find_all_eo_symbols name : (string * EO.symbol) list =
  List.filter (fun (n, _) -> n = name) !global_sig

(* Debug logging — delegates to Api_lp severity logging *)
let dbg fmt =
  let saved = !Api_lp.current_phase in
  Api_lp.current_phase := "elab";
  Printf.ksprintf (fun s ->
    Api_lp.log_info "%s" s;
    Api_lp.current_phase := saved
  ) fmt

(* Check if a symbol is an n-ary builtin that needs folding to binary *)
let is_nary_binop = function
  | s when s = EO.Builtin.eo_and || s = EO.Builtin.eo_or
        || s = EO.Builtin.eo_xor || s = EO.Builtin.eo_add
        || s = EO.Builtin.eo_mul -> true
  | _ -> false

(* Resolve a symbol name through nullary define chains *)
let rec resolve_sym_name s =
  match lookup_eo_symbol s with
  | Some (EO.Defn ([], EO.Symbol s', _)) -> resolve_sym_name s'
  | _ -> s

(* Infer substitutions for a declaration's implicit type params from actual
   argument types. Returns a list of (param_name, actual_type) pairs. *)
let infer_nil_subst decl_ps ty ts ps =
  let impl_names =
    List.filter_map (fun (n, t, _) ->
      if t = EO.Symbol EO.Builtin.ty_type then Some n else None) decl_ps
  in
  if impl_names = [] then []
  else
    let declared_arg_tys = match ty with
      | EO.Apply (s, args) when s = EO.Builtin.ty_arrow && args <> [] ->
        let n = List.length args in
        List.filteri (fun i _ -> i < n - 1) args
      | _ -> []
    in
    let actual_arg_tys =
      List.filter_map (fun t ->
        match t with
        | EO.Symbol s ->
          (match EO.prm_find s ps with
           | Some (_, ty, _) -> Some ty
           | None -> None)
        | _ -> None) ts
    in
    let bindings = Hashtbl.create 4 in
    let rec match_ty pat act =
      match pat, act with
      | EO.Symbol s, _ when List.mem s impl_names ->
        if not (Hashtbl.mem bindings s) then
          Hashtbl.add bindings s act
      | EO.Apply (f1, args1), EO.Apply (f2, args2)
        when f1 = f2 && List.length args1 = List.length args2 ->
        List.iter2 match_ty args1 args2
      | _ -> ()
    in
    List.iter2 match_ty
      (List.filteri (fun i _ -> i < List.length actual_arg_tys) declared_arg_tys)
      (List.filteri (fun i _ -> i < List.length declared_arg_tys) actual_arg_tys);
    Hashtbl.fold (fun k v acc -> (k, v) :: acc) bindings []

(* Apply a list of substitutions to an Eunoia term *)
let apply_substs substs t =
  List.fold_left (fun acc (s, t') -> EO.subst acc s t') t substs

(* ============================================================
   Prelude symbols and term builders
   ============================================================ *)

(* Prelude symbol accessors *)
let tau ()         = find "τ"
let arrow_sym ()   = find "⤳"
let dep_arrow_sym () = find "⤳d"
let app_sym ()     = find "APP"
let eo_type_sym () = find "{|eo::Type|}"
let eo_as_sym ()   = find "{|eo::as|}"

(* Symbol application with implicits *)
let rec count_leading_impl = function
  | true :: rest -> 1 + count_leading_impl rest
  | _ -> 0

let enc_sym s =
  let n = count_leading_impl s.Term.sym_impl in
  add_args (mk_Symb s) (List.init n (fun _ -> mk_Plac false))

(* Term builders *)
let tau_of t =
  mk_Appl (mk_Symb (tau ()), t)

let un_tau = function
  | Term.Appl (Term.Symb s, t) when s.Term.sym_name = "τ" -> t
  | t -> t

let hol_arrow t1 t2 =
  add_args (mk_Symb (arrow_sym ())) [t1; t2]

let hol_dep_arrow t1 f =
  add_args (mk_Symb (dep_arrow_sym ())) [t1; f]

let hol_app t1 t2 =
  add_args (enc_sym (app_sym ())) [t1; t2]

let eo_type () =
  mk_Symb (eo_type_sym ())

let eo_as t1 t2 =
  add_args (enc_sym (eo_as_sym ())) [t2; t1]

(* Integer encoding *)
let z0 ()    = find "Z0"
let zpos ()  = find "Zpos"
let zneg ()  = find "Zneg"
let pos_h () = find "H"
let pos_i () = find "I"
let pos_o () = find "O"

let rec enc_positive n =
  assert (n > 0);
  if n = 1 then mk_Symb (pos_h ())
  else
    let sym = if n mod 2 = 0 then pos_o () else pos_i () in
    mk_Appl (mk_Symb sym, enc_positive (n / 2))

let enc_int n =
  if n = 0 then mk_Symb (z0 ())
  else if n > 0 then mk_Appl (mk_Symb (zpos ()), enc_positive n)
  else mk_Appl (mk_Symb (zneg ()), enc_positive (-n))

let enc_rat num den =
  add_args (mk_Symb (find "Frac")) [enc_int num; enc_int den]

let ghost_sym name =
  let ghost_path = Sign.Ghost.path in
  match find_symbol_global name with
  | Some s when s.Term.sym_path = ghost_path -> s
  | _ ->
    let sym =
      Term.create_sym ghost_path
        Term.Public Term.Const Term.Eager false
        (Pos.none name) None mk_Kind []
    in
    Timed.(Sign.Ghost.sign.Sign.sign_symbols :=
      Lplib.Extra.StrMap.add name sym
        !(Sign.Ghost.sign.Sign.sign_symbols));
    sym

(* ============================================================
   Literal encoding
   ============================================================ *)

let enc_literal = function
  | Literal.Numeral n ->
    (* of_Z n — of_Z generated by enc_ltrl_num *)
    add_args (mk_Symb (find "of_Z")) [enc_int n]
  | Literal.Decimal d ->
    mk_Symb (ghost_sym (string_of_float d))
  | Literal.Rational (_num, _den) ->
    failf "enc_literal: rational literals not supported (no Real type)"
  | Literal.String s ->
    failf "enc_literal: string literals not supported: \"%s\"" s
  | Literal.Binary b ->
    let bits = String.sub b 2 (String.length b - 2) in
    let width = String.length bits in
    let value = int_of_string ("0b" ^ bits) in
    let mk_int n = add_args (mk_Symb (find "of_Z")) [enc_int n] in
    add_args
      (mk_Symb (find "{|@bv|}"))
      [mk_int value; mk_int width]
  | Literal.Hexadecimal h ->
    mk_Symb (ghost_sym h)

(* ============================================================
   Term encoding (with integrated elaboration)
   ============================================================ *)

(* ps = Eunoia param context (for :list checks, variable detection, n-ary)
   ctx = LambdaPi variable context *)

let rec enc_term ps ctx t =
  enc_term_inner ps ctx (EO.subst_lit_aliases t)

and enc_term_inner ps ctx = function
  | EO.Symbol s when s = EO.Builtin.ty_type ->
    eo_type ()
  | EO.Symbol "String" ->
    enc_sym (get_sym "string")

  (* Symbol: check for nullary define expansion, then context/global lookup *)
  | EO.Symbol s ->
    begin match lookup_eo_symbol s with
    | Some (EO.Defn ([], body, _)) ->
      dbg "define: %s → %s" s (Pp_eo.term_str body);
      enc_term ps ctx body
    | _ ->
      match ctxt_find ctx (esc s) with
      | Some v -> mk_Vari v
      | None -> enc_sym (get_sym s)
    end

  | EO.Literal lit ->
    enc_literal lit

  (* Arrow types *)
  | EO.Apply (s, args) when s = EO.Builtin.ty_arrow ->
    enc_arrow ps ctx args

  (* Type cast: (as T x) or (eo::as T x) *)
  | EO.Apply (s, [ty; tm]) when s = EO.Builtin.ty_as || s = EO.Builtin.eo_as ->
    eo_as (enc_term ps ctx ty) (enc_term ps ctx tm)

  (* HOL application: (_ f x) — already elaborated form *)
  | EO.Apply (s, [f; x]) when s = EO.Builtin.ty_app ->
    hol_app (enc_term ps ctx f) (enc_term ps ctx x)

  (* eo::typeof x → type of x from context *)
  | EO.Apply (op, [EO.Symbol s]) when op = EO.Builtin.eo_typeof ->
    let s_esc = esc s in
    (match List.find_opt (fun (v, _, _) -> base_name v = s_esc) ctx with
     | Some (_, ty, _) -> un_tau ty
     | None ->
       (* Also check Eunoia param context *)
       match EO.prm_find s ps with
       | Some (_, ty, _) -> enc_term ps ctx ty
       | None ->
         add_args
           (enc_sym (get_sym "{|eo::typeof|}"))
           [enc_term ps ctx (EO.Symbol s)])

  (* Builtin applications: n-ary folding, list cons, etc. *)
  | EO.Apply (s, ts) when EO.is_builtin s ->
    if is_nary_binop s && List.length ts > 2 then begin
      (* Fold n-ary builtins (eo::and, eo::or, etc.) to binary *)
      let ts' = List.map (enc_term ps ctx) ts in
      let head = enc_sym (get_sym (esc s)) in
      List.fold_left (fun acc t -> add_args head [acc; t]) (List.hd ts') (List.tl ts')
    end
    else if s = EO.Builtin.eo_list_cons then begin
      (* eo::List::cons: handle :list params *)
      let ts' = List.map (enc_term ps ctx) ts in
      match ts, ts' with
      | [_; EO.Symbol s'], [x'; xs'] when EO.prm_has_attr s' EO.List ps ->
        add_args (enc_sym (get_sym (esc EO.Builtin.eo_list_cons))) [x'; xs']
      | _ ->
        let nil = enc_sym (get_sym (esc EO.Builtin.eo_list_nil)) in
        List.fold_right (fun (t_orig, t') acc ->
          match t_orig with
          | EO.Symbol s when EO.prm_has_attr s EO.List ps ->
            add_args (enc_sym (get_sym (esc EO.Builtin.eo_list_concat))) [t'; acc]
          | _ ->
            add_args (enc_sym (get_sym (esc EO.Builtin.eo_list_cons))) [t'; acc]
        ) (List.combine ts ts') nil
    end
    else begin
      (* Other builtins: encode normally *)
      let head = enc_sym (get_sym (esc s)) in
      add_args head (List.map (enc_term ps ctx) ts)
    end

  (* Non-builtin applications: dispatch through signature *)
  | EO.Apply (s, ts) ->
    begin match EO.prm_find s ps with
    | Some _ ->
      (* Variable application: use HOL app *)
      let head =
        match ctxt_find ctx (esc s) with
        | Some v -> mk_Vari v
        | None -> enc_sym (get_sym s)
      in
      List.fold_left hol_app head (List.map (enc_term ps ctx) ts)
    | None ->
      (* Helper: count the explicit arity of an Eunoia type (-> T1 ... Tn R) *)
      let eo_type_arity = function
        | EO.Apply (s, ts) when s = EO.Builtin.ty_arrow && ts <> [] ->
          List.length ts - 1
        | _ -> 0
      in
      let all_eo = find_all_eo_symbols s in
      begin match
        all_eo |> List.mapi (fun i (s', k) -> (i, s', k))
        |> List.filter_map (fun (i, s', k) ->
          if s <> s' then None
          else match k with
          | EO.Decl (decl_ps, ty, ao) ->
            let n_opaque = List.length (List.filter
              (fun (_, _, atts) -> List.mem EO.Opaque atts) decl_ps) in
            let n_args = List.length ts - n_opaque in
            let compat = match ao with
              | Some (EO.LeftAssoc | EO.RightAssoc
                     | EO.Chainable _ | EO.Pairwise _) ->
                n_args >= 2
              | Some (EO.LeftAssocNil _ | EO.RightAssocNil _
                     | EO.LeftAssocNilNSN _ | EO.RightAssocNilNSN _
                     | EO.LeftAssocNSN _ | EO.RightAssocNSN _) ->
                n_args >= 1
              | None ->
                (* Fixed arity: must match exactly *)
                n_args = eo_type_arity ty - List.length decl_ps
              | _ -> true
            in
            if not compat then None
            else Some (enc_nary ~overload_idx:i ps ctx s k ts)
          | _ -> Some (enc_nary ~overload_idx:i ps ctx s k ts))
      with
      | t' :: _ -> t'
      | [] ->
        (* Symbol not in Eunoia signature — try direct LP encoding *)
        let head =
          match ctxt_find ctx (esc s) with
          | Some v -> mk_Vari v
          | None -> enc_sym (get_sym (esc s))
        in
        add_args head (List.map (enc_term ps ctx) ts)
      end
    end

  (* eo::define as local let-binding *)
  | EO.Bind (op, xs, body) when op = EO.Builtin.eo_define ->
    begin match xs with
    | [] -> enc_term ps ctx body
    | (name, rhs) :: rest ->
      let rhs_enc = enc_term ps ctx rhs in
      let ty = mk_Plac false in
      let v = new_var (esc name) in
      let ctx' = ctxt_add ctx v ty in
      let ps' = (name, EO.Symbol "NONE", []) :: ps in
      let body_enc = enc_term ps' ctx'
        (EO.Bind (EO.Builtin.eo_define, rest, body)) in
      Core.Term.mk_LLet (ty, rhs_enc, bind_var v body_enc)
    end

  (* Binder application (forall, exists, etc.) *)
  | EO.Bind (s, xs, body) ->
    begin match
      find_all_eo_symbols s |> List.filter_map (fun (s', k) ->
        if s = s' then Some (enc_binder ps ctx s k xs body)
        else None)
    with
    | t' :: _ -> t'
    | [] -> failf "Binder `%s` not found" s
    end

(* N-ary application encoding — replaces elaborate.ml's elab_nary,
   producing LambdaPi terms directly *)
and enc_nary ?(overload_idx=0) ps ctx s k ts =
  let enc = enc_term ps ctx in
  match k with
  (* Program constants: shallow application *)
  | EO.Prog _ ->
    let head = enc_sym (get_sym (esc s)) in
    add_args head (List.map enc ts)

  (* Nullary define: expand head, keep args *)
  | EO.Defn ([], body, _) ->
    begin match body with
    | EO.Symbol s' when ts = [] ->
      dbg "define: %s → %s" s s';
      enc_term ps ctx (EO.Symbol s')
    | EO.Symbol s' ->
      dbg "define: %s(%d args) → %s(%d args)" s (List.length ts) s' (List.length ts);
      enc_term ps ctx (EO.Apply (s', ts))
    | _ when ts = [] ->
      dbg "define: %s → %s" s (Pp_eo.term_str body);
      enc_term ps ctx body
    | _ ->
      let head = enc_sym (get_sym (esc s)) in
      add_args head (List.map enc ts)
    end

  (* Parametric define: encode normally *)
  | EO.Defn _ ->
    let head = enc_sym (get_sym (esc s)) in
    add_args head (List.map enc ts)

  (* Declarations: dispatch on associativity attribute *)
  | EO.Decl (decl_ps, ty, ao) ->
    let ts' = List.map enc ts in
    if EO.returns_type ty then begin
      let head = enc_sym (get_sym (esc s)) in
      add_args head ts'
    end else
      enc_nary_decl ~overload_idx ps ctx s decl_ps ty ao ts ts'

  | _ -> failf "Cannot encode %s as nary" s

(* Encode a Decl application with attribute dispatch.
   ts = original Eunoia args, ts' = encoded LP args *)
and enc_nary_decl ?(overload_idx=0) ps ctx s decl_ps ty ao ts ts' =
  (* Split opaque params (applied directly) from remaining (HOL app) *)
  let n_opaque =
    List.length (List.filter (fun (_, _, atts) -> List.mem EO.Opaque atts) decl_ps)
  in
  let () = if n_opaque > 0 then
    dbg "opaque: %s n_opaque=%d n_args=%d" s n_opaque (List.length ts) in
  let take_drop n xs =
    let rec go n = function
      | x :: rest when n > 0 -> let (t, d) = go (n - 1) rest in (x :: t, d)
      | xs -> ([], xs)
    in go n xs
  in
  let opaque_args, rest_ts' =
    if n_opaque > 0 && n_opaque <= List.length ts' then take_drop n_opaque ts'
    else ([], ts')
  in
  let _opaque_orig, rest_ts_orig =
    if n_opaque > 0 && n_opaque <= List.length ts then take_drop n_opaque ts
    else ([], ts)
  in
  (* Build the LP head symbol.  The overload_idx from the outer dispatch
     tells us which EO declaration was matched; unique_name assigns LP
     names in the same order, so we can directly compute the LP name. *)
  let head_sym =
    let lp_name =
      if overload_idx = 0 then esc s
      else Printf.sprintf "%s_%d" (esc s) overload_idx
    in
    dbg "overload: %s idx=%d -> LP %s" s overload_idx lp_name;
    enc_sym (get_sym lp_name)
  in
  let head =
    if opaque_args = [] then head_sym
    else add_args head_sym opaque_args
  in
  (* glue: either HOL app or list_concat for :list params *)
  let glue t_orig t_enc acc =
    match t_orig with
    | EO.Symbol s' when EO.prm_has_attr s' EO.List ps ->
      add_args (enc_sym (get_sym (esc EO.Builtin.eo_list_concat_old))) [head; t_enc; acc]
    | _ ->
      hol_app (hol_app head t_enc) acc
  in
  let glue_rev acc t_orig t_enc =
    glue t_orig t_enc acc
  in
  (* Substitute type params in nil term and encode *)
  let subst_nil_enc t_nil =
    let subs = infer_nil_subst decl_ps ty ts ps in
    if subs = [] then enc_term ps ctx t_nil
    else enc_term ps ctx (apply_substs subs t_nil)
  in
  let chop xs =
    let n = List.length xs in
    (List.filteri (fun i _ -> i < n - 1) xs, List.nth xs (n - 1))
  in
  match ao with
  | None ->
    List.fold_left hol_app head rest_ts'

  | Some (EO.RightAssocNil t_nil) ->
    begin match rest_ts_orig with
    | [_; EO.Symbol s'] when EO.prm_has_attr s' EO.List ps ->
      List.fold_left hol_app head rest_ts'
    | _ ->
      let last_is_list = match List.rev rest_ts_orig with
        | EO.Symbol s' :: _ when EO.prm_has_attr s' EO.List ps -> true
        | _ -> false
      in
      if last_is_list then begin
        let init_ts, last_t = chop rest_ts' in
        let init_orig, _ = chop rest_ts_orig in
        dbg "right-assoc-nil: %s(%d args), last is :list" s (List.length rest_ts_orig);
        List.fold_right2 glue init_orig init_ts last_t
      end else begin
        dbg "right-assoc-nil: %s(%d args), nil=%s" s (List.length rest_ts_orig) (Pp_eo.term_str t_nil);
        List.fold_right2 glue rest_ts_orig rest_ts' (subst_nil_enc t_nil)
      end
    end

  | Some (EO.LeftAssocNil t_nil) ->
    begin match rest_ts_orig with
    | [EO.Symbol s'; _] when EO.prm_has_attr s' EO.List ps ->
      List.fold_left hol_app head rest_ts'
    | _ ->
      let first_is_list = match rest_ts_orig with
        | EO.Symbol s' :: _ when EO.prm_has_attr s' EO.List ps -> true
        | _ -> false
      in
      if first_is_list then begin
        dbg "left-assoc-nil: %s(%d args), first is :list" s (List.length rest_ts_orig);
        List.fold_left2 glue_rev (List.hd rest_ts') (List.tl rest_ts_orig) (List.tl rest_ts')
      end else begin
        dbg "left-assoc-nil: %s(%d args), nil=%s" s (List.length rest_ts_orig) (Pp_eo.term_str t_nil);
        List.fold_left2 glue_rev (subst_nil_enc t_nil) rest_ts_orig rest_ts'
      end
    end

  | Some EO.RightAssoc ->
    dbg "right-assoc: %s(%d args)" s (List.length rest_ts_orig);
    let init_ts, last_t = chop rest_ts' in
    let init_orig, _ = chop rest_ts_orig in
    List.fold_right2 glue init_orig init_ts last_t

  | Some EO.LeftAssoc ->
    dbg "left-assoc: %s(%d args)" s (List.length rest_ts_orig);
    List.fold_left2 glue_rev (List.hd rest_ts') (List.tl rest_ts_orig) (List.tl rest_ts')

  | Some (EO.Chainable op) ->
    dbg "chainable: %s(%d args), op=%s" s (List.length rest_ts_orig) op;
    if List.length rest_ts_orig <= 2 then
      List.fold_left hol_app head rest_ts'
    else begin
      (* Generate pairs and encode via the combining operator *)
      let rec aux = function
        | v :: w :: vs ->
          (EO.app_ho_list (EO.Symbol s) [v; w]) :: aux (w :: vs)
        | _ -> []
      in
      enc_term ps ctx (EO.Apply (op, aux rest_ts_orig))
    end

  | Some (EO.Pairwise op) ->
    dbg "pairwise: %s(%d args), op=%s" s (List.length rest_ts_orig) op;
    if List.length rest_ts_orig <= 2 then
      List.fold_left hol_app head rest_ts'
    else begin
      let rec aux = function
        | v :: vs ->
          List.append
            (List.map (fun w -> EO.app_ho_list (EO.Symbol s) [v; w]) vs)
            (aux vs)
        | [] -> []
      in
      enc_term ps ctx (EO.Apply (op, aux rest_ts_orig))
    end

  | Some (EO.RightAssocNilNSN t_nil) ->
    dbg "right-assoc-nil-nsn: %s(%d args), nil=%s" s (List.length rest_ts_orig) (Pp_eo.term_str t_nil);
    List.fold_right2 glue rest_ts_orig rest_ts' (subst_nil_enc t_nil)

  | Some (EO.LeftAssocNilNSN t_nil) ->
    dbg "left-assoc-nil-nsn: %s(%d args), nil=%s" s (List.length rest_ts_orig) (Pp_eo.term_str t_nil);
    List.fold_left2 glue_rev (subst_nil_enc t_nil) rest_ts_orig rest_ts'

  | Some (EO.RightAssocNSN t_nil) ->
    dbg "right-assoc-nsn: %s(%d args), nil=%s" s (List.length rest_ts_orig) (Pp_eo.term_str t_nil);
    List.fold_right2 glue rest_ts_orig rest_ts' (subst_nil_enc t_nil)

  | Some (EO.LeftAssocNSN t_nil) ->
    dbg "left-assoc-nsn: %s(%d args), nil=%s" s (List.length rest_ts_orig) (Pp_eo.term_str t_nil);
    List.fold_left2 glue_rev (subst_nil_enc t_nil) rest_ts_orig rest_ts'

  | Some (EO.ArgList cons_name) ->
    (* :arg-list @cons desugars (f x y z) to (f (@cons x y z)),
       which further expands via @cons's own attribute (e.g. :right-assoc-nil).
       If there is a single argument with :list, pass it directly. *)
    dbg "arg-list: %s(%d args), cons=%s" s (List.length rest_ts_orig) cons_name;
    begin match rest_ts_orig with
    | [EO.Symbol s'] when EO.prm_has_attr s' EO.List ps ->
      hol_app head (List.hd rest_ts')
    | _ ->
      let list_term = EO.Apply (cons_name, rest_ts_orig) in
      let list_enc = enc_term ps ctx list_term in
      hol_app head list_enc
    end

  | Some (EO.Binder _ | EO.LetBinder _
         | EO.Implicit | EO.Opaque | EO.List
         | EO.Syntax _ | EO.Restrict _) ->
    List.fold_left hol_app head rest_ts'

(* Binder encoding: (forall ((x T)) body) → head [cons_term; body_enc] *)
and enc_binder ps ctx s k xs body =
  match k with
  | EO.Decl (_, _, Some (EO.Binder t_cons_name)) ->
    let t_cons_name = resolve_sym_name t_cons_name in
    let mk_var_eo (name, ty) =
      EO.Apply (EO.Builtin.eo_var, [EO.Literal (Literal.String name); ty])
    in
    (* Substitute bound variable occurrences in the body with their
       eo::var form so the encoder sees eo::var terms, not bare symbols. *)
    let body' = List.fold_left (fun acc (n, ty) ->
      EO.subst acc n (mk_var_eo (n, ty))) body xs
    in
    let bound_params = List.map (fun (n, ty) -> (n, ty, [])) xs in
    let ps' = ps @ bound_params in
    let var_terms = List.map (fun v -> enc_term ps ctx (mk_var_eo v)) xs in
    let cons_head = enc_sym (get_sym (esc t_cons_name)) in
    let cons_app = add_args cons_head var_terms in
    let body_enc = enc_term ps' ctx body' in
    let head = enc_sym (get_sym (esc s)) in
    add_args head [cons_app; body_enc]
  | _ ->
    failf "No :binder attribute for `%s`" s

and enc_arrow ps ctx = function
  | [] ->
    fail "Empty arrow type"
  | [t] ->
    enc_term ps ctx t
  | EO.Apply (op, [ty; EO.Symbol s]) :: rest when op = EO.Builtin.eo_var ->
    let s_esc = esc s in
    let eo_ty = enc_term ps ctx ty in
    let type_of_s = tau_of eo_ty in
    let v = new_var s_esc in
    let ctx' = ctxt_add ctx v type_of_s in
    let body = enc_arrow ps ctx' rest in
    let lam = mk_Abst (type_of_s, bind_var v body) in
    hol_dep_arrow eo_ty lam
  | EO.Apply (op, [EO.Symbol s]) :: rest when op = EO.Builtin.eo_quote ->
    let s_esc = esc s in
    let type_of_s =
      match List.find_opt (fun (v, _, _) -> base_name v = s_esc) ctx with
      | Some (_, ty, _) -> ty
      | None ->
        let ctx_vars = List.map (fun (v, _, _) -> base_name v) ctx in
        failf "enc_arrow: variable `%s` not in context. Available: [%s]"
          s (String.concat ", " ctx_vars)
    in
    let eo_type_of_s = un_tau type_of_s in
    let v = new_var s_esc in
    let ctx' = ctxt_add ctx v type_of_s in
    let body = enc_arrow ps ctx' rest in
    let lam = mk_Abst (type_of_s, bind_var v body) in
    hol_dep_arrow eo_type_of_s lam
  | t :: rest ->
    hol_arrow (enc_term ps ctx t) (enc_arrow ps ctx rest)

(* Parameter encoding *)
let enc_params ps =
  let ctx, impl =
    List.fold_left
      (fun (ctx, acc) (str, ty, atts) ->
         let v = new_var (esc str) in
         (* Type parameters (T : Type) have type Set (= τ {|eo::Type|}) *)
         let ty' = tau_of (enc_term [] ctx ty) in
         let ctx' = ctxt_add ctx v ty' in
         let is_impl = List.mem EO.Implicit atts in
         (ctx', is_impl :: acc))
      (empty_ctxt, [])
      ps
  in
  (* Context is built in reverse order (ctxt_add prepends), which is what
     ctxt_to_prod/ctxt_to_abst expect (they use fold_left, wrapping first
     element as innermost binder, producing Π p_n. ... Π p_1. body).

     impl is accumulated in reverse order [p_n_impl; ...; p_1_impl], but
     the final type has params in original order (p_1 outermost), so we
     must reverse impl to match: [p_1_impl; ...; p_n_impl]. *)
  (ctx, List.rev impl)

(* Constant encoding *)
type enc_result = {
  syms  : sym list;
  rules : (sym * rule) list;
  raw   : string;
}

let empty_result = { syms = []; rules = []; raw = "" }

(* Convert variables in a term to pattern variables.
   Takes a context (from enc_params) and replaces Vari nodes with Patt nodes.
   Variables not in ctx are replaced with wildcards. *)
let bind_pvars ctx full_ctx term =
  (* Build mapping from variable name to index for pattern vars *)
  let var_indices =
    List.mapi (fun i (v, _, _) -> (base_name v, i)) ctx
    |> List.rev  (* ctx is reversed, so reverse to get original order *)
  in
  (* Also track all variables from full_ctx that should become wildcards *)
  let full_names =
    List.map (fun (v, _, _) -> base_name v) full_ctx
    |> List.sort_uniq String.compare
  in
  let rec go = function
    | Core.Term.Vari v ->
      let name = base_name v in
      (match List.find_opt (fun (n, _) -> n = name) var_indices with
       | Some (_, idx) -> mk_Patt (Some idx, name, [||])
       | None ->
         (* If it's a variable from full_ctx but not in ctx, use wildcard *)
         if List.mem name full_names then mk_Plac false
         else mk_Vari v)
    | Core.Term.Symb s ->
      let name = s.Core.Term.sym_name in
      (match List.find_opt (fun (n, _) -> n = name) var_indices with
       | Some (_, idx) -> mk_Patt (Some idx, name, [||])
       | None ->
         (* If it's a name from full_ctx but not in ctx, use wildcard *)
         if List.mem name full_names then mk_Plac false
         else mk_Symb s)
    | Core.Term.Meta (m, ts) ->
      (match Timed.(!(m.Core.Term.meta_value)) with
       | None ->
         (* Unsolved meta: convert to wildcard *)
         mk_Plac false
       | Some mb ->
         (* Solved meta: unfold to its value and recurse *)
         go (Core.Term.msubst mb ts))
    | Core.Term.Appl (t1, t2) ->
      mk_Appl (go t1, go t2)
    | Core.Term.Abst (ty, b) ->
      let v, body = unbind b in
      mk_Abst (go ty, bind_var v (go body))
    | Core.Term.Prod (ty, b) ->
      let v, body = unbind b in
      mk_Prod (go ty, bind_var v (go body))
    | Core.Term.LLet (ty, t, b) ->
      let v, body = unbind b in
      Core.Term.mk_LLet (go ty, go t, bind_var v (go body))
    | t -> t
  in
  go term

let enc_decl str ps ty attr =
  let ctx, impl = enc_params ps in
  let body_ty = tau_of (enc_term [] ctx ty) in
  let body_ty = resolve_term ~ctx body_ty in
  let ty', _ = ctxt_to_prod ctx body_ty in
  let sym = add_constant ~impl (unique_name str) ty' in
  { syms = [sym]; rules = []; raw = "" }

(* Check if an Eunoia AST term contains eo::requires *)
let rec has_eo_requires = function
  | EO.Apply (s, _) when s = EO.Builtin.eo_requires -> true
  | EO.Apply (_, args) -> List.exists has_eo_requires args
  | EO.Bind (_, _, body) -> has_eo_requires body
  | _ -> false

let enc_defn str ps tm ty_opt =
  match ps with
  | [] ->
    (* Nullary defines are expanded by the elaborator — nothing to encode *)
    empty_result
  | _ ->
    let ctx, impl = enc_params ps in
    let body_raw = enc_term ps ctx tm in
    let expected_ty = Option.map (fun ty -> tau_of (enc_term ps ctx ty)) ty_opt in
    let body = resolve_term ~ctx ?expected_ty body_raw in
    (* When the body contains eo::requires (which constrains type params,
       causing the inferred body type to differ from the parametric type),
       encode as a sequential symbol + rule instead of a definition.
       This preserves the parametric return type (e.g., τ T instead of
       τ (?? ... Int Real)), which is needed for downstream type checking. *)
    let has_type_param =
      List.exists (fun (_, ty, _) -> ty = EO.Symbol EO.Builtin.ty_type) ps
    in
    if has_eo_requires tm && has_type_param then begin
      (* For defines with eo::requires and type params, encode as a
         sequential symbol + rule to preserve the parametric return type
         (LP's inference would over-specialize due to eo::requires).
         Infer return type: use last param's type if concrete, else first
         Type parameter. *)
      let return_ty_enc =
        (* Check if the last parameter has a concrete (non-type-variable) type *)
        let last_param_ty = match List.rev ps with
          | (_, ty, _) :: _ ->
            let is_type_param name =
              List.exists (fun (n, t, _) -> n = name && t = EO.Symbol EO.Builtin.ty_type) ps
            in
            (match ty with
             | EO.Symbol s when is_type_param s -> None  (* type variable *)
             | _ -> Some ty)  (* concrete type like Bool, Int, etc. *)
          | [] -> None
        in
        match last_param_ty with
        | Some ret_ty -> tau_of (enc_term ps ctx ret_ty)
        | None ->
          (* Fallback: use first Type parameter *)
          let type_param_name =
            List.find_map (fun (name, ty, _) ->
              if ty = EO.Symbol EO.Builtin.ty_type then Some (esc name) else None) ps
          in
          match type_param_name with
          | Some name ->
            (match List.find_map (fun (v, _, _) ->
                     if Core.Term.base_name v = name then Some v else None)
                     (List.rev ctx) with
             | Some tv -> tau_of (mk_Vari tv)
             | None -> tau_of (mk_Plac false))
          | None -> tau_of (mk_Plac false)
      in
      begin match return_ty_enc with
      | body_ty ->
        let body_ty = resolve_term ~ctx body_ty in
        let ty, _ = Core.Ctxt.to_prod ctx body_ty in
        let sym = add_sequential ~impl (unique_name str) ty in
        (* Build rule: sym $x1 ... $xn ↪ body *)
        let names = List.rev_map (fun (v, _, _) -> base_name v) ctx
                    |> Array.of_list in
        let vars_nb = List.length ctx in
        let lhs_args =
          let n = List.length ctx in
          List.mapi (fun i (v, _, _) ->
            mk_Patt (Some (n - 1 - i), base_name v, [||])) (List.rev ctx)
        in
        let rhs = bind_pvars ctx ctx body in
        let rule : rule = {
          lhs = lhs_args;
          rhs;
          arity = List.length lhs_args;
          arities = Array.make vars_nb 0;
          vars_nb;
          xvars_nb = 0;
          names;
          rule_pos = None;
        } in
        { syms = [sym]; rules = [(sym, rule)]; raw = "" }
      end
    end else begin
      let tm' = ctxt_to_abst ctx body in
      { syms = [add_definition ~impl (unique_name str) None tm'];
        rules = []; raw = "" }
    end

(* Rule encoding for programs *)

(* Encode a program case as a rewrite rule *)
(* Coerce a term of type τ int to τ T by wrapping with of_Z T.
   This is needed because Eunoia builtins like eo::len return raw integers
   (τ int = ℤ), but their results may be used where the declared numeral
   literal type (e.g. Int) is expected. *)
let coerce_int_to_lit ctx term expected_ty =
  let prob = Core.Term.new_problem () in
  match Core.Infer.infer_noexn prob ctx term with
  | Some (_, inferred_ty) ->
    let inner_inferred = un_tau inferred_ty in
    let inner_expected = un_tau expected_ty in
    let is_int_sym = function
      | Core.Term.Symb s -> s.Core.Term.sym_name = "int"
      | _ -> false
    in
    if is_int_sym inner_inferred && not (is_int_sym inner_expected) then
      (* Wrap: of_Z term — of_Z : τ (int ⤳ T) *)
      (try
        let of_z = find "of_Z" in
        mk_Appl (mk_Symb of_z, term)
      with _ -> term)
    else term
  | None -> term

let enc_case eo_ps ctx impl_ctx sym ?(wildcard_impl_vars=false) ?expected_ty (t1, t2 : EO.term * EO.term) =

  let enc_rhs t =
    let encoded = enc_term eo_ps ctx t |> resolve_term ~debug:!verbose ~ctx in
    let coerced = match expected_ty with
      | Some exp_ty -> coerce_int_to_lit ctx encoded exp_ty
      | None -> encoded
    in
    coerced |> bind_pvars ctx ctx
  in

  (* For the LHS, resolve_term infers the implicit args from the explicit
     pattern args. We keep the resolved implicit args when they are fully
     resolved (e.g., Seq $U instead of bare $T when the pattern refines
     the type). When resolution leaves unsolved metas, we fall back to the
     impl_ctx variable to ensure pattern variables are bound in the LHS. *)
  let enc_lhs t =
    let encoded = enc_term eo_ps ctx t in
    let resolved = resolve_term ~debug:!verbose ~ctx encoded in
    let head, args = Core.Term.get_args resolved in
    let is_our_sym = match head with
      | Core.Term.Symb s -> s == sym
      | _ -> false
    in
    if is_our_sym then begin
      let n_impl = List.length impl_ctx in
      let resolved_impl = if n_impl <= List.length args
        then List.filteri (fun i _ -> i < n_impl) args
        else []
      in
      let explicit_args = if n_impl <= List.length args
        then List.filteri (fun i _ -> i >= n_impl) args
        else args
      in
      (* For each implicit arg: use the resolved version if it has no
         unsolved metas, otherwise fall back to the impl_ctx variable. *)
      let impl_vars = List.rev_map (fun (v, _, _) -> mk_Vari v) impl_ctx in
      let is_impl_var t =
        if not wildcard_impl_vars then false
        else
          (* Unfold solved metas to check the underlying value *)
          let t' = match t with
            | Core.Term.Meta (m, ts) ->
              (match Timed.(!(m.Core.Term.meta_value)) with
               | Some mb -> Core.Term.msubst mb ts
               | None -> t)
            | _ -> t
          in
          match t' with
          | Core.Term.Vari v ->
            List.exists (fun (iv, _, _) ->
              Core.Term.eq_vars v iv) impl_ctx
          | _ -> false
      in
      let impl_args = List.map2 (fun resolved_arg _fallback ->
        if has_unsolved_metas resolved_arg || is_impl_var resolved_arg
        then mk_Plac false
        else resolved_arg
      ) resolved_impl impl_vars in
      (* Apply nonvar_metas_to_plac selectively: only to args that
         contain Stdlib.Z's int or unsolved metas. *)
      let cleanup_if_needed t =
        if has_unsolved_metas t || Api_lp.has_stdlib_int t
        then Api_lp.nonvar_metas_to_plac t
        else t
      in
      let final_impl = List.map cleanup_if_needed impl_args in
      let final_explicit = List.map cleanup_if_needed explicit_args in
      let new_args = final_impl @ final_explicit in
      bind_pvars ctx ctx (add_args (mk_Symb sym) new_args)
    end else
      bind_pvars ctx ctx resolved
  in

  let l, rhs = enc_lhs t1, enc_rhs t2 in
  let _,lhs = Core.Term.get_args l in
  let names = List.rev_map (fun (v, _, _) -> base_name v) ctx |> Array.of_list in
  let vars_nb = List.length ctx in
  let rule : rule = {
    lhs;
    rhs;
    arity = List.length lhs;
    arities = Array.make vars_nb 0;
    vars_nb;
    xvars_nb = 0;
    names;
    rule_pos = None;
  } in
  (sym, rule)

(* Deduplicate while preserving order of first occurrence *)
let dedup_params ps =
  let seen = Hashtbl.create (List.length ps) in
  List.filter (fun (name, _, _) ->
    if Hashtbl.mem seen name then false
    else (Hashtbl.add seen name (); true))
  ps

let enc_prog str ps doms ran cases =
  let ctx, _ = enc_params ps in
  let ty_raw = EO.Apply (EO.Builtin.ty_arrow, doms @ [ran]) in
  let body_ty_raw = tau_of (enc_term ps ctx ty_raw) in
  let body_ty = resolve_term ~ctx body_ty_raw in
  (* Variables from ctx that are free in the type become implicit params *)
  let free_vars = Api_lp.LibTerm.free_vars body_ty in
  let impl_ctx =
    List.filter (fun (v, _, _) -> Core.Term.VarSet.mem v free_vars) ctx
  in
  let impl = List.map (fun _ -> true) impl_ctx in
  let ty, _ = Core.Ctxt.to_prod impl_ctx body_ty in
  (* If the symbol already exists (forward declaration), reuse it
     and only encode the rules — no new symbol declaration. *)
  let escaped = esc str in
  let existing = Api_lp.find_symbol escaped in
  let sym = match existing with
    | Some s -> s
    | None   -> add_sequential ~impl (unique_name str) ty
  in
  (* Detect programs with both Int and Real param types: these need
     wildcard implicits to avoid type preservation failures with
     non-reducible type union functions like $arith_typeunion *)
  let wildcard_impl_vars =
    let param_types = List.map (fun (_, ty, _) -> ty) ps in
    let has t = List.exists (fun ty -> ty = t) param_types in
    has (EO.Symbol "Int") && has (EO.Symbol "Real")  (* CPC-specific names, not builtins *)
  in
  (* Compute expected type for RHS: τ(range) *)
  let rhs_expected_ty = tau_of (enc_term ps ctx ran) in
  let _n_cases = List.length cases in
  let rules =
    List.map (fun (lhs, rhs) ->
      enc_case ps ctx impl_ctx sym ~wildcard_impl_vars ~expected_ty:rhs_expected_ty (lhs, rhs))
    cases
  in
  (* Forward-declared symbol: return no syms so the declaration is
     not printed again.  The rules appear at this position in the
     output since each enc_result is printed in order. *)
  match existing with
  | Some _ -> { syms = []; rules; raw = "" }
  | None   -> { syms = [sym]; rules; raw = "" }

(* Create a simple rule with no pattern variables: sym arg1 arg2 ... ↪ rhs *)
let make_rule sym lhs rhs =
  let rule : rule = {
    lhs;
    rhs;
    arity = List.length lhs;
    arities = [||];
    vars_nb = 0;
    xvars_nb = 0;
    names = [||];
    rule_pos = None;
  } in
  (sym, rule)

(* Generate numeral literal infrastructure: of_Z, eo:: arithmetic symbols,
   and their computation rules.
   Called when processing declare-consts <numeral> Int.
   All arithmetic symbols are generated here as non-polymorphic,
   Int-specialized symbols. *)
let enc_ltrl_num target =
  (* target = the CPC type, e.g. Int *)
  let int_set = mk_Symb (get_sym "int") in
  (* of_Z : τ (int ⤳ Int)  —  coercion from Stdlib int to CPC Int *)
  let of_z_ty = tau_of (hol_arrow int_set target) in
  let of_z_sym = add_constant "of_Z" of_z_ty in
  (* Stdlib symbols for computation rules *)
  let stdlib_add = get_sym "+" in   (* ℤ → ℤ → ℤ *)
  let stdlib_mul = get_sym "*" in   (* ℤ → ℤ → ℤ *)
  let stdlib_neg = get_sym "—" in   (* ℤ → ℤ *)
  let stdlib_isZneg = get_sym "isZneg" in (* ℤ → 𝔹 *)
  let stdlib_isGt = get_sym "isGt" in     (* Comp → 𝔹 *)
  let stdlib_cmp = get_sym "≐" in         (* ℤ → ℤ → Comp *)
  let bool_target = mk_Symb (find "Bool") in
  (* Helper: build a rule *)
  let mk_rl sym lhs rhs nvars =
    let rule : rule = {
      lhs; rhs;
      arity = List.length lhs; arities = [||];
      vars_nb = nvars; xvars_nb = 0;
      names = [||]; rule_pos = None;
    } in (sym, rule)
  in
  let p i name = mk_Patt (Some i, name, [||]) in
  let of_z t = mk_Appl (mk_Symb of_z_sym, t) in
  (* {|eo::add|} : τ (Int ⤳ Int ⤳ Int)
     rule {|eo::add|} (of_Z $i) (of_Z $j) ↪ of_Z ($i + $j) *)
  let add_ty = tau_of (hol_arrow target (hol_arrow target target)) in
  let add_sym = add_sequential "{|eo::add|}" add_ty in
  let add_rule_ = mk_rl add_sym
    [of_z (p 0 "i"); of_z (p 1 "j")]
    (of_z (add_args (mk_Symb stdlib_add) [p 0 "i"; p 1 "j"]))
    2 in
  (* {|eo::mul|} : τ (Int ⤳ Int ⤳ Int)
     rule {|eo::mul|} (of_Z $i) (of_Z $j) ↪ of_Z ($i * $j) *)
  let mul_ty = tau_of (hol_arrow target (hol_arrow target target)) in
  let mul_sym = add_sequential "{|eo::mul|}" mul_ty in
  let mul_rule = mk_rl mul_sym
    [of_z (p 0 "i"); of_z (p 1 "j")]
    (of_z (add_args (mk_Symb stdlib_mul) [p 0 "i"; p 1 "j"]))
    2 in
  (* {|eo::neg|} : τ (Int ⤳ Int)
     rule {|eo::neg|} (of_Z $i) ↪ of_Z (— $i) *)
  let neg_ty = tau_of (hol_arrow target target) in
  let neg_sym = add_sequential "{|eo::neg|}" neg_ty in
  let neg_rule = mk_rl neg_sym
    [of_z (p 0 "i")]
    (of_z (mk_Appl (mk_Symb stdlib_neg, p 0 "i")))
    1 in
  (* {|eo::is_neg|} : τ (Int ⤳ Bool)
     rule {|eo::is_neg|} (of_Z $i) ↪ isZneg $i *)
  let is_neg_ty = tau_of (hol_arrow target bool_target) in
  let is_neg_sym = add_sequential "{|eo::is_neg|}" is_neg_ty in
  let is_neg_rule = mk_rl is_neg_sym
    [of_z (p 0 "i")]
    (mk_Appl (mk_Symb stdlib_isZneg, p 0 "i"))
    1 in
  (* {|eo::gt|} : τ (Int ⤳ Int ⤳ Bool)
     rule {|eo::gt|} (of_Z $i) (of_Z $j) ↪ isGt ($i ≐ $j) *)
  let gt_ty = tau_of (hol_arrow target (hol_arrow target bool_target)) in
  let gt_sym = add_sequential "{|eo::gt|}" gt_ty in
  let gt_rule = mk_rl gt_sym
    [of_z (p 0 "i"); of_z (p 1 "j")]
    (mk_Appl (mk_Symb stdlib_isGt,
      add_args (mk_Symb stdlib_cmp) [p 0 "i"; p 1 "j"]))
    2 in
  (* {|eo::is_z|} [T : Set] : τ (T ⤳ Bool)
     rule {|eo::is_z|} [Int] (of_Z _) ↪ true *)
  let is_z_tv = new_var "T" in
  let is_z_inner_ty = tau_of (hol_arrow (mk_Vari is_z_tv) bool_target) in
  let set_ty = tau_of (mk_Symb (eo_type_sym ())) in
  let is_z_ty = mk_Prod (set_ty, bind_var is_z_tv is_z_inner_ty) in
  let is_z_sym = add_sequential ~impl:[true] "{|eo::is_z|}" is_z_ty in
  let true_sym = find "true" in
  let is_z_rule = mk_rl is_z_sym
    [target; of_z (p 0 "_")]
    (mk_Symb true_sym)
    1 in
  (* {|eo::to_z|} : τ (Int ⤳ Int)
     rule {|eo::to_z|} (of_Z $i) ↪ of_Z $i *)
  let to_z_ty = tau_of (hol_arrow target target) in
  let to_z_sym = add_sequential "{|eo::to_z|}" to_z_ty in
  let to_z_rule = mk_rl to_z_sym
    [of_z (p 0 "i")]
    (of_z (p 0 "i"))
    1 in
  (* {|eo::zdiv|} : τ (Int ⤳ Int ⤳ Int) — no computation rules *)
  let zdiv_ty = tau_of (hol_arrow target (hol_arrow target target)) in
  let zdiv_sym = add_sequential "{|eo::zdiv|}" zdiv_ty in
  (* {|eo::zmod|} : τ (Int ⤳ Int ⤳ Int) — no computation rules *)
  let zmod_ty = tau_of (hol_arrow target (hol_arrow target target)) in
  let zmod_sym = add_sequential "{|eo::zmod|}" zmod_ty in
  { syms = [of_z_sym; add_sym; mul_sym; neg_sym;
            is_neg_sym; gt_sym; is_z_sym; to_z_sym;
            zdiv_sym; zmod_sym];
    rules = [
      add_rule_; mul_rule; neg_rule;
      is_neg_rule; gt_rule; is_z_rule; to_z_rule;
    ]; raw = "" }

let enc_ltrl cat ty =
  EO.set_lit_type cat ty;
  EO.register_lit_alias cat ty;
  let target = enc_term [] empty_ctxt ty in
  match cat with
  | Literal.STR ->
    failf "enc_ltrl: string literal category not supported"
  | Literal.NUM ->
    register_alias "{|eo::Int|}" target;
    enc_ltrl_num target
  | _ ->
    failf "enc_ltrl: unsupported literal category %s"
      (Literal.lit_category_str cat)

(* Rule encoding for declare-rule *)

(* Get the Proof symbol from prelude *)
let proof_sym () = find "Proof"

(* Build Proof(t) application *)
let mk_proof t = mk_Appl (mk_Symb (proof_sym ()), t)

(* Encode a declare-rule.

   For rules with :args, we generate:

     symbol <name>_aux [<type_params>] : τ T1 → ... → τ Tn → TYPE;
     rule <name>_aux <pattern1> ... <patternN>
       ↪ Proof <prem1> → ... → Proof <premM> → Proof <conclusion>;

     symbol <name> [<type_params>] :
       Π x1 : τ T1, ... Π xn : τ Tn, <name>_aux x1 ... xn;

   For rules without :args (only :premises), we generate:

     symbol <name> [<type_params>] (p1 : τ T1) ... :
       Proof <prem1> → ... → Proof <premM> → Proof <conclusion>;
*)
let enc_rule str ps (rdec : EO.rule_dec) =
  (* Ignore assumption for now - used for scope rules with assume-push/step-pop *)
  let _ = rdec.assm in
  (* Ignore reqs for now - should wrap conclusion in eo::requires *)
  let _ = rdec.reqs in

  let args = rdec.args in

  (* Extract premises as a flat term list.
     :premise-list F op means the rule takes an arbitrary number of premises,
     which are combined using op at proof time. For the encoding, we just
     use the pattern F as a single premise. *)
  let prems = match rdec.prem with
    | None -> []
    | Some (EO.Simple ts) -> ts
    | Some (EO.PremiseList (pattern, _op)) -> [pattern]
  in

  let conc = match rdec.conc with
    | EO.Conclusion t | EO.ConclusionExplicit t -> t
  in

  let ctx, _ = enc_params ps in

  (* Helper: build Proof p1 → Proof p2 → ... → Proof conclusion *)
  let build_proof_arrow prems conc_term =
    let conc_proof = mk_proof conc_term in
    List.fold_right
      (fun prem acc ->
         let prem_proof = mk_proof prem in
         mk_Prod (prem_proof, bind_var (new_var "_") acc))
      prems conc_proof
  in

  (* Check if an arg is a simple variable reference (not a pattern) *)
  let is_simple_arg = function
    | EO.Symbol s -> EO.prm_mem s ps  (* It's a parameter reference *)
    | _ -> false
  in

  (* Check if ALL args are simple variable references *)
  let all_args_simple = List.for_all is_simple_arg args in

  (* Premises and conclusions are formulas of type τ Bool.
     Passing this as expected_ty helps LambdaPi resolve polymorphic return types. *)
  let tau_bool = tau_of (mk_Symb (find "Bool")) in

  if args = [] || all_args_simple then begin
    (* No :args - simple rule with just premises and conclusion *)
    (* Encode premises and conclusion *)
    let prems_enc = List.map (fun p -> enc_term ps ctx p |> resolve_term ~debug:!verbose ~ctx ~expected_ty:tau_bool) prems in
    let conc_enc = enc_term ps ctx conc |> resolve_term ~debug:!verbose ~ctx ~expected_ty:tau_bool in

    (* If the conclusion has unsolved metas AND contains eo::ite (whose
       return type depends on an irreducible condition, preventing LambdaPi
       from re-inferring the types), replace unsolved metas with the first
       Set-typed variable from the context, and emit the symbol declaration
       as raw text with print_implicits=true to make the filled args visible. *)
    let rec has_eo_ite = function
      | Core.Term.Symb s -> s.Core.Term.sym_name = "{|eo::ite|}"
      | Core.Term.Appl (t1, t2) -> has_eo_ite t1 || has_eo_ite t2
      | _ -> false
    in
    let needs_explicit = Api_lp.has_unsolved_metas conc_enc && has_eo_ite conc_enc in
    let conc_enc, replacements =
      if needs_explicit then
        let type_vars = List.filter_map (fun (v, ty, _) ->
          match ty with
          | Core.Term.Appl (Core.Term.Symb s1, Core.Term.Symb s2)
            when s1.Core.Term.sym_name = "τ"
              && s2.Core.Term.sym_name = "{|eo::Type|}" -> Some v
          | _ -> None) ctx in
        match type_vars with
        | tv :: _ ->
          let solved = Api_lp.solve_set_metas_to conc_enc (mk_Vari tv) in
          (* Collect relation symbols that had unsolved metas filled *)
          let tv_name = Core.Term.base_name tv in
          let repls = ref [] in
          let rec find_relations = function
            | Core.Term.Appl _ as t ->
              let head, args = Core.Term.get_args t in
              (match head with
               | Core.Term.Symb s when
                 (let n = s.Core.Term.sym_name in
                  n = ">" || n = "<" || n = ">=" || n = "<=" || n = "=") &&
                 s.Core.Term.sym_impl <> [] ->
                 let n_impl = List.length s.Core.Term.sym_impl in
                 let impl_args = List.filteri (fun i _ -> i < n_impl) args in
                 let all_same_var = List.for_all (fun a ->
                   match a with
                   | Core.Term.Vari v -> Core.Term.base_name v = tv_name
                   | _ -> false) impl_args in
                 if all_same_var then
                   let impl_str = String.concat " " (List.map (fun _ -> tv_name) impl_args) in
                   repls := (s.Core.Term.sym_name, impl_str) :: !repls
               | _ -> ());
              List.iter find_relations args
            | _ -> ()
          in
          find_relations solved;
          (solved, !repls)
        | [] -> (conc_enc, [])
      else (conc_enc, [])
    in

    (* Build the type: Proof prem1 → ... → Proof premN → Proof conclusion *)
    let body_ty = build_proof_arrow prems_enc conc_enc in

    (* Find free type variables for implicit params *)
    let free_vars = Api_lp.LibTerm.free_vars body_ty in
    let impl_ctx =
      List.filter (fun (v, _, _) -> Core.Term.VarSet.mem v free_vars) ctx
    in
    let impl = List.map (fun _ -> true) impl_ctx in
    let ty, _ = Core.Ctxt.to_prod impl_ctx body_ty in

    let escaped_name = unique_name str in
    if replacements <> [] then
      Api_lp.register_explicit_replacements escaped_name replacements;
    let sym = add_constant ~impl escaped_name ty in
    { syms = [sym]; rules = []; raw = "" }

  end else begin
    (* Has :args - need auxiliary symbol with rewrite rule *)

    (* Create context for encoding args - need all params *)
    let arg_ctx, _ = enc_params ps in

    (* Infer the type of each arg by encoding and using LambdaPi's type inference.
       We encode the arg term, then use Infer to get its type. *)
    let infer_arg_type arg =
      let encoded = enc_term ps arg_ctx arg |> resolve_term ~ctx:arg_ctx in
      let prob = Core.Term.new_problem () in
      match Core.Infer.infer_noexn prob arg_ctx encoded with
      | Some (_, ty) ->
        (* ty is the LambdaPi type (e.g., τ U). We want just U (the Set). *)
        (* If ty = τ X, extract X. Otherwise use ty as-is. *)
        un_tau ty
      | None ->
        (* Fallback: use a placeholder *)
        failf "Cannot infer type of arg: %s" (Pp_eo.term_str arg)
    in

    (* Find parameters used in premises/conclusion but not in args.
       These are "extra" params (e.g. :premise-list variables) that must
       be added as explicit arguments to _aux so they appear in the LHS. *)
    let args_syms = EO.symbols_in_terms args in
    let rhs_syms = EO.symbols_in_terms (prems @ [conc]) in
    let param_names = List.map (fun (n, _, _) -> n) ps in
    let extra_params = List.filter (fun (n, _, _) ->
      EO.Set.mem n rhs_syms &&
      not (EO.Set.mem n args_syms) &&
      List.mem n param_names
    ) ps in
    (* Filter out Type params — they become implicit, not extra args *)
    let extra_params = List.filter (fun (_, ty, _) ->
      ty <> EO.Symbol EO.Builtin.ty_type) extra_params in

    let extra_lp_types = List.map (fun (_, ty, _) ->
      enc_term ps arg_ctx ty |> resolve_term ~ctx:arg_ctx) extra_params in
    let all_args = args @ List.map (fun (n, _, _) -> EO.Symbol n) extra_params in
    let arg_lp_types = List.map infer_arg_type args in
    let all_lp_types = arg_lp_types @ extra_lp_types in

    (* Build the _aux symbol type: τ T1 → τ T2 → ... → TYPE *)
    let aux_body_ty =
      List.fold_right
        (fun arg_ty acc ->
           let ty_enc = tau_of arg_ty in
           mk_Prod (ty_enc, bind_var (new_var "_") acc))
        all_lp_types
        (mk_Type)
    in

    (* Find implicit type params for _aux *)
    let aux_free_vars = Api_lp.LibTerm.free_vars aux_body_ty in
    let aux_impl_ctx =
      List.filter (fun (v, _, _) -> Core.Term.VarSet.mem v aux_free_vars) arg_ctx
    in
    let aux_impl = List.map (fun _ -> true) aux_impl_ctx in
    let aux_ty, _ = Core.Ctxt.to_prod aux_impl_ctx aux_body_ty in

    let aux_name = unique_name (str ^ "_aux") in
    let aux_sym = add_sequential ~impl:aux_impl aux_name aux_ty in

    (* Build the rewrite rule for _aux.
       LHS: (aux_name arg1 arg2 ... extra1 extra2 ...)
       RHS: Proof prem1 → ... → Proof conclusion *)

    (* Build LHS as an Eunoia Apply term *)
    let lhs_eo = EO.Apply (aux_name, all_args) in

    (* For RHS, we need to encode it specially since Proof is not in Eunoia.
       We'll encode the premises and conclusion, then build the arrow. *)
    let enc t = t
      |> enc_term ps arg_ctx
      |> resolve_term ~debug:!verbose ~ctx:arg_ctx ~expected_ty:tau_bool
      |> bind_pvars arg_ctx arg_ctx
    in

    let prems_enc = List.map enc prems in
    let conc_enc = enc conc in
    let rhs = build_proof_arrow prems_enc conc_enc in

    (* For LHS, use enc_case's encoding pattern *)
    let l = lhs_eo
      |> enc_term ps arg_ctx
      |> resolve_term ~debug:!verbose ~ctx:arg_ctx
      |> bind_pvars arg_ctx arg_ctx
    in
    let _, lhs_args = Core.Term.get_args l in

    let names = List.rev_map (fun (v, _, _) -> base_name v) arg_ctx |> Array.of_list in
    let vars_nb = List.length arg_ctx in

    let aux_rule : rule = {
      lhs = lhs_args;
      rhs;
      arity = List.length lhs_args;
      arities = Array.make vars_nb 0;
      vars_nb;
      xvars_nb = 0;
      names;
      rule_pos = None;
    } in

    (* Build the main symbol type:
       Π x1 : τ T1, ... Π xn : τ Tn, <name>_aux x1 ... xn *)

    (* Create fresh variables for the Π-bound args *)
    let arg_vars = List.mapi (fun i _ -> new_var (Printf.sprintf "x%d" (i + 1))) all_lp_types in

    (* Build _aux applied to implicit type params and then arg variables.
       Apply impl_ctx vars explicitly to avoid introducing placeholders. *)
    let aux_applied =
      let head =
        List.fold_left
          (fun acc (v, _, _) -> mk_Appl (acc, mk_Vari v))
          (mk_Symb aux_sym)
          (List.rev aux_impl_ctx)
      in
      List.fold_left
        (fun acc v -> mk_Appl (acc, mk_Vari v))
        head arg_vars
    in

    (* Build Π x1 : τ T1, ... Π xn : τ Tn, aux_applied *)
    let main_body_ty =
      List.fold_right2
        (fun arg_ty v acc ->
           let ty_enc = tau_of arg_ty in
           mk_Prod (ty_enc, bind_var v acc))
        all_lp_types arg_vars aux_applied
    in

    (* Find implicit type params for main symbol *)
    let main_free_vars = Api_lp.LibTerm.free_vars main_body_ty in
    let main_impl_ctx =
      List.filter (fun (v, _, _) -> Core.Term.VarSet.mem v main_free_vars) arg_ctx
    in
    let main_impl = List.map (fun _ -> true) main_impl_ctx in
    let main_ty, _ = Core.Ctxt.to_prod main_impl_ctx main_body_ty in

    let main_sym = add_constant ~impl:main_impl (unique_name str) main_ty in

    { syms = [aux_sym; main_sym];
      rules = [(aux_sym, aux_rule)]; raw = "" }
  end

(* Encode an assume command.
   (assume s F) becomes: symbol s : Proof F; *)
let enc_assume str formula =
  let ctx = empty_ctxt in
  let tau_bool = tau_of (mk_Symb (find "Bool")) in
  let formula_enc = enc_term [] ctx formula |> resolve_term ~ctx ~expected_ty:tau_bool in
  let ty = mk_proof formula_enc in
  let sym = add_constant ~impl:[] (unique_name str) ty in
  { syms = [sym]; rules = []; raw = "" }

(* Encode a step command.
   (step s F :rule r :premises (p1 ... pn) :args (a1 ... am))
   becomes: symbol s ≔ r p1 ... pn a1 ... am; (with optional : Proof F) *)
let enc_step str rule_name premises args conc_opt =
  let ctx = empty_ctxt in
  (* Build the application: (rule_name premise1 ... premiseN arg1 ... argM) *)
  let rule_sym = get_sym rule_name in
  let head = enc_sym rule_sym in
  (* Encode premises (which are proof term references) *)
  let prems_enc = List.map (fun p -> enc_term [] ctx p |> resolve_term ~debug:!verbose ~ctx) premises in
  (* Encode args *)
  let args_enc = List.map (fun a -> enc_term [] ctx a |> resolve_term ~debug:!verbose ~ctx) args in
  (* Build the full application *)
  let body_raw = List.fold_left (fun acc arg -> mk_Appl (acc, arg)) head (prems_enc @ args_enc) in
  (* Determine expected type if conclusion provided, and resolve body with it *)
  let body, expected_ty = match conc_opt with
    | Some conc ->
      let conc_enc = enc_term [] ctx conc |> resolve_term ~debug:!verbose ~ctx in
      let exp_ty = mk_proof conc_enc in
      (* Resolve body with expected type to help unification *)
      let body_resolved = resolve_term ~debug:!verbose ~ctx ~expected_ty:exp_ty body_raw in
      (body_resolved, Some exp_ty)
    | None ->
      (resolve_term ~debug:!verbose ~ctx body_raw, None)
  in
  let sym = add_definition ~impl:[] (unique_name str) expected_ty body in
  { syms = [sym]; rules = []; raw = "" }

let enc_symbol name = function
  | EO.Decl (ps, ty, attr) ->
    enc_decl name ps ty attr
  | EO.Defn (ps, body, ty_opt) ->
    enc_defn name ps body ty_opt
  | EO.Prog (ps, doms, ran, cases) ->
    enc_prog name ps doms ran cases
  | EO.Ltrl (cat, ty) ->
    enc_ltrl cat ty
  | EO.Rule (ps, rdec) ->
    enc_rule name ps rdec
  | EO.Assume formula ->
    enc_assume name formula
  | EO.Step (rule_name, premises, args, conc_opt) ->
    enc_step name rule_name premises args conc_opt

(* Encode a single named symbol. Caller is responsible for
   calling reset_overloads() once before the first symbol in a module. *)
let enc_one (name : string) (sym : EO.symbol) : enc_result =
  set_current_symbol name;
  set_current_phase "encode";
  let r = enc_symbol name sym in
  set_current_symbol "";
  set_current_phase "";
  r
