(* resolve.ml
   LambdaPi type inference and placeholder resolution.

   This module isolates all interactions with LambdaPi's inference,
   unification, and meta-variable machinery. The encoding phase
   (encode.ml) leaves placeholders for implicit arguments, and this
   module fills them in via LP's type inference. *)

open Api_lp

(* ================================================================
   Term predicates (resolution-specific)
   ================================================================ *)

(* Check if a symbol is Stdlib.Z's "int" *)
let is_stdlib_int s =
  s.Term.sym_name = "int" && s.Term.sym_path = ["Stdlib"; "Z"]

(* Check if term contains Stdlib.Z's "int" — either as a bare symbol
   (after cleanup) or as a solved meta. This indicates incorrect resolution
   (should be Int/Real, not Stdlib.Z.int). *)
let rec has_stdlib_int = function
  | Term.Symb s -> is_stdlib_int s
  | Term.Meta (m, ts) ->
    (match Timed.(!(m.Term.meta_value)) with
     | None -> false
     | Some mb -> has_stdlib_int (Term.msubst mb ts))
  | t -> term_exists (function
    | Term.Symb s -> is_stdlib_int s
    | _ -> false) t

(* ================================================================
   Term transformations (resolution-specific)
   ================================================================ *)

(* Replace solved metas with placeholders, UNLESS the solved value
   is a context variable (which would be needed as a pattern variable).
   Unsolved metas are always converted to placeholders. *)
let nonvar_metas_to_plac t =
  let rec go t =
    term_map (fun t -> match t with
      | Term.Symb s when is_stdlib_int s -> Some (mk_Plac false)
      | Term.Meta (m, ts) ->
        (match Timed.(!(m.Term.meta_value)) with
         | None -> Some (mk_Plac false)
         | Some mb ->
           let value = Term.msubst mb ts in
           (match value with
            | Term.Vari _ -> Some value
            | Term.Symb _ | Term.Meta _ -> Some (mk_Plac false)
            | _ -> Some (go value)))
      | _ -> None) t
  in go t

(* Replace unsolved metas with a given term (for best-effort type variable filling). *)
let solve_set_metas_to t replacement =
  term_map (function
    | Term.Meta (m, _) when Option.is_none Timed.(!(m.Term.meta_value)) ->
      Some replacement
    | _ -> None) t

(* ================================================================
   Core resolution: fill placeholders via LP type inference
   ================================================================ *)

(* Pretty-print a context as "x : T, y : U, ..." *)
let pp_ctx_compact () fmt ctx =
  let pp_entry fmt (v, ty, _) =
    Format.fprintf fmt "%s : %a" (base_name v) Print.term ty
  in
  Format.pp_print_list
    ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
    pp_entry fmt ctx

(* Resolve placeholders via type inference *)
let resolve_term ?(debug=false) ?(ctx=[]) ?expected_ty t =
  if not (has_plac t) then t
  else
    with_phase "resolve" @@ fun () ->
    let prob = Term.new_problem () in
    let result = match expected_ty with
      | Some exp_ty ->
        Core.Infer.check_noexn prob ctx t exp_ty
        |> Option.map (fun resolved -> (resolved, exp_ty))
      | None ->
        Core.Infer.infer_noexn prob ctx t
    in
    match result with
    | Some (resolved, ty) ->
      let _ = Core.Unif.solve_noexn prob in
      let cleaned = try Term.cleanup resolved with _ -> resolved in
      if has_unsolved_metas cleaned && debug then
        log_warn_pp (fun lbl ->
          Format.eprintf "  %s unsolved metas:@." (yellow (Printf.sprintf "[%s]" lbl));
          Format.eprintf "    ctx:  %a@." (pp_ctx_compact ()) ctx;
          Format.eprintf "    term: %a@." Print.term t;
          Format.eprintf "    got:  %a@." Print.term cleaned;
          Format.eprintf "    type: %a@.@." Print.term ty);
      cleaned
    | None ->
      log_warn_pp (fun lbl ->
        Format.eprintf "  %s resolve failed:@." (yellow (Printf.sprintf "[%s]" lbl));
        Format.eprintf "    ctx:  %a@." (pp_ctx_compact ()) ctx;
        Format.eprintf "    term: %a@.@." Print.term t);
      t

(* ================================================================
   Type inference helpers
   ================================================================ *)

(* Infer the type of a term. Returns Some ty on success, None on failure. *)
let infer_type ctx term =
  let prob = Term.new_problem () in
  match Core.Infer.infer_noexn prob ctx term with
  | Some (_, ty) -> Some ty
  | None -> None

(* Coerce a term of type τ int to τ T by wrapping with of_Z T.
   This is needed because Eunoia builtins like eo::len return raw integers
   (τ int = ℤ), but their results may be used where the declared numeral
   literal type (e.g. Int) is expected. *)
let coerce_int_to_lit ctx term expected_ty =
  let open Lp_builders in
  match infer_type ctx term with
  | Some inferred_ty ->
    let inner_inferred = un_tau inferred_ty in
    let inner_expected = un_tau expected_ty in
    let is_int_sym = function
      | Core.Term.Symb s -> s.Core.Term.sym_name = "int"
      | _ -> false
    in
    if is_int_sym inner_inferred && not (is_int_sym inner_expected) then
      (try
        let of_z = find "of_Z" in
        mk_Appl (mk_Symb of_z, term)
      with _ -> term)
    else term
  | None -> term
