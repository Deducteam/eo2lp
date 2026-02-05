(* lp_builders.ml
   Shared term-building helpers for LambdaPi encoding.
   Used by both encode.ml and enc_numerals.ml. *)

open Api_lp

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

(* Strip eo::as from a resolved term tree: eo::as reduces to its second arg
   (rule eo::as _ $x ↪ $x), so it must not appear in rewrite rule LHS
   patterns where it would never match. *)
let strip_eo_as t =
  let eas = try Some (eo_as_sym ()) with _ -> None in
  let rec go t =
    match Core.Term.get_args t with
    | Core.Term.Symb s, [_ty; tm]
      when (match eas with Some e -> s == e | None -> false) ->
      go tm
    | _ ->
      match t with
      | Core.Term.Appl (t1, t2) -> Core.Term.mk_Appl (go t1, go t2)
      | _ -> t
  in
  go t

(* Build a rewrite rule record from LHS args, RHS, and context.
   ctx can be empty for rules that don't use named context variables. *)
let mk_rule_record ?(vars_nb=0) ctx lhs rhs =
  let names = List.rev_map (fun (v, _, _) -> base_name v) ctx |> Array.of_list in
  let vars_nb = if ctx <> [] then List.length ctx else vars_nb in
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
  rule

(* Compute implicit context and type from free variables *)
let impl_from_free_vars ctx body_ty =
  let free_vars = LibTerm.free_vars body_ty in
  let impl_ctx =
    List.filter (fun (v, _, _) -> Term.VarSet.mem v free_vars) ctx
  in
  let impl = List.map (fun _ -> true) impl_ctx in
  let ty, _ = Core.Ctxt.to_prod impl_ctx body_ty in
  (ty, impl, impl_ctx)
