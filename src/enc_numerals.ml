(* enc_numerals.ml
   Integer encoding infrastructure: of_Z, eo:: arithmetic symbols,
   and integer-dependent list operations (list_len, list_nth, list_find). *)

open Api_lp
open Lp_builders

module EO = Syntax_eo

(* Result type — matches Encode.enc_result *)
type enc_result = {
  syms  : sym list;
  rules : (sym * rule) list;
}

let empty_result = { syms = []; rules = [] }

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
  let stdlib_add = get_sym "+" in
  let stdlib_mul = get_sym "*" in
  let stdlib_neg = get_sym "—" in
  let stdlib_isZneg = get_sym "isZneg" in
  let stdlib_isGt = get_sym "isGt" in
  let stdlib_cmp = get_sym "≐" in
  let bool_target = mk_Symb (find "Bool") in
  let mk_rl sym lhs rhs nvars =
    (sym, mk_rule_record ~vars_nb:nvars [] lhs rhs)
  in
  let p i name = mk_Patt (Some i, name, [||]) in
  let of_z t = mk_Appl (mk_Symb of_z_sym, t) in
  (* eo::add *)
  let add_ty = tau_of (hol_arrow target (hol_arrow target target)) in
  let add_sym = add_sequential "{|eo::add|}" add_ty in
  let add_rule_ = mk_rl add_sym
    [of_z (p 0 "i"); of_z (p 1 "j")]
    (of_z (add_args (mk_Symb stdlib_add) [p 0 "i"; p 1 "j"]))
    2 in
  (* eo::mul *)
  let mul_ty = tau_of (hol_arrow target (hol_arrow target target)) in
  let mul_sym = add_sequential "{|eo::mul|}" mul_ty in
  let mul_rule = mk_rl mul_sym
    [of_z (p 0 "i"); of_z (p 1 "j")]
    (of_z (add_args (mk_Symb stdlib_mul) [p 0 "i"; p 1 "j"]))
    2 in
  (* eo::neg *)
  let neg_ty = tau_of (hol_arrow target target) in
  let neg_sym = add_sequential "{|eo::neg|}" neg_ty in
  let neg_rule = mk_rl neg_sym
    [of_z (p 0 "i")]
    (of_z (mk_Appl (mk_Symb stdlib_neg, p 0 "i")))
    1 in
  (* eo::is_neg *)
  let is_neg_ty = tau_of (hol_arrow target bool_target) in
  let is_neg_sym = add_sequential "{|eo::is_neg|}" is_neg_ty in
  let is_neg_rule = mk_rl is_neg_sym
    [of_z (p 0 "i")]
    (mk_Appl (mk_Symb stdlib_isZneg, p 0 "i"))
    1 in
  (* eo::gt *)
  let gt_ty = tau_of (hol_arrow target (hol_arrow target bool_target)) in
  let gt_sym = add_sequential "{|eo::gt|}" gt_ty in
  let gt_rule = mk_rl gt_sym
    [of_z (p 0 "i"); of_z (p 1 "j")]
    (mk_Appl (mk_Symb stdlib_isGt,
      add_args (mk_Symb stdlib_cmp) [p 0 "i"; p 1 "j"]))
    2 in
  (* eo::is_z — polymorphic *)
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
  (* eo::to_z *)
  let to_z_ty = tau_of (hol_arrow target target) in
  let to_z_sym = add_sequential "{|eo::to_z|}" to_z_ty in
  let to_z_rule = mk_rl to_z_sym
    [of_z (p 0 "i")]
    (of_z (p 0 "i"))
    1 in
  (* eo::zdiv — no computation rules *)
  let zdiv_ty = tau_of (hol_arrow target (hol_arrow target target)) in
  let zdiv_sym = add_sequential "{|eo::zdiv|}" zdiv_ty in
  (* eo::zmod — no computation rules *)
  let zmod_ty = tau_of (hol_arrow target (hol_arrow target target)) in
  let zmod_sym = add_sequential "{|eo::zmod|}" zmod_ty in
  (* Integer-dependent list operations *)
  let set_ty = tau_of (mk_Symb (eo_type_sym ())) in
  let w = mk_Plac false in
  let app_s = app_sym () in
  let app t1 t2 = add_args (enc_sym app_s) [t1; t2] in
  let nil_sym = find "{|eo::nil|}" in
  let ite_sym = find "{|eo::ite|}" in
  let eq_sym = find "{|eo::eq|}" in
  let nil f t2 = add_args (enc_sym nil_sym) [f; t2] in
  let ite c t e = add_args (enc_sym ite_sym) [c; t; e] in
  let eq a b = add_args (enc_sym eq_sym) [a; b] in
  let mk_list_sym name impl_n inner_ty =
    let tv2 = new_var "T2" in
    let tv1 = new_var "T1" in
    let f_ty_inner = hol_arrow (mk_Vari tv1) (hol_arrow (mk_Vari tv2) (mk_Vari tv2)) in
    let body = tau_of (hol_arrow f_ty_inner (inner_ty (mk_Vari tv1) (mk_Vari tv2))) in
    let ty = mk_Prod (set_ty, bind_var tv2 (mk_Prod (set_ty, bind_var tv1 body))) in
    let impl = List.init impl_n (fun _ -> true) in
    add_sequential ~impl name ty
  in
  (* eo::list_len *)
  let list_len_sym = mk_list_sym "{|eo::list_len|}" 2
    (fun _t1 t2 -> hol_arrow t2 target) in
  let list_len_r1 = mk_rl list_len_sym
    [w; w; p 0 "f"; app (app (p 0 "f") (p 1 "x")) (p 2 "xs")]
    (add_args (mk_Symb add_sym) [
      add_args (enc_sym list_len_sym) [p 0 "f"; p 2 "xs"];
      of_z (enc_int 1)])
    3 in
  let list_len_r2 = mk_rl list_len_sym
    [w; p 3 "T2"; p 0 "f"; p 1 "x"]
    (ite (eq (p 1 "x") (nil (p 0 "f") (p 3 "T2")))
         (of_z (enc_int 0)) (of_z (enc_int 1)))
    4 in
  (* eo::list_nth *)
  let list_nth_sym = mk_list_sym "{|eo::list_nth|}" 2
    (fun t1 t2 -> hol_arrow t2 (hol_arrow target t1)) in
  let list_nth_r1 = mk_rl list_nth_sym
    [w; w; p 0 "f"; app (app (p 0 "f") (p 1 "x")) (p 2 "xs"); of_z (enc_int 0)]
    (p 1 "x")
    3 in
  let list_nth_r2 = mk_rl list_nth_sym
    [w; w; p 0 "f"; app (app (p 0 "f") (p 1 "_")) (p 2 "xs"); p 3 "i"]
    (add_args (enc_sym list_nth_sym) [p 0 "f"; p 2 "xs";
      add_args (mk_Symb add_sym) [p 3 "i"; of_z (enc_int (-1))]])
    4 in
  (* list_find_aux *)
  let find_aux_sym = mk_list_sym "list_find_aux" 2
    (fun t1 t2 -> hol_arrow t1 (hol_arrow t2 (hol_arrow target target))) in
  let find_aux_r1 = mk_rl find_aux_sym
    [w; w; p 0 "f"; p 1 "x"; app (app (p 0 "f") (p 2 "y")) (p 3 "ys"); p 4 "i"]
    (ite (eq (p 1 "x") (p 2 "y")) (p 4 "i")
      (add_args (enc_sym find_aux_sym) [p 0 "f"; p 1 "x"; p 3 "ys";
        add_args (mk_Symb add_sym) [p 4 "i"; of_z (enc_int 1)]]))
    5 in
  let find_aux_r2 = mk_rl find_aux_sym
    [w; p 5 "T2"; p 0 "f"; p 1 "x"; p 2 "xs"; p 3 "i"]
    (ite (eq (p 2 "xs") (nil (p 0 "f") (p 5 "T2")))
         (of_z (enc_int (-1)))
         (ite (eq (p 1 "x") (p 2 "xs")) (p 3 "i") (of_z (enc_int (-1)))))
    6 in
  (* eo::list_find *)
  let list_find_sym = mk_list_sym "{|eo::list_find|}" 2
    (fun t1 t2 -> hol_arrow t2 (hol_arrow t1 target)) in
  let list_find_r1 = mk_rl list_find_sym
    [w; w; p 0 "f"; p 1 "xs"; p 2 "x"]
    (add_args (enc_sym find_aux_sym) [p 0 "f"; p 2 "x"; p 1 "xs"; of_z (enc_int 0)])
    3 in

  { syms = [of_z_sym; add_sym; mul_sym; neg_sym;
            is_neg_sym; gt_sym; is_z_sym; to_z_sym;
            zdiv_sym; zmod_sym;
            list_len_sym; list_nth_sym; find_aux_sym; list_find_sym];
    rules = [add_rule_; mul_rule; neg_rule;
             is_neg_rule; gt_rule; is_z_rule; to_z_rule;
             list_len_r1; list_len_r2;
             list_nth_r1; list_nth_r2;
             find_aux_r1; find_aux_r2;
             list_find_r1]; }

(* Encode a declare-consts command.
   enc_term_fn is passed from encode.ml to avoid circular dependency. *)
let enc_ltrl ~enc_term_fn cat ty =
  EO.register_lit_alias cat ty;
  let target = enc_term_fn [] empty_ctxt ty in
  match cat with
  | Literal.STR ->
    register_alias "{|eo::String|}" target;
    empty_result
  | Literal.NUM ->
    register_alias "{|eo::Int|}" target;
    enc_ltrl_num target
  | _ ->
    failf "enc_ltrl: unsupported literal category %s"
      (Literal.lit_category_str cat)
