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

(* Rational encoding: Frac numerator denominator *)
let enc_rational n d =
  add_args (mk_Symb (find "Frac")) [enc_int n; enc_int d]

(* Rational encoding with term arguments (for pattern variables) *)
let enc_rational_var n d =
  add_args (mk_Symb (find "Frac")) [n; d]

(* Generate numeral literal infrastructure: of_Z coercion and
   Int-specialized computation rules for arithmetic builtins.
   Called when processing declare-consts <numeral> Int.
   The polymorphic arithmetic symbol declarations (eo::add, eo::mul, etc.)
   live in Prelude.lp; here we only add rules that fire for Int. *)
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
  let set_ty = tau_of (mk_Symb (eo_type_sym ())) in
  let mk_rl sym lhs rhs nvars =
    (sym, mk_rule_record ~vars_nb:nvars [] lhs rhs)
  in
  let p i name = mk_Patt (Some i, name, [||]) in
  let of_z t = mk_Appl (mk_Symb of_z_sym, t) in
  (* Look up arithmetic builtins from Prelude *)
  let add_sym = find "{|eo::add|}" in
  let mul_sym = find "{|eo::mul|}" in
  let neg_sym = find "{|eo::neg|}" in
  let is_neg_sym = find "{|eo::is_neg|}" in
  let gt_sym = find "{|eo::gt|}" in
  let is_z_sym = find "{|eo::is_z|}" in
  (* eo::to_z [T : Set] : τ (T ⤳ Int) — generated here with concrete return type *)
  let tv_to_z = new_var "T" in
  let to_z_body = tau_of (hol_arrow (mk_Vari tv_to_z) target) in
  let to_z_ty = mk_Prod (set_ty, bind_var tv_to_z to_z_body) in
  let to_z_sym = add_sequential ~impl:[true] "{|eo::to_z|}" to_z_ty in
  let _zdiv_sym = find "{|eo::zdiv|}" in
  let _zmod_sym = find "{|eo::zmod|}" in
  (* Int-specialized computation rules *)
  let add_rule_ = mk_rl add_sym
    [target; of_z (p 0 "i"); of_z (p 1 "j")]
    (of_z (add_args (mk_Symb stdlib_add) [p 0 "i"; p 1 "j"]))
    2 in
  let mul_rule = mk_rl mul_sym
    [target; of_z (p 0 "i"); of_z (p 1 "j")]
    (of_z (add_args (mk_Symb stdlib_mul) [p 0 "i"; p 1 "j"]))
    2 in
  let neg_rule = mk_rl neg_sym
    [target; of_z (p 0 "i")]
    (of_z (mk_Appl (mk_Symb stdlib_neg, p 0 "i")))
    1 in
  let is_neg_rule = mk_rl is_neg_sym
    [target; of_z (p 0 "i")]
    (mk_Appl (mk_Symb stdlib_isZneg, p 0 "i"))
    1 in
  let gt_rule = mk_rl gt_sym
    [target; of_z (p 0 "i"); of_z (p 1 "j")]
    (mk_Appl (mk_Symb stdlib_isGt,
      add_args (mk_Symb stdlib_cmp) [p 0 "i"; p 1 "j"]))
    2 in
  let true_sym = find "true" in
  let is_z_rule = mk_rl is_z_sym
    [target; of_z (p 0 "_")]
    (mk_Symb true_sym)
    1 in
  let to_z_rule = mk_rl to_z_sym
    [target; of_z (p 0 "i")]
    (of_z (p 0 "i"))
    1 in
  (* $zero/$one rules specialized at Int *)
  let zero_sym = find "{|$zero|}" in
  let one_sym = find "{|$one|}" in
  let zero_rule = mk_rl zero_sym [target] (of_z (enc_int 0)) 0 in
  let one_rule = mk_rl one_sym [target] (of_z (enc_int 1)) 0 in
  (* Integer-dependent list operations *)
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
    (add_args (enc_sym add_sym) [
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
      add_args (enc_sym add_sym) [p 3 "i"; of_z (enc_int (-1))]])
    4 in
  (* list_find_aux *)
  let find_aux_sym = mk_list_sym "list_find_aux" 2
    (fun t1 t2 -> hol_arrow t1 (hol_arrow t2 (hol_arrow target target))) in
  let find_aux_r1 = mk_rl find_aux_sym
    [w; w; p 0 "f"; p 1 "x"; app (app (p 0 "f") (p 2 "y")) (p 3 "ys"); p 4 "i"]
    (ite (eq (p 1 "x") (p 2 "y")) (p 4 "i")
      (add_args (enc_sym find_aux_sym) [p 0 "f"; p 1 "x"; p 3 "ys";
        add_args (enc_sym add_sym) [p 4 "i"; of_z (enc_int 1)]]))
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

  (* === Heterogeneous list operations (eo::List::find/nth/len) === *)
  (* These use eo::List::cons [T] as the constructor and of_Z indices *)
  let eo_list_ty = mk_Symb (find "{|eo::List|}") in
  let cons_sym = find "{|eo::List::cons|}" in
  let nil_t = mk_Symb (find "{|eo::List::nil|}") in
  let eo_type_t = mk_Symb (eo_type_sym ()) in
  (* cons_pat T x xs = @eo::List::cons T x xs (direct application) *)
  let cons_pat t x xs = add_args (mk_Appl (mk_Symb cons_sym, t)) [x; xs] in
  (* eo::List::len : τ (eo::List ⤳ Int) *)
  let hlist_len_ty = tau_of (hol_arrow eo_list_ty target) in
  let hlist_len_sym = add_sequential "{|eo::List::len|}" hlist_len_ty in
  let hlist_len_r1 = mk_rl hlist_len_sym
    [cons_pat (p 0 "T") (p 1 "x") (p 2 "xs")]
    (add_args (enc_sym add_sym) [
      add_args (enc_sym hlist_len_sym) [p 2 "xs"];
      of_z (enc_int 1)])
    3 in
  let hlist_len_r2 = mk_rl hlist_len_sym
    [nil_t]
    (of_z (enc_int 0))
    0 in
  (* eo::List::nth_type : τ (eo::List ⤳ Int ⤳ eo::Type) *)
  let hlist_nth_type_ty = tau_of (hol_arrow eo_list_ty (hol_arrow target eo_type_t)) in
  let hlist_nth_type_sym = add_sequential "{|eo::List::nth_type|}" hlist_nth_type_ty in
  let hlist_nth_type_r1 = mk_rl hlist_nth_type_sym
    [cons_pat (p 0 "T") (p 1 "_") (p 2 "_"); of_z (enc_int 0)]
    (p 0 "T")
    3 in
  let hlist_nth_type_r2 = mk_rl hlist_nth_type_sym
    [cons_pat (p 0 "_") (p 1 "_") (p 2 "xs"); p 3 "n"]
    (add_args (enc_sym hlist_nth_type_sym) [p 2 "xs";
      add_args (enc_sym add_sym) [p 3 "n"; of_z (enc_int (-1))]])
    4 in
  (* eo::List::nth [Z] (T : Set) (xs : τ eo::List) (n : τ Z) : τ T
     — we generate non-polymorphic: eo::List::nth (T : Set) ... (n : τ Int) *)
  let hlist_nth_tv = new_var "T" in
  let hlist_nth_body = tau_of (mk_Vari hlist_nth_tv) in
  let hlist_nth_inner =
    mk_Prod (tau_of target, bind_var (new_var "_n") hlist_nth_body) in
  let hlist_nth_inner2 =
    mk_Prod (tau_of eo_list_ty, bind_var (new_var "_xs") hlist_nth_inner) in
  let hlist_nth_ty =
    mk_Prod (set_ty, bind_var hlist_nth_tv hlist_nth_inner2) in
  let hlist_nth_sym = add_sequential "{|eo::List::nth|}" hlist_nth_ty in
  let hlist_nth_r1 = mk_rl hlist_nth_sym
    [p 0 "T"; cons_pat (p 1 "T") (p 2 "x") (p 3 "_"); of_z (enc_int 0)]
    (p 2 "x")
    4 in
  let hlist_nth_r2 = mk_rl hlist_nth_sym
    [p 0 "T"; cons_pat (p 1 "_") (p 2 "_") (p 3 "xs"); p 4 "n"]
    (add_args (enc_sym hlist_nth_sym) [p 0 "T"; p 3 "xs";
      add_args (enc_sym add_sym) [p 4 "n"; of_z (enc_int (-1))]])
    5 in
  (* List_find_aux : τ (eo::List ⤳ T ⤳ Int ⤳ Int) — polymorphic in search element type *)
  let hfind_aux_tv = new_var "T" in
  let hfind_aux_inner = tau_of (hol_arrow eo_list_ty
    (hol_arrow (mk_Vari hfind_aux_tv) (hol_arrow target target))) in
  let hfind_aux_ty =
    mk_Prod (set_ty, bind_var hfind_aux_tv hfind_aux_inner) in
  let hfind_aux_sym = add_sequential ~impl:[true] "{|List_find_aux|}" hfind_aux_ty in
  let hfind_aux_r1 = mk_rl hfind_aux_sym
    [w; cons_pat (p 0 "T") (p 1 "y") (p 2 "ys"); p 3 "x"; p 4 "i"]
    (ite (eq (p 3 "x") (p 1 "y")) (p 4 "i")
      (add_args (enc_sym hfind_aux_sym) [p 2 "ys"; p 3 "x";
        add_args (enc_sym add_sym) [p 4 "i"; of_z (enc_int 1)]]))
    5 in
  let hfind_aux_r2 = mk_rl hfind_aux_sym
    [w; nil_t; p 0 "x"; p 1 "i"]
    (of_z (enc_int (-1)))
    2 in
  (* eo::List::find [T U] : τ (eo::List ⤳ T ⤳ U)
     — we generate: eo::List::find [T] : τ (eo::List ⤳ T ⤳ Int) *)
  let hfind_tv = new_var "T" in
  let hfind_inner = tau_of (hol_arrow eo_list_ty
    (hol_arrow (mk_Vari hfind_tv) target)) in
  let hfind_ty =
    mk_Prod (set_ty, bind_var hfind_tv hfind_inner) in
  let hfind_sym = add_sequential ~impl:[true] "{|eo::List::find|}" hfind_ty in
  let hfind_r1 = mk_rl hfind_sym
    [w; p 0 "xs"; p 1 "x"]
    (add_args (enc_sym hfind_aux_sym) [p 0 "xs"; p 1 "x"; of_z (enc_int 0)])
    2 in

  { syms = [of_z_sym; to_z_sym;
            list_len_sym; list_nth_sym; find_aux_sym; list_find_sym;
            hlist_len_sym; hlist_nth_type_sym; hlist_nth_sym;
            hfind_aux_sym; hfind_sym];
    rules = [add_rule_; mul_rule; neg_rule;
             is_neg_rule; gt_rule; is_z_rule; to_z_rule;
             zero_rule; one_rule;
             list_len_r1; list_len_r2;
             list_nth_r1; list_nth_r2;
             find_aux_r1; find_aux_r2;
             list_find_r1;
             hlist_len_r1; hlist_len_r2;
             hlist_nth_type_r1; hlist_nth_type_r2;
             hlist_nth_r1; hlist_nth_r2;
             hfind_aux_r1; hfind_aux_r2;
             hfind_r1]; }

(* Generate rational literal infrastructure: of_Q coercion.
   Called when processing declare-consts <rational> Real. *)
let enc_ltrl_rat target =
  let rat_set = mk_Symb (get_sym "rat") in
  (* of_Q : τ (rat ⤳ Real)  —  coercion from Stdlib rational to CPC Real *)
  let of_q_ty = tau_of (hol_arrow rat_set target) in
  let of_q_sym = add_constant "of_Q" of_q_ty in
  let of_q t = mk_Appl (mk_Symb of_q_sym, t) in
  let mk_rl sym lhs rhs nvars =
    (sym, mk_rule_record ~vars_nb:nvars [] lhs rhs)
  in
  let p i name = mk_Patt (Some i, name, [||]) in
  let true_sym = find "true" in
  (* Stdlib rational arithmetic *)
  let stdlib_qadd = get_sym "qadd" in
  let stdlib_qmul = get_sym "qmul" in
  let stdlib_qneg1 = get_sym "qneg1" in
  (* Real-specialized computation rules for eo:: arithmetic *)
  let add_sym = find "{|eo::add|}" in
  let mul_sym = find "{|eo::mul|}" in
  let neg_sym = find "{|eo::neg|}" in
  (* eo::to_q [T : Set] : τ (T ⤳ Real) — generated here with concrete return type *)
  let set_ty = tau_of (mk_Symb (eo_type_sym ())) in
  let tv_q = new_var "T" in
  let to_q_body = tau_of (hol_arrow (mk_Vari tv_q) target) in
  let to_q_ty = mk_Prod (set_ty, bind_var tv_q to_q_body) in
  let to_q_sym = add_sequential ~impl:[true] "{|eo::to_q|}" to_q_ty in
  (* eo::is_q [T : Set] : τ (T ⤳ Bool) *)
  let bool_set = mk_Symb (find "Bool") in
  let tv_isq = new_var "T" in
  let is_q_body = tau_of (hol_arrow (mk_Vari tv_isq) bool_set) in
  let is_q_ty = mk_Prod (set_ty, bind_var tv_isq is_q_body) in
  let is_q_sym = add_sequential ~impl:[true] "{|eo::is_q|}" is_q_ty in
  (* eo::qdiv [T : Set] : τ (T ⤳ (T ⤳ Real)) *)
  let tv_qdiv = new_var "T" in
  let qdiv_body = tau_of (hol_arrow (mk_Vari tv_qdiv) (hol_arrow (mk_Vari tv_qdiv) target)) in
  let qdiv_ty = mk_Prod (set_ty, bind_var tv_qdiv qdiv_body) in
  let qdiv_sym = add_sequential ~impl:[true] "{|eo::qdiv|}" qdiv_ty in
  (* eo::add Real (of_Q r1) (of_Q r2) ↪ of_Q (qadd r1 r2) *)
  let add_rule = mk_rl add_sym
    [target; of_q (p 0 "r1"); of_q (p 1 "r2")]
    (of_q (add_args (mk_Symb stdlib_qadd) [p 0 "r1"; p 1 "r2"]))
    2 in
  (* eo::mul Real (of_Q r1) (of_Q r2) ↪ of_Q (qmul r1 r2) *)
  let mul_rule = mk_rl mul_sym
    [target; of_q (p 0 "r1"); of_q (p 1 "r2")]
    (of_q (add_args (mk_Symb stdlib_qmul) [p 0 "r1"; p 1 "r2"]))
    2 in
  (* eo::neg Real (of_Q r) ↪ of_Q (qneg1 r) *)
  let neg_rule = mk_rl neg_sym
    [target; of_q (p 0 "r")]
    (of_q (mk_Appl (mk_Symb stdlib_qneg1, p 0 "r")))
    1 in
  (* eo::to_q Real (of_Q r) ↪ of_Q r — identity on rationals *)
  let to_q_real_rule = mk_rl to_q_sym
    [target; of_q (p 0 "r")]
    (of_q (p 0 "r"))
    1 in
  (* eo::is_q Real (of_Q _) ↪ true *)
  let is_q_real_rule = mk_rl is_q_sym
    [target; of_q (p 0 "_")]
    (mk_Symb true_sym)
    1 in
  (* eo::qdiv Real (of_Q r1) (of_Q r2) ↪ of_Q (qdiv r1 r2) *)
  let stdlib_qdiv = get_sym "qdiv" in
  let qdiv_rule = mk_rl qdiv_sym
    [target; of_q (p 0 "r1"); of_q (p 1 "r2")]
    (of_q (add_args (mk_Symb stdlib_qdiv) [p 0 "r1"; p 1 "r2"]))
    2 in
  (* eo::to_q Int (of_Z i) ↪ of_Q (Frac i 1) — cross-type Int→Real conversion *)
  let of_z_sym = find "of_Z" in
  let of_z t = mk_Appl (mk_Symb of_z_sym, t) in
  let int_target = mk_Symb (find "Int") in
  let to_q_int_rule = mk_rl to_q_sym
    [int_target; of_z (p 0 "i")]
    (of_q (enc_rational_var (p 0 "i") (enc_int 1)))
    1 in
  (* $zero/$one rules specialized at Real *)
  let zero_sym = find "{|$zero|}" in
  let one_sym = find "{|$one|}" in
  let zero_rule = mk_rl zero_sym [target] (of_q (enc_rational 0 1)) 0 in
  let one_rule = mk_rl one_sym [target] (of_q (enc_rational 1 1)) 0 in
  { syms = [of_q_sym; to_q_sym; is_q_sym; qdiv_sym];
    rules = [add_rule; mul_rule; neg_rule;
             to_q_real_rule; to_q_int_rule; is_q_real_rule;
             qdiv_rule; zero_rule; one_rule] }

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
  | Literal.RAT ->
    register_alias "{|eo::Real|}" target;
    enc_ltrl_rat target
  | _ ->
    failf "enc_ltrl: unsupported literal category %s"
      (Literal.lit_category_str cat)
