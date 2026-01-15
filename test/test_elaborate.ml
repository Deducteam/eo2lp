open Eo2lp.Syntax_eo
open Eo2lp.Elaborate
open Eo2lp.Parse_eo

(* ============================================================
   Elaboration Test Suite

   Tests the elaboration strategy based on the Eunoia user manual
   and cpc-mini benchmark. Uses parsing capabilities to load
   actual .eo files and test realistic scenarios.
   ============================================================ *)

let test_count = ref 0
let pass_count = ref 0
let fail_count = ref 0

let reset_counts () =
  test_count := 0;
  pass_count := 0;
  fail_count := 0

let check name expected actual =
  incr test_count;
  let exp_str = term_str expected in
  let act_str = term_str actual in
  if exp_str = act_str then begin
    incr pass_count;
    Printf.printf "  [PASS] %s\n" name
  end else begin
    incr fail_count;
    Printf.printf "  [FAIL] %s\n" name;
    Printf.printf "    expected: %s\n" exp_str;
    Printf.printf "    actual:   %s\n" act_str
  end

let check_exn name f =
  incr test_count;
  try
    let _ = f () in
    incr fail_count;
    Printf.printf "  [FAIL] %s (expected exception)\n" name
  with _ ->
    incr pass_count;
    Printf.printf "  [PASS] %s (raised exception as expected)\n" name

let check_no_exn name f =
  incr test_count;
  try
    let _ = f () in
    incr pass_count;
    Printf.printf "  [PASS] %s\n" name
  with e ->
    incr fail_count;
    Printf.printf "  [FAIL] %s (exception: %s)\n" name (Printexc.to_string e)

let print_summary () =
  Printf.printf "\n========================================\n";
  Printf.printf "Total: %d | Passed: %d | Failed: %d\n"
    !test_count !pass_count !fail_count;
  Printf.printf "========================================\n"

(* ============================================================
   Core.eo Signature (from eo/Core.eo)
   ============================================================ *)

let core_signature : signature = [
  ("Bool", Decl ([], Symbol "Type", None));
  ("true", Decl ([], Symbol "Bool", None));
  ("false", Decl ([], Symbol "Bool", None));

  ("eo::requires", Decl (
    [("T", Symbol "Type", Some Implicit);
     ("U", Symbol "Type", Some Implicit);
     ("V", Symbol "Type", Some Implicit)],
    Apply ("->", [Symbol "T"; Symbol "U"; Symbol "V"; Symbol "V"]),
    None
  ));

  ("eo::typeof", Decl (
    [("T", Symbol "Type", Some Implicit)],
    Apply ("->", [Symbol "T"; Symbol "Type"]),
    None
  ));

  ("eo::eq", Decl (
    [("U", Symbol "Type", Some Implicit)],
    Apply ("->", [Symbol "U"; Symbol "U"; Symbol "Bool"]),
    None
  ));

  ("eo::ite", Decl (
    [("T", Symbol "Type", Some Implicit)],
    Apply ("->", [Symbol "Bool"; Symbol "T"; Symbol "T"; Symbol "T"]),
    None
  ));

  ("eo::cmp", Decl (
    [("T", Symbol "Type", Some Implicit); ("U", Symbol "Type", Some Implicit)],
    Apply ("->", [Symbol "T"; Symbol "U"; Symbol "Bool"]),
    None
  ));

  ("eo::is_var", Decl (
    [("T", Symbol "Type", Some Implicit)],
    Apply ("->", [Symbol "T"; Symbol "Bool"]),
    None
  ));

  ("eo::nil", Decl (
    [("U", Symbol "Type", Some Implicit); ("T", Symbol "Type", Some Implicit)],
    Apply ("->", [Apply ("->", [Symbol "U"; Symbol "T"; Symbol "T"]); Symbol "Type"; Symbol "T"]),
    None
  ));

  ("eo::cons", Decl (
    [("U", Symbol "Type", Some Implicit); ("T", Symbol "Type", Some Implicit)],
    Apply ("->", [Apply ("->", [Symbol "U"; Symbol "T"; Symbol "T"]); Symbol "U"; Symbol "T"; Symbol "T"]),
    None
  ));

  ("eo::list_concat", Decl (
    [("U", Symbol "Type", Some Implicit); ("T", Symbol "Type", Some Implicit)],
    Apply ("->", [Apply ("->", [Symbol "U"; Symbol "T"; Symbol "T"]); Symbol "T"; Symbol "T"; Symbol "T"]),
    None
  ));

  ("eo::List", Decl ([], Symbol "Type", None));
  ("eo::List::nil", Decl ([], Symbol "eo::List", None));
  ("eo::List::cons", Decl (
    [("T", Symbol "Type", Some Implicit)],
    Apply ("->", [Symbol "T"; Symbol "eo::List"; Symbol "eo::List"]),
    Some (RightAssocNil (Symbol "eo::List::nil"))
  ));

  ("eo::var", Decl ([], Apply ("->", [Symbol "String"; Symbol "Type"; Symbol "Type"]), None));

  (* HO application and arrow *)
  ("_", Decl ([], Apply ("->", [Symbol "Type"; Symbol "Type"; Symbol "Type"]), None));
  ("->", Decl ([], Apply ("->", [Symbol "Type"; Symbol "Type"; Symbol "Type"]), Some RightAssoc));
]

(* ============================================================
   Builtin.eo Signature (from cpc-mini/theories/Builtin.eo)
   ============================================================ *)

let builtin_signature : signature = core_signature @ [
  ("ite", Decl (
    [("A", Symbol "Type", Some Implicit)],
    Apply ("->", [Symbol "Bool"; Symbol "A"; Symbol "A"; Symbol "A"]),
    None
  ));

  ("not", Decl ([], Apply ("->", [Symbol "Bool"; Symbol "Bool"]), None));

  ("or", Decl ([], Apply ("->", [Symbol "Bool"; Symbol "Bool"; Symbol "Bool"]),
               Some (RightAssocNil (Symbol "false"))));

  ("and", Decl ([], Apply ("->", [Symbol "Bool"; Symbol "Bool"; Symbol "Bool"]),
                Some (RightAssocNil (Symbol "true"))));

  ("=>", Decl ([], Apply ("->", [Symbol "Bool"; Symbol "Bool"; Symbol "Bool"]),
               Some RightAssoc));

  ("xor", Decl ([], Apply ("->", [Symbol "Bool"; Symbol "Bool"; Symbol "Bool"]),
                Some LeftAssoc));

  ("=", Decl (
    [("A", Symbol "Type", Some Implicit)],
    Apply ("->", [Symbol "A"; Symbol "A"; Symbol "Bool"]),
    Some (Chainable "and")
  ));

  ("@list", Decl (
    [("T", Symbol "Type", Some Implicit)],
    Apply ("->", [Symbol "T"; Symbol "@List"; Symbol "@List"]),
    Some (RightAssocNil (Symbol "@list.nil"))
  ));
  ("@List", Decl ([], Symbol "Type", None));
  ("@list.nil", Decl ([], Symbol "@List", None));

  ("lambda", Decl (
    [("B", Symbol "Type", Some Implicit); ("L", Symbol "@List", None)],
    Apply ("->", [Symbol "B"; Symbol "Type"]),
    Some (Binder "@list")
  ));

  ("forall", Decl ([], Apply ("->", [Symbol "@List"; Symbol "Bool"; Symbol "Bool"]),
                   Some (Binder "@list")));

  ("exists", Decl ([], Apply ("->", [Symbol "@List"; Symbol "Bool"; Symbol "Bool"]),
                   Some (Binder "@list")));

  ("distinct", Decl (
    [("xs", Symbol "@List", None)],
    Apply ("eo::requires", [
      Apply ("$assoc_nil_same_type", [Symbol "@list"; Symbol "xs"]);
      Symbol "true";
      Symbol "Bool"
    ]),
    None
  ));

  ("@purify", Decl (
    [("A", Symbol "Type", Some Implicit); ("t", Symbol "A", Some Opaque)],
    Symbol "A",
    None
  ));
]

(* ============================================================
   Arith.eo Signature (from cpc-mini/theories/Arith.eo)
   ============================================================ *)

let arith_signature : signature = builtin_signature @ [
  ("Int", Decl ([], Symbol "Type", None));
  ("Real", Decl ([], Symbol "Type", None));

  ("+", Decl (
    [("T", Symbol "Type", Some Implicit); ("U", Symbol "Type", Some Implicit)],
    Apply ("->", [Symbol "T"; Symbol "U"; Apply ("$arith_typeunion", [Symbol "T"; Symbol "U"])]),
    Some (RightAssocNil (Literal (Numeral 0)))
  ));

  ("-", Decl (
    [("T", Symbol "Type", Some Implicit); ("U", Symbol "Type", Some Implicit)],
    Apply ("->", [Symbol "T"; Symbol "U"; Apply ("$arith_typeunion", [Symbol "T"; Symbol "U"])]),
    Some LeftAssoc
  ));

  ("*", Decl (
    [("T", Symbol "Type", Some Implicit); ("U", Symbol "Type", Some Implicit)],
    Apply ("->", [Symbol "T"; Symbol "U"; Apply ("$arith_typeunion", [Symbol "T"; Symbol "U"])]),
    Some (RightAssocNil (Literal (Numeral 1)))
  ));

  ("<", Decl (
    [("T", Symbol "Type", Some Implicit); ("U", Symbol "Type", Some Implicit)],
    Apply ("->", [Symbol "T"; Symbol "U"; Symbol "Bool"]),
    Some (Chainable "and")
  ));

  ("<=", Decl (
    [("T", Symbol "Type", Some Implicit); ("U", Symbol "Type", Some Implicit)],
    Apply ("->", [Symbol "T"; Symbol "U"; Symbol "Bool"]),
    Some (Chainable "and")
  ));

  (">", Decl (
    [("T", Symbol "Type", Some Implicit); ("U", Symbol "Type", Some Implicit)],
    Apply ("->", [Symbol "T"; Symbol "U"; Symbol "Bool"]),
    Some (Chainable "and")
  ));

  (">=", Decl (
    [("T", Symbol "Type", Some Implicit); ("U", Symbol "Type", Some Implicit)],
    Apply ("->", [Symbol "T"; Symbol "U"; Symbol "Bool"]),
    Some (Chainable "and")
  ));

  ("to_real", Decl (
    [("T", Symbol "Type", Some Implicit)],
    Apply ("->", [Symbol "T"; Symbol "Real"]),
    None
  ));

  ("to_int", Decl (
    [("T", Symbol "Type", Some Implicit)],
    Apply ("->", [Symbol "T"; Symbol "Int"]),
    None
  ));

  ("is_int", Decl (
    [("T", Symbol "Type", Some Implicit)],
    Apply ("->", [Symbol "T"; Symbol "Bool"]),
    None
  ));

  ("abs", Decl (
    [("T", Symbol "Type", Some Implicit)],
    Apply ("->", [Symbol "T"; Symbol "T"]),
    None
  ));
]

(* ============================================================
   Helper: Parse and elaborate a term string
   ============================================================ *)

let parse_elab sig_ str =
  let t = parse_eo_term str in
  elab (sig_, []) t

let parse_elab_ctx ctx str =
  let t = parse_eo_term str in
  elab ctx t

(* ============================================================
   SECTION 1: :right-assoc-nil Tests

   From Eunoia manual:
   (declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
   (or x y z) => (or x (or y (or z false)))
   ============================================================ *)

let test_right_assoc_nil () =
  Printf.printf "\n=== :right-assoc-nil ===\n";
  let ctx = (builtin_signature, []) in

  (* (or a b c) => (_ (_ or a) (_ (_ or b) (_ (_ or c) false))) *)
  let t1 = parse_elab_ctx ctx "(or a b c)" in
  let e1 = Apply ("_", [
    Apply ("_", [Symbol "or"; Symbol "a"]);
    Apply ("_", [
      Apply ("_", [Symbol "or"; Symbol "b"]);
      Apply ("_", [
        Apply ("_", [Symbol "or"; Symbol "c"]);
        Symbol "false"
      ])
    ])
  ]) in
  check "(or a b c)" e1 t1;

  (* (or a b) => (_ (_ or a) (_ (_ or b) false)) *)
  let t2 = parse_elab_ctx ctx "(or a b)" in
  let e2 = Apply ("_", [
    Apply ("_", [Symbol "or"; Symbol "a"]);
    Apply ("_", [
      Apply ("_", [Symbol "or"; Symbol "b"]);
      Symbol "false"
    ])
  ]) in
  check "(or a b)" e2 t2;

  (* (or a) => (_ (_ or a) false) *)
  let t3 = parse_elab_ctx ctx "(or a)" in
  let e3 = Apply ("_", [
    Apply ("_", [Symbol "or"; Symbol "a"]);
    Symbol "false"
  ]) in
  check "(or a)" e3 t3;

  (* (and a b c) with nil=true *)
  let t4 = parse_elab_ctx ctx "(and a b c)" in
  let e4 = Apply ("_", [
    Apply ("_", [Symbol "and"; Symbol "a"]);
    Apply ("_", [
      Apply ("_", [Symbol "and"; Symbol "b"]);
      Apply ("_", [
        Apply ("_", [Symbol "and"; Symbol "c"]);
        Symbol "true"
      ])
    ])
  ]) in
  check "(and a b c) nil=true" e4 t4;

  (* Arithmetic: (+ x y z) with nil=0 *)
  let ctx_arith = (arith_signature, []) in
  let t5 = parse_elab_ctx ctx_arith "(+ x y z)" in
  let e5 = Apply ("_", [
    Apply ("_", [Symbol "+"; Symbol "x"]);
    Apply ("_", [
      Apply ("_", [Symbol "+"; Symbol "y"]);
      Apply ("_", [
        Apply ("_", [Symbol "+"; Symbol "z"]);
        Literal (Numeral 0)
      ])
    ])
  ]) in
  check "(+ x y z) nil=0" e5 t5;

  (* ( * x y z) with nil=1 *)
  let t6 = parse_elab_ctx ctx_arith "(* x y z)" in
  let e6 = Apply ("_", [
    Apply ("_", [Symbol "*"; Symbol "x"]);
    Apply ("_", [
      Apply ("_", [Symbol "*"; Symbol "y"]);
      Apply ("_", [
        Apply ("_", [Symbol "*"; Symbol "z"]);
        Literal (Numeral 1)
      ])
    ])
  ]) in
  check "(* x y z) nil=1" e6 t6;

  ()

(* ============================================================
   SECTION 2: :right-assoc Tests (no nil terminator)

   From Eunoia manual:
   (declare-const => (-> Bool Bool Bool) :right-assoc)
   (=> x y z) => (=> x (=> y z))
   Binary case NOT impacted
   ============================================================ *)

let test_right_assoc () =
  Printf.printf "\n=== :right-assoc ===\n";
  let ctx = (builtin_signature, []) in

  (* (=> a b c) => (_ (_ => a) (_ (_ => b) c)) *)
  let t1 = parse_elab_ctx ctx "(=> a b c)" in
  let e1 = Apply ("_", [
    Apply ("_", [Symbol "=>"; Symbol "a"]);
    Apply ("_", [
      Apply ("_", [Symbol "=>"; Symbol "b"]);
      Symbol "c"
    ])
  ]) in
  check "(=> a b c)" e1 t1;

  (* (=> a b) - binary still curried *)
  let t2 = parse_elab_ctx ctx "(=> a b)" in
  let e2 = Apply ("_", [
    Apply ("_", [Symbol "=>"; Symbol "a"]);
    Symbol "b"
  ]) in
  check "(=> a b)" e2 t2;

  (* (=> a b c d) - four args *)
  let t3 = parse_elab_ctx ctx "(=> a b c d)" in
  let e3 = Apply ("_", [
    Apply ("_", [Symbol "=>"; Symbol "a"]);
    Apply ("_", [
      Apply ("_", [Symbol "=>"; Symbol "b"]);
      Apply ("_", [
        Apply ("_", [Symbol "=>"; Symbol "c"]);
        Symbol "d"
      ])
    ])
  ]) in
  check "(=> a b c d)" e3 t3;

  (* Arrow type: (-> A B C) *)
  let t4 = parse_elab_ctx ctx "(-> A B C)" in
  let e4 = Apply ("_", [
    Apply ("_", [Symbol "->"; Symbol "A"]);
    Apply ("_", [
      Apply ("_", [Symbol "->"; Symbol "B"]);
      Symbol "C"
    ])
  ]) in
  check "(-> A B C)" e4 t4;

  ()

(* ============================================================
   SECTION 3: :left-assoc Tests

   From Eunoia manual:
   (declare-const xor (-> Bool Bool Bool) :left-assoc)
   (xor x y z) => (xor (xor x y) z)
   ============================================================ *)

let test_left_assoc () =
  Printf.printf "\n=== :left-assoc ===\n";
  let ctx = (builtin_signature, []) in

  (* (xor a b c) => (_ (_ xor (_ (_ xor a) b)) c) *)
  let t1 = parse_elab_ctx ctx "(xor a b c)" in
  let e1 = Apply ("_", [
    Apply ("_", [Symbol "xor";
      Apply ("_", [
        Apply ("_", [Symbol "xor"; Symbol "a"]);
        Symbol "b"
      ])
    ]);
    Symbol "c"
  ]) in
  check "(xor a b c)" e1 t1;

  (* Binary *)
  let t2 = parse_elab_ctx ctx "(xor a b)" in
  let e2 = Apply ("_", [
    Apply ("_", [Symbol "xor"; Symbol "a"]);
    Symbol "b"
  ]) in
  check "(xor a b)" e2 t2;

  (* Arithmetic: (- x y z) left-assoc *)
  let ctx_arith = (arith_signature, []) in
  let t3 = parse_elab_ctx ctx_arith "(- x y z)" in
  let e3 = Apply ("_", [
    Apply ("_", [Symbol "-";
      Apply ("_", [
        Apply ("_", [Symbol "-"; Symbol "x"]);
        Symbol "y"
      ])
    ]);
    Symbol "z"
  ]) in
  check "(- x y z) left-assoc" e3 t3;

  ()

(* ============================================================
   SECTION 4: :chainable Tests

   From Eunoia manual:
   (declare-const < (-> Int Int Bool) :chainable and)
   (< a b c) => (and (< a b) (< b c))
   ============================================================ *)

let test_chainable () =
  Printf.printf "\n=== :chainable ===\n";
  let ctx = (arith_signature, []) in

  (* Binary case: (< a b) *)
  let t1 = parse_elab_ctx ctx "(< a b)" in
  Printf.printf "  (< a b) => %s\n" (term_str t1);
  check_no_exn "(< a b) elaborates" (fun () -> parse_elab_ctx ctx "(< a b)");

  (* (< a b c) should produce (and (< a b) (< b c)) *)
  let t2 = parse_elab_ctx ctx "(< a b c)" in
  Printf.printf "  (< a b c) => %s\n" (term_str t2);
  check_no_exn "(< a b c) elaborates" (fun () -> parse_elab_ctx ctx "(< a b c)");

  (* (= a b c) chainable with and *)
  let t3 = parse_elab_ctx ctx "(= a b c)" in
  Printf.printf "  (= a b c) => %s\n" (term_str t3);
  check_no_exn "(= a b c) elaborates" (fun () -> parse_elab_ctx ctx "(= a b c)");

  (* Four elements *)
  let t4 = parse_elab_ctx ctx "(< a b c d)" in
  Printf.printf "  (< a b c d) => %s\n" (term_str t4);

  ()

(* ============================================================
   SECTION 5: :binder Tests

   From Eunoia manual:
   (forall ((x Int)) body) => (forall (@list (eo::var "x" Int)) body)
   ============================================================ *)

let test_binder () =
  Printf.printf "\n=== :binder ===\n";
  let ctx = (builtin_signature, []) in

  (* Helper: create a Decl with :binder attribute *)
  let binder_decl t_cons =
    Decl ([], Apply ("->", [Symbol "@List"; Symbol "Bool"; Symbol "Bool"]), Some (Binder t_cons))
  in

  (* Single variable *)
  let t1 = elab_binder ctx
    ("forall", binder_decl "@list", [("x", Symbol "Int")], Symbol "body")
  in
  let e1 = Apply ("forall", [
    Apply ("@list", [Apply ("eo::var", [Literal (String "x"); Symbol "Int"])]);
    Symbol "body"
  ]) in
  check "forall ((x Int)) body" e1 t1;

  (* Multiple variables *)
  let t2 = elab_binder ctx
    ("forall", binder_decl "@list", [("x", Symbol "Int"); ("y", Symbol "Bool")], Symbol "body")
  in
  let e2 = Apply ("forall", [
    Apply ("@list", [
      Apply ("eo::var", [Literal (String "x"); Symbol "Int"]);
      Apply ("eo::var", [Literal (String "y"); Symbol "Bool"])
    ]);
    Symbol "body"
  ]) in
  check "forall ((x Int) (y Bool)) body" e2 t2;

  (* exists *)
  let t3 = elab_binder ctx
    ("exists", binder_decl "@list", [("x", Symbol "Int")], Symbol "body")
  in
  let e3 = Apply ("exists", [
    Apply ("@list", [Apply ("eo::var", [Literal (String "x"); Symbol "Int"])]);
    Symbol "body"
  ]) in
  check "exists ((x Int)) body" e3 t3;

  (* lambda *)
  let t4 = elab_binder ctx
    ("lambda", binder_decl "@list", [("x", Symbol "Int")], Symbol "body")
  in
  let e4 = Apply ("lambda", [
    Apply ("@list", [Apply ("eo::var", [Literal (String "x"); Symbol "Int"])]);
    Symbol "body"
  ]) in
  check "lambda ((x Int)) body" e4 t4;

  (* Missing binder attribute should fail *)
  let no_binder_decl = Decl ([], Symbol "Bool", None) in
  check_exn "binder missing attribute" (fun () ->
    elab_binder ctx ("forall", no_binder_decl, [("x", Symbol "Int")], Symbol "body")
  );

  ()

(* ============================================================
   SECTION 6: :list Parameter Tests

   From Eunoia manual:
   When a parameter is marked :list, it represents a list tail.
   (define Q ((x Bool) (y Bool :list)) (or x y))
   Q is (or x y) - y is already a list, no nil terminator
   ============================================================ *)

let test_list_param () =
  Printf.printf "\n=== :list parameter ===\n";

  (* Parameter marked :list - no nil terminator after it *)
  let ps = [("xs", Symbol "Bool", Some List)] in
  let ctx = (builtin_signature, ps) in

  let t1 = elab ctx (Apply ("or", [Symbol "a"; Symbol "xs"])) in
  Printf.printf "  (or a xs) xs:list => %s\n" (term_str t1);

  (* (or xs a) - :list in non-tail position uses eo::list_concat *)
  let t2 = elab ctx (Apply ("or", [Symbol "xs"; Symbol "a"])) in
  Printf.printf "  (or xs a) xs:list => %s\n" (term_str t2);

  (* Without :list, should get nil terminator *)
  let ps_nolist = [("y", Symbol "Bool", None)] in
  let ctx_nolist = (builtin_signature, ps_nolist) in

  let t3 = elab ctx_nolist (Apply ("or", [Symbol "a"; Symbol "y"])) in
  let e3 = Apply ("_", [
    Apply ("_", [Symbol "or"; Symbol "a"]);
    Apply ("_", [
      Apply ("_", [Symbol "or"; Symbol "y"]);
      Symbol "false"
    ])
  ]) in
  check "(or a y) no :list => has nil" e3 t3;

  ()

(* ============================================================
   SECTION 7: splice Tests (parameter substitution)
   ============================================================ *)

let test_splice () =
  Printf.printf "\n=== splice ===\n";

  (* Single explicit param *)
  let ps = [("x", Symbol "Int", None)] in
  let t = Symbol "x" in
  let ts = [Symbol "42"] in
  let (ps', t', ts') = splice (ps, t, ts) in
  check "splice single param" (Symbol "42") t';
  assert (ps' = []);
  assert (ts' = []);
  incr test_count; incr pass_count;
  Printf.printf "  [PASS] splice no leftover params/args\n";

  (* Implicit params skipped *)
  let ps2 = [("T", Symbol "Type", Some Implicit); ("x", Symbol "T", None)] in
  let t2 = Symbol "x" in
  let ts2 = [Symbol "42"] in
  let (ps2', t2', _) = splice (ps2, t2, ts2) in
  check "splice implicit skipped" (Symbol "42") t2';
  Printf.printf "  remaining params: %d\n" (List.length ps2');

  (* Nested term substitution *)
  let ps3 = [("a", Symbol "Bool", None); ("b", Symbol "Bool", None)] in
  let t3 = Apply ("=>", [Symbol "a"; Symbol "b"]) in
  let ts3 = [Symbol "p"; Symbol "q"] in
  let (_, t3', _) = splice (ps3, t3, ts3) in
  let e3 = Apply ("=>", [Symbol "p"; Symbol "q"]) in
  check "splice nested" e3 t3';

  ()

(* ============================================================
   SECTION 8: Defined Symbol Tests
   ============================================================ *)

let test_defined_symbols () =
  Printf.printf "\n=== defined symbols ===\n";

  (* Define my_impl as (=> a b) *)
  let sig_with_def = builtin_signature @ [
    ("my_impl", Defn (
      [("a", Symbol "Bool", None); ("b", Symbol "Bool", None)],
      Apply ("=>", [Symbol "a"; Symbol "b"])
    ))
  ] in
  let ctx = (sig_with_def, []) in

  (* (my_impl p q) => elaborated (=> p q) *)
  let t1 = elab ctx (Apply ("my_impl", [Symbol "p"; Symbol "q"])) in
  let e1 = Apply ("_", [
    Apply ("_", [Symbol "=>"; Symbol "p"]);
    Symbol "q"
  ]) in
  check "(my_impl p q)" e1 t1;

  ()

(* ============================================================
   SECTION 9: HO Application Tests
   ============================================================ *)

let test_ho_application () =
  Printf.printf "\n=== HO application (_) ===\n";
  let ctx = (builtin_signature, []) in

  (* (_ f x) - valid *)
  let t1 = elab ctx (Apply ("_", [Symbol "f"; Symbol "x"])) in
  check "(_ f x)" (Apply ("_", [Symbol "f"; Symbol "x"])) t1;

  (* Single arg - invalid *)
  check_exn "(_ f) invalid" (fun () ->
    elab ctx (Apply ("_", [Symbol "f"]))
  );

  (* Three args - invalid *)
  check_exn "(_ f x y) invalid" (fun () ->
    elab ctx (Apply ("_", [Symbol "f"; Symbol "x"; Symbol "y"]))
  );

  ()

(* ============================================================
   SECTION 10: Parameter-bound Symbol Tests
   ============================================================ *)

let test_param_bound () =
  Printf.printf "\n=== parameter-bound symbols ===\n";

  let ps = [("f", Apply ("->", [Symbol "Int"; Symbol "Int"]), None)] in
  let ctx = (builtin_signature, ps) in

  (* (f x y) where f is param => (_ (_ f x) y) *)
  let t1 = elab ctx (Apply ("f", [Symbol "x"; Symbol "y"])) in
  let e1 = Apply ("_", [Apply ("_", [Symbol "f"; Symbol "x"]); Symbol "y"]) in
  check "(f x y) param-bound" e1 t1;

  let t2 = elab ctx (Apply ("f", [Symbol "x"])) in
  let e2 = Apply ("_", [Symbol "f"; Symbol "x"]) in
  check "(f x) param-bound" e2 t2;

  ()

(* ============================================================
   SECTION 11: Literal Tests
   ============================================================ *)

let test_literals () =
  Printf.printf "\n=== literals ===\n";
  let ctx = (builtin_signature, []) in

  check "numeral" (Literal (Numeral 42)) (elab ctx (Literal (Numeral 42)));
  check "string" (Literal (String "hello")) (elab ctx (Literal (String "hello")));
  check "decimal" (Literal (Decimal 3.14)) (elab ctx (Literal (Decimal 3.14)));
  check "rational" (Literal (Rational (1, 2))) (elab ctx (Literal (Rational (1, 2))));

  ()

(* ============================================================
   SECTION 12: Type and eo::define Tests
   ============================================================ *)

let test_type_and_define () =
  Printf.printf "\n=== Type and eo::define ===\n";
  let ctx = (builtin_signature, []) in

  check "Type symbol" (Symbol "Type") (elab ctx (Symbol "Type"));

  let t = Bind ("eo::define", [("x", Symbol "Int")], Symbol "body") in
  check "eo::define pass-through" t (elab ctx t);

  ()

(* ============================================================
   SECTION 13: Nested Application Tests
   ============================================================ *)

let test_nested () =
  Printf.printf "\n=== nested applications ===\n";
  let ctx = (arith_signature, []) in

  (* (or (and a b) (and c d)) *)
  let t1 = parse_elab_ctx ctx "(or (and a b) (and c d))" in
  Printf.printf "  (or (and a b) (and c d)) => %s\n" (term_str t1);
  check_no_exn "nested or/and" (fun () -> parse_elab_ctx ctx "(or (and a b) (and c d))");

  (* (=> (or a b) (and c d)) *)
  let t2 = parse_elab_ctx ctx "(=> (or a b) (and c d))" in
  Printf.printf "  (=> (or a b) (and c d)) => %s\n" (term_str t2);

  (* Arithmetic in boolean *)
  let t3 = parse_elab_ctx ctx "(and (< x y) (> y z))" in
  Printf.printf "  (and (< x y) (> y z)) => %s\n" (term_str t3);

  (* not(not(a)) *)
  let t4 = parse_elab_ctx ctx "(not (not a))" in
  Printf.printf "  (not (not a)) => %s\n" (term_str t4);

  ()

(* ============================================================
   SECTION 14: @list Constructor Tests
   ============================================================ *)

let test_list_constructor () =
  Printf.printf "\n=== @list constructor ===\n";
  let ctx = (builtin_signature, []) in

  (* (@list a b c) with :right-assoc-nil @list.nil *)
  let t1 = parse_elab_ctx ctx "(@list a b c)" in
  let e1 = Apply ("_", [
    Apply ("_", [Symbol "@list"; Symbol "a"]);
    Apply ("_", [
      Apply ("_", [Symbol "@list"; Symbol "b"]);
      Apply ("_", [
        Apply ("_", [Symbol "@list"; Symbol "c"]);
        Symbol "@list.nil"
      ])
    ])
  ]) in
  check "(@list a b c)" e1 t1;

  (* Single element *)
  let t2 = parse_elab_ctx ctx "(@list a)" in
  let e2 = Apply ("_", [
    Apply ("_", [Symbol "@list"; Symbol "a"]);
    Symbol "@list.nil"
  ]) in
  check "(@list a)" e2 t2;

  ()

(* ============================================================
   SECTION 15: Error Cases
   ============================================================ *)

let test_errors () =
  Printf.printf "\n=== error cases ===\n";
  let ctx = (builtin_signature, []) in

  check_exn "unknown symbol in app" (fun () ->
    elab ctx (Apply ("unknown_symbol", [Symbol "x"]))
  );

  check_exn "unknown binder" (fun () ->
    elab ctx (Bind ("unknown_binder", [("x", Symbol "Int")], Symbol "body"))
  );

  ()

(* ============================================================
   SECTION 16: Integration Tests with Parsing
   ============================================================ *)

let test_parse_integration () =
  Printf.printf "\n=== parse + elaborate integration ===\n";

  (* Boolean terms *)
  let t1 = parse_elab builtin_signature "(or true false true)" in
  Printf.printf "  (or true false true) => %s\n" (term_str t1);

  let t2 = parse_elab builtin_signature "(and (or a b) (or c d))" in
  Printf.printf "  (and (or a b) (or c d)) => %s\n" (term_str t2);

  let t3 = parse_elab builtin_signature "(=> a (=> b c))" in
  Printf.printf "  (=> a (=> b c)) => %s\n" (term_str t3);

  let t4 = parse_elab builtin_signature "(=> a b c d)" in
  Printf.printf "  (=> a b c d) => %s\n" (term_str t4);

  (* Arithmetic *)
  let t5 = parse_elab arith_signature "(+ 1 2 3)" in
  Printf.printf "  (+ 1 2 3) => %s\n" (term_str t5);

  let t6 = parse_elab arith_signature "(- 10 5 2)" in
  Printf.printf "  (- 10 5 2) => %s\n" (term_str t6);

  let t7 = parse_elab arith_signature "(* 2 3 4)" in
  Printf.printf "  (* 2 3 4) => %s\n" (term_str t7);

  ()

(* ============================================================
   SECTION 17: Program Pattern Tests (from cpc-mini/programs/)
   ============================================================ *)

let test_program_patterns () =
  Printf.printf "\n=== program patterns ===\n";

  (* Pattern: (or F1 F2) where F2 is :list *)
  let ps = [
    ("F1", Symbol "Bool", None);
    ("F2", Symbol "Bool", Some List)
  ] in
  let ctx = (arith_signature, ps) in

  let t1 = elab ctx (Apply ("or", [Symbol "F1"; Symbol "F2"])) in
  Printf.printf "  (or F1 F2) F2:list => %s\n" (term_str t1);

  (* Pattern: (and C1 Cs) where Cs is :list *)
  let ps2 = [
    ("C1", Symbol "Bool", None);
    ("Cs", Symbol "Bool", Some List)
  ] in
  let ctx2 = (arith_signature, ps2) in

  let t2 = elab ctx2 (Apply ("and", [Symbol "C1"; Symbol "Cs"])) in
  Printf.printf "  (and C1 Cs) Cs:list => %s\n" (term_str t2);

  check_no_exn "program patterns elaborate" (fun () ->
    elab ctx2 (Apply ("or", [
      Apply ("and", [Symbol "C1"; Symbol "Cs"]);
      Symbol "false"
    ]))
  );

  ()

(* ============================================================
   SECTION 18: eo::List::cons Tests (from Core.eo)
   ============================================================ *)

(* ============================================================
   SECTION 18: Overloading Tests

   Tests that overloaded symbols are handled correctly.
   Without an LP context, the first declaration is used.
   With an LP context, typechecking resolves the overload.
   ============================================================ *)

(* Base signature for overloading tests (without pre-existing -) *)
let overload_base_signature : signature = [
  ("Int", Decl ([], Symbol "Type", None));
  ("Bool", Decl ([], Symbol "Type", None));
  ("true", Decl ([], Symbol "Bool", None));
  ("false", Decl ([], Symbol "Bool", None));
  ("+", Decl (
    [],
    Apply ("->", [Symbol "Int"; Symbol "Int"; Symbol "Int"]),
    Some (RightAssocNil (Literal (Numeral 0)))
  ));
]

(* Signature with overloaded minus: unary negation and binary subtraction *)
let overload_signature : signature = overload_base_signature @ [
  (* Binary subtraction declared first *)
  ("-", Decl (
    [],
    Apply ("->", [Symbol "Int"; Symbol "Int"; Symbol "Int"]),
    Some LeftAssoc
  ));
  (* Unary negation declared second *)
  ("-", Decl (
    [],
    Apply ("->", [Symbol "Int"; Symbol "Int"]),
    None
  ));
]

let test_overloading () =
  Printf.printf "\n=== overloading ===\n";

  (* Test overloaded symbol resolution - first matching declaration is used *)
  let ctx = (overload_signature, []) in

  (* Binary subtraction works (first declaration) *)
  check_no_exn "(- x y) uses first declaration" (fun () ->
    let _ = elab ctx (Apply ("-", [Symbol "x"; Symbol "y"])) in ()
  );

  (* Unary negation also works via first declaration with partial application *)
  check_no_exn "(- x) partial application" (fun () ->
    let _ = elab ctx (Apply ("-", [Symbol "x"])) in ()
  );

  (* Test that overloaded symbols can be looked up *)
  let count_minus =
    List.length (List.filter (fun (s, _) -> s = "-") overload_signature)
  in
  incr test_count;
  if count_minus = 2 then begin
    incr pass_count;
    Printf.printf "  [PASS] signature contains 2 declarations for -\n"
  end else begin
    incr fail_count;
    Printf.printf "  [FAIL] signature should contain 2 declarations for -, got %d\n"
      count_minus
  end;

  (* Test non-overloaded symbol *)
  let count_plus =
    List.length (List.filter (fun (s, _) -> s = "+") overload_signature)
  in
  incr test_count;
  if count_plus = 1 then begin
    incr pass_count;
    Printf.printf "  [PASS] signature contains 1 declaration for +\n"
  end else begin
    incr fail_count;
    Printf.printf "  [FAIL] signature should contain 1 declaration for +, got %d\n"
      count_plus
  end;

  ()

(* ============================================================
   SECTION 19: eo::List::cons Tests (from Core.eo)
   ============================================================ *)

let test_eo_list_cons () =
  Printf.printf "\n=== eo::List::cons ===\n";
  let ctx = (core_signature, []) in

  (* (eo::List::cons a b c) with :right-assoc-nil eo::List::nil *)
  let t1 = elab ctx (Apply ("eo::List::cons", [Symbol "a"; Symbol "b"; Symbol "c"])) in
  let e1 = Apply ("_", [
    Apply ("_", [Symbol "eo::List::cons"; Symbol "a"]);
    Apply ("_", [
      Apply ("_", [Symbol "eo::List::cons"; Symbol "b"]);
      Apply ("_", [
        Apply ("_", [Symbol "eo::List::cons"; Symbol "c"]);
        Symbol "eo::List::nil"
      ])
    ])
  ]) in
  check "(eo::List::cons a b c)" e1 t1;

  ()

(* ============================================================
   Main Test Runner
   ============================================================ *)

let run_all_tests () =
  Printf.printf "\n";
  Printf.printf "========================================\n";
  Printf.printf "  Elaboration Test Suite\n";
  Printf.printf "========================================\n";

  reset_counts ();

  test_right_assoc_nil ();
  test_right_assoc ();
  test_left_assoc ();
  test_chainable ();
  test_binder ();
  test_list_param ();
  test_splice ();
  test_defined_symbols ();
  test_ho_application ();
  test_param_bound ();
  test_literals ();
  test_type_and_define ();
  test_nested ();
  test_list_constructor ();
  test_errors ();
  test_parse_integration ();
  test_program_patterns ();
  test_overloading ();
  test_eo_list_cons ();

  print_summary ();

  if !fail_count > 0 then 1 else 0

let () =
  let code = run_all_tests () in
  exit code
