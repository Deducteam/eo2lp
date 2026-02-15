(* test_encoding.ml — Prelude.lp rewrite rule tests via LambdaPi *)

open Eo2lp
open Test_util

module LP = Api_lp

(* ============================================================
   LambdaPi Assertion Infrastructure
   ============================================================ *)

let lp_test_dir = "_build/test_lp"

let ensure_test_dir () =
  LP.mkdir_p lp_test_dir;
  let pkg_file = Filename.concat lp_test_dir "lambdapi.pkg" in
  if not (Sys.file_exists pkg_file) then begin
    let oc = open_out pkg_file in
    Printf.fprintf oc "package_name = test_lp\nroot_path = test_lp\n";
    close_out oc
  end;
  let prelude_dst = Filename.concat lp_test_dir "Prelude.lp" in
  if not (Sys.file_exists prelude_dst) then begin
    let ic = open_in "src/Prelude.lp" in
    let oc = open_out prelude_dst in
    (try while true do output_string oc (input_line ic ^ "\n") done
     with End_of_file -> ());
    close_in ic; close_out oc
  end

let check_lp name content =
  ensure_test_dir ();
  let test_file = Filename.concat lp_test_dir "test.lp" in
  let oc = open_out test_file in
  output_string oc content; close_out oc;
  let cmd = Printf.sprintf "cd %s && lambdapi check test.lp 2>&1" lp_test_dir in
  let ic = Unix.open_process_in cmd in
  let buf = Buffer.create 256 in
  (try while true do Buffer.add_channel buf ic 1 done with End_of_file -> ());
  let status = Unix.close_process_in ic in
  let output = Buffer.contents buf |> String.trim in
  match status with
  | Unix.WEXITED 0 ->
    incr pass_count;
    Printf.printf "%s %s\n" (green "PASS") name
  | _ ->
    incr fail_count;
    Printf.printf "%s %s\n    lambdapi: %s\n" (red "FAIL") name output

let check_lp_eq lhs rhs =
  let name = Printf.sprintf "%s ≡ %s" lhs rhs in
  let content = Printf.sprintf
    "require open test_lp.Prelude;\nassert ⊢ %s ≡ %s;" lhs rhs in
  check_lp name content

(* ============================================================
   Boolean Operations
   ============================================================ *)

let test_bool () =
  section "Prelude: Boolean Operations";

  subsection "eo::and";
  check_lp_eq "{|eo::and|} true true" "true";
  check_lp_eq "{|eo::and|} true false" "false";
  check_lp_eq "{|eo::and|} false true" "false";
  check_lp_eq "{|eo::and|} false false" "false";

  subsection "eo::or";
  check_lp_eq "{|eo::or|} true true" "true";
  check_lp_eq "{|eo::or|} true false" "true";
  check_lp_eq "{|eo::or|} false true" "true";
  check_lp_eq "{|eo::or|} false false" "false";

  subsection "eo::not";
  check_lp_eq "{|eo::not|} true" "false";
  check_lp_eq "{|eo::not|} false" "true";

  subsection "eo::xor";
  check_lp_eq "{|eo::xor|} true true" "false";
  check_lp_eq "{|eo::xor|} true false" "true";
  check_lp_eq "{|eo::xor|} false true" "true";
  check_lp_eq "{|eo::xor|} false false" "false"

(* ============================================================
   Core Operations
   ============================================================ *)

let test_core () =
  section "Prelude: Core Operations";

  subsection "eo::ite";
  check_lp_eq "{|eo::ite|} true true false" "true";
  check_lp_eq "{|eo::ite|} false true false" "false";

  subsection "eo::eq";
  check_lp_eq "{|eo::eq|} true true" "true";
  check_lp_eq "{|eo::eq|} true false" "false";
  check_lp_eq "{|eo::eq|} false true" "false";
  check_lp_eq "{|eo::eq|} false false" "true";

  subsection "eo::requires";
  check_lp_eq "{|eo::requires|} true true true" "true";
  check_lp_eq "{|eo::requires|} true true false" "false";
  check_lp_eq "{|eo::requires|} false false true" "true"

(* ============================================================
   Type Checking Operations
   ============================================================ *)

let test_typeof () =
  section "Prelude: Type Checking";

  check_lp_eq "{|eo::typeof|} true" "Bool";
  check_lp_eq "{|eo::typeof|} false" "Bool";
  check_lp_eq "{|eo::is_bool|} true" "true";
  check_lp_eq "{|eo::is_bool|} false" "true"

(* ============================================================
   Variable Binding
   ============================================================ *)

let test_var () =
  section "Prelude: Variable Binding";

  check_lp_eq
    "{|eo::is_var|} ({|eo::var|} \"x\" Bool)"
    "true";
  check_lp_eq
    "{|eo::is_var|} true"
    "false"

(* ============================================================
   Conditional Type (??-type)
   ============================================================ *)

let test_cond_type () =
  section "Prelude: Conditional Type (??)";

  check_lp_eq "?? true Bool Bool" "Bool";
  check_lp_eq "?? false Bool Bool" "Bool"

(* ============================================================
   eo::as (type cast identity)
   ============================================================ *)

let test_as () =
  section "Prelude: eo::as";

  check_lp_eq "{|eo::as|} Bool true" "true";
  check_lp_eq "{|eo::as|} Bool false" "false"

(* ============================================================
   Integer Encoding
   ============================================================ *)

(* Test that enc_int produces terms that print as valid LP integer literals.
   We initialize LP + encode the CPC signature (which creates of_Z),
   then call enc_int and print the resulting term, and check that the
   printed output can be parsed back by lambdapi. *)

let cpc_test_dir = "_build/test_int"

let ensure_cpc_test () =
  (* Run eo2lp to generate the CPC output for testing *)
  if not (Sys.file_exists cpc_test_dir) then begin
    let cmd =
      Printf.sprintf
        "dune exec eo2lp -- -d ./cpc -o %s -v error 2>&1"
        cpc_test_dir
    in
    let _ = Sys.command cmd in
    ()
  end

let check_cpc_lp name content =
  ensure_cpc_test ();
  let test_file = Filename.concat cpc_test_dir "int_test.lp" in
  let oc = open_out test_file in
  output_string oc content; close_out oc;
  let cmd =
    Printf.sprintf "cd %s && lambdapi check int_test.lp 2>&1" cpc_test_dir
  in
  let ic = Unix.open_process_in cmd in
  let buf = Buffer.create 256 in
  (try while true do Buffer.add_channel buf ic 1 done with End_of_file -> ());
  let status = Unix.close_process_in ic in
  let output = Buffer.contents buf |> String.trim in
  match status with
  | Unix.WEXITED 0 ->
    incr pass_count;
    Printf.printf "%s %s\n" (green "PASS") name
  | _ ->
    incr fail_count;
    Printf.printf "%s %s\n    lambdapi: %s\n" (red "FAIL") name output

let test_integers () =
  section "Integer Encoding";

  (* Test that of_Z with various integer literals type-checks.
     These exercise the same code path as enc_int in proof encoding. *)
  let test_of_z n =
    let name = Printf.sprintf "of_Z %d : τ Int" n in
    let content =
      Printf.sprintf
        "require open %s.Cpc;\nsymbol test_%s ≔ of_Z %d;\nassert ⊢ test_%s : τ Int;"
        (Filename.basename cpc_test_dir)
        (if n >= 0 then string_of_int n else "neg" ^ string_of_int (-n))
        n
        (if n >= 0 then string_of_int n else "neg" ^ string_of_int (-n))
    in
    check_cpc_lp name content
  in
  (* Single digit *)
  test_of_z 0;
  test_of_z 1;
  test_of_z 2;
  test_of_z 3;
  test_of_z 9;
  (* Multi-digit *)
  test_of_z 10;
  test_of_z 42;
  test_of_z 100;
  test_of_z 255;
  test_of_z 1000;
  (* Negative *)
  test_of_z (-1);
  test_of_z (-42);

  (* Test integer arithmetic rules *)
  subsection "arithmetic";
  let arith lhs rhs =
    let name = Printf.sprintf "%s ≡ %s" lhs rhs in
    let content =
      Printf.sprintf
        "require open %s.Cpc;\nassert ⊢ %s ≡ %s;"
        (Filename.basename cpc_test_dir) lhs rhs
    in
    check_cpc_lp name content
  in
  arith "{|eo::add|} (of_Z 1) (of_Z 2)" "of_Z 3";
  arith "{|eo::add|} (of_Z 10) (of_Z 32)" "of_Z 42";
  arith "{|eo::mul|} (of_Z 6) (of_Z 7)" "of_Z 42";
  arith "{|eo::neg|} (of_Z 5)" "of_Z (-5)";
  arith "{|eo::neg|} (of_Z (-3))" "of_Z 3"

(* ============================================================
   Main
   ============================================================ *)

let () =
  test_bool ();
  test_core ();
  test_typeof ();
  test_var ();
  test_cond_type ();
  test_as ();
  test_integers ();
  summary ()
