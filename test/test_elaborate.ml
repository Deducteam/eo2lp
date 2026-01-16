(* Signature Elaboration test suite for eo2lp *)

open Eo2lp.Parse_eo
open Eo2lp.Elaborate

let cpc_mini_dir = "./cpc-mini"

(* Optionally set via environment variable *)
let ethos_tests_dir =
  try Sys.getenv "ETHOS_TESTS_DIR"
  with Not_found ->
    Sys.getenv "HOME" ^ "/prog/ethos/tests"

let test_count = ref 0
let pass_count = ref 0
let fail_count = ref 0

let reset_counts () =
  test_count := 0;
  pass_count := 0;
  fail_count := 0

let test_elab_dir name dir ?(base_sig=[]) () =
  incr test_count;
  Printf.printf "\n========================================\n";
  Printf.printf "  Elaborating: %s\n" name;
  Printf.printf "========================================\n";
  try
    if Sys.file_exists dir && Sys.is_directory dir then (
      let signature = base_sig @ parse_eo_dir dir in
      Printf.printf "  Elaborating %d definitions...\n" (List.length signature);
      let _ = elab_sig signature in
      Printf.printf "  Elaboration complete.\n";
      Printf.printf "  [PASS] %s elaborated successfully\n" name;
      incr pass_count;
      true
    ) else (
      Printf.printf "  [SKIP] Directory not found: %s\n" dir;
      true (* Not a failure if the dir is missing *)
    )
  with e ->
    Printf.printf "  [FAIL] %s failed to elaborate\n" name;
    Printf.printf "         %s\n" (Printexc.to_string e);
    Printexc.print_backtrace stdout;
    incr fail_count;
    false

let print_summary () =
  Printf.printf "\n========================================\n";
  Printf.printf "  SUMMARY\n";
  Printf.printf "========================================\n";
  Printf.printf "  Total: %d | Passed: %d | Failed: %d\n"
    !test_count !pass_count !fail_count;
  Printf.printf "========================================\n"

let run_all_tests () =
  Printf.printf "\n";
  Printf.printf "========================================\n";
  Printf.printf "  Signature Elaboration Test Suite\n";
  Printf.printf "========================================\n";

  reset_counts ();

  let core_sig = parse_eo_file (".", "eo/Core.eo") in

  let cpc_ok = test_elab_dir "cpc-mini" cpc_mini_dir ~base_sig:core_sig () in
  let ethos_ok = test_elab_dir "ethos/tests" ethos_tests_dir ~base_sig:core_sig () in
  (* let ethos_ok = true in *)

  print_summary ();

  if cpc_ok && ethos_ok && !fail_count = 0 then 0 else 1

let () =
  let code = run_all_tests () in
  exit code
