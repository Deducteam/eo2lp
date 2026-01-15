(* Parser test suite for eo2lp
   Tests parsing of .eo files from ethos/tests and cpc-mini directories *)

open Eo2lp.Parse_eo

let cpc_mini_dir = "./cpc-mini"

(* Optionally set via environment variable *)
let ethos_tests_dir =
  try Sys.getenv "ETHOS_TESTS_DIR"
  with Not_found ->
    Sys.getenv "HOME" ^ "/prog/ethos/tests"

(* ============================================================
   Test infrastructure
   ============================================================ *)

let test_count = ref 0
let pass_count = ref 0
let fail_count = ref 0

let reset_counts () =
  test_count := 0;
  pass_count := 0;
  fail_count := 0

(* ============================================================
   File collection utilities
   ============================================================ *)

let collect_eo_files dir =
  let rec loop acc = function
    | [] -> acc
    | f :: fs when Sys.is_directory f ->
        let children =
          Sys.readdir f
          |> Array.to_list
          |> List.map (Filename.concat f)
        in
        loop acc (children @ fs)
    | f :: fs ->
        if Filename.check_suffix f ".eo" then
          loop (f :: acc) fs
        else
          loop acc fs
  in
  if Sys.file_exists dir && Sys.is_directory dir then
    loop [] [dir]
  else
    []

(* ============================================================
   Test runner
   ============================================================ *)

let test_parse_file fp =
  clear_parse_cache ();
  Eo2lp.Parse_ctx.had_parse_error := false;
  try
    let _ = parse_eo_file (".", fp) in
    if !(Eo2lp.Parse_ctx.had_parse_error) then
      Error "Parser error occurred"
    else
      Ok ()
  with e ->
    Error (Printexc.to_string e)

let run_tests name dir =
  Printf.printf "\n========================================\n";
  Printf.printf "  %s\n" name;
  Printf.printf "========================================\n";

  let files = collect_eo_files dir |> List.sort String.compare in
  let total = List.length files in

  if total = 0 then begin
    Printf.printf "  [SKIP] No .eo files found in %s\n" dir;
    (0, 0, 0)
  end else begin
    let passed = ref 0 in
    let failed = ref [] in

    List.iter (fun fp ->
      incr test_count;
      match test_parse_file fp with
      | Ok () ->
          incr passed;
          incr pass_count;
          Printf.printf "  [PASS] %s\n" fp
      | Error msg ->
          failed := (fp, msg) :: !failed;
          incr fail_count;
          Printf.printf "  [FAIL] %s\n" fp;
          Printf.printf "         %s\n" msg
    ) files;

    Printf.printf "\n  Total: %d | Passed: %d | Failed: %d\n"
      total !passed (List.length !failed);

    (total, !passed, List.length !failed)
  end

(* ============================================================
   Test: cpc-mini parsing
   ============================================================ *)

let test_cpc_mini () =
  run_tests "cpc-mini" cpc_mini_dir

(* ============================================================
   Test: ethos/tests parsing (optional, may not exist)
   ============================================================ *)

let test_ethos () =
  run_tests "ethos/tests" ethos_tests_dir

(* ============================================================
   Main test runner
   ============================================================ *)

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
  Printf.printf "  Parser Test Suite\n";
  Printf.printf "========================================\n";

  reset_counts ();

  let (_t1, _p1, f1) = test_cpc_mini () in
  let (_t2, _p2, _f2) = test_ethos () in

  print_summary ();

  (* cpc-mini failures are real bugs; ethos/tests failures are often
     expected due to newer Eunoia syntax not yet supported. *)
  if f1 > 0 then 1 else 0

let () =
  let code = run_all_tests () in
  exit code
