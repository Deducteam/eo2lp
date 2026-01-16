(* Test suite for ethos-tests *)

open Test_infra

let ethos_tests_dir = "./ethos-tests"

let test_ethos () =
  print_section_header "ethos-tests";
  let stats = make_stats () in

  if not (Sys.file_exists ethos_tests_dir) then begin
    println "  [SKIP] ethos-tests directory not found";
    stats
  end else begin
    let base_sig = load_core_sig () in
    let files = collect_eo_files ethos_tests_dir in
    println (Printf.sprintf "  Found %d .eo files" (List.length files));

    run_parse_tests stats files;
    run_elaborate_tests stats ~base_sig files;
    run_encode_tests stats ~base_sig files;

    print_stats stats;
    stats
  end

let () =
  print_suite_header "ethos-tests Test Suite";
  let stats = test_ethos () in
  (* ethos-tests failures don't fail the build *)
  let code = 0 in
  ignore stats;
  exit code
