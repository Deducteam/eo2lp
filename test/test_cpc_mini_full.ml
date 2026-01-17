(* Full integration test for the cpc-mini directory *)

open Test_infra

let () =
  print_suite_header "cpc-mini Full Integration";
  let stats = make_stats () in
  let files = collect_eo_files "./cpc-mini" in
  let base_sig = load_core_sig () in
  run_parse_tests stats files;
  run_elaborate_tests stats ~base_sig ~verbose:!verbose files;
  run_encode_tests stats ~base_sig ~verbose:!verbose files;
  print_stats stats;
  if stats.failed > 0 || stats.timed_out > 0 then exit 1
