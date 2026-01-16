(* Elaboration tests for cpc-mini *)

open Test_infra

let cpc_mini_dir = "./cpc-mini"

let collect_files () =
  collect_eo_files cpc_mini_dir
  |> List.filter (fun f -> Filename.basename f <> "Cpc.eo")

let () =
  parse_args ();
  print_suite_header "cpc-mini Elaboration Tests";
  let stats = make_stats () in

  if not (Sys.file_exists cpc_mini_dir) then begin
    println "  [SKIP] cpc-mini directory not found";
    exit 0
  end;

  let base_sig = load_core_sig () in
  let files = collect_files () in
  println (Printf.sprintf "  Found %d .eo files" (List.length files));

  run_elaborate_tests stats ~base_sig ~verbose:false files;
  print_stats stats;

  let code = if stats.failed > 0 || stats.timed_out > 0 then 1 else 0 in
  exit code
