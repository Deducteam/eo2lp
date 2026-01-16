(* Test suite for Core.eo *)

open Test_infra
open Eo2lp.Parse_eo
open Eo2lp.Elaborate
open Eo2lp.Encode

let core_file = "eo/Core.eo"

let test_core () =
  print_section_header "Core.eo";
  let stats = make_stats () in

  if not (Sys.file_exists core_file) then begin
    println "  [SKIP] Core.eo not found";
    stats
  end else begin
    (* Parse *)
    println "\n  ┌─ Parsing";
    let parse_result = test_parse_file core_file in
    record_result stats parse_result;
    print_result core_file parse_result;

    (* Get the parsed signature for elaboration/encoding *)
    clear_parse_cache ();
    let core_sig =
      try Some (parse_eo_file "." core_file)
      with _ -> None
    in

    (match core_sig with
    | None ->
        println "  [SKIP] Could not load Core.eo for elaboration/encoding"
    | Some sig_ ->
        (* Elaborate *)
        println "\n  ┌─ Elaboration";
        let elab_result =
          match with_timeout (fun () -> elab_sig sig_) with
          | None -> Timeout (!test_timeout, None)
          | Some (_, elapsed) -> Pass (elapsed, None)
          | exception Failure msg -> Fail (msg, 0.0, None)
          | exception e -> Fail (Printexc.to_string e, 0.0, None)
        in
        record_result stats elab_result;
        print_result core_file elab_result;

        (* Encode *)
        println "\n  ┌─ Encoding";
        let encode_result =
          match with_timeout (fun () ->
            let elab_sig_ = elab_sig sig_ in
            eo_sig elab_sig_
          ) with
          | None -> Timeout (!test_timeout, None)
          | Some (_, elapsed) -> Pass (elapsed, None)
          | exception Failure msg -> Fail (msg, 0.0, None)
          | exception e -> Fail (Printexc.to_string e, 0.0, None)
        in
        record_result stats encode_result;
        print_result core_file encode_result);

    print_stats stats;
    stats
  end

let () =
  parse_args ();
  print_suite_header "Core.eo Test Suite";
  let stats = test_core () in
  let code = if stats.failed > 0 || stats.timed_out > 0 then 1 else 0 in
  exit code
