(* Shared test infrastructure for eo2lp test suites *)

open Eo2lp.Parse_eo
open Eo2lp.Elaborate
open Eo2lp.Encode

(* ============================================================
   Configuration
   ============================================================ *)

let test_timeout = 0.1

(* ============================================================
   Test infrastructure
   ============================================================ *)

type test_result =
  | Pass of float  (* time in seconds *)
  | Fail of string * float
  | Timeout of float

type test_stats = {
  mutable total: int;
  mutable passed: int;
  mutable failed: int;
  mutable timed_out: int;
}

let make_stats () = { total = 0; passed = 0; failed = 0; timed_out = 0 }

let record_result stats = function
  | Pass _ -> stats.total <- stats.total + 1; stats.passed <- stats.passed + 1
  | Fail _ -> stats.total <- stats.total + 1; stats.failed <- stats.failed + 1
  | Timeout _ -> stats.total <- stats.total + 1; stats.timed_out <- stats.timed_out + 1

(* Flush helper *)
let println s = print_string s; print_newline (); flush stdout

(* Run a function with a timeout, returns None if timed out *)
let with_timeout timeout_sec f =
  let start_time = Unix.gettimeofday () in
  let timed_out = ref false in
  let old_handler = Sys.signal Sys.sigalrm
    (Sys.Signal_handle (fun _ -> timed_out := true; raise Exit)) in
  let cleanup () =
    ignore (Unix.alarm 0);
    Sys.set_signal Sys.sigalrm old_handler
  in
  ignore (Unix.alarm (int_of_float (ceil timeout_sec)));
  try
    let result = f () in
    cleanup ();
    let elapsed = Unix.gettimeofday () -. start_time in
    Some (result, elapsed)
  with
  | Exit when !timed_out ->
      cleanup ();
      None
  | e ->
      cleanup ();
      raise e

(* ============================================================
   File collection utilities
   ============================================================ *)

let collect_eo_files dir =
  let rec loop acc = function
    | [] -> acc
    | f :: fs when Sys.file_exists f && Sys.is_directory f ->
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
    loop [] [dir] |> List.sort String.compare
  else
    []

(* ============================================================
   Test: Parsing
   ============================================================ *)

let test_parse_file fp =
  clear_parse_cache ();
  Eo2lp.Parse_ctx.had_parse_error := false;
  match with_timeout test_timeout (fun () ->
    let _ = parse_eo_file "." fp in
    if !(Eo2lp.Parse_ctx.had_parse_error) then
      failwith "Parser error flag was set"
  ) with
  | None -> Timeout test_timeout
  | Some ((), elapsed) -> Pass elapsed
  | exception Failure msg -> Fail (msg, 0.0)
  | exception e -> Fail (Printexc.to_string e, 0.0)

(* ============================================================
   Test: Elaboration
   ============================================================ *)

let test_elaborate_file ~base_sig fp =
  clear_parse_cache ();
  Eo2lp.Parse_ctx.had_parse_error := false;
  match with_timeout test_timeout (fun () ->
    let sig_ = parse_eo_file "." fp in
    if !(Eo2lp.Parse_ctx.had_parse_error) then
      failwith "Parser error flag was set"
    else begin
      let full_sig = base_sig @ sig_ in
      let _ = elab_sig full_sig in
      ()
    end
  ) with
  | None -> Timeout test_timeout
  | Some ((), elapsed) -> Pass elapsed
  | exception Failure msg -> Fail (msg, 0.0)
  | exception e -> Fail (Printexc.to_string e, 0.0)

(* ============================================================
   Test: Encoding
   ============================================================ *)

let test_encode_file ~base_sig fp =
  clear_parse_cache ();
  Eo2lp.Parse_ctx.had_parse_error := false;
  match with_timeout test_timeout (fun () ->
    let sig_ = parse_eo_file "." fp in
    if !(Eo2lp.Parse_ctx.had_parse_error) then
      failwith "Parser error flag was set"
    else begin
      let full_sig = base_sig @ sig_ in
      let elab_sig_ = elab_sig full_sig in
      let _ = eo_sig elab_sig_ in
      ()
    end
  ) with
  | None -> Timeout test_timeout
  | Some ((), elapsed) -> Pass elapsed
  | exception Failure msg -> Fail (msg, 0.0)
  | exception e -> Fail (Printexc.to_string e, 0.0)

(* ============================================================
   Result printing
   ============================================================ *)

let print_result fp = function
  | Pass elapsed ->
      println (Printf.sprintf "    [PASS] %s (%.3fs)" fp elapsed)
  | Fail (msg, _) ->
      println (Printf.sprintf "    [FAIL] %s" fp);
      println (Printf.sprintf "           %s" msg)
  | Timeout elapsed ->
      println (Printf.sprintf "    [TIME] %s (>%.1fs)" fp elapsed)

(* ============================================================
   Test runners
   ============================================================ *)

let run_parse_tests stats files =
  println "\n  --- Parsing ---";
  List.iter (fun fp ->
    let result = test_parse_file fp in
    record_result stats result;
    print_result fp result
  ) files

let run_elaborate_tests stats ~base_sig files =
  println "\n  --- Elaboration ---";
  List.iter (fun fp ->
    let result = test_elaborate_file ~base_sig fp in
    record_result stats result;
    print_result fp result
  ) files

let run_encode_tests stats ~base_sig files =
  println "\n  --- Encoding ---";
  List.iter (fun fp ->
    let result = test_encode_file ~base_sig fp in
    record_result stats result;
    print_result fp result
  ) files

(* ============================================================
   Utility functions
   ============================================================ *)

let print_section_header name =
  println "\n========================================";
  println (Printf.sprintf "  %s" name);
  println "========================================"

let print_stats stats =
  println (Printf.sprintf "\n  Total: %d | Passed: %d | Failed: %d | Timeout: %d"
    stats.total stats.passed stats.failed stats.timed_out)

let print_suite_header name =
  println "";
  println "========================================";
  println (Printf.sprintf "  %s" name);
  println (Printf.sprintf "  (timeout: %.1fs per test)" test_timeout);
  println "========================================"

(* Load Core.eo and return its parsed signature *)
let load_core_sig () =
  let core_file = "eo/Core.eo" in
  if not (Sys.file_exists core_file) then begin
    println "  [WARN] Core.eo not found, using empty base signature";
    []
  end else begin
    clear_parse_cache ();
    try parse_eo_file "." core_file
    with e ->
      println (Printf.sprintf "  [WARN] Failed to load Core.eo: %s" (Printexc.to_string e));
      []
  end
