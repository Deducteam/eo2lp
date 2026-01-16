(* Shared test infrastructure for eo2lp test suites *)

open Eo2lp.Parse_eo
open Eo2lp.Elaborate
open Eo2lp.Encode

(* ============================================================
   Configuration
   ============================================================ *)

let test_timeout = ref 0.1
let verbose = ref false

let parse_args () =
  let usage = "Usage: " ^ Sys.argv.(0) ^ " [options]" in
  let speclist = [
    ("-t", Arg.Set_float test_timeout, "  Timeout in seconds per test (default: 0.1)");
    ("--timeout", Arg.Set_float test_timeout, "  Timeout in seconds per test (default: 0.1)");
    ("-v", Arg.Set verbose, "  Verbose mode");
  ] in
  Arg.parse speclist (fun _ -> ()) usage

(* ============================================================
   Test infrastructure
   ============================================================ *)

type symbol_result = {
  name : string;
  time : float;
  status : [ `Pass | `Fail of string ];
}

type test_result =
  | Pass of float * symbol_result list option (* time in seconds *)
  | Fail of string * float * symbol_result list option
  | Timeout of float * symbol_result list option

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

(* ANSI color codes *)
let green s = Printf.sprintf "\027[32m%s\027[0m" s
let red s = Printf.sprintf "\027[31m%s\027[0m" s
let yellow s = Printf.sprintf "\027[33m%s\027[0m" s
let bold s = Printf.sprintf "\027[1m%s\027[0m" s
let dim s = Printf.sprintf "\027[2m%s\027[0m" s

(* Run a function with a timeout, returns None if timed out *)
let with_timeout ?(timeout_sec = !test_timeout) f =
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
  match with_timeout (fun () ->
    let _ = parse_eo_file "." fp in
    if !(Eo2lp.Parse_ctx.had_parse_error) then
      failwith "Parser error flag was set"
  ) with
  | None -> Timeout (!test_timeout, None)
  | Some ((), elapsed) -> Pass (elapsed, None)
  | exception Failure msg -> Fail (msg, 0.0, None)
  | exception e -> Fail (Printexc.to_string e, 0.0, None)

(* ============================================================
   Test: Elaboration
   ============================================================ *)

let test_elaborate_file ~base_sig ~verbose fp =
  clear_parse_cache ();
  Eo2lp.Parse_ctx.had_parse_error := false;
  let symbol_results = ref [] in
  let hook s f =
    let start_time = Unix.gettimeofday () in
    try
      let result = f () in
      let elapsed = Unix.gettimeofday () -. start_time in
      symbol_results := { name = s; time = elapsed; status = `Pass } :: !symbol_results;
      result
    with e ->
      let elapsed = Unix.gettimeofday () -. start_time in
      let msg = Printexc.to_string e in
      symbol_results := { name = s; time = elapsed; status = `Fail msg } :: !symbol_results;
      raise e
  in
  if verbose then
    Eo2lp.Elaborate.elab_hook := hook
  else
    Eo2lp.Elaborate.elab_hook := (fun _ f -> f ());

  let reset_hook () = Eo2lp.Elaborate.elab_hook := (fun _ f -> f ()) in

  match with_timeout (fun () ->
    let sig_ = parse_eo_file "." fp in
    if !(Eo2lp.Parse_ctx.had_parse_error) then
      failwith "Parser error flag was set"
    else begin
      let full_sig = base_sig @ sig_ in
      let _ = elab_sig full_sig in
      ()
    end
  ) with
  | None ->
      reset_hook ();
      Timeout (!test_timeout, Some (List.rev !symbol_results))
  | Some ((), elapsed) ->
      reset_hook ();
      let results = List.rev !symbol_results in
      (* If any symbol failed, the whole test fails *)
      begin match List.find_opt (fun r -> match r.status with | `Fail _ -> true | _ -> false) results with
      | Some r ->
        let msg = match r.status with | `Fail s -> s | _ -> "" in
        Fail (Printf.sprintf "Symbol '%s' failed: %s" r.name msg, elapsed, Some results)
      | None ->
        Pass (elapsed, Some results)
      end
  | exception Failure msg ->
      reset_hook ();
      Fail (msg, 0.0, Some (List.rev !symbol_results))
  | exception e ->
      reset_hook ();
      Fail (Printexc.to_string e, 0.0, Some (List.rev !symbol_results))

(* ============================================================
   Test: Encoding
   ============================================================ *)

let processed_files = ref (Hashtbl.create 10)

let test_encode_file ~base_sig ~verbose fp =
  clear_parse_cache ();
  if Hashtbl.mem !processed_files fp then
    Pass (0.0, None)
  else begin
    Eo2lp.Parse_ctx.had_parse_error := false;
    let symbol_results = ref [] in
    let hook s f =
      let start_time = Unix.gettimeofday () in
      try
        let result = f () in
        let elapsed = Unix.gettimeofday () -. start_time in
        symbol_results := { name = s; time = elapsed; status = `Pass } :: !symbol_results;
        result
      with e ->
        let elapsed = Unix.gettimeofday () -. start_time in
        let msg = Printexc.to_string e in
        symbol_results := { name = s; time = elapsed; status = `Fail msg } :: !symbol_results;
        raise e
    in
    if verbose then
      Eo2lp.Encode.encode_hook := hook
    else
      Eo2lp.Encode.encode_hook := (fun _ f -> f ());

    let reset_hook () = Eo2lp.Encode.encode_hook := (fun _ f -> f ()) in

    match with_timeout (fun () ->
      let sig_ = parse_eo_file "." fp in
      if !(Eo2lp.Parse_ctx.had_parse_error) then
        failwith "Parser error flag was set"
      else begin
        let full_sig = base_sig @ sig_ in
        let elab_sig_ = elab_sig full_sig in
        let lp_sig = eo_sig elab_sig_ in
        let out_fp =
          if String.starts_with ~prefix:"./" fp then
            Filename.concat "lp" (String.sub fp 2 (String.length fp - 2) ^ ".lp")
          else
            Filename.concat "lp" (fp ^ ".lp")
        in
        Eo2lp.Api_lp.write_lp_file out_fp lp_sig;
        Hashtbl.add !processed_files fp ();
        ()
      end
    ) with
    | None ->
        reset_hook ();
        Timeout (!test_timeout, Some (List.rev !symbol_results))
    | Some ((), elapsed) ->
        reset_hook ();
        let results = List.rev !symbol_results in
        (* If any symbol failed, the whole test fails *)
        begin match List.find_opt (fun r -> match r.status with | `Fail _ -> true | _ -> false) results with
        | Some r ->
          let msg = match r.status with | `Fail s -> s | _ -> "" in
          Fail (Printf.sprintf "Symbol '%s' failed: %s" r.name msg, elapsed, Some results)
        | None ->
          Pass (elapsed, Some results)
        end
    | exception Failure msg ->
        reset_hook ();
        Fail (msg, 0.0, Some (List.rev !symbol_results))
    | exception e ->
        reset_hook ();
        Fail (Printexc.to_string e, 0.0, Some (List.rev !symbol_results))
    end

(* ============================================================
   Result printing
   ============================================================ *)

let print_result fp ?(verbose=false) =
  let print_symbols symbols =
    if verbose then
      List.iter (fun r ->
        let status_icon = match r.status with
          | `Pass -> green "✓"
          | `Fail _ -> red "✗" in
        let time_str = dim (Printf.sprintf "(%.3fs)" r.time) in
        println (Printf.sprintf "    %s %s %s" status_icon r.name time_str);
        match r.status with
        | `Fail msg -> println (Printf.sprintf "      └─ %s" (red msg))
        | _ -> ()
      ) symbols
    else ()
  in
  function
  | Pass (0.0, None) -> () (* Cached *)
  | Pass (elapsed, Some symbols) ->
      println (Printf.sprintf "  %s %s %s" (green "✓") fp (dim (Printf.sprintf "(%.3fs)" elapsed)));
      print_symbols symbols
  | Pass (elapsed, None) ->
      println (Printf.sprintf "  %s %s %s" (green "✓") fp (dim (Printf.sprintf "(%.3fs)" elapsed)))
  | Fail (msg, _, Some symbols) ->
      println (Printf.sprintf "  %s %s" (red "✗") fp);
      println (Printf.sprintf "    └─ %s" (red msg));
      print_symbols symbols
  | Fail (msg, _, None) ->
      println (Printf.sprintf "  %s %s" (red "✗") fp);
      println (Printf.sprintf "    └─ %s" (red msg))
  | Timeout (elapsed, Some symbols) ->
      println (Printf.sprintf "  %s %s %s" (yellow "⏱") fp (dim (Printf.sprintf "(>%.1fs)" elapsed)));
      print_symbols symbols
  | Timeout (elapsed, None) ->
      println (Printf.sprintf "  %s %s %s" (yellow "⏱") fp (dim (Printf.sprintf "(>%.1fs)" elapsed)))

(* ============================================================
   Test runners
   ============================================================ *)

let run_parse_tests stats files =
  println "\n  ┌─ Parsing";
  List.iter (fun fp ->
    let result = test_parse_file fp in
    record_result stats result;
    print_result fp result
  ) files

let run_elaborate_tests stats ~base_sig ~verbose files =
  println "\n  ┌─ Elaboration";
  List.iter (fun fp ->
    let result = test_elaborate_file ~base_sig ~verbose fp in
    record_result stats result;
    print_result fp ~verbose result
  ) files

let run_encode_tests stats ~base_sig ~verbose files =
  println "\n  ┌─ Encoding";
  List.iter (fun fp ->
    let result = test_encode_file ~base_sig ~verbose fp in
    record_result stats result;
    print_result fp ~verbose result
  ) files

(* ============================================================
   Utility functions
   ============================================================ *)

let print_section_header name =
  println "";
  println (Printf.sprintf "╭─ %s" (bold name));
  println "│"

let print_stats stats =
  println "";
  println (Printf.sprintf "  %s %d  │  %s %d  │  %s %d  │  %s %d"
    (bold "Total") stats.total
    (green "✓") stats.passed
    (red "✗") stats.failed
    (yellow "⏱") stats.timed_out)

let print_suite_header name =
  println "";
  println "╔══════════════════════════════════════╗";
  println (Printf.sprintf "║  %s" (bold name));
  println (Printf.sprintf "║  %s" (dim (Printf.sprintf "timeout: %.1fs per test" !test_timeout)));
  println "╚══════════════════════════════════════╝"

(* Load Core.eo and return its parsed signature *)
let load_core_sig () =
  let core_file = "eo/Core.eo" in
  if not (Sys.file_exists core_file) then begin
    println (Printf.sprintf "  %s Core.eo not found, using empty base signature" (yellow "⚠"));
    []
  end else begin
    clear_parse_cache ();
    try parse_eo_file "." core_file
    with e ->
      println (Printf.sprintf "  %s Failed to load Core.eo: %s" (yellow "⚠") (Printexc.to_string e));
      []
  end
