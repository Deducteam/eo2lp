(* main.ml
   eo2lp driver: translate Eunoia signatures to LambdaPi

   Pipeline stages:
   1. Parse all .eo files into a signature graph
   2. Initialize LambdaPi (prelude, package config)
   3. Encode all modules (encode → write .lp)
   4. Check all generated .lp files with LambdaPi
   5. Report results *)

open Syntax_eo

module Enc  = Encode
module LP   = Api_lp

(* ---------------------------------------------------------------------------
   CLI config
   --------------------------------------------------------------------------- *)

type config = {
  input_dir      : string;
  output_dir     : string;
  proofs_dir     : string option;
  proofs_only    : bool;
  verbose        : bool;
  log_level      : LP.log_level;
  no_color       : bool;
  include_expert : bool;
}

let default_config = {
  input_dir      = "./cpc";
  output_dir     = "./_build/cpc";
  proofs_dir     = None;
  proofs_only    = false;
  verbose        = false;
  log_level      = LP.Silent;
  no_color       = false;
  include_expert = false;
}

let config = ref default_config

let usage = "Usage: eo2lp [options]"

let speclist = [
  ("-d", Arg.String (fun s -> config := { !config with input_dir = s }),
   "<dir> Input directory with .eo files (default: ./cpc)");
  ("-o", Arg.String (fun s -> config := { !config with output_dir = s }),
   "<dir> Output directory for LambdaPi package (default: ./_build/cpc)");
  ("-v", Arg.String (fun s ->
     let level = LP.log_level_of_string s in
     config := { !config with verbose = true; log_level = level }),
   "<level> Verbose output with log level: info, warn, error");
  ("--proofs", Arg.String (fun s -> config := { !config with proofs_dir = Some s }),
   "<dir> Directory of .eo proof files to encode");
  ("--no-color", Arg.Unit (fun () -> config := { !config with no_color = true }),
   " Disable colored output");
  ("--expert", Arg.Unit (fun () -> config := { !config with include_expert = true }),
   " Include files from expert/ directory");
  ("--proofs-only", Arg.Unit (fun () -> config := { !config with proofs_only = true }),
   " Skip CPC encode/check, only process proofs (requires pre-built CPC in output dir)");
]

(* ---------------------------------------------------------------------------
   Terminal colors
   --------------------------------------------------------------------------- *)

let color code s =
  if !config.no_color then s
  else Printf.sprintf "\027[%sm%s\027[0m" code s

let red s    = color "31" s
let green s  = color "32" s
let yellow s = color "33" s
let dim s    = color "2" s

(* ---------------------------------------------------------------------------
   Helpers
   --------------------------------------------------------------------------- *)

let path_to_module pkg path = pkg ^ "." ^ String.concat "." path

let exn_msg = function
  | Failure msg -> msg
  | exn -> Printexc.to_string exn

exception Timeout

let with_timeout secs f =
  let old_handler = Sys.signal Sys.sigalrm
    (Sys.Signal_handle (fun _ -> raise Timeout)) in
  let old_alarm = Unix.alarm secs in
  Fun.protect ~finally:(fun () ->
    ignore (Unix.alarm 0);
    Sys.set_signal Sys.sigalrm old_handler;
    if old_alarm > 0 then ignore (Unix.alarm old_alarm))
    f

let fmt_ms dt =
  let ms = dt *. 1000. in
  if ms < 1.0 then dim "<1ms"
  else if ms < 10.0 then Printf.sprintf "%.1fms" ms
  else Printf.sprintf "%.0fms" ms

(* ---------------------------------------------------------------------------
   LambdaPi initialization
   --------------------------------------------------------------------------- *)

let clean_output_dir output_dir =
  if Sys.file_exists output_dir then begin
    (* Remove generated files (.lp, .lpo, .pkg) but preserve _test.lp files *)
    let cmd = Printf.sprintf
      "find %s \\( -name '*.lpo' -o -name '*.lp' -o -name 'lambdapi.pkg' \\) \
       ! -name '*_test.lp' -delete"
      (Filename.quote output_dir) in
    ignore (Sys.command cmd)
  end

let init_lambdapi ?(clean=true) ~output_dir ~pkg_name () =
  if clean then clean_output_dir output_dir;
  LP.mkdir_p output_dir;
  LP.generate_pkg_file output_dir pkg_name;
  LP.generate_prelude output_dir;
  let cwd = Sys.getcwd () in
  Sys.chdir output_dir;
  LP.init_library ();
  LP.apply_package_config ".";
  let prelude_path = [pkg_name; "Prelude"] in
  let sign = LP.compile ~force:true prelude_path in
  Sys.chdir cwd;
  sign

(* Load all pre-built CPC .lp files into lambdapi's memory so that
   proof encoding can reference CPC symbols without re-encoding. *)
let load_cpc_modules ~output_dir ~pkg_name (order : path list) =
  let cwd = Sys.getcwd () in
  Sys.chdir output_dir;
  List.iter (fun mod_path ->
    let lp_path = pkg_name :: mod_path in
    ignore (LP.compile ~force:true lp_path)
  ) order;
  Sys.chdir cwd

(* ---------------------------------------------------------------------------
   Result types
   --------------------------------------------------------------------------- *)

type encode_result = {
  enc_errors   : (string * string) list;  (* (symbol_name, error_msg) *)
  enc_warnings : string list;             (* free-form warning messages *)
  enc_time     : float;
}

type check_outcome =
  | Check_ok
  | Check_error of string
  | Check_skipped of string

type module_result = {
  mod_path     : path;
  mod_name     : string;
  encode       : encode_result;
  check        : check_outcome;
  check_time   : float;
  total_time   : float;
}

(* ---------------------------------------------------------------------------
   Stage 3a: Encode a single module (elab → encode → write .lp)
   --------------------------------------------------------------------------- *)

let encode_module ~pkg_name ~output_dir ~verbose
    (graph : sig_graph) (mod_path : path) =
  let node = PathMap.find mod_path graph in
  let deps = node.node_includes in
  let module_name = path_to_module pkg_name mod_path in

  LP.set_current_module module_name;

  (* Set up encoding context *)
  let full_sig = full_sig_at graph mod_path in
  Enc.set_signature full_sig;

  (* Init encoding state *)
  let module_path = pkg_name :: mod_path in
  let dep_paths = List.map (fun dep -> pkg_name :: dep) deps in
  let _sign = LP.init_sign ~deps:dep_paths module_path in
  Enc.reset_overloads ();

  (* Process every symbol: encode directly from raw Eunoia AST.
     Errors are collected, not fatal — we always write the .lp file. *)
  let errors = ref [] in
  let output_items = ref [] in

  if verbose then
    Printf.printf "\n%s\n  %s\n%s\n%!"
      (dim (String.make 72 '='))
      (String.concat "/" mod_path)
      (dim (String.make 72 '='));

  List.iter (fun (name, def) ->
    try
      if verbose then LP.clear_resolve_traces ();
      let result = Enc.enc_one name def in
      let item =
        { LP.oi_syms  = result.Enc.syms;
          oi_rules = result.Enc.rules; }
      in
      output_items := item :: !output_items;
      if verbose then begin
        let traces = LP.get_resolve_traces () in
        let lp_src = LP.render_item item in
        if lp_src <> "" then begin
          Printf.printf "\n  %s\n" (dim (Pp_eo.symbol_str (name, def)));
          Printf.printf "  %s\n" (dim (String.make 40 '-'));
          if traces <> [] then begin
            List.iter (fun (pre, post) ->
              Printf.printf "  %s %s\n" (yellow "[resolve]") (LP.strip_lp_escapes pre);
              Printf.printf "  %s %s\n" (yellow "       ⇝") (LP.strip_lp_escapes post)
            ) traces;
            Printf.printf "  %s\n" (dim (String.make 40 '-'))
          end;
          String.split_on_char '\n' lp_src
          |> List.iter (fun line -> Printf.printf "  %s\n" line);
          flush stdout
        end
      end
    with e ->
      let msg = exn_msg e in
      errors := (name, msg) :: !errors
  ) node.node_sig;

  let errors = List.rev !errors in

  (* Always write the .lp file with whatever succeeded *)
  let out_path =
    Filename.concat output_dir (String.concat "/" mod_path ^ ".lp")
  in
  LP.mkdir_p (Filename.dirname out_path);
  let prelude_module = pkg_name ^ ".Prelude" in
  let dep_modules = List.map (path_to_module pkg_name) deps in
  LP.write_lp_file out_path ~prelude_module ~deps:dep_modules
    (List.rev !output_items);

  if verbose && errors <> [] then
    List.iter (fun (sym, msg) ->
      Printf.eprintf "  [%s:%s] %s\n%!" module_name sym msg
    ) errors;

  LP.set_current_module "";
  errors

(* ---------------------------------------------------------------------------
   Stage 3b: Check a single module with LambdaPi
   --------------------------------------------------------------------------- *)

let check_module ~output_dir ~verbose:_ (mod_path : path) =
  let rel_path = String.concat "/" mod_path ^ ".lp" in
  LP.check_file ~verbose:false output_dir rel_path

(* ---------------------------------------------------------------------------
   Stage 5: Encode a single proof file against the full CPC signature
   --------------------------------------------------------------------------- *)

let encode_proof ~pkg_name ~output_dir ~verbose
    ~(cpc_sig : Syntax_eo.signature) ~(top_module : path)
    (name : string) (proof_sig : Syntax_eo.signature) =
  let proof_path = ["proofs"; name] in
  let module_name = path_to_module pkg_name proof_path in

  LP.set_current_module module_name;

  (* The proof sees the full CPC signature plus its own local declarations *)
  Enc.set_signature (cpc_sig @ proof_sig);

  (* Init LP sign: proof depends on the top-level CPC module *)
  let module_path = pkg_name :: proof_path in
  let dep_path = pkg_name :: top_module in
  let _sign = LP.init_sign ~deps:[dep_path] module_path in
  Enc.reset_overloads ();
  Enc.reset_assumptions ();

  let errors = ref [] in
  let output_items = ref [] in

  List.iter (fun (sym_name, def) ->
    try
      let result = Enc.enc_one sym_name def in
      output_items :=
        { LP.oi_syms  = result.Enc.syms;
          oi_rules = result.Enc.rules; } :: !output_items
    with e ->
      let msg = exn_msg e in
      errors := (sym_name, msg) :: !errors
  ) proof_sig;

  let errors = List.rev !errors in

  let out_path =
    Filename.concat output_dir (String.concat "/" proof_path ^ ".lp")
  in
  LP.mkdir_p (Filename.dirname out_path);
  let prelude_module = pkg_name ^ ".Prelude" in
  let dep_module = path_to_module pkg_name top_module in
  LP.write_lp_file out_path ~prelude_module ~deps:[dep_module]
    (List.rev !output_items);

  (* Validate assumption stack balance *)
  let stack_depth = Enc.assumption_stack_depth () in
  let errors =
    if stack_depth > 0 then
      errors @ [("(stack)", Printf.sprintf
        "assumption stack not empty after proof encoding (%d unpopped)" stack_depth)]
    else errors
  in

  if verbose && errors <> [] then
    List.iter (fun (sym, msg) ->
      Printf.eprintf "  [%s:%s] %s\n%!" module_name sym msg
    ) errors;

  LP.set_current_module "";
  errors

(* ---------------------------------------------------------------------------
   Module tree display
   --------------------------------------------------------------------------- *)

let print_module_tree graph =
  let modules = PathMap.fold (fun p _ acc -> p :: acc) graph [] in
  let grouped = List.fold_left (fun acc path ->
    match path with
    | [] -> acc
    | group :: rest ->
      let name = String.concat "/" rest in
      let existing =
        Option.value ~default:[] (List.assoc_opt group acc)
      in
      (group, name :: existing) :: List.remove_assoc group acc
  ) [] modules in
  let grouped =
    List.map (fun (g, ns) -> (g, List.rev ns)) (List.rev grouped)
  in
  Printf.printf "[\n";
  List.iter (fun (group, names) ->
    match names with
    | [] -> Printf.printf "  %s\n" group
    | [""] -> Printf.printf "  %s\n" group
    | _ ->
      Printf.printf "  %s.(\n" group;
      let rec print_wrapped col = function
        | [] -> ()
        | name :: rest ->
          let sep = if col = 4 then "" else ", " in
          let new_col = col + String.length sep + String.length name in
          if new_col > 60 && col > 4 then begin
            Printf.printf ",\n    %s" name;
            print_wrapped (4 + String.length name) rest
          end else begin
            Printf.printf "%s%s" sep name;
            print_wrapped new_col rest
          end
      in
      Printf.printf "    ";
      print_wrapped 4 names;
      Printf.printf "\n  ),\n"
  ) grouped;
  Printf.printf "]\n"

(* ---------------------------------------------------------------------------
   Failure report: extract location, source line, and error body
   --------------------------------------------------------------------------- *)

let print_failure output_dir (name, phase, msg) =
  (* Convert module name cpc.programs.Foo to file path programs/Foo.lp *)
  let lp_path =
    match String.split_on_char '.' name with
    | _ :: rest ->
      Filename.concat output_dir (String.concat "/" rest ^ ".lp")
    | [] -> ""
  in
  let lines = String.split_on_char '\n' msg in
  let first_line = match lines with l :: _ -> l | [] -> msg in
  let body_lines = match lines with _ :: rest -> rest | [] -> [] in
  (* Try to extract a [line:col-col] location bracket *)
  let loc_source =
    try
      let _ = Str.search_forward
        (Str.regexp "\\(\\[[0-9][^]]*\\]\\)") first_line 0 in
      let loc = Str.matched_group 1 first_line in
      let line_num =
        let _ = Str.search_forward
          (Str.regexp "\\[\\([0-9]+\\):[0-9]") loc 0 in
        int_of_string (Str.matched_group 1 loc)
      in
      let source =
        try
          let ic = open_in lp_path in
          Fun.protect ~finally:(fun () -> close_in ic) (fun () ->
            for _ = 1 to line_num - 1 do ignore (input_line ic) done;
            let line = String.trim (input_line ic) in
            let max_len = 72 in
            if String.length line > max_len
            then String.sub line 0 max_len ^ "..."
            else line)
        with _ -> ""
      in
      Some (loc, source)
    with Not_found -> None
  in
  Printf.printf "  %s: %s\n" (red name) (dim (Printf.sprintf "[%s]" phase));
  (match loc_source with
   | Some (loc, source) ->
     if source <> "" then
       Printf.printf "    %s %s\n" loc (dim source)
     else
       Printf.printf "    %s\n" loc
   | None ->
     Printf.printf "    %s\n" first_line);
  List.iter (fun l ->
    Printf.printf "      %s\n" l
  ) body_lines

(* ---------------------------------------------------------------------------
   Main entry point
   --------------------------------------------------------------------------- *)

let run () =
  Arg.parse speclist (fun _ -> ()) usage;

  let input_dir  = !config.input_dir in
  let output_dir = !config.output_dir in
  let pkg_name   = Filename.basename output_dir in
  let verbose    = !config.verbose in

  (* -- Stage 1: Parse ---------------------------------------------------- *)

  let t0 = Unix.gettimeofday () in
  Printf.printf "parsing %s... " input_dir;
  flush stdout;
  let graph =
    Parse_eo.build_sig ~include_expert:!config.include_expert input_dir
  in
  (match Parse_eo.check_dag graph with
   | Ok () -> ()
   | Error cycle ->
     Printf.printf "%s\n" (red "FAIL");
     Printf.printf "  Cycle in include graph: %s\n"
       (String.concat " -> " (List.map path_str cycle));
     exit 1);
  Printf.printf "%s (%s)\n" (green "ok") (fmt_ms (Unix.gettimeofday () -. t0));

  print_module_tree graph;

  (* -- Stage 2: Initialize LambdaPi -------------------------------------- *)

  let t1 = Unix.gettimeofday () in
  Printf.printf "initializing lambdapi... ";
  flush stdout;
  let proofs_only = !config.proofs_only in
  let prelude_sign =
    init_lambdapi ~clean:(not proofs_only) ~output_dir ~pkg_name () in
  LP.init prelude_sign;
  LP.set_log_level !config.log_level;
  LP.set_verbose verbose;
  Printf.printf "%s (%s)\n"
    (green "ok") (fmt_ms (Unix.gettimeofday () -. t1));

  (* Topological order for processing *)
  let order = topo_sort_graph graph in
  let total = List.length order in

  (* -- Stages 3-4: Encode and check CPC modules (skipped with --proofs-only) *)

  let results : module_result list =
    if proofs_only then begin
      (* Load pre-built CPC modules into lambdapi *)
      let t2 = Unix.gettimeofday () in
      Printf.printf "loading %d modules... " total;
      flush stdout;
      load_cpc_modules ~output_dir ~pkg_name order;
      Printf.printf "%s (%s)\n"
        (green "ok") (fmt_ms (Unix.gettimeofday () -. t2));
      []
    end else begin
      (* -- Stage 3: Encode all modules ----------------------------------- *)
      let t2 = Unix.gettimeofday () in
      Printf.printf "encoding %d modules... " total;
      flush stdout;

      let encode_results : (path * encode_result) list =
        List.map (fun mod_path ->
          let t_start = Unix.gettimeofday () in
          let errors =
            try encode_module ~pkg_name ~output_dir ~verbose graph mod_path
            with e ->
              let name = path_to_module pkg_name mod_path in
              [("(module)", Printf.sprintf "%s: %s" name (exn_msg e))]
          in
          let enc = {
            enc_errors   = errors;
            enc_warnings = [];
            enc_time     = Unix.gettimeofday () -. t_start;
          } in
          (mod_path, enc)
        ) order
      in

      let encode_errs =
        List.filter (fun (_, enc) -> enc.enc_errors <> []) encode_results
      in
      let t_encode = Unix.gettimeofday () -. t2 in
      if encode_errs = [] then
        Printf.printf "%s (%s)\n" (green "ok") (fmt_ms t_encode)
      else
        Printf.printf "%s %d/%d with errors (%s)\n"
          (red "WARN") (List.length encode_errs) total (fmt_ms t_encode);

      (* -- Stage 4: Check all modules with LambdaPi ---------------------- *)
      let t3 = Unix.gettimeofday () in
      Printf.printf "checking %d modules... " total;
      flush stdout;

      let results : module_result list =
        List.map (fun (mod_path, enc) ->
          let mod_name = path_to_module pkg_name mod_path in
          let t_start = Unix.gettimeofday () in
          let r = check_module ~output_dir ~verbose mod_path in
          let dt = Unix.gettimeofday () -. t_start in
          let check = match r with
            | LP.Check_ok    -> Check_ok
            | LP.Check_error msg -> Check_error msg
          in
          { mod_path; mod_name; encode = enc;
            check; check_time = dt;
            total_time = enc.enc_time +. dt }
        ) encode_results
      in

      let check_failures =
        List.filter (fun r ->
          match r.check with Check_error _ -> true | _ -> false) results
      in
      let t_check = Unix.gettimeofday () -. t3 in
      if check_failures = [] then
        Printf.printf "%s (%s)\n" (green "ok") (fmt_ms t_check)
      else
        Printf.printf "%s %d/%d failed (%s)\n"
          (red "FAIL") (List.length check_failures) total (fmt_ms t_check);

      results
    end
  in

  (* -- Stage 5: Encode and check proofs (if --proofs given) -------------- *)

  let proof_results : module_result list =
    match !config.proofs_dir with
    | None -> []
    | Some proofs_dir ->
      (* Find the top-level module (last in topo order) *)
      let top_module = List.nth order (List.length order - 1) in
      (* Build the full CPC signature for proof encoding *)
      let cpc_sig = full_sig_at graph top_module in

      (* Parse proof files *)
      let t4 = Unix.gettimeofday () in
      let is_tty_parse = Unix.isatty Unix.stdout in
      Printf.printf "parsing proofs in %s...%!" proofs_dir;
      let parse_progress i total name =
        if is_tty_parse then
          Printf.printf "\rparsing proofs in %s... [%d/%d] %s%s%!"
            proofs_dir i total name (String.make 20 ' ')
      in
      let proofs_raw =
        Parse_eo.parse_proof_dir ~progress:parse_progress proofs_dir in
      if is_tty_parse then Printf.printf "\r%s\r%!" (String.make 80 ' ');
      let n_parse_errors =
        List.length (List.filter (fun (_, _, e) -> e > 0) proofs_raw) in
      if n_parse_errors > 0 then
        Printf.printf "%s %d proofs, %s (%s)\n"
          (yellow "WARN") (List.length proofs_raw)
          (yellow (Printf.sprintf "%d with parse errors (skipped)" n_parse_errors))
          (fmt_ms (Unix.gettimeofday () -. t4))
      else
        Printf.printf "%s %d proofs (%s)\n"
          (green "ok") (List.length proofs_raw)
          (fmt_ms (Unix.gettimeofday () -. t4));
      (* Filter out proofs with parse errors *)
      let proofs = List.filter_map (fun (name, sig_, errs) ->
        if errs > 0 then begin
          Printf.printf "  %s: %s\n" name
            (yellow (Printf.sprintf "%d parse errors, skipping" errs));
          None
        end else
          Some (name, sig_)
      ) proofs_raw in
      let n_proofs = List.length proofs in

      if n_proofs = 0 then []
      else begin
        (* Encode proofs *)
        let t5 = Unix.gettimeofday () in
        Printf.printf "encoding %d proofs...\n" n_proofs;
        flush stdout;

        let n_enc_ok = ref 0 in
        let n_enc_err = ref 0 in
        let is_tty = Unix.isatty Unix.stdout in

        let proof_encode_results =
          List.mapi (fun i (name, proof_sig) ->
            let t_start = Unix.gettimeofday () in
            let errors =
              try
                with_timeout 5 (fun () ->
                  encode_proof ~pkg_name ~output_dir ~verbose
                    ~cpc_sig ~top_module name proof_sig)
              with
              | Timeout ->
                [("(timeout)", "encoding timed out (>5s)")]
              | e ->
                let mod_name = path_to_module pkg_name ["proofs"; name] in
                [("(module)", Printf.sprintf "%s: %s" mod_name (exn_msg e))]
            in
            let dt = Unix.gettimeofday () -. t_start in
            let enc = {
              enc_errors   = errors;
              enc_warnings = [];
              enc_time     = dt;
            } in
            if errors = [] then incr n_enc_ok
            else incr n_enc_err;
            if is_tty then
              Printf.printf "\r  encode [%d/%d] %d ok, %d err: %s%s%!"
                (i + 1) n_proofs !n_enc_ok !n_enc_err name
                (String.make 20 ' ')
            else if errors <> [] then
              Printf.printf "  encode [%d/%d] %s: %s\n%!"
                (i + 1) n_proofs name (snd (List.hd errors));
            (name, enc)
          ) proofs
        in

        if is_tty then Printf.printf "\r%s\r" (String.make 80 ' ');
        let t_penc = Unix.gettimeofday () -. t5 in
        if !n_enc_err = 0 then
          Printf.printf "  encode: %s %d proofs (%s)\n"
            (green "ok") n_proofs (fmt_ms t_penc)
        else
          Printf.printf "  encode: %s %d/%d with errors (%s)\n"
            (red "WARN") !n_enc_err n_proofs (fmt_ms t_penc);
        flush stdout;

        (* Check proofs *)
        let t6 = Unix.gettimeofday () in
        let n_chk_ok = ref 0 in
        let n_chk_fail = ref 0 in

        let proof_results =
          List.mapi (fun i (name, enc) ->
            let proof_path = ["proofs"; name] in
            let mod_name = path_to_module pkg_name proof_path in
            let t_start = Unix.gettimeofday () in
            let check =
              if enc.enc_errors <> [] then
                Check_skipped "encode errors"
              else
                (try
                  let r = with_timeout 10 (fun () ->
                    check_module ~output_dir ~verbose proof_path) in
                  (match r with
                   | LP.Check_ok -> Check_ok
                   | LP.Check_error msg -> Check_error msg)
                with Timeout ->
                  Check_error "check timed out (>10s)")
            in
            let dt = Unix.gettimeofday () -. t_start in
            (match check with
             | Check_ok -> incr n_chk_ok
             | Check_error _ | Check_skipped _ -> incr n_chk_fail);
            if is_tty then
              Printf.printf "\r  check  [%d/%d] %d ok, %d fail: %s%s%!"
                (i + 1) n_proofs !n_chk_ok !n_chk_fail name
                (String.make 20 ' ')
            else
              (match check with
               | Check_error msg ->
                 Printf.printf "  check  [%d/%d] %s: %s\n%!"
                   (i + 1) n_proofs name msg
               | _ -> ());
            { mod_path = proof_path; mod_name;
              encode = enc; check; check_time = dt;
              total_time = enc.enc_time +. dt }
          ) proof_encode_results
        in

        if is_tty then Printf.printf "\r%s\r" (String.make 80 ' ');
        let t_pchk = Unix.gettimeofday () -. t6 in
        if !n_chk_fail = 0 then
          Printf.printf "  check:  %s %d proofs (%s)\n"
            (green "ok") n_proofs (fmt_ms t_pchk)
        else
          Printf.printf "  check:  %s %d/%d failed (%s)\n"
            (red "FAIL") !n_chk_fail n_proofs (fmt_ms t_pchk);
        flush stdout;

        proof_results
      end
  in

  (* -- Stage 6: Report --------------------------------------------------- *)

  let all_results = results @ proof_results in
  let all_total = List.length all_results in

  (* Collect all failures: encode errors + check errors *)
  let failures = ref [] in

  List.iter (fun r ->
    (* Report encode errors *)
    if r.encode.enc_errors <> [] then begin
      let first_sym, first_msg = List.hd r.encode.enc_errors in
      let msg =
        if List.length r.encode.enc_errors = 1 then
          Printf.sprintf "%s: %s" first_sym first_msg
        else
          Printf.sprintf "%s: %s (+%d more)"
            first_sym first_msg
            (List.length r.encode.enc_errors - 1)
      in
      failures := (r.mod_name, "encode", msg) :: !failures
    end;
    (* Report check errors *)
    (match r.check with
     | Check_error msg ->
       failures := (r.mod_name, "check", msg) :: !failures
     | _ -> ())
  ) all_results;

  let failures = List.rev !failures in
  let n_passed =
    List.length (List.filter (fun r ->
      r.encode.enc_errors = [] &&
      (match r.check with Check_ok -> true | _ -> false)
    ) all_results)
  in
  let n_failed = all_total - n_passed in

  (* Summary line *)
  let status_str, status_color =
    if n_failed > 0 then ("FAIL", red) else ("OK", green)
  in
  Printf.printf "%s: %d passed" (status_color status_str) n_passed;
  if n_failed > 0 then Printf.printf ", %d failed" n_failed;
  Printf.printf "\n";

  (* Detailed failure output *)
  if failures <> [] then begin
    List.iter (print_failure output_dir) failures;
    let failed_names =
      List.filter_map (fun r ->
        if r.encode.enc_errors <> [] ||
           (match r.check with Check_error _ -> true | _ -> false)
        then Some (String.concat "/" r.mod_path)
        else None
      ) all_results
      |> List.sort_uniq String.compare
    in
    Printf.printf "Failed: %s\n" (String.concat ", " failed_names)
  end;

  (* Verbose: per-module detail *)
  if verbose then begin
    Printf.printf "\n%s\n" (dim "--- per-module detail ---");
    List.iter (fun r ->
      let status = match r.check with
        | Check_ok -> green "ok"
        | Check_error _ -> red "FAIL"
        | Check_skipped reason -> dim (Printf.sprintf "skip (%s)" reason)
      in
      Printf.printf "%s %s  enc %s  check %s\n"
        status r.mod_name (fmt_ms r.encode.enc_time) (fmt_ms r.check_time);
      if r.encode.enc_errors <> [] then
        List.iter (fun (sym, msg) ->
          Printf.printf "  ├─ %s %s\n" (red sym) msg
        ) r.encode.enc_errors
    ) all_results
  end;

  LP.reset ();
  if n_failed > 0 then exit 1;
  exit 0
