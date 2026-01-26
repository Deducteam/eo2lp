(* main.ml
   eo2lp driver: translate Eunoia signatures to LambdaPi *)

module EO = struct
  include Parse_eo
  include Syntax_eo
end

module Elab = Elaborate
module Enc  = Encode
module LP   = Api_lp

(* CLI config *)

type config = {
  input_dir  : string option;
  output_dir : string option;
  verbose    : bool;
  debug      : bool;
  no_color   : bool;
  only       : string option;
  proof_mode : string option;  (* Legacy: Path to logic package for proof mode *)
  proofs_dir : string option;  (* Directory containing proof .eo files to process after logic *)
  survey_dir : string option;  (* Directory to survey for rules needed *)
  job_file   : string option;  (* Single job file to process *)
  jobs_dir   : string option;  (* Directory containing job files *)
}

let default_config = {
  input_dir  = None;
  output_dir = None;
  verbose    = false;
  debug      = false;
  no_color   = false;
  only       = None;
  proof_mode = None;
  proofs_dir = None;
  survey_dir = None;
  job_file   = None;
  jobs_dir   = None;
}

let config = ref default_config

let usage =
  "Usage: eo2lp -d <input> -o <output> [options]"

let speclist = [
  ("-d",
   Arg.String (fun s ->
     config := { !config with input_dir = Some s }),
   "<dir> Input directory with .eo files");
  ("-o",
   Arg.String (fun s ->
     config := { !config with output_dir = Some s }),
   "<dir> Output directory for LambdaPi package");
  ("-v",
   Arg.Unit (fun () ->
     config := { !config with verbose = true }),
   " Verbose output");
  ("-c",
   Arg.Unit (fun () ->
     config := { !config with no_color = true }),
   " Disable colored output");
  ("--color",
   Arg.Unit (fun () ->
     config := { !config with no_color = false }),
   " Enable colored output");
  ("--debug",
   Arg.Unit (fun () ->
     config := { !config with
       debug = true;
       no_color = true }),
   " Debug mode: cpc-mini -> cpc (no color)");
  ("--only",
   Arg.String (fun s ->
     config := { !config with only = Some s }),
   "<pat> Process only modules matching pattern");
  ("--proof",
   Arg.String (fun s ->
     config := { !config with proof_mode = Some s }),
   "<lp_path>,<eo_path> Proof mode: use logic LP package at <lp_path> and EO source at <eo_path>");
  ("--proofs",
   Arg.String (fun s ->
     config := { !config with proofs_dir = Some s }),
   "<dir> Process proof .eo files in <dir> after encoding the logic");
  ("--survey",
   Arg.String (fun s ->
     config := { !config with survey_dir = Some s }),
   "<dir> Survey proof files in <dir> to build minimal CPC (filter unused symbols)");
  ("--job",
   Arg.String (fun s ->
     config := { !config with job_file = Some s }),
   "<file> Process a single job file");
  ("--jobs",
   Arg.String (fun s ->
     config := { !config with jobs_dir = Some s }),
   "<dir> Process all job files in directory");
]

(* Helpers *)

let path_to_module pkg path =
  pkg ^ "." ^ String.concat "." path

(* Survey proof files to find which rules are needed *)
let survey_proofs_dir dir =
  let files = Sys.readdir dir in
  let eo_files =
    Array.to_list files
    |> List.filter (fun f -> Filename.check_suffix f ".eo")
  in
  (* Parse each proof file and collect rules *)
  let all_rules =
    List.fold_left (fun acc f ->
      let path = Filename.concat dir f in
      try
        (* Read file and strip outer parens if present (cvc5 wraps proofs) *)
        let content = In_channel.with_open_text path In_channel.input_all in
        let content = String.trim content in
        let content =
          if String.length content > 2 &&
             content.[0] = '(' &&
             content.[String.length content - 1] = ')' &&
             content.[1] <> 'd' (* not starting with (declare... *)
          then
            String.sub content 1 (String.length content - 2)
          else content
        in
        let proof_sig = EO.parse_eo_string content in
        let rules = EO.rules_in_signature proof_sig in
        EO.Set.union acc rules
      with e ->
        Printf.eprintf "Warning: Failed to parse %s: %s\n" path (Printexc.to_string e);
        acc
    ) EO.Set.empty eo_files
  in
  all_rules

(* LambdaPi initialization *)

let init_lambdapi ~output_dir ~pkg_name =
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

(* Initialize for proof mode: load an existing logic package's Main.lp *)
let init_lambdapi_proof ~logic_dir ~output_dir ~pkg_name =
  LP.mkdir_p output_dir;
  LP.generate_pkg_file output_dir pkg_name;
  (* Don't generate Prelude - we use the logic's *)
  let cwd = Sys.getcwd () in
  Sys.chdir logic_dir;
  LP.init_library ();
  LP.apply_package_config ".";
  (* Compile Main.lp which imports everything from the logic.
     Use force:true to recompile since .lpo files may be from different process *)
  let logic_pkg = Filename.basename logic_dir in
  let main_path = [logic_pkg; "Main"] in
  let sign = LP.compile ~force:true main_path in
  Sys.chdir cwd;
  sign

(* Module processing *)

type process_result =
  | Success of float * float * float * float
  | Skipped of string
  | Error   of string

let processed_modules : (EO.path, bool) Hashtbl.t =
  Hashtbl.create 32

let process_module ~pkg_name ~output_dir ~verbose ?logic_pkg ?(logic_eo_sig=[]) graph path =
  let node = EO.PathMap.find path graph in

  (* Check dependencies - skip in proof mode since we use the logic package *)
  let deps_ok =
    logic_pkg <> None ||
    List.for_all (fun dep ->
      match Hashtbl.find_opt processed_modules dep with
      | Some true -> true
      | _ -> not (EO.PathMap.mem dep graph))
    node.EO.node_includes
  in

  if not deps_ok then begin
    let failed_dep =
      List.find (fun dep ->
        match Hashtbl.find_opt processed_modules dep with
        | Some true -> false
        | _ -> EO.PathMap.mem dep graph)
      node.EO.node_includes
    in
    Skipped (Printf.sprintf "dep %s"
      (path_to_module pkg_name failed_dep))
  end
  else begin
    let phase = ref "init" in
    try
      let module_name = path_to_module pkg_name path in
      LP.set_current_module module_name;
      let t0 = Unix.gettimeofday () in

      phase := "deps";
      let full_sig = EO.full_sig_at graph path in
      (* In proof mode, prepend the logic's Eunoia signature *)
      let full_sig = logic_eo_sig @ full_sig in
      let t1 = Unix.gettimeofday () in

      phase := "elaborate";
      let elab_sig =
        Elab.elab_sig_with_ctx full_sig node.EO.node_sig
      in
      let t2 = Unix.gettimeofday () in

      phase := "encode";
      let module_path = pkg_name :: path in
      (* In proof mode, use the logic's Main as dependency *)
      let dep_paths = match logic_pkg with
        | Some lp -> [[lp; "Main"]]
        | None ->
          List.map (fun dep -> pkg_name :: dep)
            node.EO.node_includes
      in
      let sign = LP.init_sign ~deps:dep_paths module_path in
      let enc_result = Enc.enc_signature elab_sig in
      let t3 = Unix.gettimeofday () in

      (* Check for encoding errors *)
      if enc_result.Enc.errors <> [] then begin
        Hashtbl.replace processed_modules path false;
        let first_err = List.hd enc_result.Enc.errors in
        Error (snd first_err)
      end
      else begin
        phase := "write";
        let out_path =
          Filename.concat output_dir
            (String.concat "/" path ^ ".lp")
        in
        LP.mkdir_p (Filename.dirname out_path);
        (* In proof mode, import logic.Main; otherwise import own deps *)
        let (prelude_module, deps) = match logic_pkg with
          | Some lp -> (lp ^ ".Main", [lp ^ ".Main"])
          | None ->
            (pkg_name ^ ".Prelude",
             List.map (path_to_module pkg_name) node.EO.node_includes)
        in
        LP.write_lp_file out_path
          ~prelude_module ~deps sign enc_result.Enc.rules ~after_rules_map:enc_result.Enc.after_rules_map;

        phase := "check";
        let rel_path = String.concat "/" path ^ ".lp" in
        let check_result =
          LP.check_file ~verbose output_dir rel_path
        in
        let t4 = Unix.gettimeofday () in

        match check_result with
        | LP.Check_ok ->
          Hashtbl.replace processed_modules path true;
          Success (t1-.t0, t2-.t1, t3-.t2, t4-.t3)
        | LP.Check_error msg ->
          Hashtbl.replace processed_modules path false;
          Error (Printf.sprintf "[check] %s" msg)
      end

    with
    | Failure msg ->
      Hashtbl.replace processed_modules path false;
      Error (Printf.sprintf "[%s] %s" !phase msg)
    | exn ->
      Hashtbl.replace processed_modules path false;
      Error (Printf.sprintf "[%s] %s" !phase (Printexc.to_string exn))
  end

(* Error formatting *)

let red s =
  if !config.no_color then s
  else "\027[31m" ^ s ^ "\027[0m"

let yellow s =
  if !config.no_color then s
  else "\027[33m" ^ s ^ "\027[0m"

let green s =
  if !config.no_color then s
  else "\027[32m" ^ s ^ "\027[0m"

let cyan s =
  if !config.no_color then s
  else "\027[36m" ^ s ^ "\027[0m"

let dim s =
  if !config.no_color then s
  else "\027[2m" ^ s ^ "\027[0m"

let parse_lp_error msg =
  let re =
    Str.regexp {|\[\([^]]+\.lp\):\([0-9]+\):\([0-9]+\)[^]]*\]|}
  in
  try
    let _ = Str.search_forward re msg 0 in
    let file = Str.matched_group 1 msg in
    let line = int_of_string (Str.matched_group 2 msg) in
    let col  = int_of_string (Str.matched_group 3 msg) in
    let rest_start = Str.match_end () in
    let error_msg =
      String.sub msg rest_start
        (String.length msg - rest_start)
      |> String.trim
    in
    Some (file, line, col, error_msg)
  with Not_found -> None

let truncate max_len s =
  if String.length s <= max_len then s
  else String.sub s 0 (max_len - 3) ^ "..."

let relative_path path =
  let cwd = Sys.getcwd () ^ "/" in
  if String.length path > String.length cwd &&
     String.sub path 0 (String.length cwd) = cwd
  then
    String.sub path (String.length cwd)
      (String.length path - String.length cwd)
  else
    let build_prefix = "_build/default/" in
    try
      let idx =
        Str.search_forward
          (Str.regexp_string build_prefix) path 0
      in
      String.sub path (idx + String.length build_prefix)
        (String.length path - idx - String.length build_prefix)
    with Not_found -> path

let read_source_context file line context =
  try
    let ic = open_in file in
    let lines = ref [] in
    let n = ref 1 in
    (try
      while true do
        let l = input_line ic in
        if !n >= line - context && !n <= line + context
        then lines := (!n, l) :: !lines;
        incr n
      done
    with End_of_file -> ());
    close_in ic;
    List.rev_map (fun (n, l) ->
      let marker = if n = line then ">" else " " in
      let truncated = truncate 72 l in
      Printf.sprintf "  %s %3d | %s" marker n truncated)
    !lines
  with _ -> []

let format_failure name msg =
  let buf = Buffer.create 256 in
  Buffer.add_string buf
    (dim (Printf.sprintf "-- %s " name));
  Buffer.add_string buf
    (dim (String.make (max 0 (60 - String.length name)) '-'));
  Buffer.add_char buf '\n';

  (match parse_lp_error msg with
  | Some (file, line, _col, error_msg) ->
    Buffer.add_string buf
      (Printf.sprintf "   %s\n\n" (red error_msg));
    let context_lines = read_source_context file line 2 in
    if context_lines <> [] then
      List.iter (fun l ->
        Buffer.add_string buf (cyan l);
        Buffer.add_char buf '\n')
      context_lines

  | None ->
    let lines = String.split_on_char '\n' msg in
    let meaningful =
      List.filter (fun l ->
        let l = String.trim l in
        l <> ""
        && not (String.length l >= 5 &&
                String.sub l 0 5 = "Start")
        && not (String.length l >= 3 &&
                String.sub l 0 3 = "End"))
      lines
    in
    match meaningful with
    | first :: _ ->
      Buffer.add_string buf
        (Printf.sprintf "   %s\n"
          (red (String.trim first)))
    | [] ->
      Buffer.add_string buf "   (unknown error)\n");

  Buffer.contents buf

(* Process a single proof file using existing logic signatures *)
let process_proof ~pkg_name ~output_dir ~logic_eo_sig ~verbose proof_file =
  let proof_name = Filename.chop_extension (Filename.basename proof_file) in
  let module_name = pkg_name ^ ".proofs." ^ proof_name in

  let phase = ref "init" in
  try
    LP.set_current_module module_name;
    let t0 = Unix.gettimeofday () in

    (* Parse the proof file *)
    phase := "parse";
    let proof_sig = EO.parse_file proof_file in
    let t1 = Unix.gettimeofday () in

    (* Elaborate with full logic signature context *)
    phase := "elaborate";
    let elab_sig = Elab.elab_sig_with_ctx logic_eo_sig proof_sig in
    let t2 = Unix.gettimeofday () in

    (* Create LambdaPi signature that depends on cpc.Main *)
    phase := "encode";
    let module_path = [pkg_name; "proofs"; proof_name] in
    let dep_paths = [[pkg_name; "Main"]] in
    let _sign = LP.init_sign ~deps:dep_paths module_path in
    let enc_result = Enc.enc_signature elab_sig in
    let t3 = Unix.gettimeofday () in

    (* Check for encoding errors *)
    if enc_result.Enc.errors <> [] then begin
      let first_err = List.hd enc_result.Enc.errors in
      Error (snd first_err)
    end
    else begin
      (* Write output file *)
      phase := "write";
      let out_path = Filename.concat output_dir ("proofs/" ^ proof_name ^ ".lp") in
      LP.mkdir_p (Filename.dirname out_path);
      let prelude_module = pkg_name ^ ".Main" in
      let deps = [pkg_name ^ ".Main"] in
      LP.write_lp_file out_path ~prelude_module ~deps _sign enc_result.Enc.rules ~after_rules_map:enc_result.Enc.after_rules_map;

      (* Check the output *)
      phase := "check";
      let rel_path = "proofs/" ^ proof_name ^ ".lp" in
      let check_result = LP.check_file ~verbose output_dir rel_path in
      let t4 = Unix.gettimeofday () in

      match check_result with
      | LP.Check_ok -> Success (t1-.t0, t2-.t1, t3-.t2, t4-.t3)
      | LP.Check_error msg -> Error (Printf.sprintf "[check] %s" msg)
    end
  with
  | Failure msg -> Error (Printf.sprintf "[%s] %s" !phase msg)
  | exn -> Error (Printf.sprintf "[%s] %s" !phase (Printexc.to_string exn))

(* Process all proof files in a directory *)
let process_proofs ~pkg_name ~output_dir ~logic_eo_sig ~verbose proofs_dir =
  (* Find all .eo files in the proofs directory *)
  let files = Sys.readdir proofs_dir in
  let eo_files =
    Array.to_list files
    |> List.filter (fun f -> Filename.check_suffix f ".eo")
    |> List.sort compare
  in

  if eo_files = [] then begin
    (0, 0, [])
  end
  else begin
    let passed = ref 0 in
    let failed = ref 0 in
    let failures = ref [] in

    List.iter (fun eo_file ->
      let proof_path = Filename.concat proofs_dir eo_file in
      let proof_name = Filename.chop_extension eo_file in
      let module_name = pkg_name ^ ".proofs." ^ proof_name in

      let result = process_proof ~pkg_name ~output_dir ~logic_eo_sig ~verbose proof_path in
      match result with
      | Success (t_parse, t_elab, t_enc, t_check) ->
        incr passed;
        if verbose then
          Printf.printf "\n  %s %s (%.0f+%.0f+%.0f+%.0fms)"
            (green "ok") proof_name
            (t_parse *. 1000.) (t_elab *. 1000.)
            (t_enc *. 1000.) (t_check *. 1000.)
      | Skipped _ ->
        () (* Proofs don't get skipped *)
      | Error msg ->
        incr failed;
        failures := (module_name, msg) :: !failures)
    eo_files;

    (!passed, !failed, List.rev !failures)
  end

(* Main entry point *)

(* Process a single job *)
let process_job (job : EO.job) (base_output_dir : string) =
  let output_dir = Filename.concat base_output_dir job.job_name in
  let pkg_name = job.job_name in

  Printf.printf "\n=== Job: %s ===\n" job.job_name;
  Printf.printf "  Logic: %s\n" job.job_logic;
  Printf.printf "  Output: %s\n" output_dir;

  (* Stage 1: Parse logic *)
  let t_parse_start = Unix.gettimeofday () in
  Printf.printf "parsing %s... " job.job_logic;
  flush stdout;
  let graph = EO.build_sig_graph job.job_logic None in
  let t_parse = Unix.gettimeofday () -. t_parse_start in
  Printf.printf "%s (%.0fms)\n" (green "ok") (t_parse *. 1000.);

  (* Stage 2: Get proof files and survey for needed rules *)
  let proof_files = match job.job_proofs with
    | EO.ProofDir dir ->
      Sys.readdir dir
      |> Array.to_list
      |> List.filter (fun f -> Filename.check_suffix f ".eo")
      |> List.map (Filename.concat dir)
    | EO.ProofFiles files -> files
  in

  Printf.printf "found %d proof files\n" (List.length proof_files);

  (* Survey proofs for needed rules *)
  let t_survey_start = Unix.gettimeofday () in
  Printf.printf "surveying proofs... ";
  flush stdout;
  let needed_rules =
    List.fold_left (fun acc f ->
      try
        let content = In_channel.with_open_text f In_channel.input_all in
        let proof_sig = EO.parse_eo_string content in
        let rules = EO.rules_in_signature proof_sig in
        EO.Set.union acc rules
      with _ -> acc
    ) EO.Set.empty proof_files
  in

  (* Compute minimal graph *)
  let full_sig = EO.full_sig graph in
  let fundamental = [
    "Type"; "Bool"; "Int"; "true"; "false"; "not"; "and"; "or"; "=>";
    "="; "ite"; "Proof"; "->"; "@List"; "eo::List"; "eo::List::cons"; "eo::List::nil"
  ] in
  let seeds = EO.Set.of_list (EO.Set.elements needed_rules @ fundamental) in
  let dep_map = EO.build_dependency_map full_sig in
  let closure = EO.transitive_closure dep_map seeds in
  let t_survey = Unix.gettimeofday () -. t_survey_start in
  Printf.printf "%s %d rules -> %d symbols (%.0fms)\n"
    (green "ok") (EO.Set.cardinal needed_rules) (EO.Set.cardinal closure) (t_survey *. 1000.);

  (* Filter graph *)
  let graph = EO.PathMap.map (fun node ->
    let filtered_sig = EO.filter_signature node.EO.node_sig closure in
    { node with EO.node_sig = filtered_sig }
  ) graph in

  (* Check for cycles *)
  (match EO.check_dag graph with
   | Error cycle ->
     Printf.printf "Error: Cycle detected in %s\n" job.job_name;
     List.iter (fun p -> Printf.printf "  -> %s\n" (EO.path_str p)) cycle;
     (0, 1)
   | Ok () ->
     (* Initialize lambdapi *)
     let t_init_start = Unix.gettimeofday () in
     Printf.printf "initializing lambdapi... ";
     flush stdout;
     let prelude_sign = init_lambdapi ~output_dir ~pkg_name in
     LP.init prelude_sign;
     LP.set_verbose false;
     let t_init = Unix.gettimeofday () -. t_init_start in
     Printf.printf "%s (%.0fms)\n" (green "ok") (t_init *. 1000.);

     (* Process modules *)
     Hashtbl.clear processed_modules;
     let order = EO.topo_sort graph in
     let total = List.length order in

     let t_encode_start = Unix.gettimeofday () in
     Printf.printf "encoding %d modules... " total;
     flush stdout;

     let passed = ref 0 in
     let failed = ref 0 in

     List.iter (fun path ->
       let result = process_module ~pkg_name ~output_dir ~verbose:!config.verbose graph path in
       match result with
       | Success _ -> incr passed
       | Skipped _ -> ()
       | Error _ -> incr failed
     ) order;

     let t_encode = Unix.gettimeofday () -. t_encode_start in
     if !failed > 0 then
       Printf.printf "%s %d/%d (%.0fms)\n" (red "FAIL") !failed total (t_encode *. 1000.)
     else
       Printf.printf "%s (%.0fms)\n" (green "ok") (t_encode *. 1000.);

     LP.reset ();
     (!passed, !failed))

let run () =
  Arg.parse speclist (fun _ -> ()) usage;

  (* Job mode: process job files *)
  (match !config.job_file, !config.jobs_dir with
  | Some job_file, _ ->
    let output_dir = match !config.output_dir with
      | Some d -> d
      | None -> "_build/jobs"
    in
    let job = EO.parse_job_file job_file in
    let (passed, failed) = process_job job output_dir in
    Printf.printf "\nTotal: %d passed, %d failed\n" passed failed;
    if failed > 0 then exit 1 else exit 0
  | None, Some jobs_dir ->
    let output_dir = match !config.output_dir with
      | Some d -> d
      | None -> "_build/jobs"
    in
    let job_files = EO.find_job_files jobs_dir in
    Printf.printf "Found %d job files in %s\n" (List.length job_files) jobs_dir;
    let total_passed = ref 0 in
    let total_failed = ref 0 in
    List.iter (fun jf ->
      let job = EO.parse_job_file jf in
      let (p, f) = process_job job output_dir in
      total_passed := !total_passed + p;
      total_failed := !total_failed + f
    ) job_files;
    Printf.printf "\n=== Summary ===\n";
    Printf.printf "Total: %d passed, %d failed\n" !total_passed !total_failed;
    if !total_failed > 0 then exit 1 else exit 0
  | None, None -> ());

  (* Legacy mode: -d/-o flags *)
  let input_dir, output_dir =
    if !config.debug then ("./cpc-tiny", "./cpc")
    else
      match !config.input_dir, !config.output_dir with
      | Some i, Some o -> (i, o)
      | _ ->
        Printf.eprintf
          "Error: Both -d and -o are required (or use --job/--jobs)\n";
        exit 1
  in

  let pkg_name = Filename.basename output_dir in

  (* Stage 1: Parse logic files *)
  let t_parse_start = Unix.gettimeofday () in
  Printf.printf "parsing %s... " input_dir;
  flush stdout;
  let graph = EO.build_sig_graph input_dir None in
  let t_parse = Unix.gettimeofday () -. t_parse_start in
  Printf.printf "%s (%.0fms)\n" (green "ok") (t_parse *. 1000.);

  (* Stage 2: Survey proofs if specified *)
  let graph = match !config.survey_dir with
    | None -> graph
    | Some survey_dir ->
      let t_survey_start = Unix.gettimeofday () in
      Printf.printf "surveying %s... " survey_dir;
      flush stdout;
      let needed_rules = survey_proofs_dir survey_dir in
      if !config.verbose then
        Printf.printf "\n  Rules needed: %s\n"
          (String.concat ", " (EO.Set.elements needed_rules));

      (* Get full signature from graph *)
      let full_sig = EO.full_sig graph in
      let full_count = List.length full_sig in

      (* Compute transitive closure of dependencies *)
      (* Start with needed rules + fundamental types that are always needed *)
      let fundamental = [
        "Type"; "Bool"; "Int"; "true"; "false"; "not"; "and"; "or"; "=>";
        "="; "ite"; "Proof"; "->"; "@List"; "eo::List"; "eo::List::cons"; "eo::List::nil"
      ] in
      let seeds = EO.Set.of_list (EO.Set.elements needed_rules @ fundamental) in
      let dep_map = EO.build_dependency_map full_sig in
      let closure = EO.transitive_closure dep_map seeds in
      let closure_count = EO.Set.cardinal closure in
      let t_survey = Unix.gettimeofday () -. t_survey_start in
      Printf.printf "%s %d/%d symbols (%.0fms)\n"
        (green "ok") closure_count full_count (t_survey *. 1000.);

      (* Filter each node's signature to only include symbols in closure *)
      EO.PathMap.map (fun node ->
        let filtered_sig = EO.filter_signature node.EO.node_sig closure in
        { node with EO.node_sig = filtered_sig }
      ) graph
  in

  (* Check for cycles *)
  (match EO.check_dag graph with
   | Error cycle ->
     Printf.printf "Error: Cycle detected:\n";
     List.iter (fun p ->
       Printf.printf "  -> %s\n" (EO.path_str p))
     cycle;
     exit 1
   | Ok () -> ());

  (* Stage 3: Initialize lambdapi *)
  let t_init_start = Unix.gettimeofday () in
  Printf.printf "initializing lambdapi... ";
  flush stdout;
  let (logic_pkg, logic_eo_sig) = match !config.proof_mode with
    | Some proof_arg ->
      (* Parse "lp_path,eo_path" *)
      let (logic_dir, logic_eo_dir) = match String.split_on_char ',' proof_arg with
        | [lp; eo] -> (lp, eo)
        | _ ->
          Printf.eprintf "Error: --proof requires format: <lp_path>,<eo_path>\n";
          exit 1
      in
      let logic_pkg = Filename.basename logic_dir in
      let main_sign = init_lambdapi_proof ~logic_dir ~output_dir ~pkg_name in
      LP.init main_sign;
      (* Load the logic's Eunoia signature for elaboration *)
      let logic_graph = EO.build_sig_graph logic_eo_dir None in
      let logic_full_sig = EO.full_sig logic_graph in
      (Some logic_pkg, logic_full_sig)
    | None ->
      let prelude_sign = init_lambdapi ~output_dir ~pkg_name in
      LP.init prelude_sign;
      (None, [])
  in
  LP.set_verbose false;
  let t_init = Unix.gettimeofday () -. t_init_start in
  Printf.printf "%s (%.0fms)\n" (green "ok") (t_init *. 1000.);

  (* Process modules in topological order *)
  Hashtbl.clear processed_modules;
  let order = EO.topo_sort graph in

  (* Filter by --only pattern if specified *)
  let order =
    match !config.only with
    | None -> order
    | Some pattern ->
      List.filter (fun path ->
        let name = String.concat "/" path in
        let pat_lower = String.lowercase_ascii pattern in
        let name_lower = String.lowercase_ascii name in
        try
          ignore (Str.search_forward
            (Str.regexp_string pat_lower) name_lower 0);
          true
        with Not_found -> false)
      order
  in

  (* Stage 4: Encode modules *)
  let total = List.length order in
  let t_encode_start = Unix.gettimeofday () in
  Printf.printf "encoding %d modules... " total;
  flush stdout;

  let passed  = ref 0 in
  let skipped = ref 0 in
  let failed  = ref 0 in
  let failures = ref [] in

  List.iter (fun path ->
    let module_name = path_to_module pkg_name path in
    let result =
      process_module ~pkg_name ~output_dir
        ~verbose:!config.verbose ?logic_pkg ~logic_eo_sig graph path
    in
    match result with
    | Success (t_deps, t_elab, t_enc, t_check) ->
      incr passed;
      if !config.verbose then
        Printf.printf "\n  %s %s (%.0f+%.0f+%.0f+%.0fms)"
          (green "ok") module_name
          (t_deps *. 1000.) (t_elab *. 1000.)
          (t_enc *. 1000.) (t_check *. 1000.)
    | Skipped _ ->
      incr skipped
    | Error msg ->
      incr failed;
      failures := (module_name, msg) :: !failures)
  order;

  let t_encode = Unix.gettimeofday () -. t_encode_start in
  if !config.verbose then Printf.printf "\n";
  if !failed > 0 then
    Printf.printf "%s %d/%d failed (%.0fms)\n" (red "FAIL") !failed total (t_encode *. 1000.)
  else
    Printf.printf "%s (%.0fms)\n" (green "ok") (t_encode *. 1000.);

  (* Print failures *)
  if !failures <> [] then begin
    Printf.printf "  Failed modules:\n";
    List.iter (fun (name, msg) ->
      Printf.printf "    %s %s: %s\n" (red "X") name msg)
      (List.rev !failures)
  end;

  (* Generate Main.lp if we have proofs to process (and not in proof_mode) *)
  (match (!config.proofs_dir, !config.proof_mode) with
  | (Some _, None) ->
    (* Generate Main.lp that imports all successfully processed modules *)
    let main_path = Filename.concat output_dir "Main.lp" in
    let oc = open_out main_path in
    Printf.fprintf oc "// Auto-generated: imports all %s modules\n" pkg_name;
    Printf.fprintf oc "require open %s.Prelude;\n" pkg_name;
    List.iter (fun path ->
      if Hashtbl.find_opt processed_modules path = Some true then
        Printf.fprintf oc "require open %s;\n" (path_to_module pkg_name path))
    order;
    close_out oc;
    Printf.printf "Generated %s\n" main_path;

    (* Compile Main.lp to make it available for proofs *)
    let cwd = Sys.getcwd () in
    Sys.chdir output_dir;
    let main_module_path = [pkg_name; "Main"] in
    ignore (LP.compile ~force:true main_module_path);
    Sys.chdir cwd
  | _ -> ());

  (* Stage 5: Process proof files if --proofs was specified *)
  let (proof_passed, proof_failed, proof_failures) =
    match (!config.proofs_dir, !config.proof_mode) with
    | (Some proofs_dir, None) ->
      (* Get full logic signature for elaboration context *)
      let logic_eo_sig = EO.full_sig graph in
      let eo_files = Array.to_list (Sys.readdir proofs_dir)
        |> List.filter (fun f -> Filename.check_suffix f ".eo")
      in
      let proof_count = List.length eo_files in
      let t_proofs_start = Unix.gettimeofday () in
      Printf.printf "encoding %d proofs... " proof_count;
      flush stdout;
      let (p, f, failures) =
        process_proofs ~pkg_name ~output_dir ~logic_eo_sig ~verbose:!config.verbose proofs_dir
      in
      let t_proofs = Unix.gettimeofday () -. t_proofs_start in
      if f > 0 then
        Printf.printf "%s %d/%d failed (%.0fms)\n" (red "FAIL") f proof_count (t_proofs *. 1000.)
      else
        Printf.printf "%s (%.0fms)\n" (green "ok") (t_proofs *. 1000.);
      (* Print failures *)
      if failures <> [] then begin
        Printf.printf "  Failed proofs:\n";
        List.iter (fun (name, msg) ->
          Printf.printf "    %s %s: %s\n" (red "X") name msg)
          failures
      end;
      (p, f, failures)
    | _ -> (0, 0, [])
  in

  (* Combine results *)
  let total_passed = !passed + proof_passed in
  let total_failed = !failed + proof_failed in
  let all_failures = List.rev !failures @ proof_failures in

  (* Summary line *)
  let status_str, status_color =
    if total_failed > 0 then ("FAIL", red)
    else ("OK", green)
  in
  Printf.printf "%s: %d passed"
    (status_color status_str)
    total_passed;
  if !skipped > 0 then
    Printf.printf ", %d skipped" !skipped;
  if total_failed > 0 then
    Printf.printf ", %d failed" total_failed;
  Printf.printf "\n";

  (* Print failed names for easy parsing by benchmark runner *)
  if all_failures <> [] then begin
    let failed_names =
      List.map (fun (name, _) ->
        match String.split_on_char '.' name with
        | _ :: rest -> String.concat "/" rest
        | [] -> name)
      all_failures
    in
    Printf.printf "Failed: %s\n"
      (String.concat ", " failed_names)
  end;

  LP.reset ();
  if total_failed > 0 then exit 1;
  (* Exit cleanly to avoid LambdaPi cleanup issues *)
  exit 0

let () = run ()
