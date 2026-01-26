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
}

let default_config = {
  input_dir  = None;
  output_dir = None;
  verbose    = false;
  debug      = false;
  no_color   = false;
  only       = None;
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
]

(* Helpers *)

let path_to_module pkg path =
  pkg ^ "." ^ String.concat "." path

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

(* Module processing *)

type process_result =
  | Success of float * float * float * float
  | Skipped of string
  | Error   of string

let processed_modules : (EO.path, bool) Hashtbl.t =
  Hashtbl.create 32

let process_module ~pkg_name ~output_dir ~verbose graph path =
  let node = EO.PathMap.find path graph in

  (* Check dependencies *)
  let deps_ok =
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
    try
      let module_name = path_to_module pkg_name path in
      LP.set_current_module module_name;
      let t0 = Unix.gettimeofday () in

      let full_sig = EO.full_sig_at graph path in
      let t1 = Unix.gettimeofday () in

      let elab_sig =
        Elab.elab_sig_with_ctx full_sig node.EO.node_sig
      in
      let t2 = Unix.gettimeofday () in

      let module_path = pkg_name :: path in
      let dep_paths =
        List.map (fun dep -> pkg_name :: dep)
          node.EO.node_includes
      in
      let sign = LP.init_sign ~deps:dep_paths module_path in
      let (rules, after_rules_map) = Enc.enc_signature elab_sig in
      let t3 = Unix.gettimeofday () in

      let out_path =
        Filename.concat output_dir
          (String.concat "/" path ^ ".lp")
      in
      LP.mkdir_p (Filename.dirname out_path);
      let prelude_module = pkg_name ^ ".Prelude" in
      let deps =
        List.map (path_to_module pkg_name)
          node.EO.node_includes
      in
      LP.write_lp_file out_path
        ~prelude_module ~deps sign rules ~after_rules_map;

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
        Error msg

    with
    | Failure msg ->
      Hashtbl.replace processed_modules path false;
      Error msg
    | exn ->
      Hashtbl.replace processed_modules path false;
      Error (Printexc.to_string exn)
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

(* Main entry point *)

let run () =
  Arg.parse speclist (fun _ -> ()) usage;

  let input_dir, output_dir =
    if !config.debug then ("./cpc-tiny", "./cpc")
    else
      match !config.input_dir, !config.output_dir with
      | Some i, Some o -> (i, o)
      | _ ->
        Printf.eprintf
          "Error: Both -d and -o are required\n";
        exit 1
  in

  let pkg_name = Filename.basename output_dir in
  let graph = EO.build_sig_graph input_dir None in

  (* Check for cycles *)
  (match EO.check_dag graph with
   | Error cycle ->
     Printf.printf "Error: Cycle detected:\n";
     List.iter (fun p ->
       Printf.printf "  -> %s\n" (EO.path_str p))
     cycle;
     exit 1
   | Ok () -> ());

  (* Initialize lambdapi with prelude *)
  let prelude_sign = init_lambdapi ~output_dir ~pkg_name in
  LP.init prelude_sign;
  LP.set_verbose false;

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

  let total = List.length order in
  Printf.printf "eo2lp: processing %d modules\n" total;
  flush stdout;

  let passed  = ref 0 in
  let skipped = ref 0 in
  let failed  = ref 0 in
  let failures = ref [] in

  List.iter (fun path ->
    let module_name = path_to_module pkg_name path in
    let result =
      process_module ~pkg_name ~output_dir
        ~verbose:!config.verbose graph path
    in
    match result with
    | Success (t_deps, t_elab, t_enc, t_check) ->
      incr passed;
      if !config.verbose then
        Printf.printf "  %s %s (%.0f+%.0f+%.0f+%.0fms)\n"
          (green "ok") module_name
          (t_deps *. 1000.) (t_elab *. 1000.)
          (t_enc *. 1000.) (t_check *. 1000.)
    | Skipped _ ->
      incr skipped
    | Error msg ->
      incr failed;
      failures := (module_name, msg) :: !failures;
      Printf.printf "  %s %s\n" (red "X") module_name)
  order;

  (* Print failures with context *)
  if !failures <> [] then begin
    Printf.printf "\n";
    List.iter (fun (name, msg) ->
      print_string (format_failure name msg);
      print_newline ())
    (List.rev !failures)
  end;

  (* Summary *)
  let status_str, status_color =
    if !failed > 0 then ("FAIL", red)
    else ("OK", green)
  in
  Printf.printf "%s: %s"
    (status_color status_str)
    (green (Printf.sprintf "%d passed" !passed));
  if !skipped > 0 then
    Printf.printf ", %s"
      (yellow (Printf.sprintf "%d skipped" !skipped));
  if !failed > 0 then
    Printf.printf ", %s"
      (red (Printf.sprintf "%d failed" !failed));
  Printf.printf "\n";

  if !failures <> [] then begin
    let failed_names =
      List.rev_map (fun (name, _) ->
        match String.split_on_char '.' name with
        | _ :: rest -> String.concat "/" rest
        | [] -> name)
      !failures
    in
    Printf.printf "Failed: %s\n"
      (String.concat ", " failed_names)
  end;

  LP.reset ();
  if !failed > 0 then exit 1;
  (* Exit cleanly to avoid LambdaPi cleanup issues *)
  exit 0

let () = run ()
