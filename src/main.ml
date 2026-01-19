(* ============================================================
   eo2lp: Translate Eunoia signatures to LambdaPi
   ============================================================ *)

module EO = struct
  include Parse_eo
  include Syntax_eo
  include Elaborate
end

module LP = struct
  include Syntax_lp
  include Api_lp
  include Encode
end

(* ============================================================
   CLI Configuration
   ============================================================ *)

type config = {
  input_dir : string option;
  output_dir : string option;
  verbose : bool;
  debug : bool;
}

let default_config = {
  input_dir = None;
  output_dir = None;
  verbose = false;
  debug = false;
}

let config = ref default_config

let usage = "Usage: eo2lp -d <input_dir> -o <output_dir> [options]"

let speclist = [
  ("-d", Arg.String (fun s -> config := { !config with input_dir = Some s }),
   "<dir> Input directory containing .eo files");
  ("-o", Arg.String (fun s -> config := { !config with output_dir = Some s }),
   "<dir> Output directory for LambdaPi package");
  ("-v", Arg.Unit (fun () -> config := { !config with verbose = true }),
   " Verbose output");
  ("--debug", Arg.Unit (fun () -> config := { !config with debug = true }),
   " Debug mode: read from ./cpc-mini, write to ./cpc, run lambdapi check");
  ("--verbose", Arg.Unit (fun () -> config := { !config with debug = true; verbose = true }),
   " Debug mode with verbose lambdapi output (shows inference/unification)");
]

(* ============================================================
   LambdaPi Package Generation
   ============================================================ *)

let mkdir_p dir =
  let rec aux dir =
    if not (Sys.file_exists dir) then begin
      aux (Filename.dirname dir);
      Sys.mkdir dir 0o755
    end
  in aux dir

let path_to_module pkg path = pkg ^ "." ^ String.concat "." path

let generate_pkg_file output_dir pkg_name =
  let oc = open_out (Filename.concat output_dir "lambdapi.pkg") in
  Printf.fprintf oc "package_name = %s\nroot_path = %s\n" pkg_name pkg_name;
  close_out oc

let generate_prelude output_dir =
  let src = "src/Prelude.lp" in
  let dst = Filename.concat output_dir "Prelude.lp" in
  let ic = open_in src in
  let oc = open_out dst in
  try
    let rec copy () =
      output_string oc (input_line ic ^ "\n");
      copy ()
    in copy ()
  with End_of_file ->
    close_in ic;
    close_out oc

let stdlib_modules = [
  "Stdlib.Set"; "Stdlib.HOL"; "Stdlib.List";
  "Stdlib.String"; "Stdlib.Z"; "Stdlib.Bool"
]

let generate_lp_file graph pkg_name output_dir path =
  match EO.PathMap.find_opt path graph with
  | None -> ()
  | Some node ->
      let full_sig = EO.full_sig_at graph path in
      let elab_sig = EO.elab_sig_with_ctx full_sig node.node_sig in
      let lp_sig = LP.eo_sig_with_overloads elab_sig in
      let out_path = Filename.concat output_dir (String.concat "/" path ^ ".lp") in
      mkdir_p (Filename.dirname out_path);
      let prelude_module = pkg_name ^ ".Prelude" in
      let prelude_qualified = LP.RequireAs (prelude_module, "eo") in
      let deps = List.map (path_to_module pkg_name) node.node_includes in
      let open_imports =
        if deps = [] then
          LP.Require [prelude_module]
        else
          LP.Require deps
      in
        Api_lp.write_lp_file out_path (prelude_qualified :: open_imports :: lp_sig)

(* ============================================================
   Translation
   ============================================================ *)

let translate input_dir output_dir =
  let graph = EO.build_sig_graph input_dir None in
  match EO.check_dag graph with
  | Error cycle ->
      Printf.printf "Error: Cycle detected in include graph:\n";
      List.iter (fun p -> Printf.printf "  -> %s\n" (EO.path_str p)) cycle;
      exit 1
  | Ok () ->
      mkdir_p output_dir;
      let pkg_name = Filename.basename output_dir in
      generate_pkg_file output_dir pkg_name;
      generate_prelude output_dir;
      let paths = EO.topo_sort graph in
      List.iter (generate_lp_file graph pkg_name output_dir) paths;
      Printf.printf "Generated %d LambdaPi files in %s\n" (List.length paths + 1) output_dir

(* ============================================================
   Debug mode with lambdapi checking
   ============================================================ *)

let timed f =
  let t0 = Sys.time () in
  let res = f () in
  let t1 = Sys.time () in
  (res, t1 -. t0)

let debug_mode ~verbose =
  let input_dir = "./cpc-mini" in
  let output_dir = "./cpc" in
  Printf.printf "eo2lp debug mode%s\n" (if verbose then " (verbose)" else "");
  Printf.printf "  input:  %s\n" input_dir;
  Printf.printf "  output: %s\n\n" output_dir;

  let parsing_times_log = ref [] in
  let graph =
    try EO.build_sig_graph input_dir (Some parsing_times_log)
    with Failure msg -> Printf.printf "Error during parsing: %s\n" msg; exit 1
  in
  let parsing_times = Hashtbl.create (List.length !parsing_times_log) in
  List.iter (fun (file, time) -> Hashtbl.add parsing_times file time) !parsing_times_log;

  let n_modules = EO.PathMap.cardinal graph in
  Printf.printf "Parsed %d modules.\n" n_modules;

  match EO.check_dag graph with
  | Error cycle ->
      Printf.printf "Error: Cycle detected:\n";
      List.iter (fun p -> Printf.printf "  -> %s\n" (EO.path_str p)) cycle;
      exit 1
  | Ok () ->
      mkdir_p output_dir;
      let pkg_name = Filename.basename output_dir in
      generate_pkg_file output_dir pkg_name;
      generate_prelude output_dir;
      let paths = EO.topo_sort graph in

      let passed = ref 0 in
      let skipped = ref 0 in
      let failed = ref [] in
      let failed_set = Hashtbl.create 16 in
      Printf.printf "Processing and checking %d modules...\n" (List.length paths);

      let process_path path =
        let node = EO.PathMap.find path graph in
        let module_name = pkg_name ^ "." ^ String.concat "." path in
        let failed_dep = List.find_opt (Hashtbl.mem failed_set) node.EO.node_includes in

        match failed_dep with
        | Some dep ->
            incr skipped;
            Hashtbl.add failed_set path ();
            let dep_name = pkg_name ^ "." ^ String.concat "." dep in
            Printf.printf "  - %-40s (skipped due to failed dependency %s)\n" module_name dep_name

        | None ->
            let (elab_sig, elab_time), (lp_sig, enc_time) =
              let (elab_sig, elab_time) = timed (fun () ->
                let full_sig = EO.full_sig_at graph path in
                EO.elab_sig_with_ctx full_sig node.node_sig
              ) in
              let (lp_sig, enc_time) = timed (fun () ->
                LP.eo_sig_with_overloads elab_sig
              ) in
              (elab_sig, elab_time), (lp_sig, enc_time)
            in

            let out_path = Filename.concat output_dir (String.concat "/" path ^ ".lp") in
            mkdir_p (Filename.dirname out_path);
            let prelude_module = pkg_name ^ ".Prelude" in
            let prelude_qualified = LP.RequireAs (prelude_module, "eo") in
            let deps = List.map (path_to_module pkg_name) node.node_includes in
            let open_imports = if deps = [] then LP.Require [prelude_module] else LP.Require deps in
            Api_lp.write_lp_file out_path (prelude_qualified :: open_imports :: lp_sig);

            let ((exit_status, output), check_time) = timed (fun () ->
                let debug_flags = if verbose then "--debug=iu" else "" in
                let rel_path = String.concat "/" path ^ ".lp" in
                let cmd = Printf.sprintf "cd %s && lambdapi check %s -w %s 2>&1" output_dir debug_flags rel_path in
                let ic = Unix.open_process_in cmd in
                let output_buffer = Buffer.create 256 in
                (try while true do Buffer.add_channel output_buffer ic 1 done with End_of_file -> ());
                let exit_status = Unix.close_process_in ic in
                (exit_status, Buffer.contents output_buffer |> String.trim)
            ) in

            let parsing_time = Hashtbl.find_opt parsing_times node.node_file |> Option.value ~default:0.0 in

            let status_str, ok = match exit_status with
              | Unix.WEXITED 0 -> "✓", true
              | _ -> "✗", false
            in
            Printf.printf "  %s %-40s (parse: %.3fs, elab: %.3fs, enc: %.3fs, check: %.3fs)\n"
              status_str module_name parsing_time elab_time enc_time check_time;

            if ok then
              incr passed
            else begin
              Hashtbl.add failed_set path ();
              failed := (module_name, output) :: !failed;
              if verbose then
                Printf.printf "%s\n" output
            end
      in
      List.iter (fun path ->
        try process_path path
        with Failure msg ->
          let module_name = pkg_name ^ "." ^ String.concat "." path in
          Printf.printf "  ✗ %-40s (error during elaboration/encoding)\n" module_name;
          Printf.printf "    Error: %s\n" msg;
          Hashtbl.add failed_set path ();
          failed := (module_name, msg) :: !failed
      ) paths;

      Printf.printf "\n";
      if !failed = [] then
        Printf.printf "All %d modules passed.\n" n_modules
      else begin
        Printf.printf "%d passed, %d skipped, %d failed\n\n" !passed !skipped (List.length !failed);
        if not verbose then begin
          Printf.printf "Summary of failures:\n";
          List.iter (fun (m, err) ->
            let first_line = try String.split_on_char '\n' err |> List.hd with _ -> err in
            Printf.printf "  - %s: %s\n" m first_line
          ) (List.rev !failed)
        end else begin
          List.iter (fun (m, err) ->
            Printf.printf "── %s ──\n%s\n\n" m err
          ) (List.rev !failed)
        end
      end;
      if List.length !failed > 0 then exit 1

(* ============================================================
   Main entry point
   ============================================================ *)

let main () =
  Arg.parse speclist (fun _ -> ()) usage;
  let cfg = !config in
  if cfg.debug then
    debug_mode ~verbose:cfg.verbose
  else
    match cfg.input_dir, cfg.output_dir with
    | Some input_dir, Some output_dir ->
        translate input_dir output_dir
    | _ ->
        Printf.printf "%s\n" usage

(* Note: main() is called from eo2lp_cli.ml *)
