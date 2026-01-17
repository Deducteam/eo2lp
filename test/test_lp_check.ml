(* End-to-end test with lambdapi check *)

open Eo2lp
open Test_infra

let red s = Printf.sprintf "\027[31m%s\027[0m" s
let green s = Printf.sprintf "\027[32m%s\027[0m" s

let path_to_lp_module (pkg_name : string) (path : Syntax_eo.path) : string =
  pkg_name ^ "." ^ String.concat "." path

let meta_preamble = {|require open
  Stdlib.Set
  Stdlib.HOL
  Stdlib.List
  Stdlib.String
  Stdlib.Z
  Stdlib.Bool;

symbol eo⋅⋅Type : Set;
rule τ eo⋅⋅Type ↪ Set;

|}

let generate_lp_file
    (graph : Syntax_eo.sig_graph)
    (pkg_name : string)
    (output_dir : string)
    (path : Syntax_eo.path)
  : unit =
  match Syntax_eo.PathMap.find_opt path graph with
  | None -> ()
  | Some node ->
      let full_sig = Elaborate.full_sig_at graph path in
      let elab_sig = Elaborate.elab_sig_with_ctx full_sig node.node_sig in
      let lp_sig = Encode.eo_sig elab_sig in

      let rel_path = String.concat "/" path ^ ".lp" in
      let out_path = Filename.concat output_dir rel_path in

      let out_dir = Filename.dirname out_path in
      let rec mkdir_p dir =
        if not (Sys.file_exists dir) then begin
          mkdir_p (Filename.dirname dir);
          Sys.mkdir dir 0o755
        end
      in
      mkdir_p out_dir;

      let has_external_core = !Parse_eo.core_prelude <> [] in
      if node.node_includes = [] && not has_external_core then begin
        let oc = open_out out_path in
        output_string oc meta_preamble;
        List.iter (fun cmd ->
          output_string oc (Syntax_lp.command_str cmd);
          output_string oc "\n"
        ) lp_sig;
        close_out oc
      end else begin
        let requires =
          List.map (fun inc_path ->
            path_to_lp_module pkg_name inc_path
          ) node.node_includes
        in
        let all_requires = (pkg_name ^ ".Core") :: "Stdlib.Set" :: requires in
        let require_cmd = Syntax_lp.Require all_requires in
        Api_lp.write_lp_file out_path (require_cmd :: lp_sig)
      end

let generate_pkg_file (output_dir : string) (pkg_name : string) (root_path : string) : unit =
  let pkg_path = Filename.concat output_dir "lambdapi.pkg" in
  let ch = open_out pkg_path in
  Printf.fprintf ch "package_name = %s\n" pkg_name;
  Printf.fprintf ch "root_path = %s\n" root_path;
  close_out ch

let run_lp_check (input_dir : string) : bool =
  let tmp_dir = Filename.concat (Filename.get_temp_dir_name ()) "eo2lp_check" in
  let rec rm_rf path =
    if Sys.file_exists path then begin
      if Sys.is_directory path then begin
        Array.iter (fun f -> rm_rf (Filename.concat path f)) (Sys.readdir path);
        Unix.rmdir path
      end else
        Sys.remove path
    end
  in
  rm_rf tmp_dir;

  Printf.printf "Building signature graph from %s...\n" input_dir;
  let graph = Parse_eo.build_sig_graph input_dir in

  match Parse_eo.check_dag graph with
  | Error cycle ->
      Printf.printf "%s Cycle detected in graph:\n" (red "FAIL");
      List.iter (fun p -> Printf.printf "  -> %s\n" (Syntax_eo.path_str p)) cycle;
      false
  | Ok () ->
      let pkg_name = "eo2lp_test" in
      let output_dir = Filename.concat tmp_dir pkg_name in
      let rec mkdir_p dir =
        if not (Sys.file_exists dir) then begin
          mkdir_p (Filename.dirname dir);
          Sys.mkdir dir 0o755
        end
      in
      mkdir_p output_dir;
      generate_pkg_file output_dir pkg_name pkg_name;
      let paths = Parse_eo.topo_sort graph in
      List.iter (fun path ->
        generate_lp_file graph pkg_name output_dir path
      ) paths;

      Printf.printf "\nGenerated %d files. Running lambdapi check...\n\n" (List.length paths);
      let lp_pass = ref 0 in
      let lp_fail = ref 0 in

      List.iter (fun path ->
        let rel_path = String.concat "/" path ^ ".lp" in
        let cmd = Printf.sprintf "cd %s && lambdapi check %s 2>&1" output_dir rel_path in
        let ic = Unix.open_process_in cmd in
        let output = Buffer.create 256 in
        begin try while true do Buffer.add_channel output ic 1 done with End_of_file -> () end;
        let status = Unix.close_process_in ic in
        let output_str = Buffer.contents output in
        match status with
        | Unix.WEXITED 0 ->
            incr lp_pass;
            Printf.printf "  %-40s %s\n" (Syntax_eo.path_str path) (green "PASS")
        | _ ->
            incr lp_fail;
            Printf.printf "  %-40s %s\n" (Syntax_eo.path_str path) (red "FAIL");
            String.split_on_char '\n' output_str
            |> List.iter (fun line -> if String.length line > 0 then Printf.printf "      %s\n" line)
      ) paths;

      Printf.printf "\n%s\n" (String.make 50 '-');
      Printf.printf "Results: %s %d passed, %s %d failed\n"
        (green "✓") !lp_pass
        (red "✗") !lp_fail;
      rm_rf tmp_dir;
      !lp_fail = 0

let () =
  print_suite_header "LambdaPi End-to-End Check";
  let core_file = "eo/Core.eo" in
  if Sys.file_exists core_file then
    let core_sig = Parse_eo.parse_eo_file "." core_file in
    Elaborate.set_core_prelude core_sig
  else
    Printf.printf "Warning: Core.eo not found, skipping lp-check test.\n";

  let success = run_lp_check "./cpc-mini" in
  if not success then exit 1
