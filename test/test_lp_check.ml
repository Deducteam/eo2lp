(* End-to-end test with lambdapi check *)

open Eo2lp
open Test_infra

let red s = Printf.sprintf "\027[31m%s\027[0m" s
let green s = Printf.sprintf "\027[32m%s\027[0m" s
let yellow s = Printf.sprintf "\027[33m%s\027[0m" s

let path_to_lp_module (pkg_name : string) (path : Syntax_eo.path) : string =
  pkg_name ^ "." ^ String.concat "." path

let stdlib_modules = [
  "Stdlib.Set"; "Stdlib.HOL"; "Stdlib.List";
  "Stdlib.String"; "Stdlib.Z"; "Stdlib.Bool"
]

let generate_lp_file
    (graph : Syntax_eo.sig_graph)
    (pkg_name : string)
    (output_dir : string)
    (path : Syntax_eo.path)
  : unit =
  match Syntax_eo.PathMap.find_opt path graph with
  | None -> ()
  | Some node ->
      let full_sig = Syntax_eo.full_sig_at graph path in
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

      let prelude_module = pkg_name ^ ".Prelude" in
      let prelude_qualified = Syntax_lp.RequireAs (prelude_module, "eo") in
      let deps = List.map (path_to_lp_module pkg_name) node.node_includes in
      let open_imports = Syntax_lp.Require (stdlib_modules @ [prelude_module] @ deps) in
      Api_lp.write_lp_file out_path (prelude_qualified :: open_imports :: lp_sig)

let generate_pkg_file (output_dir : string) (pkg_name : string) (root_path : string) : unit =
  let pkg_path = Filename.concat output_dir "lambdapi.pkg" in
  let ch = open_out pkg_path in
  Printf.fprintf ch "package_name = %s\n" pkg_name;
  Printf.fprintf ch "root_path = %s\n" root_path;
  close_out ch

type check_status =
  | Passed
  | Failed of string  (* error output *)
  | Skipped of Syntax_eo.path  (* skipped because this dependency failed *)

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

      (* Generate Prelude.lp using main.ml's approach *)
      let prelude_content = Main.prelude_content in
      let oc = open_out (Filename.concat output_dir "Prelude.lp") in
      output_string oc prelude_content;
      close_out oc;

      let paths = Syntax_eo.topo_sort graph in
      List.iter (fun path ->
        generate_lp_file graph pkg_name output_dir path
      ) paths;

      Printf.printf "\nGenerated %d files. Running lambdapi check...\n\n" (List.length paths + 1);

      (* Track status for each path *)
      let status_map = Hashtbl.create (List.length paths) in
      let lp_pass = ref 0 in
      let lp_fail = ref 0 in
      let lp_skip = ref 0 in

      (* Check paths in topological order *)
      List.iter (fun path ->
        (* Check if any dependency failed *)
        let (node : Syntax_eo.sig_node) = Syntax_eo.PathMap.find path graph in
        let failed_dep = List.find_opt (fun dep ->
          match Hashtbl.find_opt status_map dep with
          | Some (Failed _) | Some (Skipped _) -> true
          | _ -> false
        ) node.node_includes in

        match failed_dep with
        | Some dep ->
            (* Skip this path because a dependency failed *)
            incr lp_skip;
            Hashtbl.add status_map path (Skipped dep);
            Printf.printf "  %-40s %s\n"
              (Syntax_eo.path_str path)
              (yellow (Printf.sprintf "SKIP (dep %s failed)" (Syntax_eo.path_str dep)))
        | None ->
            (* All dependencies passed, run the check *)
            let rel_path = String.concat "/" path ^ ".lp" in
            (* Use -w to disable warnings *)
            let cmd = Printf.sprintf "cd %s && lambdapi check -w -c %s 2>&1" output_dir rel_path in
            let ic = Unix.open_process_in cmd in
            let output = Buffer.create 256 in
            begin try while true do Buffer.add_channel output ic 1 done with End_of_file -> () end;
            let status = Unix.close_process_in ic in
            let output_str = Buffer.contents output in
            match status with
            | Unix.WEXITED 0 ->
                incr lp_pass;
                Hashtbl.add status_map path Passed;
                Printf.printf "  %-40s %s\n" (Syntax_eo.path_str path) (green "PASS")
            | _ ->
                incr lp_fail;
                Hashtbl.add status_map path (Failed output_str);
                Printf.printf "  %-40s %s\n" (Syntax_eo.path_str path) (red "FAIL");
                String.split_on_char '\n' output_str
                |> List.iter (fun line -> if String.length line > 0 then Printf.printf "      %s\n" line)
      ) paths;

      (* Also check the top-level Cpc.lp if it exists *)
      let cpc_path = Filename.concat output_dir "Cpc.lp" in
      if Sys.file_exists cpc_path then begin
        (* Check if any module failed - if so, skip Cpc *)
        if !lp_fail > 0 then begin
          incr lp_skip;
          Printf.printf "  %-40s %s\n" "Cpc" (yellow "SKIP (dependencies failed)")
        end else begin
          let cmd = Printf.sprintf "cd %s && lambdapi check -w -c Cpc.lp 2>&1" output_dir in
          let ic = Unix.open_process_in cmd in
          let output = Buffer.create 256 in
          begin try while true do Buffer.add_channel output ic 1 done with End_of_file -> () end;
          let status = Unix.close_process_in ic in
          let output_str = Buffer.contents output in
          match status with
          | Unix.WEXITED 0 ->
              incr lp_pass;
              Printf.printf "  %-40s %s\n" "Cpc" (green "PASS")
          | _ ->
              incr lp_fail;
              Printf.printf "  %-40s %s\n" "Cpc" (red "FAIL");
              String.split_on_char '\n' output_str
              |> List.iter (fun line -> if String.length line > 0 then Printf.printf "      %s\n" line)
        end
      end;

      Printf.printf "\n%s\n" (String.make 50 '-');
      Printf.printf "Results: %s %d passed, %s %d failed, %s %d skipped\n"
        (green "✓") !lp_pass
        (red "✗") !lp_fail
        (yellow "⊘") !lp_skip;
      rm_rf tmp_dir;
      !lp_fail = 0

let () =
  print_suite_header "LambdaPi End-to-End Check";
  let success = run_lp_check "./cpc-mini" in
  if not success then exit 1
