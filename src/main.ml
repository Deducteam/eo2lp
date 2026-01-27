(* main.ml
   eo2lp driver: translate Eunoia signatures to LambdaPi *)

open Syntax_eo

module Elab = Elaborate
module Enc  = Encode
module LP   = Api_lp

(* CLI config *)

type config = {
  input_dir  : string;
  output_dir : string;
  verbose    : bool;
  no_color   : bool;
}

let default_config = {
  input_dir  = "./cpc";
  output_dir = "./_build/cpc";
  verbose    = false;
  no_color   = false;
}

let config = ref default_config

let usage = "Usage: eo2lp [options]"

let speclist = [
  ("-d", Arg.String (fun s -> config := { !config with input_dir = s }),
   "<dir> Input directory with .eo files (default: ./cpc)");
  ("-o", Arg.String (fun s -> config := { !config with output_dir = s }),
   "<dir> Output directory for LambdaPi package (default: ./_build/cpc)");
  ("-v", Arg.Unit (fun () -> config := { !config with verbose = true }),
   " Verbose output");
  ("--no-color", Arg.Unit (fun () -> config := { !config with no_color = true }),
   " Disable colored output");
]

(* Terminal colors *)

let color code s = if !config.no_color then s else Printf.sprintf "\027[%sm%s\027[0m" code s
let red s = color "31" s
let green s = color "32" s
let cyan s = color "36" s
let dim s = color "2" s

(* Helpers *)

let path_to_module pkg path = pkg ^ "." ^ String.concat "." path

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
  | Success of float * float * float  (* elab, enc, check times *)
  | Skipped of string
  | Error of string

let processed_modules : (path, bool) Hashtbl.t = Hashtbl.create 32

(* Get module dependencies from the signature graph *)
let module_deps (s : signature) (mod_path : path) : path list =
  (* Collect all dependencies from symbols in this module *)
  let syms = sig_module_symbols s mod_path in
  let all_dep_sids = List.fold_left (fun acc (name, _) ->
    let sid = { sid_module = mod_path; sid_name = name } in
    match sig_find s sid with
    | Some entry -> SymbolSet.union acc entry.se_deps
    | None -> acc
  ) SymbolSet.empty syms in
  (* Extract unique module paths from dependencies *)
  SymbolSet.fold (fun sid acc ->
    if sid.sid_module <> mod_path && not (List.mem sid.sid_module acc) then
      sid.sid_module :: acc
    else acc
  ) all_dep_sids []

let process_module ~pkg_name ~output_dir ~verbose (s : signature) (mod_path : path) =
  let deps = module_deps s mod_path in
  let all_modules = sig_modules s in

  (* Check if dependencies have been processed successfully *)
  let deps_ok = List.for_all (fun dep ->
    match Hashtbl.find_opt processed_modules dep with
    | Some true -> true
    | _ -> not (List.mem dep all_modules)  (* external dep is ok *)
  ) deps in

  if not deps_ok then begin
    let failed_dep = List.find (fun dep ->
      match Hashtbl.find_opt processed_modules dep with
      | Some true -> false
      | _ -> List.mem dep all_modules
    ) deps in
    Skipped (Printf.sprintf "dep %s" (path_to_module pkg_name failed_dep))
  end
  else begin
    let phase = ref "init" in
    try
      let module_name = path_to_module pkg_name mod_path in
      LP.set_current_module module_name;
      let t0 = Unix.gettimeofday () in

      (* Elaborate this module's symbols *)
      phase := "elaborate";
      let elab_syms = Elab.elab_module mod_path in
      let t1 = Unix.gettimeofday () in

      (* Encode to LambdaPi *)
      phase := "encode";
      let module_path = pkg_name :: mod_path in
      let dep_paths = List.map (fun dep -> pkg_name :: dep) deps in
      let _sign = LP.init_sign ~deps:dep_paths module_path in
      let enc_result = Enc.enc_signature elab_syms in
      let t2 = Unix.gettimeofday () in

      if enc_result.Enc.errors <> [] then begin
        Hashtbl.replace processed_modules mod_path false;
        let first_err = List.hd enc_result.Enc.errors in
        Error (snd first_err)
      end
      else begin
        (* Write .lp file *)
        phase := "write";
        let out_path = Filename.concat output_dir (String.concat "/" mod_path ^ ".lp") in
        LP.mkdir_p (Filename.dirname out_path);
        let prelude_module = pkg_name ^ ".Prelude" in
        let dep_modules = List.map (path_to_module pkg_name) deps in
        LP.write_lp_file out_path ~prelude_module ~deps:dep_modules _sign
          enc_result.Enc.rules ~after_rules_map:enc_result.Enc.after_rules_map;

        (* Check with LambdaPi *)
        phase := "check";
        let rel_path = String.concat "/" mod_path ^ ".lp" in
        let check_result = LP.check_file ~verbose output_dir rel_path in
        let t3 = Unix.gettimeofday () in

        match check_result with
        | LP.Check_ok ->
          Hashtbl.replace processed_modules mod_path true;
          Success (t1-.t0, t2-.t1, t3-.t2)
        | LP.Check_error msg ->
          Hashtbl.replace processed_modules mod_path false;
          Error (Printf.sprintf "[check] %s" msg)
      end

    with
    | Failure msg ->
      Hashtbl.replace processed_modules mod_path false;
      Error (Printf.sprintf "[%s] %s" !phase msg)
    | exn ->
      Hashtbl.replace processed_modules mod_path false;
      Error (Printf.sprintf "[%s] %s" !phase (Printexc.to_string exn))
  end

(* Main entry point *)

let run () =
  Arg.parse speclist (fun _ -> ()) usage;

  let input_dir = !config.input_dir in
  let output_dir = !config.output_dir in

  let pkg_name = Filename.basename output_dir in

  (* Stage 1: Parse *)
  let t_parse_start = Unix.gettimeofday () in
  Printf.printf "parsing %s... " input_dir;
  flush stdout;
  let s = Parse_eo.build_sig input_dir in
  let t_parse = Unix.gettimeofday () -. t_parse_start in
  Printf.printf "%s (%.0fms)\n" (green "ok") (t_parse *. 1000.);

  (* Print modules as a grouped tree, wrapping at 60 chars *)
  let modules = sig_modules s in
  let grouped = List.fold_left (fun acc path ->
    match path with
    | [] -> acc
    | group :: rest ->
      let name = String.concat "/" rest in
      let existing = Option.value ~default:[] (List.assoc_opt group acc) in
      (group, name :: existing) :: List.remove_assoc group acc
  ) [] modules in
  let grouped = List.map (fun (g, ns) -> (g, List.rev ns)) (List.rev grouped) in
  Printf.printf "[\n";
  List.iter (fun (group, names) ->
    match names with
    | [] -> Printf.printf "  %s\n" group  (* single module at root *)
    | [""] -> Printf.printf "  %s\n" group  (* single module at root *)
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
  Printf.printf "]\n";

  (* Set up elaboration with the full signature *)
  Elab.set_signature s;

  (* Stage 2: Initialize LambdaPi *)
  let t_init_start = Unix.gettimeofday () in
  Printf.printf "initializing lambdapi... ";
  flush stdout;
  let prelude_sign = init_lambdapi ~output_dir ~pkg_name in
  LP.init prelude_sign;
  LP.set_verbose false;
  let t_init = Unix.gettimeofday () -. t_init_start in
  Printf.printf "%s (%.0fms)\n" (green "ok") (t_init *. 1000.);

  (* Get module order *)
  let order = sig_module_order s in

  (* Stage 3: Encode modules *)
  let total = List.length order in
  let t_encode_start = Unix.gettimeofday () in
  Printf.printf "encoding %d modules... " total;
  flush stdout;

  Hashtbl.clear processed_modules;
  let passed = ref 0 in
  let skipped = ref 0 in
  let failed = ref 0 in
  let failures = ref [] in

  List.iter (fun mod_path ->
    let module_name = path_to_module pkg_name mod_path in
    let result = process_module ~pkg_name ~output_dir ~verbose:!config.verbose s mod_path in
    match result with
    | Success (t_elab, t_enc, t_check) ->
      incr passed;
      if !config.verbose then
        Printf.printf "\n  %s %s (%.0f+%.0f+%.0fms)"
          (green "ok") module_name
          (t_elab *. 1000.) (t_enc *. 1000.) (t_check *. 1000.)
    | Skipped reason ->
      incr skipped;
      if !config.verbose then
        Printf.printf "\n  %s %s (%s)" (dim "skip") module_name reason
    | Error msg ->
      incr failed;
      failures := (module_name, msg) :: !failures
  ) order;

  let t_encode = Unix.gettimeofday () -. t_encode_start in
  if !config.verbose then Printf.printf "\n";

  if !failed > 0 then
    Printf.printf "%s %d/%d failed (%.0fms)\n" (red "FAIL") !failed total (t_encode *. 1000.)
  else
    Printf.printf "%s (%.0fms)\n" (green "ok") (t_encode *. 1000.);

  (* Summary *)
  let status_str, status_color =
    if !failed > 0 then ("FAIL", red) else ("OK", green)
  in
  Printf.printf "%s: %d passed" (status_color status_str) !passed;
  if !skipped > 0 then Printf.printf ", %d skipped" !skipped;
  if !failed > 0 then Printf.printf ", %d failed" !failed;
  Printf.printf "\n";

  (* Print failed names and errors *)
  if !failures <> [] then begin
    List.iter (fun (name, msg) ->
      Printf.printf "  %s: %s\n" (red name) msg
    ) (List.rev !failures);
    let failed_names = List.map (fun (name, _) ->
      match String.split_on_char '.' name with
      | _ :: rest -> String.concat "/" rest
      | [] -> name
    ) !failures in
    Printf.printf "Failed: %s\n" (String.concat ", " failed_names)
  end;

  LP.reset ();
  if !failed > 0 then exit 1;
  exit 0

let () = run ()
