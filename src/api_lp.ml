(* api_lp.ml *)
open Syntax_lp

(* Configuration for the LambdaPi package structure *)
let package_name = "eo2lp"
let lp_dir = "lp"
let tmp_file = "lp/tmp.lp"

(* Convert a file path to a LambdaPi module path *)
(* e.g., "lp/theories/Builtin.lp" -> "eo2lp.theories.Builtin" *)
let file_to_module_path (filepath : string) : string =
  let without_lp =
    if String.starts_with ~prefix:"lp/" filepath then
      String.sub filepath 3 (String.length filepath - 3)
    else filepath
  in
  let without_ext =
    if String.ends_with ~suffix:".lp" without_lp then
      String.sub without_lp 0 (String.length without_lp - 3)
    else without_lp
  in
  let with_dots =
    String.map
      (fun c -> if c = '/' then '.' else c)
      without_ext
  in
    package_name ^ "." ^ with_dots

(* Result type for LambdaPi operations *)
type lp_result =
  | Ok
  | Error of string

let run_lambdapi (args : string list) : lp_result =
  let cmd = "lambdapi " ^ String.concat " " args in
  let (ic, oc, ec) = Unix.open_process_full cmd (Unix.environment ()) in
  close_out oc;

  let read_all ch =
    let buf = Buffer.create 1024 in
    try
      while true do
        Buffer.add_channel buf ch 1024
      done;
      assert false
    with End_of_file -> Buffer.contents buf
  in

  let stdout = read_all ic in
  let stderr = read_all ec in
  let status = Unix.close_process_full (ic, oc, ec) in

  match status with
  | Unix.WEXITED 0 -> Ok
  | _ -> Error (stdout ^ stderr)

(* Write commands to a file *)
let write_lp_file (filepath : string) (commands : command list) : unit =
  (* Ensure directory exists *)
  let dir = Filename.dirname filepath in
  let rec mkdir_p path =
    if not (Sys.file_exists path) then (
      mkdir_p (Filename.dirname path);
      Unix.mkdir path 0o755
    )
  in
  if dir <> "." && dir <> "" then mkdir_p dir;

  (* Write file *)
  let oc = open_out filepath in
  List.iter (fun cmd ->
    output_string oc (command_str cmd);
    output_string oc "\n"
  ) commands;
  close_out oc

(* Check if a term is well-typed in the context of a given file *)
let check_term_type
    (current_file : string)  (* e.g., "lp/theories/Builtin.lp" *)
    (term : term)            (* the term to check *)
  : lp_result =

  let module_path = file_to_module_path current_file in

  (* Create tmp.lp with require and type query *)
  let tmp_commands = [
    Require [module_path];
  ] in

  write_lp_file tmp_file tmp_commands;

  (* Append the type query *)
  let oc = open_out_gen [Open_append; Open_text] 0o644 tmp_file in
  Printf.fprintf oc "type %s;\n" (term_str term);
  close_out oc;

  (* Run lambdapi check *)
  run_lambdapi ["check"; tmp_file; "-c"; "-w"]

(* Check if a file typechecks correctly *)
let check_file (filepath : string) : lp_result =
  run_lambdapi ["check"; filepath; "-c"; "-w"]

(* Helper to check if result is ok *)
let is_ok : lp_result -> bool = function
  | Ok -> true
  | Error _ -> false

(* Helper to get error message *)
let error_msg : lp_result -> string option = function
  | Ok -> None
  | Error msg -> Some msg

(* ---------------------------- *)

(* During translation of cpc-mini/theories/Builtin.eo *)
let current_file = "lp/Core.lp"

(* Check if a term typechecks *)
let foo () =
  match check_term_type current_file
    (App (Var "List", Var ("List"))) with
  | Ok -> Printf.printf "Term is well-typed!\n"
  | Error err -> Printf.printf "Error:\n%s\n" err
