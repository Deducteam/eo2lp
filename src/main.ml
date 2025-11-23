open Lexing

open Syntax_eo
open Interface_eo

(* find eo files in dir *)
let find_eo_files (dir : string) : string list =
  Array.fold_left
    (fun acc name ->
      if Filename.check_suffix name ".eo" then
        (Filename.concat dir name) :: acc
      else
        acc
    )
    [] (Sys.readdir dir)

let parse_eo_command (lx : lexbuf) : eo_command option =
  try
    Parser.toplevel_eof Lexer.token lx
  with
  | Parser.Error ->
      let pos = lx.lex_curr_p in
      Printf.printf
        "Parser error in at line %d, column %d: token '%s'\n"
        pos.pos_lnum
        (pos.pos_cnum - pos.pos_bol + 1)
        (Lexing.lexeme lx);
      None

let parse_eo_file (fp : string) : eo_command list =
  let ch = open_in fp in
  Printf.printf "Parsing: %s\n" fp;
  let lx = Lexing.from_channel ch in
  let cmds = ref [] in
  try
    while true do
      match parse_eo_command lx with
      | Some cmd -> cmds := cmd :: !cmds
      | None -> raise Exit
    done;
    assert false (* unreachable *)
  with
  | Exit -> close_in ch; List.rev !cmds
  | exn -> close_in ch; raise exn

let proc_eo_file (fp : string) : jlist =
  List.concat_map
    (fun cmd ->
      (* Printf.printf "Processing:\n%s\n" (eo_command_str cmd); *)
      let js = proc_eo_command cmd in
      Printf.printf "\n%s\n" (jlist_str js);
      js)
    (parse_eo_file fp)

let cpc_root  = "../cvc5/proofs/eo/cpc"
let cpc_mini  =
  List.map (fun fp -> Filename.concat cpc_root fp)
    [
      "programs/Utils.eo";
      (* "theories/Builtin.eo";
      "rules/Builtin.eo"; *)
    ]

(* let cpc_paths : string list =
  (* List.concat_map
    (fun dir -> find_eo_files
      (Filename.concat cpc_root dir)
    )
    ["."; "theories"; "programs"; "rules"] *) *)

let cpc_commands : eo_command list =
  List.concat_map parse_eo_file cpc_mini

let cpc_judgements : judgement list =
  List.concat_map proc_eo_file cpc_mini
