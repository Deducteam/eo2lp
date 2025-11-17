open Lexing
open Syntax_eo

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

let cpc_root = "../cvc5/proofs/eo/cpc"

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

let (cpc_theories, cpc_rules, cpc_progs) =
  let eos dir =
    List.concat_map
    (fun fp ->
      Printf.printf "Parsing: %s\n" fp;
      parse_eo_file fp
    )
    (find_eo_files (Filename.concat cpc_root dir))
  in
    (eos "theories", eos "rules", eos "programs")

let cpc = List.concat [cpc_theories; cpc_progs; cpc_rules]
let print_eo_sig cs =
  List.map
    (fun cmd -> Printf.printf "%s\n" (eo_command_str cmd))
    cs
