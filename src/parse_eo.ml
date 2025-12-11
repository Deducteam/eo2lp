open Lexing
open Syntax_eo

let parse_eo_term (str : string) : term =
  let lx = Lexing.from_string str in
  try
    Parser.term Lexer.token lx
  with
    Parser.Error -> failwith "error when parsing term."

let parse_eo_params (str : string) : param list =
  let lx = Lexing.from_string str in
  try
    Parser.params Lexer.token lx
  with
    Parser.Error -> failwith "error when parsing term."

let parse_command (lx : Lexing.lexbuf) : command option =
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

let parse_eo_file (fp : string) : command list =
  let ch = open_in fp in
  Printf.printf "Parsing: %s\n" fp;
  let lx = Lexing.from_channel ch in
  let cmds = ref [] in
  try
    while true do
      match parse_command lx with
      | Some cmd -> cmds := cmd :: !cmds
      | None -> raise Exit
    done;
    assert false (* unreachable *)
  with
  | Exit -> close_in ch; List.rev !cmds
  | exn -> close_in ch; raise exn

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
