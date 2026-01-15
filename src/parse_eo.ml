open Lexing
open Syntax_eo

let to_absolute p =
  if Fpath.is_abs p then p
  else Fpath.(v (Sys.getcwd ()) // p) |> Fpath.normalize

(* Returns: string list (e.g., ["programs"; "Utils"]) *)
let get_logical_path (root, abs_fp : Fpath.t * Fpath.t) : string list =
  match Fpath.relativize ~root abs_fp with
  | None -> Printf.ksprintf failwith
      "File %s is not inside root %s"
      (Fpath.to_string abs_fp) (Fpath.to_string root)
  | Some rel ->
      rel |> Fpath.rem_ext |> Fpath.segs

(* root: string (absolute path to project root)
   fp : string (absolute path to current file)
   str : string (the raw string from the include command) *)
let resolve (root,fp,str : string * string * string) : string list =
  let rt_abs = to_absolute (Fpath.v root) in
  let fp_abs = to_absolute (Fpath.v fp) in
  let cwd = Fpath.parent fp_abs in
  let target = Fpath.((cwd // v str) |> normalize)  in
  get_logical_path (rt_abs, target)


let parse_eo_term (str : string) : term =
  let lx = Lexing.from_string str in
  try Parser.term Lexer.token lx
  with Parser.Error -> failwith "error when parsing term."

let parse_eo_params (str : string) : param list =
  let lx = Lexing.from_string str in
  try Parser.params Lexer.token lx
  with Parser.Error -> failwith "error when parsing term."

let parse_command (lx : Lexing.lexbuf) : (string * const) list option =
  try Some (Parser.toplevel_eof Lexer.token lx)
  with Parser.Error ->
    let pos = lx.lex_curr_p in
    Printf.printf
      "Parser error at line %d, column %d: token '%s'\n"
      pos.pos_lnum
      (pos.pos_cnum - pos.pos_bol + 1)
      (Lexing.lexeme lx);
    Parse_ctx.had_parse_error := true;
    None

(* Cache for parsed files, keyed by absolute path *)
let parse_cache : (string, signature) Hashtbl.t = Hashtbl.create 32

let clear_parse_cache () = Hashtbl.clear parse_cache

let rec parse_eo_file (root, fp : string * string) : signature =
  let fp_abs = to_absolute (Fpath.v fp) in
  let fp_key = Fpath.to_string fp_abs in

  (* Check cache first *)
  match Hashtbl.find_opt parse_cache fp_key with
  | Some cached -> cached
  | None ->
    (* Printf.printf "Parsing: %s\n" fp; *)
    let ch = open_in fp in
    let lx = Lexing.from_channel ch in
    let _sig = ref [] in

    (* Set up the include callback with current file's context *)
    let cwd = Fpath.parent fp_abs in
    let old_callback = !Parse_ctx.parse_include_callback in
    Parse_ctx.parse_include_callback := (fun include_path ->
      let target = Fpath.((cwd // v include_path) |> normalize) in
      parse_eo_file (root, Fpath.to_string target)
    );

    let result =
      try while true do (
        match parse_command lx with
        | Some [] -> raise Exit
        | Some syms -> _sig := List.rev_append syms !_sig
        | None -> raise Exit
      ) done; assert false

      with
      | Exit -> close_in ch; List.rev !_sig
      | exn -> close_in ch; raise exn
    in
    Parse_ctx.parse_include_callback := old_callback;
    Hashtbl.add parse_cache fp_key result;
    result

let dir_contents dir =
  let rec loop result = function
    | f::fs when Sys.is_directory f ->
          Sys.readdir f
          |> Array.to_list
          |> List.map (Filename.concat f)
          |> List.append fs
          |> loop result
    | f::fs ->
        loop (f::result) fs
    | []    -> result
  in
    loop [] [dir]

(* let parse_eo_dir (root_str : string) : environment =
  let root = to_absolute (Fpath.v root_str) in
  let root_abs_str = Fpath.to_string root in

  (* Your existing recursive directory search *)
  let fps = List.filter
    (fun fp -> Filename.check_suffix fp ".eo")
    (dir_contents root_abs_str) in

  let f fp_str =
    let fp = to_absolute (Fpath.v fp_str) in
    let key = get_logical_path (root,fp) in

    (* 2. Parse, passing the absolute root string for inner resolution *)
     (key, parse_eo_file (root_abs_str, Fpath.to_string fp))

  in
    List.map f fps *)
