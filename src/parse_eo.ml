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

(* Returns: Some (Some syms) for a command, Some None for EOF, None for error *)
let parse_command (lx : Lexing.lexbuf) : (string * const) list option option =
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

(* Remove duplicate symbols, keeping the last occurrence, preserving order. *)
let unique sgn =
  let sgn_rev = List.rev sgn in
  let seen = Hashtbl.create (List.length sgn_rev) in
  let result_rev = List.filter (fun (s, _) ->
    let fresh = not (Hashtbl.mem seen s) in
    if fresh then Hashtbl.add seen s ();
    fresh
  ) sgn_rev in
  List.rev result_rev

let rec parse_eo_file (root : string) (fp : string) : signature =
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
    Parse_ctx.parse_include_callback :=
    (fun include_path ->
      let target = Fpath.((cwd // v include_path) |> normalize) in
      parse_eo_file root (Fpath.to_string target)
    );

    let result =
      try while true do (
        match parse_command lx with
        | Some (Some syms) -> _sig := List.rev_append syms !_sig
        | Some None -> raise Exit  (* EOF *)
        | None -> raise Exit  (* Parse error *)
      ) done; assert false

      with
      | Exit -> close_in ch; List.rev !_sig
      | exn -> close_in ch; raise exn
    in
    Parse_ctx.parse_include_callback := old_callback;
    let unique_result = unique result in
    Hashtbl.add parse_cache fp_key unique_result;
    unique_result

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

let parse_eo_dir (root_str : string) : signature =
  let root = to_absolute (Fpath.v root_str) in
  let root_abs_str = Fpath.to_string root in

  let fps = List.filter
    (fun fp -> Filename.check_suffix fp ".eo")
    (dir_contents root_abs_str) in

  let signatures = List.map (fun fp_str ->
    parse_eo_file root_abs_str fp_str
  ) fps in

  List.concat signatures

(* ============================================================
   New v2 parsing: builds signature graph (DAG)
   ============================================================ *)

(* Parse a single command using v2 parser (separates includes) *)
let parse_command_v2 (lx : Lexing.lexbuf)
    : [ `Sig of (string * const) list | `Include of string ] option option =
  try Some (Parser.toplevel_eof_v2 Lexer.token lx)
  with Parser.Error ->
    let pos = lx.lex_curr_p in
    Printf.printf
      "Parser error at line %d, column %d: token '%s'\n"
      pos.pos_lnum
      (pos.pos_cnum - pos.pos_bol + 1)
      (Lexing.lexeme lx);
    Parse_ctx.had_parse_error := true;
    None

(* Parse a single file, returning local signature and raw include paths *)
let parse_file_local (root : string) (fp : string) : file_parse_result =
  let root_abs = to_absolute (Fpath.v root) in
  let fp_abs = to_absolute (Fpath.v fp) in
  let fp_key = Fpath.to_string fp_abs in
  let cwd = Fpath.parent fp_abs in

  let ch = open_in fp_key in
  let lx = Lexing.from_channel ch in
  let local_sig = ref [] in
  let includes = ref [] in

  let result =
    try while true do
      match parse_command_v2 lx with
      | Some (Some (`Sig syms)) ->
          local_sig := List.rev_append syms !local_sig
      | Some (Some (`Include inc_str)) ->
          (* Resolve include path relative to current file *)
          let target = Fpath.((cwd // v inc_str) |> normalize) in
          let inc_path = get_logical_path (root_abs, target) in
          includes := inc_path :: !includes
      | Some None -> raise Exit  (* EOF *)
      | None -> raise Exit  (* Parse error *)
    done; assert false
    with
    | Exit -> close_in ch
    | exn -> close_in ch; raise exn
  in
  let _ = result in
  {
    fpr_path = get_logical_path (root_abs, fp_abs);
    fpr_file = fp_key;
    fpr_includes = List.rev !includes;
    fpr_sig = unique (List.rev !local_sig);
  }

(* Collect all .eo files in a directory *)
let collect_eo_files (dir : string) : string list =
  let dir_abs = to_absolute (Fpath.v dir) in
  let dir_str = Fpath.to_string dir_abs in
  List.filter
    (fun fp -> Filename.check_suffix fp ".eo")
    (dir_contents dir_str)

(* Build the signature graph from a directory *)
let build_sig_graph (root : string) : sig_graph =
  let root_abs = to_absolute (Fpath.v root) in
  let root_str = Fpath.to_string root_abs in
  let files = collect_eo_files root_str in

  (* Parse all files to get file_parse_results *)
  let parse_results = List.map (parse_file_local root_str) files in

  (* Build the graph *)
  List.fold_left (fun graph fpr ->
    let node = {
      node_path = fpr.fpr_path;
      node_file = fpr.fpr_file;
      node_includes = fpr.fpr_includes;
      node_sig = fpr.fpr_sig;
    } in
    PathMap.add fpr.fpr_path node graph
  ) PathMap.empty parse_results

(* Check if the graph is a DAG (no cycles) *)
let check_dag (graph : sig_graph) : (unit, path list) result =
  let visiting = Hashtbl.create 16 in
  let visited = Hashtbl.create 16 in

  let rec visit path ancestors =
    if Hashtbl.mem visited path then Ok ()
    else if Hashtbl.mem visiting path then
      (* Cycle detected - return the cycle *)
      Error (path :: ancestors)
    else begin
      Hashtbl.add visiting path ();
      match PathMap.find_opt path graph with
      | None ->
          Hashtbl.add visited path ();
          Ok ()
      | Some node ->
          let check_child p =
            match visit p (path :: ancestors) with
            | Ok () -> Ok ()
            | Error cycle -> Error cycle
          in
          match List.fold_left (fun acc p ->
            match acc with
            | Error _ -> acc
            | Ok () -> check_child p
          ) (Ok ()) node.node_includes with
          | Error cycle -> Error cycle
          | Ok () ->
              Hashtbl.remove visiting path;
              Hashtbl.add visited path ();
              Ok ()
    end
  in
  PathMap.fold (fun path _ acc ->
    match acc with
    | Error _ -> acc
    | Ok () -> visit path []
  ) graph (Ok ())
