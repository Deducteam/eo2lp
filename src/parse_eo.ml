(* parse_eo.ml
   Eunoia file parsing and signature graph construction *)

open Lexing
open Syntax_eo

let had_parse_error : bool ref = ref false

(* Path utilities *)

let to_absolute p =
  if Fpath.is_abs p then p
  else Fpath.(v (Sys.getcwd ()) // p) |> Fpath.normalize

let get_logical_path (root, abs_fp) =
  match Fpath.relativize ~root abs_fp with
  | None ->
    Printf.ksprintf failwith
      "File %s is not inside root %s"
      (Fpath.to_string abs_fp) (Fpath.to_string root)
  | Some rel ->
    rel |> Fpath.rem_ext |> Fpath.segs

(* Basic term/param parsers for tests *)

let parse_eo_term str =
  let lx = Lexing.from_string str in
  try Parser.term Lexer.token lx
  with Parser.Error -> failwith "error parsing term"

let parse_eo_params str =
  let lx = Lexing.from_string str in
  try Parser.params Lexer.token lx
  with Parser.Error -> failwith "error parsing params"

(* Deduplication *)

let unique sgn =
  let seen = Hashtbl.create (List.length sgn) in
  List.filter (fun (s, c) ->
    let key = (s, c) in
    let fresh = not (Hashtbl.mem seen key) in
    if fresh then Hashtbl.add seen key ();
    fresh)
  sgn

(* Directory traversal *)

let dir_contents dir =
  let rec loop result = function
    | f :: fs when Sys.is_directory f ->
      Sys.readdir f
      |> Array.to_list
      |> List.map (Filename.concat f)
      |> List.append fs
      |> loop result
    | f :: fs ->
      loop (f :: result) fs
    | [] ->
      result
  in
  loop [] [dir]

(* Check if path contains "expert" directory *)
let is_expert_path fp root =
  match Fpath.relativize ~root:(to_absolute (Fpath.v root)) (to_absolute (Fpath.v fp)) with
  | None -> false
  | Some rel ->
    let segs = Fpath.segs rel in
    List.mem "expert" segs

(* Command parsing with error recovery *)

let parse_command lx =
  try Some (Parser.toplevel_eof Lexer.token lx)
  with Parser.Error ->
    let pos = lx.lex_curr_p in
    let file = if pos.pos_fname = "" then "<unknown>" else pos.pos_fname in
    let token = Lexing.lexeme lx in
    let token_display = if String.length token > 20 then String.sub token 0 17 ^ "..." else token in
    Printf.eprintf
      "Parse error in %s at line %d, column %d: unexpected token '%s'\n%!"
      file
      pos.pos_lnum
      (pos.pos_cnum - pos.pos_bol + 1)
      token_display;
    had_parse_error := true;
    None

(* Parse a single file and return a sig_node *)

let parse_file root fp : sig_node =
  let root_abs = to_absolute (Fpath.v root) in
  let fp_abs = to_absolute (Fpath.v fp) in
  let fp_key = Fpath.to_string fp_abs in
  let cwd = Fpath.parent fp_abs in

  let ch = open_in fp_key in
  let lx = Lexing.from_channel ch in
  lx.lex_curr_p <- { lx.lex_curr_p with pos_fname = fp_key };
  let local_sig = ref [] in
  let includes = ref [] in

  (try
    while true do
      match parse_command lx with
      | Some (Some (`Sig syms)) ->
        local_sig := List.rev_append syms !local_sig
      | Some (Some (`Include inc_str)) ->
        let target = Fpath.((cwd // v inc_str) |> normalize) in
        let inc_path = get_logical_path (root_abs, target) in
        includes := inc_path :: !includes
      | Some None -> raise Exit
      | None -> raise Exit
    done
  with
  | Exit -> close_in ch
  | exn  -> close_in ch; raise exn);

  {
    node_path     = get_logical_path (root_abs, fp_abs);
    node_file     = fp_key;
    node_includes = List.rev !includes;
    node_sig      = unique (List.rev !local_sig);
  }

(* Build a sig_graph from a directory of .eo files *)

let build_sig ?(include_expert=false) root : sig_graph =
  let root_abs = to_absolute (Fpath.v root) in
  let root_str = Fpath.to_string root_abs in
  let files =
    dir_contents root_str
    |> List.filter (fun fp ->
         Filename.check_suffix fp ".eo" &&
         (include_expert || not (is_expert_path fp root_str)))
  in

  let parse_results = List.map (fun file -> parse_file root_str file) files in

  List.fold_left (fun graph node ->
    PathMap.add node.node_path node graph)
  PathMap.empty parse_results

(* Check for cycles in the include graph *)

let check_dag graph =
  let visiting = Hashtbl.create 16 in
  let visited = Hashtbl.create 16 in

  let rec visit path ancestors =
    if Hashtbl.mem visited path then Ok ()
    else if Hashtbl.mem visiting path then
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
          | Ok ()     -> Ok ()
          | Error cyc -> Error cyc
        in
        match
          List.fold_left (fun acc p ->
            match acc with
            | Error _ -> acc
            | Ok ()   -> check_child p)
          (Ok ()) node.node_includes
        with
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
    | Ok ()   -> visit path [])
  graph (Ok ())

(* ============================================================
   Proof file parsing
   ============================================================ *)

(* Parse a single .eo proof file into a flat signature.
   Proof files have no includes — just declarations, defines, assumes, steps. *)
let parse_proof_file (filepath : string) : string * signature =
  let stem = Filename.chop_extension (Filename.basename filepath) in
  let ch = open_in filepath in
  let lx = Lexing.from_channel ch in
  lx.lex_curr_p <- { lx.lex_curr_p with pos_fname = filepath };
  let sig_ = ref [] in
  (try
    while true do
      match parse_command lx with
      | Some (Some (`Sig syms)) ->
        sig_ := List.rev_append syms !sig_
      | Some (Some (`Include _)) -> ()  (* ignore includes in proof files *)
      | Some None -> raise Exit
      | None -> raise Exit
    done
  with
  | Exit -> close_in ch
  | exn  -> close_in ch; raise exn);
  (stem, List.rev !sig_)

(* Parse all .eo files in a directory into a list of (name, signature) pairs *)
let parse_proof_dir (dir : string) : (string * signature) list =
  let files =
    Sys.readdir dir
    |> Array.to_list
    |> List.filter (fun f -> Filename.check_suffix f ".eo")
    |> List.sort String.compare
    |> List.map (Filename.concat dir)
  in
  List.map parse_proof_file files

(* ============================================================
   Job file parsing
   ============================================================ *)

let parse_job_file (path : string) : Syntax_eo.job =
  let content = In_channel.with_open_text path In_channel.input_all in

  let extract_value key =
    let re = Str.regexp (key ^ "[ \t\n]+\\([^ \t\n()]+\\)") in
    try
      ignore (Str.search_forward re content 0);
      Some (Str.matched_group 1 content)
    with Not_found -> None
  in

  let extract_nested key subkey =
    let re = Str.regexp (key ^ "[ \t\n]+(" ^ subkey ^ "[ \t\n]+\\([^ \t\n()]+\\))") in
    try
      ignore (Str.search_forward re content 0);
      Some (Str.matched_group 1 content)
    with Not_found -> None
  in

  let name = match extract_value "name" with
    | Some n -> n
    | None -> failwith (Printf.sprintf "Job file %s: missing (name ...)" path)
  in

  let logic = match extract_value "logic" with
    | Some l -> l
    | None -> failwith (Printf.sprintf "Job file %s: missing (logic ...)" path)
  in

  let proofs =
    match extract_nested "proofs" "dir" with
    | Some d -> Syntax_eo.ProofDir d
    | None ->
      let files_re = Str.regexp {|(proofs[ \t\n]+(files[ \t\n]+\([^)]+\)))|} in
      (try
        ignore (Str.search_forward files_re content 0);
        let fs = Str.matched_group 1 content in
        let files = String.split_on_char ' ' (String.trim fs)
                    |> List.filter (fun s -> s <> "") in
        Syntax_eo.ProofFiles files
      with Not_found ->
        failwith (Printf.sprintf "Job file %s: missing (proofs ...)" path))
  in

  { Syntax_eo.job_name = name; job_logic = logic; job_proofs = proofs }

let find_job_files (dir : string) : string list =
  Sys.readdir dir
  |> Array.to_list
  |> List.filter (fun f -> Filename.check_suffix f ".job")
  |> List.map (Filename.concat dir)
  |> List.sort String.compare
