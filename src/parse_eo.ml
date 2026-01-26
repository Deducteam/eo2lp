(* parse_eo.ml
   Eunoia file parsing and signature graph construction *)

open Lexing
open Syntax_eo

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

let resolve (root, fp, str) =
  let rt_abs = to_absolute (Fpath.v root) in
  let fp_abs = to_absolute (Fpath.v fp) in
  let cwd = Fpath.parent fp_abs in
  let target = Fpath.((cwd // v str) |> normalize) in
  get_logical_path (rt_abs, target)

(* Basic parsers *)

let parse_eo_term str =
  let lx = Lexing.from_string str in
  try Parser.term Lexer.token lx
  with Parser.Error -> failwith "error parsing term"

let parse_eo_params str =
  let lx = Lexing.from_string str in
  try Parser.params Lexer.token lx
  with Parser.Error -> failwith "error parsing params"

let parse_command lx =
  try Some (Parser.toplevel_eof Lexer.token lx)
  with Parser.Error ->
    let pos = lx.lex_curr_p in
    let file = if pos.pos_fname = "" then "<string>" else pos.pos_fname in
    let token = Lexing.lexeme lx in
    let token_display = if String.length token > 20 then String.sub token 0 17 ^ "..." else token in
    Printf.eprintf
      "Parse error in %s at line %d, column %d: unexpected token '%s'\n%!"
      file
      pos.pos_lnum
      (pos.pos_cnum - pos.pos_bol + 1)
      token_display;
    Parse_ctx.had_parse_error := true;
    None

(* Parse cache *)

let parse_cache : (string, signature) Hashtbl.t =
  Hashtbl.create 32

let clear_parse_cache () = Hashtbl.clear parse_cache

(* String parsing *)

let parse_eo_string src =
  let lx = Lexing.from_string src in
  let _sig = ref [] in
  try
    while true do
      match parse_command lx with
      | Some (Some syms) ->
        _sig := List.rev_append syms !_sig
      | Some None -> raise Exit
      | None -> raise Exit
    done;
    assert false
  with Exit -> List.rev !_sig

(* Parse a standalone file (for proof scripts) *)
let parse_file path =
  if not (Sys.file_exists path) then
    failwith (Printf.sprintf "File not found: %s" path);
  let ch =
    try open_in path
    with Sys_error msg -> failwith (Printf.sprintf "Cannot open %s: %s" path msg)
  in
  let lx = Lexing.from_channel ch in
  lx.lex_curr_p <- { lx.lex_curr_p with pos_fname = path };
  let _sig = ref [] in
  let parse_errors = ref 0 in
  let result =
    try
      while true do
        match parse_command lx with
        | Some (Some syms) ->
          _sig := List.rev_append syms !_sig
        | Some None -> raise Exit
        | None ->
          incr parse_errors;
          if !parse_errors > 10 then raise Exit
      done;
      assert false
    with
    | Exit -> close_in ch; List.rev !_sig
    | exn  -> close_in ch; raise exn
  in
  result

(* Core prelude *)

let init_core_prelude () =
  let core_sig = parse_eo_string Syntax_eo.core_eo_source in
  Syntax_eo.set_core_prelude core_sig

let core_prelude_initialized = ref false

let ensure_core_prelude () =
  if not !core_prelude_initialized then begin
    init_core_prelude ();
    core_prelude_initialized := true
  end

(* Deduplication *)

let unique sgn =
  let seen = Hashtbl.create (List.length sgn) in
  List.filter (fun (s, c) ->
    let key = (s, c) in
    let fresh = not (Hashtbl.mem seen key) in
    if fresh then Hashtbl.add seen key ();
    fresh)
  sgn

(* File parsing *)

let rec parse_eo_file root fp =
  let fp_abs = to_absolute (Fpath.v fp) in
  let fp_key = Fpath.to_string fp_abs in

  match Hashtbl.find_opt parse_cache fp_key with
  | Some cached -> cached
  | None ->
    let ch = open_in fp in
    let lx = Lexing.from_channel ch in
    let _sig = ref [] in

    let cwd = Fpath.parent fp_abs in
    let old_callback = !Parse_ctx.parse_include_callback in
    Parse_ctx.parse_include_callback := (fun include_path ->
      let target =
        Fpath.((cwd // v include_path) |> normalize)
      in
      parse_eo_file root (Fpath.to_string target));

    let result =
      try
        while true do
          match parse_command lx with
          | Some (Some syms) ->
            _sig := List.rev_append syms !_sig
          | Some None -> raise Exit
          | None -> raise Exit
        done;
        assert false
      with
      | Exit -> close_in ch; List.rev !_sig
      | exn  -> close_in ch; raise exn
    in
    Parse_ctx.parse_include_callback := old_callback;
    let unique_result = unique result in
    Hashtbl.add parse_cache fp_key unique_result;
    unique_result

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

let parse_eo_dir root_str =
  let root = to_absolute (Fpath.v root_str) in
  let root_abs_str = Fpath.to_string root in
  let fps =
    List.filter
      (fun fp -> Filename.check_suffix fp ".eo")
      (dir_contents root_abs_str)
  in
  let signatures =
    List.map (fun fp_str ->
      parse_eo_file root_abs_str fp_str)
    fps
  in
  List.concat signatures

(* V2 parsing: builds signature graph *)

let parse_command_v2 lx =
  try Some (Parser.toplevel_eof_v2 Lexer.token lx)
  with Parser.Error ->
    let pos = lx.lex_curr_p in
    let file = if pos.pos_fname = "" then "<string>" else pos.pos_fname in
    let token = Lexing.lexeme lx in
    let token_display = if String.length token > 20 then String.sub token 0 17 ^ "..." else token in
    Printf.eprintf
      "Parse error in %s at line %d, column %d: unexpected token '%s'\n%!"
      file
      pos.pos_lnum
      (pos.pos_cnum - pos.pos_bol + 1)
      token_display;
    Parse_ctx.had_parse_error := true;
    None

let parse_file_local root fp =
  let root_abs = to_absolute (Fpath.v root) in
  let fp_abs = to_absolute (Fpath.v fp) in
  let fp_key = Fpath.to_string fp_abs in
  let cwd = Fpath.parent fp_abs in

  let ch = open_in fp_key in
  let lx = Lexing.from_channel ch in
  let local_sig = ref [] in
  let includes = ref [] in

  let result =
    try
      while true do
        match parse_command_v2 lx with
        | Some (Some (`Sig syms)) ->
          local_sig := List.rev_append syms !local_sig
        | Some (Some (`Include inc_str)) ->
          let target =
            Fpath.((cwd // v inc_str) |> normalize)
          in
          let inc_path = get_logical_path (root_abs, target) in
          includes := inc_path :: !includes
        | Some None -> raise Exit
        | None -> raise Exit
      done;
      assert false
    with
    | Exit -> close_in ch
    | exn  -> close_in ch; raise exn
  in
  let _ = result in
  {
    fpr_path     = get_logical_path (root_abs, fp_abs);
    fpr_file     = fp_key;
    fpr_includes = List.rev !includes;
    fpr_sig      = unique (List.rev !local_sig);
  }

let collect_eo_files dir =
  let dir_abs = to_absolute (Fpath.v dir) in
  let dir_str = Fpath.to_string dir_abs in
  List.filter
    (fun fp -> Filename.check_suffix fp ".eo")
    (dir_contents dir_str)

let build_sig_graph root time_log_opt =
  ensure_core_prelude ();
  let root_abs = to_absolute (Fpath.v root) in
  let root_str = Fpath.to_string root_abs in
  let files = collect_eo_files root_str in

  let timed f =
    let t0 = Sys.time () in
    let res = f () in
    let t1 = Sys.time () in
    (res, t1 -. t0)
  in

  let parse_results =
    List.map (fun file ->
      let res, time =
        timed (fun () -> parse_file_local root_str file)
      in
      (match time_log_opt with
       | Some log -> log := (res.fpr_file, time) :: !log
       | None -> ());
      res)
    files
  in

  List.fold_left (fun graph fpr ->
    let node = {
      node_path     = fpr.fpr_path;
      node_file     = fpr.fpr_file;
      node_includes = fpr.fpr_includes;
      node_sig      = fpr.fpr_sig;
    } in
    PathMap.add fpr.fpr_path node graph)
  PathMap.empty parse_results

(* Build a symbol graph from a directory of .eo files *)
let build_symbol_graph root =
  ensure_core_prelude ();
  let root_abs = to_absolute (Fpath.v root) in
  let root_str = Fpath.to_string root_abs in
  let files = collect_eo_files root_str in

  (* Parse all files *)
  let parse_results =
    List.map (fun file -> parse_file_local root_str file) files
  in

  (* Convert to (path, signature) list for build_graph *)
  let modules = List.map (fun fpr ->
    (fpr.fpr_path, fpr.fpr_sig)
  ) parse_results in

  (* Build the symbol graph with resolved dependencies *)
  Syntax_eo.build_graph modules

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
          | Ok ()      -> Ok ()
          | Error cyc  -> Error cyc
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
   Job file parsing
   ============================================================ *)

(* Simple S-expression parser for job files *)
let parse_job_file (path : string) : Syntax_eo.job =
  let content = In_channel.with_open_text path In_channel.input_all in

  (* Helper to extract value from (key value) pattern *)
  let extract_value key =
    (* In Str: \( \) are grouping, literal parens don't need escaping in char class *)
    let re = Str.regexp (key ^ "[ \t\n]+\\([^ \t\n()]+\\)") in
    try
      ignore (Str.search_forward re content 0);
      Some (Str.matched_group 1 content)
    with Not_found -> None
  in

  (* Helper to extract nested value from (key (subkey value)) pattern *)
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
      (* Try to match (proofs (files f1 f2 ...)) *)
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

(* Find all .job files in a directory *)
let find_job_files (dir : string) : string list =
  Sys.readdir dir
  |> Array.to_list
  |> List.filter (fun f -> Filename.check_suffix f ".job")
  |> List.map (Filename.concat dir)
  |> List.sort String.compare
