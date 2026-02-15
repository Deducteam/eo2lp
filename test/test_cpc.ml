(* test_cpc.ml — Per-module tests for the CPC translation pipeline.

   For each CPC module, we:
   1. Verify the generated .lp file exists with expected symbols/rules
   2. Run lambdapi check -c -w on the generated .lp file *)

open Test_util

(* ============================================================
   Infrastructure
   ============================================================ *)

let build_dir = "test/cpc"

(** Read a generated .lp file *)
let read_lp rel_path =
  let fp = Filename.concat build_dir rel_path in
  if not (Sys.file_exists fp) then
    failwith (Printf.sprintf "File not found: %s" fp);
  let ic = open_in fp in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  Bytes.to_string s

(** Check a generated .lp file with lambdapi check -c -w *)
let check_lp_file path =
  let lp_file = Filename.concat build_dir (path ^ ".lp") in
  if not (Sys.file_exists lp_file) then begin
    Printf.printf "    file not found: %s\n" lp_file;
    false
  end else begin
    let rel_path = path ^ ".lp" in
    let cmd =
      Printf.sprintf
        "cd %s && NO_COLOR=1 timeout --signal=KILL 30 lambdapi check -c -w %s 2>&1"
        (Filename.quote build_dir) (Filename.quote rel_path)
    in
    let ic = Unix.open_process_in cmd in
    let buf = Buffer.create 256 in
    (try while true do Buffer.add_channel buf ic 1 done with End_of_file -> ());
    let status = Unix.close_process_in ic in
    let output = Buffer.contents buf |> String.trim in
    let ok = match status with Unix.WEXITED 0 -> true | _ -> false in
    if not ok then
      Printf.printf "    lambdapi: %s\n" output;
    ok
  end

(** Check if a string starts with a prefix *)
let starts_with s prefix =
  String.length s >= String.length prefix &&
  String.sub s 0 (String.length prefix) = prefix

(** Count lines starting with any of the given prefixes *)
let count_lines_with_prefix content prefixes =
  let lines = String.split_on_char '\n' content in
  List.fold_left (fun acc line ->
    if List.exists (starts_with line) prefixes then acc + 1 else acc
  ) 0 lines

let count_symbols content =
  count_lines_with_prefix content
    ["constant symbol "; "sequential symbol "; "symbol "]

let count_rules content =
  count_lines_with_prefix content ["rule "; "with "]

(** Check that a string contains a substring *)
let has_substr haystack needle =
  try ignore (Str.search_forward (Str.regexp_string needle) haystack 0); true
  with Not_found -> false

(** Run all checks for a single CPC module *)
let check_module ~name ~path ~min_symbols ~min_rules =
  subsection name;

  (* 1. File exists *)
  let lp_path = path ^ ".lp" in
  let full_path = Filename.concat build_dir lp_path in
  check_true (name ^ ": file exists") (Sys.file_exists full_path);

  if Sys.file_exists full_path then begin
    let content = read_lp lp_path in

    (* 2. Symbol and rule counts (minimum thresholds) *)
    let n_sym = count_symbols content in
    check_true
      (Printf.sprintf "%s: >= %d symbols (got %d)" name min_symbols n_sym)
      (n_sym >= min_symbols);

    let n_rules = count_rules content in
    check_true
      (Printf.sprintf "%s: >= %d rules (got %d)" name min_rules n_rules)
      (n_rules >= min_rules);

    (* 3. Check generated .lp with lambdapi *)
    check_true (name ^ ": lambdapi check") (check_lp_file path)
  end

(* ============================================================
   Theories
   ============================================================ *)

let test_theories () =
  section "CPC Theories";

  check_module
    ~name:"theories/Builtin"
    ~path:"theories/Builtin"
    ~min_symbols:9
    ~min_rules:2;

  check_module
    ~name:"theories/Arith"
    ~path:"theories/Arith"
    ~min_symbols:24
    ~min_rules:16;

  check_module
    ~name:"theories/Ints"
    ~path:"theories/Ints"
    ~min_symbols:10
    ~min_rules:0;

  check_module
    ~name:"theories/Arrays"
    ~path:"theories/Arrays"
    ~min_symbols:4
    ~min_rules:0;

  check_module
    ~name:"theories/Quantifiers"
    ~path:"theories/Quantifiers"
    ~min_symbols:4
    ~min_rules:1;

  check_module
    ~name:"theories/Sets"
    ~path:"theories/Sets"
    ~min_symbols:13
    ~min_rules:0

(* ============================================================
   Programs
   ============================================================ *)

let test_programs () =
  section "CPC Programs";

  check_module
    ~name:"programs/Utils"
    ~path:"programs/Utils"
    ~min_symbols:17
    ~min_rules:16;

  check_module
    ~name:"programs/Nary"
    ~path:"programs/Nary"
    ~min_symbols:2
    ~min_rules:4;

  check_module
    ~name:"programs/Arith"
    ~path:"programs/Arith"
    ~min_symbols:12
    ~min_rules:4;

  check_module
    ~name:"programs/AciNorm"
    ~path:"programs/AciNorm"
    ~min_symbols:7
    ~min_rules:12;

  check_module
    ~name:"programs/DistinctValues"
    ~path:"programs/DistinctValues"
    ~min_symbols:6
    ~min_rules:15;

  check_module
    ~name:"programs/PolyNorm"
    ~path:"programs/PolyNorm"
    ~min_symbols:2
    ~min_rules:2;

  check_module
    ~name:"programs/Quantifiers"
    ~path:"programs/Quantifiers"
    ~min_symbols:6
    ~min_rules:14

(* ============================================================
   Rules
   ============================================================ *)

let test_rules () =
  section "CPC Rules";

  check_module
    ~name:"rules/Builtin"
    ~path:"rules/Builtin"
    ~min_symbols:7
    ~min_rules:7;

  check_module
    ~name:"rules/Booleans"
    ~path:"rules/Booleans"
    ~min_symbols:76
    ~min_rules:29;

  check_module
    ~name:"rules/Arith"
    ~path:"rules/Arith"
    ~min_symbols:25
    ~min_rules:47;

  check_module
    ~name:"rules/Arrays"
    ~path:"rules/Arrays"
    ~min_symbols:6
    ~min_rules:2;

  check_module
    ~name:"rules/Uf"
    ~path:"rules/Uf"
    ~min_symbols:27
    ~min_rules:20;

  check_module
    ~name:"rules/Sets"
    ~path:"rules/Sets"
    ~min_symbols:11
    ~min_rules:14;

  check_module
    ~name:"rules/Quantifiers"
    ~path:"rules/Quantifiers"
    ~min_symbols:29
    ~min_rules:27;

  check_module
    ~name:"rules/Rewrites"
    ~path:"rules/Rewrites"
    ~min_symbols:115
    ~min_rules:10

(* ============================================================
   Top-level Cpc module
   ============================================================ *)

let test_cpc () =
  section "CPC Top-Level";

  check_module
    ~name:"Cpc"
    ~path:"Cpc"
    ~min_symbols:18
    ~min_rules:39

(* ============================================================
   Structural checks across all modules
   ============================================================ *)

let test_structure () =
  section "CPC Structure";

  (* All 21 modules + Prelude should be present *)
  let expected_files = [
    "Prelude.lp";
    "theories/Builtin.lp"; "theories/Arith.lp"; "theories/Ints.lp";
    "theories/Arrays.lp"; "theories/Quantifiers.lp"; "theories/Sets.lp";
    "programs/Utils.lp"; "programs/Nary.lp"; "programs/Arith.lp";
    "programs/AciNorm.lp"; "programs/DistinctValues.lp";
    "programs/PolyNorm.lp"; "programs/Quantifiers.lp";
    "rules/Builtin.lp"; "rules/Booleans.lp"; "rules/Arith.lp";
    "rules/Arrays.lp"; "rules/Uf.lp"; "rules/Sets.lp";
    "rules/Quantifiers.lp"; "rules/Rewrites.lp";
    "Cpc.lp";
  ] in
  List.iter (fun f ->
    let fp = Filename.concat build_dir f in
    check_true
      (Printf.sprintf "exists: %s" f)
      (Sys.file_exists fp)
  ) expected_files;

  (* Each module (except Prelude) should require open its dependencies *)
  let check_requires path expected_dep =
    let content = read_lp path in
    check_true
      (Printf.sprintf "%s requires %s" path expected_dep)
      (has_substr content (Printf.sprintf "require open %s" expected_dep))
  in
  check_requires "theories/Builtin.lp" "cpc.programs.Utils";
  check_requires "theories/Arith.lp" "cpc.theories.Builtin";
  check_requires "theories/Ints.lp" "cpc.theories.Arith";
  check_requires "theories/Arrays.lp" "cpc.theories.Builtin";
  check_requires "programs/Utils.lp" "cpc.Prelude";
  check_requires "programs/Nary.lp" "cpc.theories.Arith";

  (* No module should have empty content (beyond the require line) *)
  List.iter (fun f ->
    if f <> "Prelude.lp" then begin
      let content = read_lp f in
      let lines = String.split_on_char '\n' content in
      let non_empty = List.filter (fun l ->
        let t = String.trim l in t <> "" && not (has_substr t "require open")
      ) lines in
      check_true
        (Printf.sprintf "%s has content beyond requires" f)
        (List.length non_empty > 0)
    end
  ) expected_files

(* ============================================================
   Proof encoding regression tests
   ============================================================ *)

let test_proofs () =
  section "Proof Encoding";

  (* Test proof encoding by running eo2lp --proofs on small test fixtures.
     This exercises the full encode_proof pipeline including:
     - assume/step encoding
     - assumption stack (push/pop)
     - define expansion
     - rule application with premises and args *)
  let test_proofs_dir = "test/proofs" in
  if not (Sys.file_exists test_proofs_dir) then begin
    Printf.printf "    no test proofs directory found, skipping\n";
  end else begin
    let proof_files =
      Sys.readdir test_proofs_dir
      |> Array.to_list
      |> List.filter (fun f -> Filename.check_suffix f ".eo")
      |> List.sort String.compare
    in
    check_true "test proof fixtures exist"
      (List.length proof_files >= 1);

    (* Run eo2lp with --proofs on the test fixtures *)
    let cmd =
      Printf.sprintf
        "cd %s && dune exec eo2lp -- -o %s --proofs %s --no-color 2>&1"
        (Filename.quote (Sys.getcwd ()))
        (Filename.quote build_dir)
        (Filename.quote test_proofs_dir)
    in
    let ic = Unix.open_process_in cmd in
    let buf = Buffer.create 1024 in
    (try while true do Buffer.add_channel buf ic 1 done with End_of_file -> ());
    let status = Unix.close_process_in ic in
    let output = Buffer.contents buf in

    let exit_ok = match status with Unix.WEXITED 0 -> true | _ -> false in

    (* Check that encoding succeeded *)
    check_true "eo2lp --proofs exits 0" exit_ok;

    if not exit_ok then
      Printf.printf "    output:\n%s\n" output;

    (* Check that generated .lp files exist for each proof *)
    List.iter (fun f ->
      let name = Filename.chop_extension f in
      let lp_path = Filename.concat build_dir
        (Printf.sprintf "proofs/%s.lp" name) in
      check_true
        (Printf.sprintf "proof %s: .lp file generated" name)
        (Sys.file_exists lp_path);

      (* Verify generated file has content and type-checks *)
      if Sys.file_exists lp_path then begin
        let content = read_lp (Printf.sprintf "proofs/%s.lp" name) in
        let n_sym = count_symbols content in
        check_true
          (Printf.sprintf "proof %s: has symbols (got %d)" name n_sym)
          (n_sym >= 1);
        check_true
          (Printf.sprintf "proof %s: lambdapi check" name)
          (check_lp_file (Printf.sprintf "proofs/%s" name))
      end
    ) proof_files;

    (* Check output indicates no failures *)
    let has_fail = has_substr output "FAIL" || has_substr output "failed" in
    check_true "no proof encoding/checking failures" (not has_fail)
  end

(* ============================================================
   Main
   ============================================================ *)

let () =
  test_structure ();
  test_theories ();
  test_programs ();
  test_rules ();
  test_cpc ();
  test_proofs ();
  summary ()
