(* test_sig_graph.ml — Signature graph construction and topological sort tests *)

open Eo2lp
open Syntax_eo
open Test_util

module LP = Api_lp

(* ============================================================
   Helpers
   ============================================================ *)

let write_eo dir rel_path content =
  let fp = Filename.concat dir rel_path in
  LP.mkdir_p (Filename.dirname fp);
  let oc = open_out fp in
  output_string oc content;
  close_out oc

let path_names order =
  List.map (fun p -> String.concat "/" p) order

(* ============================================================
   Two-module graph
   ============================================================ *)

let test_two_modules () =
  section "Sig Graph: Two Modules";

  let dir = "_build/test_sig2" in
  LP.mkdir_p dir;
  write_eo dir "theories/Builtin.eo"
    "(declare-const Bool Type)\n(declare-const Int Type)\n";
  write_eo dir "theories/Arith.eo"
    "(include \"Builtin.eo\")\n(declare-const + (-> Int Int Int) :left-assoc)\n";

  let graph = Parse_eo.build_sig dir in
  let n_mods = PathMap.cardinal graph in
  check_true (Printf.sprintf "parsed %d modules" n_mods) (n_mods = 2);

  let order = topo_sort_graph graph in
  let names = path_names order in
  check_true "topo order: Builtin before Arith"
    (match names with
     | [a; b] -> a = "theories/Builtin" && b = "theories/Arith"
     | _ -> false);

  let arith_node = PathMap.find ["theories"; "Arith"] graph in
  check_true "Arith includes Builtin"
    (List.mem ["theories"; "Builtin"] arith_node.node_includes);

  let builtin_node = PathMap.find ["theories"; "Builtin"] graph in
  check_true "Builtin has 2 symbols" (List.length builtin_node.node_sig = 2);
  check_true "Arith has 1 symbol" (List.length arith_node.node_sig = 1)

(* ============================================================
   Three-module chain: C <- B <- A
   ============================================================ *)

let test_three_chain () =
  section "Sig Graph: Three-Module Chain";

  let dir = "_build/test_sig3" in
  LP.mkdir_p dir;
  write_eo dir "t/C.eo" "(declare-const C_sym Type)\n";
  write_eo dir "t/B.eo" "(include \"C.eo\")\n(declare-const B_sym Type)\n";
  write_eo dir "t/A.eo" "(include \"B.eo\")\n(declare-const A_sym Type)\n";

  let graph = Parse_eo.build_sig dir in
  check_true "3 modules" (PathMap.cardinal graph = 3);

  let order = topo_sort_graph graph in
  let names = path_names order in
  check_true "topo order: C, B, A"
    (match names with
     | [a; b; c] -> a = "t/C" && b = "t/B" && c = "t/A"
     | _ -> false)

(* ============================================================
   Diamond dependency: A -> B, A -> C, B -> D, C -> D
   ============================================================ *)

let test_diamond () =
  section "Sig Graph: Diamond Dependency";

  let dir = "_build/test_sig_diamond" in
  LP.mkdir_p dir;
  write_eo dir "m/D.eo" "(declare-const D_sym Type)\n";
  write_eo dir "m/B.eo" "(include \"D.eo\")\n(declare-const B_sym Type)\n";
  write_eo dir "m/C.eo" "(include \"D.eo\")\n(declare-const C_sym Type)\n";
  write_eo dir "m/A.eo" "(include \"B.eo\")\n(include \"C.eo\")\n(declare-const A_sym Type)\n";

  let graph = Parse_eo.build_sig dir in
  check_true "4 modules" (PathMap.cardinal graph = 4);

  let order = topo_sort_graph graph in
  let names = path_names order in
  (* D must come before B and C; B and C before A *)
  let idx_of n = match List.find_index (fun x -> x = n) names with
    | Some i -> i | None -> -1 in
  let d = idx_of "m/D" in
  let b = idx_of "m/B" in
  let c = idx_of "m/C" in
  let a = idx_of "m/A" in
  check_true "D before B" (d < b);
  check_true "D before C" (d < c);
  check_true "B before A" (b < a);
  check_true "C before A" (c < a);
  check_true "D appears once" (List.length (List.filter ((=) "m/D") names) = 1)

(* ============================================================
   Cycle detection
   ============================================================ *)

let test_cycle_detection () =
  section "Sig Graph: Cycle Detection";

  let dir = "_build/test_sig_cycle" in
  LP.mkdir_p dir;
  write_eo dir "c/X.eo" "(include \"Y.eo\")\n(declare-const X_sym Type)\n";
  write_eo dir "c/Y.eo" "(include \"X.eo\")\n(declare-const Y_sym Type)\n";

  let graph = Parse_eo.build_sig dir in
  let result = Parse_eo.check_dag graph in
  check_true "cycle detected"
    (match result with Error _ -> true | Ok () -> false)

(* ============================================================
   full_sig_at: transitive includes
   ============================================================ *)

let test_full_sig_at () =
  section "Sig Graph: full_sig_at";

  let dir = "_build/test_sig_full" in
  LP.mkdir_p dir;
  write_eo dir "f/Base.eo" "(declare-const base_s Type)\n";
  write_eo dir "f/Mid.eo" "(include \"Base.eo\")\n(declare-const mid_s Type)\n";
  write_eo dir "f/Top.eo" "(include \"Mid.eo\")\n(declare-const top_s Type)\n";

  let graph = Parse_eo.build_sig dir in

  (* full_sig_at Top should include all three modules' symbols *)
  let full = full_sig_at graph ["f"; "Top"] in
  let names = List.map fst full in
  check_true "full_sig has base_s" (List.mem "base_s" names);
  check_true "full_sig has mid_s" (List.mem "mid_s" names);
  check_true "full_sig has top_s" (List.mem "top_s" names);

  (* full_sig_at Base should only have base_s *)
  let base_full = full_sig_at graph ["f"; "Base"] in
  let base_names = List.map fst base_full in
  check_true "base full_sig has base_s" (List.mem "base_s" base_names);
  check_true "base full_sig lacks mid_s" (not (List.mem "mid_s" base_names))

(* ============================================================
   Symbol deduplication
   ============================================================ *)

let test_dedup () =
  section "Sig Graph: Deduplication";

  let dir = "_build/test_sig_dedup" in
  LP.mkdir_p dir;
  (* Same symbol declared twice in one file *)
  write_eo dir "d/Dup.eo"
    "(declare-const foo Bool)\n(declare-const foo Bool)\n(declare-const bar Int)\n";

  let graph = Parse_eo.build_sig dir in
  let node = PathMap.find ["d"; "Dup"] graph in
  check_true "dedup: 2 unique symbols" (List.length node.node_sig = 2)

(* ============================================================
   Main
   ============================================================ *)

let () =
  test_two_modules ();
  test_three_chain ();
  test_diamond ();
  test_cycle_detection ();
  test_full_sig_at ();
  test_dedup ();
  summary ()
