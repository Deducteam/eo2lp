(* Test suite for signature graph (DAG) functionality *)

open Eo2lp.Parse_eo
open Eo2lp.Syntax_eo

(* ANSI color codes *)
let green s = Printf.sprintf "\027[32m%s\027[0m" s
let red s = Printf.sprintf "\027[31m%s\027[0m" s
let bold s = Printf.sprintf "\027[1m%s\027[0m" s
let dim s = Printf.sprintf "\027[2m%s\027[0m" s

let println s = print_string s; print_newline (); flush stdout

let () =
  println "";
  println "======================================";
  println (Printf.sprintf "  %s" (bold "Signature Graph Tests"));
  println "======================================";
  println "";

  (* Test 1: Build graph from cpc-mini *)
  println (Printf.sprintf "  %s Building signature graph from cpc-mini..." (dim "[1]"));
  let graph = build_sig_graph "./cpc-mini" in
  let node_count = PathMap.cardinal graph in
  println (Printf.sprintf "      %s Found %d nodes" (green "OK") node_count);
  assert (node_count > 0);

  (* Test 2: Check DAG property *)
  println (Printf.sprintf "  %s Checking DAG property (no cycles)..." (dim "[2]"));
  begin match check_dag graph with
  | Ok () ->
      println (Printf.sprintf "      %s Graph is a valid DAG" (green "OK"))
  | Error cycle ->
      println (Printf.sprintf "      %s Cycle detected: %s"
        (red "FAIL")
        (String.concat " -> " (List.map path_str cycle)));
      assert false
  end;

  (* Test 3: Topological sort *)
  println (Printf.sprintf "  %s Testing topological sort..." (dim "[3]"));
  let sorted = topo_sort graph in
  println (Printf.sprintf "      %s Sorted %d paths" (green "OK") (List.length sorted));
  assert (List.length sorted = node_count);

  (* Test 4: Check specific nodes exist *)
  println (Printf.sprintf "  %s Checking expected nodes exist..." (dim "[4]"));
  let expected_paths = [
    ["theories"; "Builtin"];
    ["theories"; "Arith"];
    ["programs"; "Utils"];
  ] in
  List.iter (fun path ->
    match PathMap.find_opt path graph with
    | Some node ->
        println (Printf.sprintf "      %s %s (%d symbols)"
          (green "OK") (path_str path) (List.length node.node_sig))
    | None ->
        println (Printf.sprintf "      %s %s not found" (red "FAIL") (path_str path));
        assert false
  ) expected_paths;

  (* Test 5: Check include dependencies *)
  println (Printf.sprintf "  %s Checking include dependencies..." (dim "[5]"));
  begin match PathMap.find_opt ["theories"; "Arith"] graph with
  | Some node ->
      let has_builtin = List.mem ["theories"; "Builtin"] node.node_includes in
      if has_builtin then
        println (Printf.sprintf "      %s theories.Arith includes theories.Builtin" (green "OK"))
      else begin
        println (Printf.sprintf "      %s theories.Arith should include theories.Builtin" (red "FAIL"));
        assert false
      end
  | None ->
      println (Printf.sprintf "      %s theories.Arith not found" (red "FAIL"));
      assert false
  end;

  (* Test 6: Full signature at node *)
  println (Printf.sprintf "  %s Testing full_sig_at..." (dim "[6]"));
  let full_sig = full_sig_at graph ["theories"; "Arith"] in
  println (Printf.sprintf "      %s Full signature at theories.Arith: %d symbols"
    (green "OK") (List.length full_sig));
  assert (List.length full_sig > 0);

  (* Test 7: Flatten graph *)
  println (Printf.sprintf "  %s Testing flatten_graph..." (dim "[7]"));
  let flat_sig = flatten_graph graph in
  println (Printf.sprintf "      %s Flattened signature: %d symbols"
    (green "OK") (List.length flat_sig));
  assert (List.length flat_sig > 0);

  (* Summary *)
  println "";
  println "======================================";
  println (Printf.sprintf "  %s All graph tests passed!" (green "SUCCESS"));
  println "======================================";
  println ""
