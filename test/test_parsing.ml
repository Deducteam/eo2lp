(* test_parsing.ml — Lexer + Parser tests *)

open Eo2lp
open Syntax_eo
open Test_util

let p s = Pp_eo.term_str (Parse_eo.parse_eo_term s)
let eq = check_eq (fun s -> s)

let pp_params s =
  String.concat ", "
    (List.map (fun (n, t, _) -> Printf.sprintf "(%s %s)" n (Pp_eo.term_str t))
       (Parse_eo.parse_eo_params s))

let pp_params_attrs s =
  String.concat ", "
    (List.map (fun (n, t, atts) ->
       Printf.sprintf "(%s %s%s)" n (Pp_eo.term_str t)
         (if atts = [] then ""
          else " " ^ String.concat " " (List.map Pp_eo.symbol_attr_str atts)))
       (Parse_eo.parse_eo_params s))

(* ============================================================
   Terms
   ============================================================ *)

let test_terms () =
  section "Parsing: Terms";

  eq "symbol" ~input:"foo" ~expected:"foo" ~actual:(p "foo");
  eq "int literal" ~input:"42" ~expected:"42" ~actual:(p "42");
  eq "neg int" ~input:"-7" ~expected:"-7" ~actual:(p "-7");
  eq "zero" ~input:"0" ~expected:"0" ~actual:(p "0");
  eq "decimal" ~input:"3.14" ~expected:"3.14" ~actual:(p "3.14");
  eq "binary" ~input:"#b1010" ~expected:"" ~actual:(p "#b1010");
  eq "hex" ~input:"#xFF" ~expected:"" ~actual:(p "#xFF");
  eq "string" ~input:{|"hello"|} ~expected:{|"hello"|} ~actual:(p {|"hello"|});
  eq "apply" ~input:"(f x y)"
    ~expected:"(f x y)" ~actual:(p "(f x y)");
  eq "nested apply" ~input:"(f (g x) y)"
    ~expected:"(f (g x) y)" ~actual:(p "(f (g x) y)");
  eq "arrow 2" ~input:"(-> A B)"
    ~expected:"(-> A B)" ~actual:(p "(-> A B)");
  eq "arrow 3" ~input:"(-> A B C)"
    ~expected:"(-> A B C)" ~actual:(p "(-> A B C)");
  eq "HOL app" ~input:"(_ f x)"
    ~expected:"(_ f x)" ~actual:(p "(_ f x)");
  eq "binder" ~input:"(forall ((x Bool)) x)"
    ~expected:"(forall ((x Bool)) x)"
    ~actual:(p "(forall ((x Bool)) x)");
  eq "nested binder" ~input:"(forall ((x Bool) (y Int)) (and x y))"
    ~expected:"(forall ((x Bool), (y Int)) (and x y))"
    ~actual:(p "(forall ((x Bool) (y Int)) (and x y))");
  eq "Type" ~input:"Type" ~expected:"Type" ~actual:(p "Type");
  eq "eo builtin" ~input:"(eo::and x y)"
    ~expected:"(eo::and x y)" ~actual:(p "(eo::and x y)");
  eq "rational" ~input:"3/4" ~expected:"(mkrat 3 4)" ~actual:(p "3/4")

(* ============================================================
   Parameters
   ============================================================ *)

let test_params () =
  section "Parsing: Parameters";

  eq "single param" ~input:"((x Bool))"
    ~expected:"(x Bool)" ~actual:(pp_params "((x Bool))");
  eq "two params" ~input:"((x Bool) (y Int))"
    ~expected:"(x Bool), (y Int)"
    ~actual:(pp_params "((x Bool) (y Int))");
  eq "three params" ~input:"((a Type) (b Type) (c Bool))"
    ~expected:"(a Type), (b Type), (c Bool)"
    ~actual:(pp_params "((a Type) (b Type) (c Bool))");
  eq "empty params" ~input:"()"
    ~expected:""
    ~actual:(pp_params "()")

let test_param_attrs () =
  section "Parsing: Parameter Attributes";

  eq "implicit" ~input:"((T Type :implicit))"
    ~expected:"(T Type :implicit)"
    ~actual:(pp_params_attrs "((T Type :implicit))");
  eq "list" ~input:"((xs Bool :list))"
    ~expected:"(xs Bool :list)"
    ~actual:(pp_params_attrs "((xs Bool :list))");
  eq "opaque" ~input:"((n Int :opaque))"
    ~expected:"(n Int :opaque)"
    ~actual:(pp_params_attrs "((n Int :opaque))")

(* ============================================================
   Commands (via parse_file on temp files)
   ============================================================ *)

let write_temp_eo content =
  let dir = "_build/test_parse_tmp" in
  Api_lp.mkdir_p (Filename.concat dir "theories");
  let fp = Filename.concat dir "theories/Test.eo" in
  let oc = open_out fp in
  output_string oc content;
  close_out oc;
  (dir, fp)

let test_commands () =
  section "Parsing: Commands";

  (* declare-const *)
  let dir, fp = write_temp_eo "(declare-const foo Bool)\n" in
  let node = Parse_eo.parse_file dir fp in
  check_true "declare-const: 1 symbol" (List.length node.node_sig = 1);
  check_true "declare-const: name=foo"
    (match node.node_sig with
     | [("foo", Decl ([], Symbol "Bool", None))] -> true
     | _ -> false);

  (* declare-const with attribute *)
  let dir, fp = write_temp_eo
    "(declare-const and (-> Bool Bool Bool) :right-assoc-nil true)\n" in
  let node = Parse_eo.parse_file dir fp in
  check_true "declare-const with attr: name=and"
    (match node.node_sig with
     | [("and", Decl ([], _, Some (RightAssocNil (Symbol "true"))))] -> true
     | _ -> false);

  (* define *)
  let dir, fp = write_temp_eo "(define foo () 42)\n" in
  let node = Parse_eo.parse_file dir fp in
  check_true "define: name=foo"
    (match node.node_sig with
     | [("foo", Defn ([], Literal (Literal.Numeral 42), None))] -> true
     | _ -> false);

  (* define with params *)
  let dir, fp = write_temp_eo "(define bar ((x Bool)) x)\n" in
  let node = Parse_eo.parse_file dir fp in
  check_true "define with param"
    (match node.node_sig with
     | [("bar", Defn ([("x", Symbol "Bool", [])], Symbol "x", None))] -> true
     | _ -> false);

  (* program *)
  let dir, fp = write_temp_eo
    "(program $id ((x Bool)) :signature (Bool) Bool ((($id x) x)))\n" in
  let node = Parse_eo.parse_file dir fp in
  check_true "program: name=$id"
    (match node.node_sig with
     | [("$id", Prog _)] -> true
     | _ -> false);

  (* include *)
  let dir, _fp = write_temp_eo "(declare-const A Type)\n" in
  let fp2 = Filename.concat dir "theories/Test2.eo" in
  let oc = open_out fp2 in
  Printf.fprintf oc "(include \"Test.eo\")\n(declare-const B (-> A A))\n";
  close_out oc;
  let node2 = Parse_eo.parse_file dir fp2 in
  check_true "include: has dependency"
    (node2.node_includes <> []);
  check_true "include: 1 own symbol" (List.length node2.node_sig = 1);

  (* multiple symbols *)
  let dir, fp = write_temp_eo
    "(declare-const a Bool)\n(declare-const b Int)\n(declare-const c Type)\n" in
  let node = Parse_eo.parse_file dir fp in
  check_true "multiple: 3 symbols" (List.length node.node_sig = 3)

(* ============================================================
   Main
   ============================================================ *)

let () =
  test_terms ();
  test_params ();
  test_param_attrs ();
  test_commands ();
  summary ()
