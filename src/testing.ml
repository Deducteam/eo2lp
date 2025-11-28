open Main

(* open Elaborate *)
let cpc_root  = "../cvc5/proofs/eo/cpc"
let cpc_mini  =
  let con fp = Filename.concat cpc_root fp in
  let fps = ["programs/Utils.eo"; "theories/Builtin.eo"] in
  List.map con fps

(* let cpc_commands : command list =
  List.concat_map parse_eo_file cpc_mini *)

let write_line ch str =
  if str = "" then
    ()
  else
    output_string ch str;
    output_char ch '\n'

let write_lps ch lps =
  let f lp = write_line ch (LP.lp_command_str lp)
  in List.iter f lps

let proc_cpc : unit =
  let
    lps = List.concat_map proc_eo_file cpc_mini and
    ch = open_out "lp/out.lp" and
    reqs = [
      LP.Require ["Logic.U.Set"; "Logic.U.Arrow"];
      LP.Require ["eo2lp.Core"]
    ]
  in
    write_lps ch reqs;
    List.iter (write_lps ch) lps;
    close_out ch;


(* let test_elab_tms : eterm list =
  let ps = parse_eo_params
    "((x Bool) (y Bool) (z Bool :list) (w Bool :list))"
  in
  let ts =
    List.map parse_eo_term
    [
      "(or x y)";
      "(or x z)";
      "(or x z y)";
      "(or x)";
      "(or z)";
      "(or z y w x)";
    ]
  in
    Printf.printf
      "\nTesting elaboration of `:right-assoc-nil` constants:\n";
    List.map
    (fun t ->
      let t' = elab cpc_judgements ps t in
      Printf.printf "%s\n" (eterm_str t'); t')
    ts *)

(* let test_elab_tys : eterm list =
  let ps = parse_eo_params
    "((T1 Type) (T2 Type))"
  in
  let ts =
    List.map parse_eo_term
    [
      "T1";
      "Type";
      "(-> T1 T2 T2)";
      "(-> T1 T2 Type)";
      "(-> (-> T1 T2) Type)"
    ]
  in
    Printf.printf
      "\nTesting elaboration of arrow types.\n";
    List.map
    (fun t ->
      let t' = elab cpc_judgements ps t in
      Printf.printf "%s\n" (eterm_str t'); t')
    ts

let test_lp_tms =
  Printf.printf "\nTesting translation to LambdaPi terms:\n";
  List.map
    (fun t ->
      let t' = Translate.translate_tm t in
      Printf.printf "%s\n" (Syntax_lp.term_str t');
      t')
    test_elab_tms

let test_lp_tys =
  Printf.printf "\nTesting translation to LambdaPi types:\n";
  List.map
    (fun t ->
      let t' = Translate.translate_ty t in
      Printf.printf "%s\n" (Syntax_lp.term_str t');
      t')
    test_elab_tys *)
