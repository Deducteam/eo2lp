open Syntax_eo
open Parse_eo
open Main


(* open Elaborate *)
let cpc_root  = "../cvc5/proofs/eo/cpc"
let cpc_mini  =
  List.map (fun fp -> Filename.concat cpc_root fp)
    [
      "programs/Utils.eo";
      "theories/Builtin.eo";
      (* "rules/Builtin.eo"; *)
    ]

let cpc_commands : command list =
  List.concat_map parse_eo_file cpc_mini

let proc_cpc : unit =
  List.iter proc_eo_file cpc_mini

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
