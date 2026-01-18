(* ============================================================
   eo2lp: Translate Eunoia signatures to LambdaPi
   ============================================================ *)

module EO = struct
  include Parse_eo
  include Syntax_eo
  include Elaborate
end

module LP = struct
  include Syntax_lp
  include Api_lp
  include Encode
end

(* ============================================================
   CLI Configuration
   ============================================================ *)

type config = {
  input_dir : string option;
  output_dir : string option;
  verbose : bool;
}

let default_config = {
  input_dir = None;
  output_dir = None;
  verbose = false;
}

let config = ref default_config

let usage = "Usage: eo2lp -d <input_dir> -o <output_dir> [options]"

let speclist = [
  ("-d", Arg.String (fun s -> config := { !config with input_dir = Some s }),
   "<dir> Input directory containing .eo files");
  ("-o", Arg.String (fun s -> config := { !config with output_dir = Some s }),
   "<dir> Output directory for LambdaPi package");
  ("-v", Arg.Unit (fun () -> config := { !config with verbose = true }),
   " Verbose output");
]

(* ============================================================
   LambdaPi Package Generation
   ============================================================ *)

let mkdir_p dir =
  let rec aux dir =
    if not (Sys.file_exists dir) then begin
      aux (Filename.dirname dir);
      Sys.mkdir dir 0o755
    end
  in aux dir

let path_to_module pkg path = pkg ^ "." ^ String.concat "." path

let generate_pkg_file output_dir pkg_name =
  let oc = open_out (Filename.concat output_dir "lambdapi.pkg") in
  Printf.fprintf oc "package_name = %s\nroot_path = %s\n" pkg_name pkg_name;
  close_out oc

let prelude_content = {|require open
  Stdlib.Set
  Stdlib.HOL
  Stdlib.List
  Stdlib.String
  Stdlib.Z
  Stdlib.Bool;

symbol ℚ : TYPE;

// the set of all Eunoia types.
symbol Type : Set;
rule τ Type ↪ Set;

// higher-order application.
symbol ⋅ [a b] : τ (a ⤳ b) → τ a → τ b;
notation ⋅ infix left 5;

// inlined typechecking.
symbol _as (a : Set) (x : τ a) : τ a;
rule _as _ $x ↪ $x;

// Core types - use Stdlib types where possible
symbol Bool : Set ≔ bool;
rule τ Bool ↪ 𝔹;
symbol String : Set ≔ string;
rule τ String ↪ Stdlib.String.String;
symbol Z : Set ≔ int;
rule τ Z ↪ ℤ;
symbol Q : Set;
rule τ Q ↪ ℚ;
symbol mkrat : ℤ → ℤ → ℚ;

// Eunoia builtins
sequential symbol is_ok [T : Set]: τ (T ⤳ Bool);
sequential symbol ite [T : Set]: τ (Bool ⤳ T ⤳ T ⤳ T);
sequential symbol eq [U : Set]: τ (U ⤳ U ⤳ Bool);
sequential symbol is_eq [T : Set] [S : Set]: τ (T ⤳ S ⤳ Bool);
sequential symbol requires [T : Set] [U : Set] [V : Set]: τ (T ⤳ U ⤳ V ⤳ V);
sequential symbol hash [T : Set]: τ (T ⤳ Z);
sequential symbol typeof [T : Set]: τ (T ⤳ Type);
sequential symbol nameof [T : Set]: τ (T ⤳ String);
sequential symbol var [T : Set]: τ (String ⤳ T ⤳ T);
sequential symbol cmp [T : Set] [U : Set]: τ (T ⤳ U ⤳ Bool);
sequential symbol is_var [T : Set]: τ (T ⤳ Bool);
sequential symbol is_z [T : Set]: τ (T ⤳ Bool);
sequential symbol and : τ (Bool ⤳ Bool ⤳ Bool);
sequential symbol or : τ (Bool ⤳ Bool ⤳ Bool);
sequential symbol xor : τ (Bool ⤳ Bool ⤳ Bool);
sequential symbol not : τ (Bool ⤳ Bool);
sequential symbol add [T : Set]: τ (T ⤳ T ⤳ T);
sequential symbol mul [T : Set]: τ (T ⤳ T ⤳ T);
sequential symbol neg [T : Set]: τ (T ⤳ T);
sequential symbol qdiv [T : Set]: τ (T ⤳ T ⤳ T);
sequential symbol zdiv [T : Set]: τ (T ⤳ T ⤳ T);
sequential symbol zmod [T : Set]: τ (T ⤳ T ⤳ T);
sequential symbol is_neg [T : Set]: τ (T ⤳ Bool);
sequential symbol gt [T : Set] [U : Set]: τ (T ⤳ U ⤳ Bool);
sequential symbol len [T : Set]: τ (T ⤳ Z);
sequential symbol concat [T : Set]: τ (T ⤳ T ⤳ T);
sequential symbol extract [T : Set]: τ (T ⤳ Z ⤳ Z ⤳ T);
sequential symbol find : τ (String ⤳ String ⤳ Z);
sequential symbol to_z [T : Set]: τ (T ⤳ Z);
sequential symbol to_q [T : Set]: τ (T ⤳ Q);
sequential symbol to_bin [T : Set]: τ (Z ⤳ T ⤳ T);
sequential symbol to_str [T : Set]: τ (T ⤳ String);
sequential symbol quote [T : Set]: τ (T ⤳ T);
sequential symbol nil [U : Set] [T : Set]: τ ((U ⤳ T ⤳ T) ⤳ Type ⤳ T);
sequential symbol cons [U : Set] [T : Set]: τ ((U ⤳ T ⤳ T) ⤳ U ⤳ T ⤳ T);
sequential symbol list_concat [U : Set] [T : Set]: τ ((U ⤳ T ⤳ T) ⤳ T ⤳ T ⤳ T);
sequential symbol list_len [F : Set] [T : Set]: τ (F ⤳ T ⤳ Z);
sequential symbol list_nth [F : Set] [T : Set]: τ (F ⤳ T ⤳ Z ⤳ T);
sequential symbol list_find [F : Set] [T : Set]: τ (F ⤳ T ⤳ T ⤳ Z);
sequential symbol list_rev [F : Set] [T : Set]: τ (F ⤳ T ⤳ T);
sequential symbol list_erase [F : Set] [T : Set]: τ (F ⤳ T ⤳ T ⤳ T);
sequential symbol list_erase_all [F : Set] [T : Set]: τ (F ⤳ T ⤳ T ⤳ T);
sequential symbol list_setof [F : Set] [T : Set]: τ (F ⤳ T ⤳ T);
sequential symbol list_minclude [F : Set] [T : Set]: τ (F ⤳ T ⤳ T ⤳ Bool);
sequential symbol list_meq [F : Set] [T : Set]: τ (F ⤳ T ⤳ T ⤳ Bool);
sequential symbol list_diff [F : Set] [T : Set]: τ (F ⤳ T ⤳ T ⤳ T);
sequential symbol list_inter [F : Set] [T : Set]: τ (F ⤳ T ⤳ T ⤳ T);
sequential symbol list_singleton_elim [F : Set] [T : Set]: τ (F ⤳ T ⤳ T);
sequential symbol List : Set;
sequential symbol List__nil : τ List;
symbol ∎ ≔ List__nil;
sequential symbol List__cons [T : Set]: τ (T ⤳ List ⤳ List);
|}

let generate_prelude output_dir =
  let oc = open_out (Filename.concat output_dir "Prelude.lp") in
  output_string oc prelude_content;
  close_out oc

let stdlib_modules = [
  "Stdlib.Set"; "Stdlib.HOL"; "Stdlib.List";
  "Stdlib.String"; "Stdlib.Z"; "Stdlib.Bool"
]

let generate_lp_file graph pkg_name output_dir path =
  match EO.PathMap.find_opt path graph with
  | None -> ()
  | Some node ->
      let full_sig = EO.full_sig_at graph path in
      let elab_sig = EO.elab_sig_with_ctx full_sig node.node_sig in
      let lp_sig = LP.eo_sig elab_sig in
      let out_path = Filename.concat output_dir (String.concat "/" path ^ ".lp") in
      mkdir_p (Filename.dirname out_path);
      let prelude_module = pkg_name ^ ".Prelude" in
      let prelude_qualified = LP.RequireAs (prelude_module, "eo") in
      let deps = List.map (path_to_module pkg_name) node.node_includes in
      let open_imports =
        if deps = [] then
          LP.Require [prelude_module]
        else
          LP.Require deps
      in
        Api_lp.write_lp_file out_path (prelude_qualified :: open_imports :: lp_sig)

let print_graph graph =
  Printf.printf "Signature graph (%d nodes):\n" (EO.PathMap.cardinal graph);
  EO.PathMap.iter (fun path node ->
    Printf.printf "  %s -> [%s]\n"
      (EO.path_str path)
      (String.concat ", " (List.map EO.path_str node.EO.node_includes))
  ) graph

(* ============================================================
   Translation
   ============================================================ *)

let translate input_dir output_dir verbose =
  if verbose then Printf.printf "Building signature graph from %s...\n" input_dir;
  let graph = EO.build_sig_graph input_dir in
  if verbose then print_graph graph;
  match EO.check_dag graph with
  | Error cycle ->
      Printf.printf "Error: Cycle detected in include graph:\n";
      List.iter (fun p -> Printf.printf "  -> %s\n" (EO.path_str p)) cycle;
      exit 1
  | Ok () ->
      if verbose then Printf.printf "DAG check passed.\n";
      mkdir_p output_dir;
      let pkg_name = Filename.basename output_dir in
      generate_pkg_file output_dir pkg_name;
      generate_prelude output_dir;
      let paths = EO.topo_sort graph in
      List.iter (fun path ->
        if verbose then Printf.printf "Generating %s...\n" (EO.path_str path);
        generate_lp_file graph pkg_name output_dir path
      ) paths;
      Printf.printf "Generated %d LambdaPi files in %s\n" (List.length paths + 1) output_dir

(* ============================================================
   Main entry point
   ============================================================ *)

let main () =
  Arg.parse speclist (fun _ -> ()) usage;
  let cfg = !config in
  match cfg.input_dir, cfg.output_dir with
  | Some input_dir, Some output_dir ->
      translate input_dir output_dir cfg.verbose
  | _ ->
      Printf.printf "%s\n" usage

(* Note: main() is called from eo2lp_cli.ml *)
