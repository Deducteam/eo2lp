(* parse_ctx.ml
   Context for recursive parsing of includes *)

open Syntax_eo

let parse_include_callback : (string -> signature) ref =
  ref (fun _ -> [])

let had_parse_error : bool ref = ref false
