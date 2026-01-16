
type lit_category =
  NUM | DEC | RAT | BIN | HEX | STR
and literal =
  | Numeral of int
  | Decimal of float
  | Rational of int * int
  | Binary of string
  | Hexadecimal of string
  | String of string

let lit_category_str =
  function
  | NUM -> "<numeral>"
  | DEC -> "<decimal>"
  | RAT -> "<decimal>"
  | BIN -> "<binary>"
  | HEX -> "<hexadecimal>"
  | STR -> "<string>"

let literal_str =
  function
  | Numeral n -> string_of_int n
  | Decimal d -> string_of_float d
  | Rational (n, d) ->
    string_of_int n ^ "/" ^ string_of_int d
  | String s -> "\"" ^ s ^ "\""
  | Binary _ ->
    (* Printf.printf "WARNING: unhandled binary.\n"; *)
    ""
  | Hexadecimal _ ->
    (* Printf.printf "WARNING: unhandled hex.\n";  *)
    ""
