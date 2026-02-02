(* literal.ml
   Literal categories and values *)

type lit_category =
  | NUM | DEC | RAT | BIN | HEX | STR

and literal =
  | Numeral     of int
  | Decimal     of float
  | Rational    of int * int
  | Binary      of string
  | Hexadecimal of string
  | String      of string

let lit_category_str = function
  | NUM -> "<numeral>"
  | DEC -> "<decimal>"
  | RAT -> "<rational>"
  | BIN -> "<binary>"
  | HEX -> "<hexadecimal>"
  | STR -> "<string>"

let literal_str = function
  | Numeral n   -> string_of_int n
  | Decimal d   -> string_of_float d
  | Rational (n, d) -> Printf.sprintf "(mkrat %d %d)" n d
  | String s    -> "\"" ^ s ^ "\""
  | Binary _    -> ""
  | Hexadecimal _ -> ""
