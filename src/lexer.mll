{
open Parser
}

let simple_symbol =
  ['a'-'z' 'A'-'Z' '+' '-' '/' '*' '^' '=' '%' '?' '!' '.' '$' '_' '&' '<' '>' '@' '#']
  ['a'-'z' 'A'-'Z' '0'-'9' '+' '-' '/' '*' '^' '=' '%' '?' '!' '.' '$' '_' '&' '<' '>' '@' ':']*
let symbol = simple_symbol | '|' [^ '|' '\\']* '|'

let digit = ['0'-'9']
let hexdigit = ['0'-'9' 'a'-'f' 'A'-'F']
let binary_digit = ['0' '1']

let string = '"' ([^'"'])* '"'
let numeral = '-'? digit+
let decimal = '-'? digit+ '.' digit+
let rational = '-'? digit+ '/' digit+
let binary = "#b" binary_digit+
let hexadecimal = "#x" hexdigit+


rule token = parse
  | ';' [^'\n']* '\n' { Lexing.new_line lexbuf; token lexbuf }  (* Ignore comments *)
  | ';' [^'\n']* eof  { token lexbuf }   (* Ignore comments at end of file *)
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | '"' [^ '"']* '"' as s
    {
      (* Remove the first and last character *)
      let content = String.sub s 1 (String.length s - 2) in
      STRING content
    }
  | eof             { EOF }
  | '('             { LPAREN }
  | ')'             { RPAREN }
  (* common commands *)
  | "declare-const"      { DECLARE_CONST }
  | "declare-datatype"   { DECLARE_DATATYPE }
  | "declare-datatypes"  { DECLARE_DATATYPES }
  | "set-option"         { SET_OPTION }
  | "echo"               { ECHO }
  | "exit"               { EXIT }
  | "reset"              { RESET }
  (* eunoia context modifying commands *)
  | "declare-rule"                  { DECLARE_RULE }
  | "declare-consts"                { DECLARE_CONSTS }
  | "declare-parameterized-const"   { DECLARE_PARAM_CONST }
  | "define"                        { DEFINE }
  | "include"                       { INCLUDE }
  | "program"                       { PROGRAM }
  | "reference"                     { REFERENCE }
  (* constant attributes *)
  | ":right-assoc-nil-non-singleton-nil" { RIGHT_ASSOC_NIL_NSN }
  | ":left-assoc-nil-non-singleton-nil"  { LEFT_ASSOC_NIL_NSN }
  | ":right-assoc-nil" { RIGHT_ASSOC_NIL }
  | ":left-assoc-nil"  { LEFT_ASSOC_NIL }
  | ":right-assoc"     { RIGHT_ASSOC }
  | ":left-assoc"      { LEFT_ASSOC }
  | ":chainable"       { CHAINABLE }
  | ":pairwise"        { PAIRWISE }
  | ":arg-list"        { ARG_LIST }
  | ":binder"          { BINDER }
  (* variable attributes *)
  | ":implicit"        { IMPLICIT }
  | ":opaque"          { OPAQUE }
  | ":list"            { LIST }
  (* type attribute for `define` command *)
  | ":type" { TYPE }
  (* sorry attribute for `declare-rule` command *)
  | ":sorry" { SORRY }
  (* eunoia proof script commands *)
  | "assume"         { ASSUME }
  | "assume-push"    { ASSUME_PUSH }
  | "step"           { STEP }
  | "step-pop"       { STEP_POP }
  (* rule declaration attributes *)
  | ":conclusion"    { CONCLUSION }
  | ":assumption"    { ASSUMPTION }
  | ":premise-list"  { PREMISE_LIST }
  | ":premises"      { PREMISES }
  | ":args"          { ARGS }
  | ":requires"      { REQUIRES }
  | ":rule"          { RULE }
  | ":signature "    { SIGNATURE }
  (* syntactic categories *)
  | "<string>"       { STR }
  | "<numeral>"      { NUM }
  | "<decimal>"      { DEC }
  | "<rational>"     { RAT }
  | "<binary>"       { BIN }
  | "<hexadecimal>"  { HEX }
  (* syntactic literals *)
  | numeral as x     { NUMERAL (int_of_string x) }
  | decimal as x     { DECIMAL (float_of_string x) }
  | rational as x    { RATIONAL
        (let [y;z] = String.split_on_char '/' x in
            (int_of_string y, int_of_string z)) }
  | binary as x      { BINARY x }
  | hexadecimal as x { HEXADECIMAL x }
  | symbol as s      { SYMBOL s }
  | _ { token lexbuf }
