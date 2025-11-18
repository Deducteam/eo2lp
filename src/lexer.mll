{
open Parser
}

let simple_symbol =
  ['a'-'z' 'A'-'Z' '+' '-' '/' '*' '^' '=' '%' '?' '!' '.' '$' '_' '&' '<' '>' '@' '#']
  ['a'-'z' 'A'-'Z' '0'-'9' '+' '-' '/' '*' '^' '=' '%' '?' '!' '.' '$' '_' '&' '<' '>' '@' ':']*
let symbol = simple_symbol | '|' [^ '|' '\\']* '|'
let numeral = ['0'-'9']+
let decimal = numeral '.' numeral
let rational = numeral '/' numeral
let binary = "#b" ['0'-'1']+
let hexadecimal = "#x" ['0'-'9' 'a'-'f' 'A'-'F']+
let string = '"' ([^'"'])* '"'

rule token = parse
  | ';' [^'\n']* '\n' { Lexing.new_line lexbuf; token lexbuf }  (* Ignore comments *)
  | ';' [^'\n']* eof  { token lexbuf }   (* Ignore comments at end of file *)
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | eof             { EOF }
  | '('             { LPAREN }
  | ')'             { RPAREN }
  | ':'             { COLON }
  | "!"             { BANG }
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
  | symbol as s              { SYMBOL s }
  | '"' (([^'"'])* as s) '"' { STRING s }
  | numeral as x     { NUMERAL (int_of_string x) }
  | decimal as x     { DECIMAL (float_of_string x) }
  | rational as x    { RATIONAL
        (let [y;z] = String.split_on_char '/' x in
            (int_of_string y, int_of_string z)) }
  (*
  | binary as x      { BINARY x }
  | hexadecimal as x { HEXADECIMAL x }
  *)
  | _ { token lexbuf }
