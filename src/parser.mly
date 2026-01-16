%{
open Syntax_eo
open Literal

let flatten =
  Option.fold ~none:[] ~some:(fun x -> x)

let lit_cat_to_str = function
  | NUM -> "<numeral>"
  | DEC -> "<decimal>"
  | RAT -> "<rational>"
  | BIN -> "<binary>"
  | HEX -> "<hexadecimal>"
  | STR -> "<string>"
%}

%token <string> SYMBOL

%token <int> NUMERAL
%token <float> DECIMAL
%token <int * int> RATIONAL
%token <string> BINARY
%token <string> HEXADECIMAL
%token <string> STRING

%token LPAREN RPAREN EOF
%token STR NUM DEC RAT BIN HEX

%token
  DECLARE_CONST
  DECLARE_DATATYPE
  DECLARE_DATATYPES
  ECHO
  EXIT
  RESET
  SET_OPTION

%token
  ASSUME ASSUME_PUSH
  DECLARE_CONSTS DECLARE_PARAM_CONST
  DECLARE_RULE
  DEFINE
  INCLUDE
  PROGRAM
  REFERENCE
  STEP STEP_POP

%token
  RIGHT_ASSOC_NIL_NSN LEFT_ASSOC_NIL_NSN
  RIGHT_ASSOC_NSN LEFT_ASSOC_NSN
  RIGHT_ASSOC_NIL LEFT_ASSOC_NIL
  RIGHT_ASSOC LEFT_ASSOC
  CHAINABLE PAIRWISE ARG_LIST BINDER LET_BINDER

%token
  IMPLICIT OPAQUE LIST SYNTAX RESTRICT

%token
  PUSH POP PAR AS

%token
  TYPE SORRY

%token
  ASSUMPTION
  PREMISES
  PREMISE_LIST
  ARGS
  REQUIRES
  CONCLUSION
  CONCLUSION_EXPLICIT
  SIGNATURE
  RULE

%start <(string * const) list option> toplevel_eof
%start <term> term
%start <param list> params


%%
toplevel_eof:
  | EOF        { None }
  | command    { Some $1 }

symbol:
  | s = SYMBOL { s }
  | AS { "as" }
  | PAR { "par" }

literal:
  | x = NUMERAL      { Numeral x  }
  | x = DECIMAL      { Decimal x  }
  | p = RATIONAL     { Rational (fst p, snd p) }
  | s = STRING       { String s }
  | b = BINARY       { Binary b }
  | h = HEXADECIMAL  { Hexadecimal h }

cases:
  | LPAREN; cs = nonempty_list(case); RPAREN
  { cs }


common_command:
  | LPAREN; DECLARE_CONST;
      s = symbol ;
      t = term;
      ao = option(const_attr);
    RPAREN
  {
    [(s, Decl ([], t, ao))]
  }
  | LPAREN; DECLARE_DATATYPE;
      s = symbol ;
      dt = datatype_dec;
    RPAREN
  { [] }
  | LPAREN; DECLARE_DATATYPES;
      LPAREN; sts = list(sort_dec); RPAREN;
      LPAREN; dts = list(datatype_dec); RPAREN;
    RPAREN
  { [] }
  | LPAREN; ECHO;
      str_opt = option(STRING);
    RPAREN;
  { [] }
  | LPAREN; EXIT; RPAREN
  { [] }
  | LPAREN; RESET; RPAREN
  { [] }
  | LPAREN; SET_OPTION; s = symbol; v = option(term); RPAREN
  { [] }
  | LPAREN; PUSH; n = option(NUMERAL); RPAREN
  { [] }
  | LPAREN; POP; n = option(NUMERAL); RPAREN
  { [] }

command:
  | LPAREN; ASSUME;
      s = symbol ;
      t = term;
    RPAREN
  {
    []
  }
  | LPAREN; ASSUME_PUSH;
      s = symbol ;
      t = term;
    RPAREN
  {
    []
  }
  | LPAREN; DECLARE_CONSTS;
      l = lit_category;
      t = term;
    RPAREN
  { [] }
  | LPAREN; DECLARE_PARAM_CONST;
      s = symbol ;
      LPAREN; ps = list(param); RPAREN;
      ty = term;
      att_opt = option(const_attr);
    RPAREN
  {
    [(s, Decl (ps, ty, att_opt))]
  }
  | LPAREN; DECLARE_RULE;
      s = symbol ;
      LPAREN; xs = list(param); RPAREN;
      assm_opt  = option(assumption);
      prems_opt = option(premises);
      args_opt  = option(arguments);
      reqs_opt  = option(reqs);
      conc = conclusion;
      att_opt = option(rule_attr);
    RPAREN
  { let r =
      {
        assm = assm_opt;
        prem = prems_opt;
        args = flatten args_opt;
        reqs = (
          match reqs_opt with
          | Some cs -> cs
          | None -> []);
        conc = conc
      }
    in
      (* _sig := M.add s
        { prm = []; att = None; typ = None; def = None }
       !_sig; *)
    (* _sym(s, Rule (xs, r)); *)
    if Option.is_some att_opt then
      Printf.printf "WARNING: (:sorry, rule %s)\n" s;

    []
  }
  | LPAREN; DEFINE;
      s = symbol ;
      LPAREN; ps = list(param); RPAREN; t = term;
      ty_opt = option(defn_attr);
    RPAREN
  {
    [(s, Defn (ps, t))]
  }
  | LPAREN; INCLUDE;
      str = STRING;
    RPAREN
  {
    !Parse_ctx.parse_include_callback str
  }
  | LPAREN; PROGRAM;
      s = symbol ;
      LPAREN; ps = list(param); RPAREN;
      SIGNATURE;
        LPAREN; doms = nonempty_list(term); RPAREN;
        ran = term;
      cs_opt = option(cases);
    RPAREN
  { let cs = Option.fold ~none:[] ~some:(fun x -> x) cs_opt in
    let ty = prog_ty (doms,ran) in
    let qs = prog_ty_params ty ps in
    let rs = prog_cs_params cs ps in
    [(s, Prog ((qs, ty), (rs, cs)))]
  }

  | LPAREN; REFERENCE;
      str = STRING ;
      s_opt = option(symbol);
    RPAREN
  { [] }

  | LPAREN; STEP;
      s1 = symbol ;
      t = term;
      RULE; s2 = symbol ;
      prem_opt = option(simple_premises);
      args_opt = option(arguments);
    RPAREN
  {
    let (xs,ys) = (flatten prem_opt, flatten args_opt) in
    (* (s1, Step (s2, xs, ys, t)) |> _sym; *)

    []
  }

  | LPAREN; STEP;
      s1 = symbol ;
      RULE; s2 = symbol ;
      prem_opt = option(simple_premises);
      args_opt = option(arguments);
    RPAREN
  {
    let (xs,ys) = (flatten prem_opt, flatten args_opt) in
    (* (s1, Step (s2, xs, ys, Symbol "true")) |> _sym; *)

    []
  }

  | LPAREN; STEP_POP;
      s1 = symbol ;
      t = term;
      RULE; s2 = symbol ;
      prem_opt = option(simple_premises);
      args_opt = option(arguments);
    RPAREN
  {
    let (xs,ys) = (flatten prem_opt, flatten args_opt) in
    Printf.printf "WARNING. (step-pop ...)";
    (* (s1, Step (s2, xs, ys, t)) |> _sym; *)
    []
  }

  | LPAREN; STEP_POP;
      s1 = symbol ;
      RULE; s2 = symbol ;
      prem_opt = option(simple_premises);
      args_opt = option(arguments);
    RPAREN
  {
    let (xs,ys) = (flatten prem_opt, flatten args_opt) in
    Printf.printf "WARNING. (step-pop ...)";
    (* (s1, Step (s2, xs, ys, Symbol "true")) |> _sym; *)
    []
  }

  | c = common_command
  { c }

const_attr:
  | RIGHT_ASSOC_NIL; t = term { RightAssocNil t }
  | RIGHT_ASSOC_NIL_NSN; t = term { RightAssocNilNSN t }
  | LEFT_ASSOC_NIL; t = term  { LeftAssocNil t }
  | LEFT_ASSOC_NIL_NSN; t = term { LeftAssocNilNSN t }
  | RIGHT_ASSOC_NSN; t = term { RightAssocNSN t }
  | LEFT_ASSOC_NSN; t = term  { LeftAssocNSN t }
  | RIGHT_ASSOC { RightAssoc }
  | LEFT_ASSOC { LeftAssoc }
  | CHAINABLE; s = symbol { Chainable s }
  | PAIRWISE; s = symbol  { Pairwise s }
  | BINDER; s = symbol    { Binder s }
  | ARG_LIST; s = symbol  { ArgList s }
  | LET_BINDER; t = term  { LetBinder t }

param_attr:
  | LIST     { List }
  | IMPLICIT { Implicit }
  | OPAQUE   { Opaque }
  | SYNTAX; t = term { Syntax t }
  | SYNTAX; lc = lit_category { Syntax (Symbol (lit_cat_to_str lc)) }
  | RESTRICT; t = term { Restrict t }

defn_attr:
  | TYPE; t = term
  { t }

rule_attr:
  | SORRY
  { Sorry }

term:
  | l = literal
  { Literal l  }
  | s = symbol
  { Symbol s }
  | LPAREN;
      s = symbol ;
      ts = nonempty_list(term);
    RPAREN
  { Apply (s, ts) }
  | LPAREN;
      b = symbol;
      LPAREN; xs = nonempty_list(var); RPAREN;
      t = term;
    RPAREN
  { Bind (b, xs, t) }
  | LPAREN;
      AS;
      s = symbol;
      t = term;
    RPAREN
  { Apply ("as", [Symbol s; t]) }
  | LPAREN;
      LPAREN; AS; s = symbol; ty = term; RPAREN;
      ts = nonempty_list(term);
    RPAREN
  { Apply ("_", [Apply ("as", [Symbol s; ty]); Apply ("@app", ts)]) }

var:
  | LPAREN;
      s = symbol; t = term;
    RPAREN
  { (s, t) }

param:
  | LPAREN;
      s = symbol;
      t = term;
      atts = list(param_attr);
    RPAREN
  { (s, t, atts) }

params:
  | LPAREN;
    ps = list(param)
    RPAREN
  { ps }

case:
  | LPAREN;
      t1 = term; t2 = term;
    RPAREN
  { (t1, t2) }

sort_dec:
  | LPAREN;
      s = symbol ;
      n = NUMERAL;
    RPAREN
  { SortDec (s, n) }
sel_dec:
  | LPAREN;
      s = symbol ;
      t = term;
    RPAREN
  { SelDec (s, t) }
cons_dec:
  | LPAREN;
      s = symbol ;
      xs = list(sel_dec);
    RPAREN
  { ConsDec (s, xs) }
datatype_dec:
  | LPAREN;
      xs = nonempty_list(cons_dec);
    RPAREN
  { DatatypeDec xs }
  | LPAREN;
      PAR;
      LPAREN; ps = nonempty_list(symbol); RPAREN;
      LPAREN; xs = nonempty_list(cons_dec); RPAREN;
    RPAREN
  { DatatypeDec xs }  (* parametric datatype - params discarded for now *)

lit_category:
  | NUM { NUM }
  | DEC { DEC }
  | RAT { RAT }
  | BIN { BIN }
  | HEX { HEX }
  | STR { STR }

assumption:
  | ASSUMPTION; t = term
  { t }
simple_premises:
  | PREMISES; LPAREN; ts = list(term); RPAREN;
  { ts }
premises:
  | ts = simple_premises
  { Simple ts }
  | PREMISE_LIST; t1 = term; t2 = term
  { PremiseList (t1,t2) }
arguments:
  | ARGS; LPAREN; ts = list(term); RPAREN;
  { ts }
reqs:
  | REQUIRES; cs = cases
  { cs }
conclusion:
  | CONCLUSION; t = term
  { Conclusion t }
  | CONCLUSION_EXPLICIT; t = term
  { ConclusionExplicit t }
