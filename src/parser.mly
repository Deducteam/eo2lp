%{
open Syntax_eo
%}

%token <string> SYMBOL

%token <int> NUMERAL
%token <float> DECIMAL
%token <int * int> RATIONAL
%token <string> BINARY
%token <string> HEXADECIMAL
%token <string> STRING

%token LPAREN RPAREN COLON BANG EOF
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
  ASSUMPTION
  PREMISES
  PREMISE_LIST
  ARGS
  REQUIRES
  CONCLUSION
  CONCLUSION_EXPLICIT
  SIGNATURE
  TYPE
  RULE

%start <eo_command option> toplevel_eof

%%
toplevel_eof:
  | EOF        { None }
  | eo_command { Some $1 }

symbol:
  | s = SYMBOL { Symbol s }

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

eo_command:
  | LPAREN; ASSUME;
      s = symbol ;
      t = term;
    RPAREN
  { Assume (s,t) }
  | LPAREN; ASSUME_PUSH;
      s = symbol ;
      t = term;
    RPAREN
  { AssumePush (s,t) }
  | LPAREN; DECLARE_CONSTS;
      l = lit_category;
      t = term;
    RPAREN
  { DeclareConsts (l,t) }
  | LPAREN; DECLARE_PARAM_CONST;
      s = symbol ;
      LPAREN; xs = list(param); RPAREN;
      t = term;
      atts = list(attr);
    RPAREN
  { DeclareParamConst (s, xs, t, atts) }
  | LPAREN; DECLARE_RULE;
      s = symbol ;
      LPAREN; xs = list(param); RPAREN;
      assm  = option(assumption);
      prems = option(premises);
      args  = option(arguments);
      reqs  = option(reqs);
      conc  = conclusion;
      atts  = list(attr);
    RPAREN
  { DeclareRule (s, xs,
      RuleDec (assm, prems, args, reqs, conc),
      atts
    )
  }
  | LPAREN; DEFINE;
      s = symbol ;
      LPAREN; xs = list(param); RPAREN;
      t = term;
      ty_opt = option(ty_attr);
    RPAREN
  { Define (s,xs,t,ty_opt) }
  | LPAREN; INCLUDE;
      str = STRING;
    RPAREN
  { Include str }
  | LPAREN; PROGRAM;
      s = symbol ;
      LPAREN; xs = list(param); RPAREN;
      SIGNATURE;
        LPAREN; doms = nonempty_list(term); RPAREN;
        ran = term;
      cs_opt = option(cases);
    RPAREN
  { let cs = match cs_opt with
      | Some cs -> cs
      | None -> [] in
    Program (s, xs, (doms, ran), cs)
  }
  | LPAREN; REFERENCE;
      str = STRING ;
      s_opt = option(symbol);
    RPAREN
  { Reference (str, s_opt) }
  | LPAREN; STEP;
      s1 = symbol ;
      t_opt = option(term);
      RULE; s2 = symbol ;
      prem_opt = option(simple_premises);
      args_opt = option(arguments);
    RPAREN
  { Step (s1, t_opt, s2, prem_opt, args_opt) }
  | LPAREN; STEP_POP;
      s1 = symbol ;
      t_opt = option(term);
      RULE; s2 = symbol ;
      prem_opt = option(simple_premises);
      args_opt = option(arguments);
    RPAREN
  { StepPop (s1, t_opt, s2, prem_opt, args_opt) }
  | c = common_command
  { Common c }

common_command:
  | LPAREN; DECLARE_CONST;
      s = symbol ;
      t = term;
      atts = list(attr);
    RPAREN
  { DeclareConst (s,t,atts) }
  | LPAREN; DECLARE_DATATYPE;
      s = symbol ;
      dt = datatype_dec;
    RPAREN
  { DeclareDatatype (s, dt) }
  | LPAREN; DECLARE_DATATYPES;
      LPAREN; sts = list(sort_dec); RPAREN;
      LPAREN; dts = list(datatype_dec); RPAREN;
    RPAREN
  { DeclareDatatypes (sts, dts) }
  | LPAREN; ECHO;
      str_opt = option(STRING);
    RPAREN;
  { Echo (str_opt) }
  | LPAREN; EXIT; RPAREN
  { Exit }
  | LPAREN; RESET; RPAREN
  { Reset }
  | LPAREN; SET_OPTION; a = attr; RPAREN
  { SetOption (a) }


keyword:
  | COLON; s = SYMBOL
  { Colon s }

attr:
  | kw = keyword; t_opt = option(term)
  { Attr (kw, t_opt) }

ty_attr:
  | TYPE; t = term
  { t }

term:
  | l = literal
  { Literal l  }
  | s = symbol
  { Sym s }
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
      BANG;
      t = term;
      atts = nonempty_list(attr);
    RPAREN
  { Bang (t, atts) }

var:
  | LPAREN;
      s = symbol; t = term;
    RPAREN
  { (s, t) }

param:
  | LPAREN;
      s = symbol;
      t = term;
      xs = list(attr);
    RPAREN
  { Param (s, t, xs) }

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

lit_category:
  | NUM { NUM }
  | DEC { DEC }
  | RAT { RAT }
  | BIN { BIN }
  | HEX { HEX }
  | STR { STR }

assumption:
  | ASSUMPTION; t = term
  { Assumption t }
simple_premises:
  | PREMISES; LPAREN; ts = list(term); RPAREN;
  { Premises ts }
premises:
  | ts = simple_premises
  { Simple ts }
  | PREMISE_LIST; t1 = term; t2 = term
  { PremiseList (t1,t2) }
arguments:
  | ARGS; LPAREN; ts = list(term); RPAREN;
  { Args ts }
reqs:
  | REQUIRES; LPAREN; cs = list(case); RPAREN
  { Requires cs }
conclusion:
  | CONCLUSION; t = term
  { Conclusion t }
  | CONCLUSION_EXPLICIT; t = term
  { ConclusionExplicit t }
