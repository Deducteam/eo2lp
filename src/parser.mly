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
  RIGHT_ASSOC_NIL LEFT_ASSOC_NIL
  RIGHT_ASSOC LEFT_ASSOC
  CHAINABLE PAIRWISE ARG_LIST BINDER

%token
  IMPLICIT OPAQUE LIST

%token
  TYPE

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

%start <command option> toplevel_eof
%start <term> term
%start <param list> params


%%
toplevel_eof:
  | EOF        { None }
  | command    { Some $1 }

symbol:
  | s = SYMBOL { s }

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

command:
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
      att = const_attr;
    RPAREN
  { DeclareParamConst (s, xs, t, att) }
  | LPAREN; DECLARE_RULE;
      s = symbol ;
      LPAREN; xs = list(param); RPAREN;
      assm_opt  = option(assumption);
      prems_opt = option(premises);
      args_opt  = option(arguments);
      reqs_opt  = option(reqs);
      conc = conclusion;
    RPAREN
  { let drop = Option.fold ~none:[] ~some:(fun x -> x) in
    let r =
      {
        assumption = assm_opt;
        premises = prems_opt;
        args = drop args_opt;
        reqs = drop reqs_opt;
        conclusion = conc
      }
    in
      DeclareRule (s, xs, r)
  }
  | LPAREN; DEFINE;
      s = symbol ;
      LPAREN; xs = list(param); RPAREN;
      t = term;
      ty_opt = option(defn_attr);
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
      att_opt = option(const_attr);
    RPAREN
  { DeclareConst (s,t,att_opt) }
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
  | LPAREN; SET_OPTION; s = symbol; RPAREN
  { SetOption (s) }

const_attr:
  | RIGHT_ASSOC_NIL; t = term { RightAssocNil t }
  | RIGHT_ASSOC_NIL_NSN; t = term { RightAssocNilNSN t }
  | LEFT_ASSOC_NIL; t = term  { LeftAssocNil t }
  | LEFT_ASSOC_NIL_NSN; t = term { LeftAssocNilNSN t }
  | RIGHT_ASSOC { RightAssoc t }
  | LEFT_ASSOC { LeftAssoc t  }
  | CHAINABLE; s = symbol { Chainable s }
  | PAIRWISE; s = symbol  { Pairwise s }
  | ARG_LIST; s = symbol  { ArgList s }
  | BINDER; s = symbol    { Symbol s }

var_attr:
  | LIST     { List }
  | IMPLICIT { Implicit }
  | OPAQUE   { Opaque }

defn_attr:
  | TYPE; t = term
  { t }

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

var:
  | LPAREN;
      s = symbol; t = term;
    RPAREN
  { (s, t) }

param:
  | LPAREN;
      s = symbol;
      t = term;
      att = var_attr;
    RPAREN
  { (s, t, att) }

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
