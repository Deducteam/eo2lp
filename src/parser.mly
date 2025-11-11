%{
open Ast
open Option
%}

%token <string> SYMBOL STRING
%token <int> NUMERAL
%token <float> DECIMAL
%token <int * int> RATIONAL

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
  ASSERT
  CHECK_SAT CHECK_SAT_ASSUMING
  DECLARE_FUN
  DECLARE_SORT
  DEFINE_CONST
  DEFINE_FUN
  DEFINE_SORT
  SET_INFO
  SET_LOGIC

%token
  ASSUMPTION
  PREMISES
  PREMISE_LIST
  ARGS
  ARG_LIST
  REQUIRES
  CONCLUSION
  CONCLUSION_EXPLICIT
  SIGNATURE
  TYPE

%start <eo_command option> toplevel_eof

%%
eo_command:
  | LPAREN; ASSUME;
      s = SYMBOL;
      t = term;
    RPAREN
  { Assume (s,t) }
  | LPAREN; ASSUME_PUSH;
      s = SYMBOL;
      t = term;
    RPAREN
  { AssumePush (s,t) }
  | LPAREN; DECLARE_CONSTS;
      l = lit_category;
      t = term;
    RPAREN
  { DeclareConsts (l,t) }
  | LPAREN; DECLARE_PARAM_CONST;
      s = SYMBOL;
      LPAREN; xs = list(param); RPAREN;
      t = term;
      as = list(attr);
    RPAREN
  { DeclareParamConst (s,xs,t,as) }
  | LPAREN; DECLARE_RULE;
      s = SYMBOL;
      LPAREN; xs = list(param); RPAREN;
      assm  = option(assumption);
      prems = option(premises);
      args  = option(arguments);
      reqs  = option(reqs);
      conc  = conclusion;
      atts  = list(attr);
    RPAREN
  { DeclareRule (s,
      RuleDec (
        assm, prems,
        (match args with
        | Some ts -> ts
        | None    -> []),
        (match reqs with
        | Some cs -> cs
        | None    -> []),
        conc
      ),
      atts
    )
  }
  | LPAREN; DEFINE;
      s = SYMBOL;
      LPAREN; xs = list(param); RPAREN;
      t = term;
      as = list(attr);
    RPAREN
  { Define (s,xs,t,as) }
  | LPAREN; INCLUDE;
      str = string;
    RPAREN
  { Include str }
  | LPAREN; PROGRAM;
      s = SYMBOL;
      LPAREN; xs = list(param); RPAREN;
      SIGNATURE;
        LPAREN; doms = nonempty_list(term); RPAREN;
        ran = term;
      LPAREN; cs = nonempty_list(case); RPAREN;
    RPAREN
  { Program (s, xs, (doms, ran), cs) }
  | LPAREN; REFERENCE;
      str = string;
      s_opt = option(SYMBOL);
    RPAREN
  { Reference (str, s_opt) }
  | LPAREN; STEP;
      s1 = SYMBOL;
      t_opt = option(term);
      RULE; s2 = SYMBOL;
      prem_opt = option(simple_premises);
      args_opt = option(arguments);
    RPAREN
  { Step (s1, t_opt, s2, prem_opt, ) }
  | LPAREN; STEP_POP;
      SYMBOL;
      option(term);
      RULE; SYMBOL;
      option(simple_premises);
      option(arguments);
    RPAREN
  {}
  | common_command
  { Common $1 }

common_command:
  | LPAREN; DECLARE_CONST;
      SYMBOL;
      term;
      list(attr);
    RPAREN
  {}
  | LPAREN; DECLARE_DATATYPE;
      SYMBOL;
      datatype_dec;
    RPAREN
  {}
  | LPAREN; DECLARE_DATATYPES;
      SYMBOL;
      LPAREN; list(sort_dec); RPAREN;
      LPAREN; list(datatype_dec); RPAREN;
    RPAREN
  {}
  | LPAREN; ECHO;
      option(string);
    RPAREN;
  {}
  | LPAREN; RESET; RPAREN
  | LPAREN; SET_OPTION; attr; RPAREN

literal:
  | NUMERAL  { Numeral $1  }
  | DECIMAL  { Decimal $1  }
  | RATIONAL { Rational $1 }
  | STRING   { String $1   }

keyword:
  | COLON; SYMBOL
  { Colon $2 }

attr:
  | KEYWORD; option(term)
  { ($2, $3) }

term:
  | literal  { Literal $1  }
  | SYMBOL   { Symbol $1 }
  | LPAREN;
      SYMBOL;
      nonempty_list(term);
    RPAREN
  { Apply ($2, $3) }
  | LPAREN;
      EO_DEFINE;
      LPAREN; nonempty_list(var); RPAREN;
      term;
    RPAREN
  { Let ($4, $6) }
  | LPAREN;
      BANG;
      term;
      nonempty_list(attr);
    RPAREN
  { Bang ($3, $4) }

var:
  | LPAREN;
      SYMBOL; term;
    RPAREN
  { ($2, $3) }

param:
  | LPAREN; SYMBOL; term; list(attr); RPAREN
  { Param ($2, Type $3, $4) }

case:
  | LPAREN; term; term; RPAREN
  { ($2, $3) }

sel_dec:
  | LPAREN; SYMBOL; term; RPAREN
  {}
cons_dec:
  | LPAREN; SYMBOL; list(sel_dec); RPAREN
  {}
datatype_dec:
  | LPAREN; nonempty_list(cons_dec); RPAREN
  {}

lit_category:
  | NUM { NUM }
  | DEC { DEC }
  | RAT { RAT }
  | BIN { BIN }
  | HEX { HEX }
  | STR { STR }

toplevel_eof:
  | EOF { None }
  | toplevel { Some $1 }

toplevel:
  | eo_command     { $1 }
  | smt2_command   { $1 }


assumption:
  | ASSUMTPION; term
  { Assumption $2 }
simple_premises:
  | PREMISES; LPAREN; list(term); RPAREN;
  { Premises $2 }
premises:
  | simple_premises
  { Simple $1 }
  | PREMISE_LIST; term; term
  { PremiseList ($2,$3) }
arguments:
  | ARGS; LPAREN; list(term); RPAREN;
  { Args $3 }
reqs:
  | REQUIRES; LPAREN; list(case); RPAREN
  { Requires $3 }
conclusion:
  | CONCLUSION; term
  { Conclusion $2 }
  | CONCLUSION_EXPLICIT; term
  { ConclusionExplicit $2 }
