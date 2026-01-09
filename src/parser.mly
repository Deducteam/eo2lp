%{
open Syntax_eo
let flatten =
  Option.fold ~none:[] ~some:(fun x -> x)
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


common_command:
  | LPAREN; DECLARE_CONST;
      s = symbol ;
      t = term;
      att_opt = option(const_attr);
    RPAREN
  {
    let lv = (if is_kind t then Ty else Tm) in
    let dec = Decl ([], t, att_opt, lv) in
    _sig := M.add s dec !_sig;
    DeclareConst (s,t,att_opt)
  }
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

command:
  | LPAREN; ASSUME;
      s = symbol ;
      t = term;
    RPAREN
  {
    let ty  = mk_proof t in
    let dec = Decl ([], ty, None, Ty) in
    _sig := M.add s dec !_sig;
    Assume (s,t)
  }
  | LPAREN; ASSUME_PUSH;
      s = symbol ;
      t = term;
    RPAREN
  {
    let ty  = mk_proof t in
    let dec = Decl ([], ty, None, Ty) in
    _sig := M.add s dec !_sig;
    AssumePush (s,t)
  }
  | LPAREN; DECLARE_CONSTS;
      l = lit_category;
      t = term;
    RPAREN
  { DeclareConsts (l,t) }
  | LPAREN; DECLARE_PARAM_CONST;
      s = symbol ;
      LPAREN; ps = list(param); RPAREN;
      ty = term;
      att_opt = option(const_attr);
    RPAREN
  {
    let lv = (if is_kind ty then Ty else Tm) in
    let dec = Decl (ps, ty, att_opt, Tm) in
    _sig := M.add s dec !_sig;

    DeclareParamConst (s, ps, ty, att_opt)
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
    DeclareRule (s, xs, r, att_opt)
  }
  | LPAREN; DEFINE;
      s = symbol ;
      LPAREN; ps = list(param); RPAREN; t = term;
      ty_opt = option(defn_attr);
    RPAREN
  {
    let dec = Defn (ps, t) in
    _sig := M.add s dec !_sig;
    Define (s,ps,t,ty_opt)
  }
  | LPAREN; INCLUDE;
      str = STRING;
    RPAREN
  { Include [str] }

  | LPAREN; PROGRAM;
      s = symbol ;
      LPAREN; ps = list(param); RPAREN;
      SIGNATURE;
        LPAREN; doms = nonempty_list(term); RPAREN;
        ran = term;
      cs_opt = option(cases);
    RPAREN
  { let cs =
      match cs_opt with
      | Some cs -> cs
      | None -> []
    in
    let ty = prog_ty (doms,ran) in
    let lv = (if is_kind ty then Ty else Tm) in
    let qs = prog_ty_params ty ps in
    let dec = Decl (qs, ty, None, lv) in
    _sig := M.add s dec !_sig;

    let rs = prog_cs_params cs ps in
    Program (s, (qs, ty), (rs, cs))
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
  {
    let (xs,ys) = (flatten prem_opt, flatten args_opt) in
    let s1_ty =
      match t_opt with
      | Some t -> mk_proof t
      | None -> Printf.ksprintf failwith
        "Please ask your SMT solver to print conclusions
        of proof steps."
    in
    let s1_def = Apply (s2, List.append xs ys) in
    let dec = Decl ([], s1_ty, None, Ty) in
    _sig := M.add s1 dec !_sig;
    Step (s1, s1_ty, s2, xs, ys)
  }

  | LPAREN; STEP_POP;
      s1 = symbol ;
      t_opt = option(term);
      RULE; s2 = symbol ;
      prem_opt = option(simple_premises);
      args_opt = option(arguments);
    RPAREN
  {
    let (xs,ys) = (flatten prem_opt, flatten args_opt) in
    let s1_ty =
      match t_opt with
      | Some t -> mk_proof t
      | None -> Printf.ksprintf failwith
        "Please ask your SMT solver to print conclusions."
    in
    let s1_def = Apply (s2, List.append xs ys) in
    let dec = Decl ([], s1_ty, None, Ty) in
    _sig := M.add s1 dec !_sig;
    StepPop (s1, s1_ty, s2, xs, ys)
  }

  | c = common_command
  { Common c }

const_attr:
  | RIGHT_ASSOC_NIL; t = term { RightAssocNil t }
  | RIGHT_ASSOC_NIL_NSN; t = term { RightAssocNilNSN t }
  | LEFT_ASSOC_NIL; t = term  { LeftAssocNil t }
  | LEFT_ASSOC_NIL_NSN; t = term { LeftAssocNilNSN t }
  | RIGHT_ASSOC { RightAssoc }
  | LEFT_ASSOC { LeftAssoc }
  | CHAINABLE; s = symbol { Chainable s }
  | PAIRWISE; s = symbol  { Pairwise s }
  | BINDER; s = symbol    { Binder s }
  | ARG_LIST; s = symbol  { ArgList s }

param_attr:
  | LIST     { List }
  | IMPLICIT { Implicit }
  | OPAQUE   { Opaque }

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

var:
  | LPAREN;
      s = symbol; t = term;
    RPAREN
  { (s, t) }

param:
  | LPAREN;
      s = symbol;
      t = term;
      att = option(param_attr);
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
