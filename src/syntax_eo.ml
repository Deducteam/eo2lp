type symbol = string

type keyword =
  | Colon of symbol

type lit_category =
  NUM | DEC | RAT | BIN | HEX | STR

type literal =
  | Numeral of int
  | Decimal of float
  | Rational of int * int
  | String of string

type term =
  | Sym of symbol
  | Literal of literal
  | Let of ((symbol * term) list) * term
  | Apply of symbol * (term list)
  | Bang of term * (attr list)
and attr = keyword * (term option)

type typ =
  | Type of term

type param =
  | Param of symbol * typ * (attr list)

(* types for datatype declarations *)
type sort_dec = symbol * int
and sel_dec = symbol * typ
and cons_dec = symbol * (sel_dec list)
and dt_dec = cons_dec list

(* types for inference rule declarations *)
type assumption =
  | Assumption of term
and simple_premises =
  | Premises of term list
and premises =
  | Simple of simple_premises
  | PremiseList of term * term
and arguments =
  | Args of term list
and reqs =
  | Requires of (term * term) list
and conclusion =
  | Conclusion of term
  | ConclusionExplicit of term
and rl_dec =
  assumption option *
  premises option *
  arguments *
  reqs *
  conclusion


(* commands shared by smtlib2 and eunoia *)
type common_command =
  | DeclareConst     of symbol * typ * attr list
  | DeclareDatatype  of symbol * dt_dec
  | DeclareDatatypes of (sort_dec list) * (dt_dec list)
  | Echo             of string
  | Exit
  | Reset
  | SetOption        of attr

(* commands exclusive to eunoia *)
type eo_command =
  | Assume            of symbol * term
  | AssumePush        of symbol * term
  | DeclareConsts     of symbol * typ * (attr list)
  | DeclareParamConst of symbol * param list * typ * attr list
  | DeclareRule       of symbol * rl_dec
  | Define            of symbol * param list * term * attr list
  | Include           of string
  | Program           of symbol * param list * (typ list * typ) * ((term * term) list)
  | Reference         of string * symbol
  | Step              of symbol * term option * symbol * simple_premises * arguments
  | StepPop           of symbol * term option * symbol * simple_premises * arguments
  | CommonEO          of common_command

(* deprecated stuff. *)
type smt2_command =
  | Assert           of term
  | CheckSat
  | CheckSatAssuming of term list
  | DeclareFun       of symbol * typ list * typ * attr list
  | DeclareSort      of symbol * int
  | DefineConst      of symbol * term
  | DefineFun        of symbol * param list * typ * term
  | DefineSort       of symbol * symbol list * typ
  | SetInfo          of attr
  | SetLogic         of symbol
  | CommonSMT        of common_command
