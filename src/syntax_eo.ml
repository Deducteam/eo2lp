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

type param =
  | Param of symbol * term * (attr list)

(* types for datatype declarations *)
type sort_dec = symbol * int
and sel_dec = symbol * term
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
and rule_dec =
  | RuleDec of
      assumption option * premises option *
      arguments option * reqs option * conclusion


(* commands exclusive to eunoia *)
type eo_command =
  | Assume            of symbol * term
  | AssumePush        of symbol * term
  | DeclareConsts     of lit_category * term
  | DeclareParamConst of symbol * param list * term * attr list
  | DeclareRule       of symbol * rule_dec * attr list
  | Define            of symbol * param list * term * attr list
  | Include           of string
  | Program           of symbol * param list * (term list * term) * ((term * term) list)
  | Reference         of string * symbol option
  | Step              of symbol * term option * symbol * simple_premises option * arguments option
  | StepPop           of symbol * term option * symbol * simple_premises option * arguments option
  | Common            of common_command
and common_command =
  | DeclareConst     of symbol * term * attr list
  | DeclareDatatype  of symbol * dt_dec
  | DeclareDatatypes of (sort_dec list) * (dt_dec list)
  | Echo             of string
  | Exit
  | Reset
  | SetOption        of attr



(* deprecated stuff. *)
(* type smt2_command =
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
  | CommonSMT        of common_command *)
