type symbol =
  | Symbol of string

let symbol_str =
  function (Symbol s) -> s

type keyword =
  | Colon of string

let keyword_str =
  function (Colon s) -> s

type lit_category =
  NUM | DEC | RAT | BIN | HEX | STR

let lit_category_str =
  function
  | NUM -> "<numeral>"
  | DEC -> "<decimal>"
  | RAT -> "<decimal>"
  | BIN -> "<binary>"
  | HEX -> "<hexadecimal>"
  | STR -> "<string>"

type literal =
  | Numeral of int
  | Decimal of float
  | Rational of int * int
  | String of string


let literal_str =
  function
  | Numeral n -> string_of_int n
  | Decimal d -> string_of_float d
  | Rational (n, d) -> string_of_int n ^ "/" ^ string_of_int d
  | String s -> "\"" ^ s ^ "\""


type term =
  | Sym of symbol
  | Literal of literal
  | Bind of symbol * ((symbol * term) list) * term
  | Apply of symbol * (term list)
  | Bang of term * (attr list)
and attr =
  | Attr of keyword * (term option)
and atts = attr list

let list_str (f : 'a -> string) =
  fun xs -> (String.concat " " (List.map f xs))

let list_suffix_str (f : 'a -> string) =
  function
  | [] -> ""
  | ys -> " " ^ (list_str f ys)

let rec
  var_str = fun (s,t) ->
    Printf.sprintf "%s ≔ %s"
      (symbol_str s)
      (term_str t)
and
  attr_str = function (Attr (kw,t_opt)) ->
    let kw_str = keyword_str kw in
    match t_opt with
    | Some t -> Printf.sprintf ":%s %s" kw_str (term_str t)
    | None   -> Printf.sprintf ":%s" kw_str
and
  term_str = function
  | Sym s       -> symbol_str s
  | Literal l   -> literal_str l
  | Bind (b, xs, t) ->
      let xs' = List.map var_str xs in
      Printf.sprintf "(%s %s in %s)"
        (symbol_str b)
        (String.concat ", " xs')
        (term_str t)
  | Apply (s, ts) ->
      Printf.sprintf "(%s %s)"
        (symbol_str s)
        (String.concat " " (List.map term_str ts))
  | Bang (t, xs) ->
      Printf.sprintf "(! %s %s)"
        (term_str t)
        (list_str attr_str xs)
and term_list_str = fun ts ->
  String.concat " " (List.map term_str ts)



type param =
  | Param of symbol * term * (attr list)
type params = param list

let param_str = function
  | (Param (s,t,xs)) ->
    Printf.sprintf "(%s %s%s)"
      (symbol_str s)
      (term_str t)
      (list_suffix_str attr_str xs)

type cases = (term * term) list

let term_pair_str (t,t') =
  Printf.sprintf "(%s %s)"
    (term_str t)
    (term_str t')

let cases_str = list_str term_pair_str

(* types for datatype declarations *)
type sort_dec =
  | SortDec of symbol * int
and sel_dec =
  | SelDec of symbol * term
and cons_dec =
  | ConsDec of symbol * (sel_dec list)
and dt_dec =
  | DatatypeDec of cons_dec list

let sort_dec_str = function
  | SortDec (s,n) ->
      Printf.sprintf "(%s %d)" (symbol_str s) n
and sel_dec_str = function
  | SelDec (s,t) ->
      Printf.sprintf "(%s %s)" (symbol_str s) (term_str t)
let cons_dec_str = function
  | ConsDec (s, xs) ->
      Printf.sprintf "(%s %s)"
        (symbol_str s)
        (String.concat " " (List.map sel_dec_str xs))
let dt_dec_str = function
  | DatatypeDec xs ->
      Printf.sprintf "(%s)"
        (String.concat " " (List.map cons_dec_str xs))

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
  | Requires of cases
and conclusion =
  | Conclusion of term
  | ConclusionExplicit of term
and rule_dec =
  | RuleDec of
      assumption option * premises option *
      arguments option * reqs option * conclusion

let assumption_str = function
  | Assumption t ->
      Printf.sprintf ":assumption %s" (term_str t)
and simple_premises_str = function
  | Premises ts ->
      Printf.sprintf ":premises %s"
        (String.concat " " (List.map term_str ts))
let premises_str = function
  | Simple sp -> simple_premises_str sp
  | PremiseList (t, t') ->
      Printf.sprintf ":premsie-list %s %s"
        (term_str t)
        (term_str t')
and arguments_str = function
  | Args ts -> Printf.sprintf ":args %s" (term_list_str ts)
and reqs_str = function
  | Requires cs ->
      Printf.sprintf ":requires (%s)"
        (cases_str cs)
and conclusion_str = function
  | Conclusion t ->
      Printf.sprintf ":conclusion %s" (term_str t)
  | ConclusionExplicit t ->
      Printf.sprintf ":conclusion-explicit %s" (term_str t)

let opt_newline (f : 'a -> string) (x_opt : 'a option) =
    match x_opt with
    | Some x -> Printf.sprintf "  %s\n" (f x)
    | None -> ""

let opt_str (f : 'a -> string) =
  Option.fold ~none:"" ~some:f

let opt_suffix_str (f : 'a -> string) =
  Option.fold ~none:"" ~some:(fun x -> " " ^ (f x))

let rule_dec_str = function
  | RuleDec (assm_opt, prems_opt, args_opt, reqs_opt, conc)
    -> Printf.sprintf "%s%s%s%s%s"
        (opt_newline assumption_str assm_opt)
        (opt_newline premises_str prems_opt)
        (opt_newline arguments_str args_opt)
        (opt_newline reqs_str reqs_opt)
        (opt_newline conclusion_str (Some conc))


type common_command =
  | DeclareConst     of symbol * term * attr list
  | DeclareDatatype  of symbol * dt_dec
  | DeclareDatatypes of (sort_dec list) * (dt_dec list)
  | Echo             of string option
  | Exit
  | Reset
  | SetOption        of attr

let common_command_str = function
  | DeclareConst (s,t,xs) ->
      Printf.sprintf "(declare-const %s %s %s)"
        (symbol_str s)
        (term_str t)
        (list_suffix_str attr_str xs)
  | DeclareDatatype (s,dt) ->
      Printf.sprintf "(declare-datatype %s %s)"
        (symbol_str s)
        (dt_dec_str dt)
  | DeclareDatatypes (xs,ys) ->
      Printf.sprintf "(declare-datatypes (%s) (%s))"
        (String.concat "" (List.map sort_dec_str xs))
        (String.concat "" (List.map dt_dec_str ys))
  | Echo (str_opt) ->
      Printf.sprintf "(echo%s)"
        (opt_suffix_str (fun x -> x) str_opt)
  | Reset -> "(reset)"
  | SetOption x ->
      Printf.sprintf "(set-option %s)" (attr_str x)

(* commands exclusive to eunoia *)
type eo_command =
  | Assume            of symbol * term
  | AssumePush        of symbol * term
  | DeclareConsts     of lit_category * term
  | DeclareParamConst of symbol * params * term * attr list
  | DeclareRule       of symbol * params * rule_dec * attr list
  | Define            of symbol * params * term * (term option)
  | Include           of string
  | Program           of symbol * params
                         * (term list * term)
                         * cases
  | Reference         of string * symbol option
  | Step              of symbol * term option * symbol * simple_premises option * arguments option
  | StepPop           of symbol * term option * symbol * simple_premises option * arguments option
  | Common            of common_command


let eo_command_str = function
  | Assume (s,t) ->
      Printf.sprintf "(assume %s %s)"
        (symbol_str s)
        (term_str t)
  | AssumePush (s,t) ->
      Printf.sprintf "(assume-push %s %s)"
        (symbol_str s)
        (term_str t)
  | DeclareConsts (lc,t) ->
      Printf.sprintf "(declare-consts %s %s)"
        (lit_category_str lc)
        (term_str t)
  | DeclareParamConst (s,xs,t,ys) ->
      Printf.sprintf
        "(declare-parameterized-const %s (%s) %s%s)"
        (symbol_str s)
        (list_str param_str xs)
        (term_str t)
        (list_suffix_str attr_str ys)
  | DeclareRule (s,xs,rdec,ys) ->
      Printf.sprintf "(declare-rule %s (%s)\n%s%s)"
        (symbol_str s)
        (list_str param_str xs)
        (rule_dec_str rdec)
        (list_suffix_str attr_str ys)
  | Define (s,xs,t,t_opt) ->
      Printf.sprintf "(define %s (%s)\n %s%s\n)"
        (symbol_str s)
        (list_str param_str xs)
        (term_str t)
        (opt_suffix_str term_str t_opt)
  | Include s ->
      Printf.sprintf "(include '%s')" s
  | Program (s,xs,(ts,t),cs) ->
      Printf.sprintf
        "(program %s (%s)\n  :signature (%s) %s\n (%s\n )\n)"
        (symbol_str s)
        (list_str param_str xs)
        (term_list_str ts)
        (term_str t)
        (cases_str cs)
  | Reference (str, s_opt) ->
      Printf.sprintf "(reference %s %s)"
        str (opt_str symbol_str s_opt)
  | Step (s,t_opt,s',sp_opt,args_opt) ->
      Printf.sprintf "(step %s %s %s%s%s)"
        (symbol_str s)
        (opt_str term_str t_opt)
        (symbol_str s')
        (opt_suffix_str simple_premises_str sp_opt)
        (opt_suffix_str arguments_str args_opt)
  | StepPop (s,t_opt,s',sp_opt,args_opt) ->
      Printf.sprintf "(step-pop %s %s %s%s%s)"
        (symbol_str s)
        (opt_str term_str t_opt)
        (symbol_str s')
        (opt_suffix_str simple_premises_str sp_opt)
        (opt_suffix_str arguments_str args_opt)
  | Common c ->
      common_command_str c

(* deprecated stuff. *)
(* type smt2_command =
  | Assert           of term
  | CheckSat
  | CheckSatAssuming of term list
  | DeclareFun       of symbol * typ list * typ * attr list
  | DeclareSort      of symbol * int
  | DefineConst      of symbol * term
  | DefineFun        of symbol * params * typ * term
  | DefineSort       of symbol * symbol list * typ
  | SetInfo          of attr
  | SetLogic         of symbol
  | CommonSMT        of common_command *)
