type lit_category =
  NUM | DEC | RAT | BIN | HEX | STR
and literal =
  | Numeral of int
  | Decimal of float
  | Rational of int * int
  | Binary of string
  | Hexadecimal of string
  | String of string

type term =
  | Symbol of string
  | Apply of string * (term list)
  | Literal of literal
  | Bind of string * (var list) * term
and var = (string * term)
and case = (term * term)

type const_attr =
  | RightAssocNil of term
  | RightAssocNilNSN of term
  | LeftAssocNil of term
  | LeftAssocNilNSN of term
  | RightAssoc
  | LeftAssoc
  | ArgList of string
  | Chainable of string
  | Pairwise of string
  | Binder of string
type param_attr =
  Implicit | Opaque | List

type param = string * term * (param_attr option)

type common_command =
  | DeclareConst     of string * term * (const_attr option)
  | DeclareDatatype  of string * dt_dec
  | DeclareDatatypes of (sort_dec list) * (dt_dec list)
  | Echo             of string option
  | Exit
  | Reset
  | SetOption        of string
and sort_dec =
  | SortDec of string * int
and sel_dec =
  | SelDec of string * term
and cons_dec =
  | ConsDec of string * (sel_dec list)
and dt_dec =
  | DatatypeDec of cons_dec list


(* type for Eunoia-exclusive commands *)
type command =
  | Assume            of string * term
  | AssumePush        of string * term
  | DeclareConsts     of lit_category * term
  | DeclareParamConst of string * param list * term * (const_attr option)
  | DeclareRule       of string * param list * rule_dec * (sorry option)
  | Define            of string * param list * term * (term option)
  | Include           of path
  | Program           of string * param list * (term list * term) * case list
  | Reference         of string * string option
  | Step              of string * term option * string * term list * term list
  | StepPop           of string * term option * string * term list * term list
  | Common            of common_command
(* types for `declare-rule` *)
and premises =
  | Simple of term list
  | PremiseList of term * term
and conclusion =
  | Conclusion of term
  | ConclusionExplicit of term
and rule_dec =
  {
    assm : term option;
    prem : premises option;
    args : term list;
    reqs : case list;
    conc : conclusion;
  }
and sorry = Sorry
(* type of paths for `include` *)
and path = string list

(* signature maps each symbol to its params/attr/type/def. *)
module M = Map.Make(String)

type level = Tm | Ty | Pg
type symdecl =
  | Decl of param list * term * const_attr option * level
  | Defn of param list * term
type signature = symdecl M.t
type context = signature * param list
type environment = (path * command list) list
(* ---- helpers -------- *)
(* ##########
  deprecated?
  no longer needed because we post-elab term datatype?

let _app ((t1,t2) : term * term) : term =
  Apply ("_", [t1;t2])

let _app_bin (f : term) : term * term -> term =
  fun (t1,t2) -> _app (_app (f,t1), t2)

let _app_list (f : term) (ts : term list) : term =
  List.fold_left (fun t_acc t -> _app (t_acc,t)) f ts
##########*)
module L = List

let rec is_kind : term -> bool =
  function
  | Symbol "Type" -> true
  | Apply ("->", ts) -> L.exists is_kind ts
  | _ -> false

(* can probably destroy all of this???  *)
let mk_eo_var (s,t : var) : term =
  Apply("eo::var", [Literal (String s); t])

let mk_proof (t : term) : term =
  Apply("Proof", [t])

let is_builtin (str : string) : bool =
  String.starts_with ~prefix:"eo::" str

let is_prog (str : string) : bool =
  not (str = "eo::List::cons" || str = "eo::List::nil")
  &&
  (is_builtin str || String.starts_with ~prefix:"$" str)

let is_def (s : string) (sgn : signature) =
  match M.find_opt s sgn with
  | Some (Defn _) -> true
  | _ -> false

let get_att_opt (s : string) (sgn : signature) =
  match M.find_opt s sgn with
  | Some (Decl (_,_,att_opt,_)) -> att_opt
  | None -> None

(* save signature info at parse time *)
let _sig : signature ref = ref (M.of_list
  [
    ("Type", Decl ([], Symbol "Kind", None, Ty))
  ])

let mk_arrow_ty (ts : term list) (t : term) : term =
  Apply ("->", List.append ts [t])

let mk_aux_str (str : string) : string =
  (str ^ "_aux")

let mk_reqs_tm ((t1,t2) : term * term) (t3 : term) : term =
  Apply ("eo::requires", [t1;t2;t3])

let mk_reqs_list_tm (cs : case list) (t : term) : term =
  List.fold_left (fun acc c -> mk_reqs_tm c acc) t cs

let mk_conc_tm (cs : case list) : conclusion -> term =
  function
  | Conclusion t ->
      mk_reqs_list_tm cs t
  | ConclusionExplicit t ->
      Printf.printf "WARNING! --- :conclusion-explicit\n";
      mk_reqs_list_tm cs t

let mk_arg_vars (arg_tys : term list) : (string * term) list =
  let arg_sym =
    (fun i t -> (("α" ^ string_of_int i), t))
  in
    List.mapi arg_sym arg_tys

(* find the type of `s` wrt. `ps`. *)
let find_param_typ_opt
  (s : string) (ps : param list) : term option =
  let f (s',t,_) =
    if s = s' then Some t else None
  in
    List.find_map f ps

(* find the attribute of `s` wrt. `ps`.  *)
let find_param_attr_opt
  (s : string) (ps : param list) : param_attr option =
  let f (s',_,att_opt) =
    if s = s' then att_opt else None
  in
    List.find_map f ps

let is_list_param =
  fun s ps -> (find_param_attr_opt s ps) = (Some List)

let lcat_of : literal -> lit_category =
  function
  | Numeral _  -> NUM
  | Decimal _  -> DEC
  | Rational _ -> RAT
  | Binary _   -> BIN
  | Hexadecimal _ -> HEX
  | String _      -> STR

(* ------------------------------------------------*)

(* ---- pretty printing -------- *)
let opt_newline (f : 'a -> string) (x_opt : 'a option) =
  match x_opt with
  | Some x -> Printf.sprintf "  %s\n" (f x)
  | None -> ""

let opt_str (f : 'a -> string) =
  Option.fold ~none:"" ~some:f

let opt_suffix_str (f : 'a -> string) =
  Option.fold ~none:"" ~some:(fun x -> " " ^ (f x))

(* TODO. introduce types for literal categories. *)
let lit_category_str =
  function
  | NUM -> "<numeral>"
  | DEC -> "<decimal>"
  | RAT -> "<decimal>"
  | BIN -> "<binary>"
  | HEX -> "<hexadecimal>"
  | STR -> "<string>"

let literal_str =
  function
  | Numeral n -> string_of_int n
  | Decimal d -> string_of_float d
  | Rational (n, d) ->
    string_of_int n ^ "/" ^ string_of_int d
  | String s -> "\"" ^ s ^ "\""
  | Binary _ -> Printf.printf
    "WARNING: unhandled binary."; ""
  | Hexadecimal _ -> Printf.printf
    "WARNING: unhandled hex."; ""

let list_str (f : 'a -> string) =
  fun xs -> (String.concat " " (List.map f xs))

let list_suffix_str (f : 'a -> string) =
  function
  | [] -> ""
  | ys -> " " ^ (list_str f ys)

let param_attr_str = function
  | Implicit -> ":implicit"
  | Opaque -> ":opaque"
  | List -> ":list"

let rec
  var_str = fun (str,t) ->
    Printf.sprintf "(%s %s)"
      str (term_str t)
and
  const_attr_str = function
  | RightAssoc -> ":right-assoc"
  | LeftAssoc  -> ":left-assoc"
  | RightAssocNil t ->
      Printf.sprintf ":right-assoc-nil %s" (term_str t)
  | LeftAssocNil t ->
      Printf.sprintf ":left-assoc-nil %s" (term_str t)
  | RightAssocNilNSN t ->
      Printf.sprintf ":right-assoc-nil-non-singleton-nil %s" (term_str t)
  | LeftAssocNilNSN t ->
      Printf.sprintf ":left-assoc-nil-non-singleton-nil %s" (term_str t)
  | Chainable s ->
      Printf.sprintf ":chainable %s" s
  | Binder s ->
      Printf.sprintf ":binder %s" s
  | Pairwise s ->
      Printf.sprintf ":pairwise %s" s
  | ArgList s ->
      Printf.sprintf ":arg-list %s" s
and
  term_str = function
  | Symbol str  -> str
  | Literal l   -> literal_str l
  | Bind (str, xs, t) ->
      let xs' = List.map var_str xs in
      Printf.sprintf "(%s (%s) %s)"
        str (String.concat ", " xs')
        (term_str t)
  | Apply (s, ts) ->
      Printf.sprintf "(%s %s)"
        s (String.concat " " (List.map term_str ts))
and term_list_str = fun ts ->
  String.concat " " (List.map term_str ts)

let param_str (s,t,att) =
  Printf.sprintf "(%s %s%s)"
    s (term_str t)
    (opt_suffix_str param_attr_str att)

let case_str (t,t') =
  Printf.sprintf "(%s %s)"
    (term_str t)
    (term_str t')

let case_list_str : case list -> string =
  list_str case_str

let sort_dec_str = function
  | SortDec (s,n) ->
      Printf.sprintf "(%s %d)" s n
and sel_dec_str = function
  | SelDec (s,t) ->
      Printf.sprintf "(%s %s)" s (term_str t)
let cons_dec_str = function
  | ConsDec (s, xs) ->
      Printf.sprintf "(%s %s)"
        s
        (String.concat " " (List.map sel_dec_str xs))
let dt_dec_str = function
  | DatatypeDec xs ->
      Printf.sprintf "(%s)"
        (String.concat " " (List.map cons_dec_str xs))

let premises_str = function
  | Simple ts ->
      Printf.sprintf ":premises %s"
      (term_list_str ts)
  | PremiseList (t, t') ->
      Printf.sprintf ":premsie-list %s %s"
      (term_str t) (term_str t')
and assumption_str t =
  Printf.sprintf ":assumption %s" (term_str t)
and arguments_str ts =
  Printf.sprintf ":args %s" (term_list_str ts)
and reqs_str cs =
  Printf.sprintf ":requires (%s)" (case_list_str cs)
and conclusion_str = function
  | Conclusion t ->
    Printf.sprintf ":conclusion %s" (term_str t)
  | ConclusionExplicit t ->
    Printf.sprintf ":conclusion-explicit %s" (term_str t)

let rule_dec_str ({assm; prem; args; reqs; conc} : rule_dec) : string =
  Printf.sprintf "%s%s%s%s%s"
    (opt_newline assumption_str assm)
    (opt_newline premises_str prem)
    (opt_newline arguments_str (Some args))
    (opt_newline reqs_str (Some reqs))
    (opt_newline conclusion_str (Some conc))

let common_command_str = function
  | DeclareConst (s,t,att) ->
      Printf.sprintf "(declare-const %s %s %s)"
        s (term_str t)
        (opt_suffix_str const_attr_str att)
  | DeclareDatatype (s,dt) ->
      Printf.sprintf "(declare-datatype %s %s)"
        s (dt_dec_str dt)
  | DeclareDatatypes (xs,ys) ->
      Printf.sprintf "(declare-datatypes (%s) (%s))"
        (String.concat "" (List.map sort_dec_str xs))
        (String.concat "" (List.map dt_dec_str ys))
  | Echo (str_opt) ->
      Printf.sprintf "(echo%s)"
        (opt_suffix_str (fun x -> x) str_opt)
  | Reset -> "(reset)"
  | SetOption x ->
      Printf.sprintf "(set-option %s)" (x)
  | Exit -> "(exit)"

let command_str = function
  | Assume (s,t) ->
      Printf.sprintf "(assume %s %s)"
        s (term_str t)
  | AssumePush (s,t) ->
      Printf.sprintf "(assume-push %s %s)"
        s (term_str t)
  | DeclareConsts (lc,t) ->
      Printf.sprintf "(declare-consts %s %s)"
        (lit_category_str lc)
        (term_str t)
  | DeclareParamConst (s,ps,t,att_opt) ->
      Printf.sprintf
        "(declare-parameterized-const %s (%s) %s%s)"
        s (list_str param_str ps)
        (term_str t)
        (opt_suffix_str const_attr_str att_opt)
  | DeclareRule (s,xs,rdec,sorry_opt) ->
      Printf.sprintf "(declare-rule %s (%s)\n%s\n%s)"
        s (list_str param_str xs)
        (rule_dec_str rdec)
        (opt_newline (fun _ -> ":sorry") sorry_opt)
  | Define (s,xs,t,t_opt) ->
      Printf.sprintf "(define %s (%s) %s%s)"
        s (list_str param_str xs)
        (term_str t)
        (opt_suffix_str term_str t_opt)
  | Include p ->
      Printf.sprintf "(include %s)" (String.concat "." p)
  | Program (s,xs,(ts,t),cs) ->
      Printf.sprintf
        "(program %s (%s) :signature (%s) %s (...))"
        s (list_str param_str xs)
        (term_list_str ts) (term_str t)
        (* (case_list_str cs) *)
  | Reference (str, s_opt) ->
      Printf.sprintf "(reference %s %s)"
        str (opt_str (fun x -> x) s_opt)
  | Step (s,t_opt,s',ts,ts') ->
      Printf.sprintf "(step %s %s %s%s%s)"
        s (opt_str term_str t_opt) s'
        (list_suffix_str term_str ts)
        (list_suffix_str term_str ts')
  | StepPop (s,t_opt,s',ts,ts') ->
      Printf.sprintf "(step-pop %s %s %s%s%s)"
        s (opt_str term_str t_opt) s'
        (list_suffix_str term_str ts)
        (list_suffix_str term_str ts')
  | Common c ->
      common_command_str c

(* TODO. actually implement *)
let ty_of (t : term) : term =
  Symbol ("TY[" ^  term_str t ^ "]")

(* ------------------------------------------------------ *)
