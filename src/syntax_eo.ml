open Literal
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
  | Program           of string
                       * (param list * term)
                       * (param list * case list)
  | Reference         of string * string option
  | Step              of string * term * string * term list * term list
  | StepPop           of string * term * string * term list * term list
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
and sorry = Sorry (* `:sorry` attribute for `declare-rule`.*)
and path = string list (* type of paths for `include`. *)

(* signature maps each symbol to its params/attr/type/def. *)

module L = struct
  include List
  let split_last (xs : 'a list) : ('a list * 'a) =
    let ys = List.rev xs in
    (List.rev (List.tl ys), List.hd ys)
end

module S = String
module M = Map.Make(S)


type level = Tm | Ty
type symbol =
  (* | Prm of term * param_attr * level *)
  | Dcl of param list * term * const_attr option * level
  | Dfn of param list * term
  | Prg of param list * term * case list * level
type signature = (string * symbol) list

let _sig : signature ref = ref []

let _sym : string * symbol -> unit =
  fun (s, sym) -> _sig := L.append !_sig [(s,sym)]

let att_of (s : string) (sgn : signature) : const_attr option =
  match L.assoc_opt s sgn with
  | Some Dcl (_,_,ao,_) -> ao
  | _ -> failwith "Invalid query."

type context = signature * param list

let _pn : string -> param -> bool =
  (fun s (s',_,_) -> s = s')
let _pa : param_attr -> param -> bool =
  (fun pa (_,_,pao) -> Some pa = pao)
let __pa : (string * param_attr) -> param list -> bool =
  fun (s,pa) -> L.exists (fun p -> _pn s p && _pa pa p)

type environment = (path * signature) list
let _env : environment ref = ref []

let rec is_kind : term -> bool =
  function
  | Symbol "Type" -> true
  | Apply ("->", ts) -> L.exists is_kind ts
  | _ -> false

let lv_of : term -> level =
  fun t -> if is_kind t then Ty else Tm

let app_raw : term -> term list -> term =
  fun t ts ->
    match t,ts with
    | (Symbol s, []) -> Symbol s
    | (Symbol s, ts) -> Apply (s, ts)
    | (Apply (s,ts), ts') -> Apply (s, L.append ts ts')

let app_ho : term -> term -> term =
  fun t t' -> Apply ("_", [t;t'])

let app_ho_list : term -> term list -> term =
  fun t ts -> L.fold_left app_ho t ts

let rec subst : term -> param -> term -> term =
  fun t p t' ->
    match t with
    | Symbol s -> if _pn s p then t' else t
    | Apply (s, ts) ->
      let ts' = L.map (fun t -> subst t p t') ts in
      if _pn s p
        then app_raw t' ts'
        else Apply (s, ts')

(* reduce application of explicit params.*)
let rec splice
    (ps,t,ts : param list * term * term list)
  : (param list * term * term list)
=
  match ps, ts with
  | (([],_)|(_,[])) -> (ps, t, ts)
  | (p :: ps, ts) when _pa Implicit p ->
      splice (ps, t, ts)
  | (p :: ps, t' :: ts) ->
      splice (ps, subst t p t', ts)

let glue (ps,f : param list * term)
  : term -> term -> term
=
  fun t1 t2 ->
    begin match t1 with
    | Symbol s when __pa (s,List) ps ->
      Apply ("eo::list_concat",[f;t1;t2])
    | _ ->
      app_ho_list f [t1;t2]
    end

let app_nary
  (ps : param list) (f,ts : term * term list)
  (ao : const_attr option) : term
=
  let g x y = glue (ps,f) x y in
  let h y x = glue (ps,f) y x in
  begin match ao with
  (* ---- *)
  | None -> app_ho_list f ts
  (* ---- *)
  | Some RightAssocNil t_nil -> (
    match ts with
    | [t1; Symbol s] when __pa (s,List) ps ->
      app_ho_list f ts
    | _ ->
      L.fold_right g ts t_nil
    )
  (* ---- *)
  | Some LeftAssocNil t_nil -> (
    match ts with
    | [t1; Symbol s] when __pa (s,List) ps ->
      app_ho_list f ts
    | _ ->
      L.fold_left h f ts
    )
  (* ---- *)
  | Some RightAssoc ->
    let (ts', t') =
      L.split_last ts
    in
      L.fold_right g ts' t'
  (* ---- *)
  | Some LeftAssoc ->
    let (t',ts') =
      (List.hd ts, List.tl ts)
    in
      L.fold_left h t' ts'
  (* ---- *)
  | Some Chainable op ->
    let rec aux =
      function
      | v :: w :: vs -> (app_ho_list f [v;w]) :: aux vs
      | _ -> []
    in
      Apply (op, aux ts)
  (* ---- *)
  | Some Pairwise op ->
    let rec aux =
      function
      | v :: vs ->
        L.append
          (L.map (fun w -> app_ho_list f [v;w]) vs)
          (aux vs)
      | [] -> []
    in
      Apply (op, aux ts)
  (* ---- *)
  | Some a ->
    failwith "unimplemented elaboration strategy."
  (* ---- *)
  end

let app_binder
  (f,xs,t : term * var list * term)
  (ao : const_attr option) : term =
  match ao with
  | Some Binder t_cons ->
    let mk_var = fun (s,t) ->
      Apply("eo::var", [Literal (String s); t])
    in
      app_ho_list f [Apply (t_cons, L.map mk_var xs); t]
  | None -> failwith "No :binder attribute."

let rec is_free
  (s : string) : term -> bool =
  function
  | Symbol s' -> s = s'
  | Apply (s',ts) -> (s = s') || L.exists (is_free s) ts
  | Literal _ -> false
  | Bind (s, vs, t) ->
    let b1 = List.exists (fun (_,ty) -> is_free s ty) vs
    and b2 = is_free s t in (b1 || b2)

let prog_ty
  (doms,ran : term list * term) : term
=
  Apply ("->", List.append doms [ran])

let prog_ty_params (t : term)
  : param list -> param list =
  let f (s,ty,_) =
    if is_free s t then
      Some (s, ty, Some Implicit)
    else
      None
  in
    L.filter_map f

let prog_cs_params (cs : case list)
  : param list -> param list =
  let f ((s,_,_) as p) =
    let g (t,t') = is_free s t || is_free s t' in
    if L.exists g cs then (Some p) else None
  in
    L.filter_map f

(* ---------------------------------------------- *)

let mk_proof (t : term) : term =
  Apply("Proof", [t])

let is_builtin (str : string) : bool =
  String.starts_with ~prefix:"eo::" str

let is_prog (str : string) : bool =
  not (str = "eo::List::cons" || str = "eo::List::nil")
  &&
  (is_builtin str || String.starts_with ~prefix:"$" str)

(* let get_att_opt (s : string) (sgn : signature) =
  match M.find_opt s sgn with
  | Some (Decl (_,_,att_opt,_)) -> att_opt
  | None -> None *)




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
  | Program (s,(ps,ty),(qs,cs)) ->
      Printf.sprintf
        "(program %s\n:type (%s) %s\n:cases (%s) (%s))"
        s (list_str param_str ps) (term_str ty)
          (list_str param_str qs) (case_list_str cs)
  | Reference (str, s_opt) ->
      Printf.sprintf "(reference %s %s)"
        str (opt_str (fun x -> x) s_opt)
  | Step (s,t_opt,s',ts,ts') ->
      Printf.sprintf "(step %s %s %s%s%s)"
        s (term_str t_opt) s'
        (list_suffix_str term_str ts)
        (list_suffix_str term_str ts')
  | StepPop (s,t_opt,s',ts,ts') ->
      Printf.sprintf "(step-pop %s %s %s%s%s)"
        s (term_str t_opt) s'
        (list_suffix_str term_str ts)
        (list_suffix_str term_str ts')
  | Common c ->
      common_command_str c

(* TODO. actually implement *)
let ty_of (t : term) : term =
  Symbol ("TY[" ^  term_str t ^ "]")

(* let symbol_str =
  function
  | Decl (ps, t, _) ->
    "Decl(" ^ S.concat ", " (L.map param_str ps) ^ ", " ^ term_str t ^ ")"
  | Prog (ps, t, cs) -> "Prog(" ^ S.concat ", " (L.map param_str ps) ^ ", " ^ term_str t ^ ", " ^ S.concat ", " (L.map case_str cs) ^ ")"
  | Defn (ps, t) -> "Defn(" ^ S.concat ", " (L.map param_str ps) ^ ", " ^ term_str t ^ ")"

(* ------------------------------------------------------ *) *)
