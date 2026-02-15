(* pp_eo.ml
   Pretty-printing for Eunoia AST *)

open Syntax_eo
open Literal

(* Helpers *)

let opt_str f = Option.fold ~none:"" ~some:f

let opt_suffix_str f =
  Option.fold ~none:"" ~some:(fun x -> " " ^ f x)

let list_str f xs =
  String.concat " " (List.map f xs)

let list_suffix_str f = function
  | [] -> ""
  | ys -> " " ^ list_str f ys

(* Core term/attr printers (mutually recursive) *)

let rec var_str (str, t) =
  Printf.sprintf "(%s %s)" str (term_str t)

and symbol_attr_str = function
  | RightAssoc -> ":right-assoc"
  | LeftAssoc  -> ":left-assoc"
  | RightAssocNil t ->
    Printf.sprintf ":right-assoc-nil %s" (term_str t)
  | LeftAssocNil t ->
    Printf.sprintf ":left-assoc-nil %s" (term_str t)
  | RightAssocNilNSN t ->
    Printf.sprintf
      ":right-assoc-nil-non-singleton-nil %s"
      (term_str t)
  | LeftAssocNilNSN t ->
    Printf.sprintf
      ":left-assoc-nil-non-singleton-nil %s"
      (term_str t)
  | RightAssocNSN t ->
    Printf.sprintf
      ":right-assoc-non-singleton-nil %s"
      (term_str t)
  | LeftAssocNSN t ->
    Printf.sprintf
      ":left-assoc-non-singleton-nil %s"
      (term_str t)
  | Chainable s  -> Printf.sprintf ":chainable %s" s
  | Binder s     -> Printf.sprintf ":binder %s" s
  | Pairwise s   -> Printf.sprintf ":pairwise %s" s
  | ArgList s    -> Printf.sprintf ":arg-list %s" s
  | LetBinder t  ->
    Printf.sprintf ":let-binder %s" (term_str t)
  | Implicit     -> ":implicit"
  | Opaque       -> ":opaque"
  | List         -> ":list"
  | Syntax t     ->
    Printf.sprintf ":syntax %s" (term_str t)
  | Restrict t   ->
    Printf.sprintf ":restrict %s" (term_str t)

and term_str = function
  | Symbol str  -> str
  | Literal l   -> literal_str l
  | Bind (str, xs, t) ->
    let xs' = List.map var_str xs in
    Printf.sprintf "(%s (%s) %s)"
      str (String.concat ", " xs') (term_str t)
  | Apply (s, ts) ->
    Printf.sprintf "(%s %s)"
      s (String.concat " " (List.map term_str ts))

and term_list_str ts =
  String.concat " " (List.map term_str ts)

(* Parameter and case printers *)

let param_str (s, t, atts) =
  Printf.sprintf "(%s %s%s)"
    s (term_str t)
    (list_suffix_str symbol_attr_str atts)

let case_str (t, t') =
  Printf.sprintf "(%s %s)" (term_str t) (term_str t')

let case_list_str = list_str case_str

(* Rule declaration printers *)

let premises_str = function
  | Simple ts ->
    Printf.sprintf ":premises %s" (term_list_str ts)
  | PremiseList (t, t') ->
    Printf.sprintf ":premise-list %s %s"
      (term_str t) (term_str t')

let assumption_str t =
  Printf.sprintf ":assumption %s" (term_str t)

let arguments_str ts =
  Printf.sprintf ":args %s" (term_list_str ts)

let reqs_str cs =
  Printf.sprintf ":requires (%s)" (case_list_str cs)

let conclusion_str = function
  | Conclusion t ->
    Printf.sprintf ":conclusion %s" (term_str t)
  | ConclusionExplicit t ->
    Printf.sprintf ":conclusion-explicit %s" (term_str t)

let rule_dec_str ?(indent="  ") { assm; prem; args; reqs; conc } =
  let opt_list = function [] -> None | xs -> Some xs in
  let line f = function
    | Some x -> Printf.sprintf "%s%s\n" indent (f x)
    | None   -> ""
  in
  Printf.sprintf "%s%s%s%s%s"
    (line assumption_str assm)
    (line premises_str prem)
    (line arguments_str (opt_list args))
    (line reqs_str (opt_list reqs))
    (line conclusion_str (Some conc))

(* Symbol printers *)

let symbol_str = function
  | s, Decl (ps, t, ao) ->
    Printf.sprintf "(decl %s (%s) %s (%s))"
      s (list_str param_str ps)
      (term_str t) (opt_str symbol_attr_str ao)
  | s, Defn (ps, t, ty_opt) ->
    Printf.sprintf "(defn %s (%s) %s%s)"
      s (list_str param_str ps) (term_str t)
      (match ty_opt with None -> "" | Some ty -> " :type " ^ term_str ty)
  | s, Ltrl (cat, t) ->
    Printf.sprintf "(declare-consts %s %s)"
      (lit_category_str cat) (term_str t)
  | s, Prog (ps, doms, ran, cs) ->
    let cases = List.map case_str cs in
    Printf.sprintf "(prog %s ((%s)\n    :signature (%s) %s)\n  (%s))"
      s (list_str param_str ps)
      (term_list_str doms) (term_str ran)
      (String.concat "\n   " cases)
  | s, Rule (ps, rd) ->
    let body = rule_dec_str ~indent:"    " rd in
    let body = if String.ends_with ~suffix:"\n" body
      then String.sub body 0 (String.length body - 1) else body in
    Printf.sprintf "(rule %s (%s)\n%s)" s (list_str param_str ps) body
  | s, Assume t ->
    Printf.sprintf "(assume %s %s)" s (term_str t)
  | s, AssumePush t ->
    Printf.sprintf "(assume-push %s %s)" s (term_str t)
  | s, Step (rule_name, prems, args, conc_opt) ->
    Printf.sprintf "(step %s %s %s%s%s)"
      s rule_name
      (list_suffix_str term_str prems)
      (list_suffix_str term_str args)
      (opt_suffix_str term_str conc_opt)
  | s, StepPop (rule_name, prems, args, conc_opt) ->
    Printf.sprintf "(step-pop %s %s %s%s%s)"
      s rule_name
      (list_suffix_str term_str prems)
      (list_suffix_str term_str args)
      (opt_suffix_str term_str conc_opt)

let sig_str sgn =
  String.concat "\n" (List.map symbol_str sgn)
