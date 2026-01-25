(* resolve.ml
   Implicit argument resolution using LambdaPi *)

module Term = Core.Term

type term      = Term.term
type sym       = Term.sym
type rule      = Term.rule
type signature = Core.Sign.t

(* Resolution context *)

type resolve_ctx = {
  problem   : Term.problem;
  signature : signature;
}

let create_ctx sgn = {
  problem   = Term.new_problem ();
  signature = sgn;
}

(* Term resolution *)

let resolve_term ctx t =
  match Core.Infer.infer_noexn ctx.problem [] t with
  | Some (elaborated, _ty) ->
    let _ = Core.Unif.solve_noexn ctx.problem in
    Term.cleanup elaborated
  | None -> t

let resolve_term_check ctx t ty =
  match Core.Infer.check_noexn ctx.problem [] t ty with
  | Some elaborated ->
    let _ = Core.Unif.solve_noexn ctx.problem in
    Term.cleanup elaborated
  | None -> t

(* Rule resolution *)

let resolve_rule ctx _sym rule =
  let rhs' = resolve_term ctx rule.Term.rhs in
  { rule with Term.rhs = rhs' }

(* Symbol resolution *)

let resolve_symbol_def ctx sym =
  match Timed.(!(sym.Term.sym_def)) with
  | Some def ->
    let def' = resolve_term ctx def in
    Timed.(sym.Term.sym_def := Some def')
  | None -> ()

(* Batch resolution *)

let resolve_rules sgn rules =
  let ctx = create_ctx sgn in
  List.map (fun (sym, rule) ->
    (sym, resolve_rule ctx sym rule))
  rules

let resolve_definitions sgn =
  let ctx = create_ctx sgn in
  Lplib.Extra.StrMap.iter (fun _name sym ->
    resolve_symbol_def ctx sym)
  Timed.(!(failwith ""))

let resolve_all sgn rules =
  resolve_definitions sgn;
  resolve_rules sgn rules
