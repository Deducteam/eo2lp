(* encode.ml
   Eunoia to LambdaPi encoding *)

module EO = Syntax_eo
open Api_lp

(* Re-exports for main.ml *)
let verbose     = Api_lp.verbose
let set_verbose = Api_lp.set_verbose

(* Overload management *)
let overload_counts : (string, int) Hashtbl.t =
  Hashtbl.create 32

let lit_type_substitutions : (string, string) Hashtbl.t =
  Hashtbl.create 8

let reset_overloads () =
  Hashtbl.clear overload_counts;
  reset_symbol_storage ()

let reset () =
  Api_lp.reset ();
  Hashtbl.clear lit_type_substitutions;
  reset_overloads ()

(* Literal encoding *)
let enc_literal = function
  | Literal.Numeral n ->
    enc_int n
  | Literal.Decimal d ->
    mk_Symb (ghost_sym (string_of_float d))
  | Literal.Rational (num, den) ->
    add_args
      (mk_Symb (find "{|eo::mkrat|}"))
      [enc_int num; enc_int den]
  | Literal.String s ->
    mk_Symb (ghost_sym ("\"" ^ s ^ "\""))
  | Literal.Binary b ->
    mk_Symb (ghost_sym ("#b" ^ b))
  | Literal.Hexadecimal h ->
    mk_Symb (ghost_sym ("#x" ^ h))

(* Term encoding *)
let rec enc_term ctx = function
  | EO.Symbol "Type" ->
    eo_type ()
  | EO.Symbol s ->
    (match ctxt_find ctx (esc s) with
     | Some v -> mk_Vari v
     | None   -> enc_sym (get_sym s))
  | EO.Literal lit ->
    enc_literal lit
  | EO.Apply ("->", args) ->
    enc_arrow ctx args
  | EO.Apply (("as" | "eo::as"), [ty; tm]) ->
    eo_as (enc_term ctx ty) (enc_term ctx tm)
  | EO.Apply ("_", [f; x]) ->
    hol_app (enc_term ctx f) (enc_term ctx x)
  | EO.Apply (s, ts) ->
    add_args
      (enc_sym (get_sym (esc s)))
      (List.map (enc_term ctx) ts)
  | EO.Bind ("eo::define", xs, body) ->
    List.fold_right
      (fun (s, t) acc ->
         Core.Term.mk_LLet
           (mk_Plac false,
            enc_term ctx t,
            bind_var (new_var s) acc))
      xs (enc_term ctx body)

and enc_arrow ctx = function
  | [] ->
    failwith "Empty arrow type"
  | [t] ->
    enc_term ctx t
  | EO.Apply ("eo::quote", [_]) :: _ ->
    failwith "TODO: dependent arrow"
  | t :: rest ->
    hol_arrow (enc_term ctx t) (enc_arrow ctx rest)

(* Parameter encoding *)
let enc_params ps =
  let ctx, impl =
    List.fold_left
      (fun (ctx, acc) (str, ty, atts) ->
         let v = new_var (esc str) in
         let ty' = tau_of (enc_term ctx ty) in
         let ctx' = ctxt_add ctx v ty' in
         let is_impl = List.mem EO.Implicit atts in
         (ctx', is_impl :: acc))
      (empty_ctxt, [])
      ps
  in
  (ctx, List.rev impl)

(* Constant encoding *)
type enc_result = {
  sym   : sym option;
  rules : (sym * rule) list;
}

let empty_result = { sym = None; rules = [] }

let enc_decl str ps ty _attr =
  let ctx, impl = enc_params ps in
  let ty', _ = ctxt_to_prod ctx (enc_term ctx ty) in
  { sym   = Some (add_constant ~impl (esc str) (tau_of ty'));
    rules = [] }

let enc_defn str ps tm =
  let ctx, impl = enc_params ps in
  let tm' = ctxt_to_abst ctx (enc_term ctx tm) in
  { sym   = Some (add_definition ~impl (esc str) None tm');
    rules = [] }

let enc_prog str ps doms ran _cases =
  let ctx, _ = enc_params ps in
  let ty_raw = EO.Apply ("->", doms @ [ran]) in
  let ty_params = EO.free_params ps ty_raw in
  let ty_ctx, _ = enc_params ty_params in
  let impl = List.map (fun _ -> true) ty_params in
  let ty, _ = Core.Ctxt.to_prod ty_ctx (enc_term ctx ty_raw) in
  { sym   = Some (add_sequential ~impl (esc str) ty);
    rules = [] }

let enc_ltrl cat ty =
  (match ty with
   | EO.Symbol ty_name -> EO.set_lit_type cat ty_name
   | _ -> ());
  (match ty, cat with
   | EO.Symbol n, Literal.NUM ->
     Hashtbl.replace lit_type_substitutions n "{|eo::Int|}"
   | EO.Symbol n, (Literal.DEC | Literal.RAT) ->
     Hashtbl.replace lit_type_substitutions n "{|eo::Rat|}"
   | EO.Symbol n, Literal.STR ->
     Hashtbl.replace lit_type_substitutions n "{|eo::String|}"
   | _ -> ());
  empty_result

let enc_const name = function
  | EO.Decl (ps, ty, attr) ->
    enc_decl name ps ty attr
  | EO.Defn (ps, body) ->
    enc_defn name ps body
  | EO.Prog (ps, doms, ran, cases) ->
    enc_prog name ps doms ran cases
  | EO.Ltrl (cat, ty) ->
    enc_ltrl cat ty
  | EO.Rule _ ->
    empty_result

(* Signature encoding *)
let enc_signature sig_ =
  reset_overloads ();
  let all_rules = ref [] in
  List.iter
    (fun (name, const) ->
       try
         let result = enc_const name const in
         all_rules := !all_rules @ result.rules
       with Failure msg ->
         if !verbose then
           Format.eprintf "  Skipping '%s': %s@." name msg)
    sig_;
  !all_rules
