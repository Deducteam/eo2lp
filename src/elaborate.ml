(* elaborate.ml
   Elaboration with overloading resolution

   Handles:
   - N-ary operators (assoc-nil attributes)
   - Binders (:binder attribute)
   - Defined symbol expansion
   - Overloading resolution via LambdaPi *)

open Syntax_eo

let is_nary_binop = function
  | "eo::and" | "eo::or" | "eo::xor"
  | "eo::add" | "eo::mul" | "eo::concat" -> true
  | _ -> false

(* Check if type returns `Type` (type constructor) *)
let rec returns_type = function
  | Symbol "Type" -> true
  | Apply ("->", ts) when ts <> [] ->
    returns_type (L.hd (L.rev ts))
  | _ -> false

let wt _ = true

let glue (ps, f) t1 t2 =
  match t1 with
  | Symbol s when prm_has_attr s List ps ->
    Apply ("eo::list_concat", [f; t1; t2])
  | _ ->
    app_ho_list f [t1; t2]

(* Main elaboration *)

let rec elab (sgn, ps as ctx : context) t =
  elab_inner ctx t

and elab_inner (sgn, ps as ctx : context) = function
  (* literals, Type, -> *)
  | Literal _ | Symbol "Type" | Symbol "->" as t ->
    t

  (* symbols *)
  | Symbol s ->
    begin match L.assoc_opt s sgn with
    | Some (Defn ([], Symbol s')) ->
      elab ctx (Symbol s')
    | _ ->
      Symbol s
    end

  (* applications *)
  | Apply (s, ts) ->
    if is_builtin s then
      Apply (s, L.map (elab ctx) ts)
    else begin
      match prm_find s ps with
      | Some (s, ty, ao) ->
        app_ho_list (Symbol s) (L.map (elab ctx) ts)
      | None ->
        begin match
          sgn |> L.filter_map (function
            | (s', k) when s = s' ->
              let t' = elab_nary ctx (s, k, ts) in
              if wt t' then Some t' else None
            | _ -> None)
        with
        | t' :: _ -> t'
        | [] ->
          Printf.ksprintf failwith
            "Symbol `%s` not found in context." s
        end
    end

  (* eo::define as local let-binding *)
  | Bind ("eo::define", xs, t') ->
    begin match xs with
    | [] ->
      elab ctx t'
    | (x, tx) :: ys ->
      let tx' = elab ctx tx in
      let ctx' = (sgn, (x, Symbol "NONE", []) :: ps) in
      Bind ("eo::define", [(x, tx')],
        elab ctx' (Bind ("eo::define", ys, t')))
    end

  (* binder application *)
  | Bind (s, xs, t) ->
    begin match
      sgn |> L.filter_map (function
        | (s', k) when s = s' ->
          let t' = elab_binder ctx (s, k, xs, t) in
          if wt t' then Some t' else None
        | _ -> None)
    with
    | t' :: _ -> t'
    | [] ->
      Printf.ksprintf failwith
        "Symbol `%s` not found in context." s
    end

(* N-ary application elaboration *)

and elab_nary (sgn, ps as ctx : context) (s, k, ts) =
  match k with
  (* program constants: HO application *)
  | Prog _ ->
    app_ho_list (Symbol s) (L.map (elab ctx) ts)

  (* nullary macro - expand *)
  | Defn ([], body) ->
    begin match body with
    | Symbol s' when ts = [] ->
      elab ctx (Symbol s')
    | Symbol s' ->
      elab ctx (Apply (s', ts))
    | _ when ts = [] ->
      elab ctx body
    | _ ->
      Apply (s, L.map (elab ctx) ts)
    end

  | Defn (qs, t) ->
    Apply (s, L.map (elab ctx) ts)

  (* object-level constants *)
  | Decl (_, ty, ao) ->
    let ts' = L.map (elab ctx) ts in
    if returns_type ty then
      Apply (s, ts')
    else begin
      let g x y = glue (ps, Symbol s) x y in
      let h y x = glue (ps, Symbol s) y x in
      match ao with
      | None ->
        app_ho_list (Symbol s) ts'

      | Some RightAssocNil t_nil ->
        begin match ts with
        | [_; Symbol s'] when prm_has_attr s' List ps ->
          app_ho_list (Symbol s) ts'
        | _ ->
          L.fold_right g ts' (elab ctx t_nil)
        end

      | Some LeftAssocNil t_nil ->
        begin match ts with
        | [Symbol s'; _] when prm_has_attr s' List ps ->
          app_ho_list (Symbol s) ts'
        | _ ->
          L.fold_left h (elab ctx t_nil) ts'
        end

      | Some RightAssoc ->
        let (init, last) = L.chop ts' in
        L.fold_right g init last

      | Some LeftAssoc ->
        L.fold_left h (L.hd ts') (L.tl ts')

      | Some Chainable op ->
        let rec aux = function
          | v :: w :: vs ->
            (app_ho_list (Symbol s) [v; w]) :: aux (w :: vs)
          | _ -> []
        in
        elab ctx (Apply (op, aux ts))

      | Some Pairwise op ->
        let rec aux = function
          | v :: vs ->
            L.append
              (L.map
                (fun w -> app_ho_list (Symbol s) [v; w])
                vs)
              (aux vs)
          | [] -> []
        in
        elab ctx (Apply (op, aux ts))

      | Some RightAssocNilNSN t_nil ->
        L.fold_right g ts' (elab ctx t_nil)

      | Some LeftAssocNilNSN t_nil ->
        L.fold_left h (elab ctx t_nil) ts'

      | Some RightAssocNSN t_nil ->
        L.fold_right g ts' (elab ctx t_nil)

      | Some LeftAssocNSN t_nil ->
        L.fold_left h (elab ctx t_nil) ts'

      | Some (Binder _) ->
        app_ho_list (Symbol s) ts'

      | Some (ArgList _) ->
        app_ho_list (Symbol s) ts'

      | Some (LetBinder _) ->
        app_ho_list (Symbol s) ts'
    end

  | Ltrl _ | Rule _ ->
    failwith "Cannot elaborate Ltrl/Rule as nary"

(* Binder elaboration *)

and elab_binder ctx (s, k, xs, t) =
  match k with
  | Decl (_, _, Some Binder t_cons) ->
    let mk_var (s, t) =
      Apply ("eo::var", [Literal (String s); t])
    in
    let (sgn, outer_ps) = ctx in
    let bound_params =
      L.map (fun (n, ty) -> (n, ty, [])) xs
    in
    let ctx' = (sgn, outer_ps @ bound_params) in
    Apply (s, [Apply (t_cons, L.map mk_var xs); elab ctx' t])
  | _ ->
    failwith "No :binder attribute."

(* Auxiliary elaborators *)

and elab_prm ctx =
  L.map (fun (s, t, ao) -> (s, elab ctx t, ao))

and elab_cs ctx =
  L.map (fun (t, t') -> (elab ctx t, elab ctx t'))

and elab_const ctx = function
  | Decl (m, t, ao) ->
    Decl (m, elab ctx t, ao)

  | Defn (ps, t) ->
    let ps' = elab_prm ctx ps in
    let sgn, _ = ctx in
    let ctx' = (sgn, ps') in
    Defn (ps', elab ctx' t)

  | Prog (ps, doms, ran, cs) ->
    let sgn, outer_ps = ctx in
    let ps' = elab_prm ctx ps in
    let ctx_body = (sgn, outer_ps @ ps') in
    let doms' = L.map (elab ctx_body) doms in
    let ran' = elab ctx_body ran in
    let cs' = elab_cs ctx_body cs in
    Prog (ps', doms', ran', cs')

  | Ltrl (cat, ty) ->
    Ltrl (cat, elab ctx ty)

  | Rule (ps, assm, prems, args, reqs, conc) ->
    let ps' = elab_prm ctx ps in
    let sgn, outer_ps = ctx in
    let ctx' = (sgn, outer_ps @ ps') in
    Rule (ps', elab ctx' assm,
          L.map (elab ctx') prems,
          L.map (elab ctx') args,
          elab_cs ctx' reqs,
          elab ctx' conc)

(* Signature elaboration *)

let elab_hook : (string -> (unit -> 'a) -> 'a) ref =
  ref (fun _ f -> f ())

let elab_sig sgn =
  let rec aux sgn_acc = function
    | [] ->
      List.rev sgn_acc
    | (s, c) :: sgn_rest ->
      let ctx = (sgn_acc @ [(s, c)] @ sgn_rest, []) in
      let c' = !elab_hook s (fun () -> elab_const ctx c) in
      aux ((s, c') :: sgn_acc) sgn_rest
  in
  aux [] sgn

let elab_sig_with_ctx ctx_sig local_sig =
  let rec aux sgn_acc = function
    | [] ->
      List.rev sgn_acc
    | (s, c) :: sgn_rest ->
      let ctx =
        (ctx_sig @ sgn_acc @ [(s, c)] @ sgn_rest, [])
      in
      let c' = !elab_hook s (fun () -> elab_const ctx c) in
      aux ((s, c') :: sgn_acc) sgn_rest
  in
  aux [] local_sig
