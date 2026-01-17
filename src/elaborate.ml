open Syntax_eo
(* ============================================================
   Elaboration with Overloading Resolution

   This module elaborates Eunoia terms, handling:
   - N-ary operators (:right-assoc-nil, :left-assoc-nil, etc.)
   - Binders (:binder attribute)
   - Defined symbol expansion
   - Overloading resolution via LambdaPi typechecking
   ============================================================ *)
let debug = ref true

(* Check if a type has return type `Type` (i.e., is a type constructor) *)
let rec returns_type : term -> bool = function
  | Symbol "Type" -> true
  | Apply ("->", ts) when ts <> [] -> returns_type (L.hd (L.rev ts))
  | _ -> false

let wt : term -> bool = fun t -> true
let glue (ps, f : param list * term)
  : term -> term -> term =
  (fun t1 t2 ->
    match t1 with
    | Symbol s when prm_has_attr s List ps ->
      Apply ("eo::list_concat", [f; t1; t2])
    | _ -> app_ho_list f [t1; t2]
  )

let rec elab (sgn, ps as ctx : context)
  : term -> term =
fun t ->
  elab_inner ctx t

and elab_inner (sgn, ps as ctx : context)
  : term -> term =
function
(* ---- literals, `Type`, and `->`. ---- *)
| Literal _ | Symbol "Type" | Symbol "->" as t -> t
(* ---- symbols. ----  *)
| Symbol s ->
  (* Check if this symbol is a nullary macro that should be expanded *)
  begin match sgn |> L.find_opt (fun (s', _) -> s = s') with
  | Some (_, Defn ([], Symbol s')) -> elab ctx (Symbol s')
  | _ -> Symbol s
  end
(* ---- applications. ---- *)
| Apply (s, ts) ->
  (* if !debug then
    Printf.printf "Elaborating: %s\n" (Syntax_eo.term_str (Apply (s, ts))); *)
  if is_builtin s then
    Apply (s, L.map (elab ctx) ts)
  else
    begin match prm_find s ps with
    | Some (s,ty,ao) ->
      app_ho_list (Symbol s) (L.map (elab ctx) ts)

    | None ->
      begin match
        sgn |> L.filter_map
          (function
          | (s', k) when s = s' ->
            let t' = elab_nary ctx (s,k,ts) in
            if wt t' then Some t' else None
          | _ -> None)
        with
        | t' :: _ -> t'
        | [] ->
          Printf.ksprintf failwith "Symbol `%s` not found in context." s
      end
    end
(* ---- eo::define as local let-binding. ---- *)
| Bind ("eo::define", xs, t') ->
    begin match xs with
    | [] -> elab ctx t'
    | (x,tx) :: ys ->
      let tx' = elab ctx tx in
      let ctx' = (sgn, (x, Symbol "NONE", []) :: ps) in
      Bind ("eo::define", [(x,tx')],
        elab ctx' (Bind ("eo::define", ys, t'))
      )
    end
(* ---- binder application. ---- *)
| Bind (s, xs, t) ->
  begin match
    sgn |> L.filter_map
      (function
      | (s', k) when s = s' ->
        let t' = elab_binder ctx (s,k,xs,t) in
        if wt t' then Some t' else None
      | _ -> None
      )
    with
    | t' :: _ -> t'
    | [] -> Printf.ksprintf failwith
      "Symbol `%s` not found in context." s
    end

(* ==== elaboration of n-ary applcation syntax. ====  *)
and elab_nary
    (sgn, ps as ctx : context)
    (s, k, ts : string * const * term list)
  : term =
  match k with
  (* program constants. descend and elaborate arguments. *)
  | Prog _ -> Apply (s, (L.map (elab ctx) ts))
  (* macro-level constants. Expand if it's a simple abbreviation (no params, just a symbol). *)
  | Defn ([], Symbol s') when ts = [] ->
    (* Simple macro: (define @foo () @@foo) - expand to the target symbol *)
    elab ctx (Symbol s')

  | Defn ([], Symbol s') ->
    (* Simple macro with arguments - expand and apply arguments *)
    elab ctx (Apply (s', ts))

  | Defn (qs,t) -> Apply (s, (L.map (elab ctx) ts))
  (* object-level constants. *)
  | Decl (_,ty,ao) ->
    let ts' = (L.map (elab ctx) ts) in
    (* Type constructors (returning Type) use regular application, not HO application *)
    if returns_type ty then
      (* Type constructor: use simple Apply *)
      Apply (s, ts')
    else begin
      let g x y = glue (ps, Symbol s) x y in
      let h y x = glue (ps, Symbol s) y x in
      match ao with
      | None -> app_ho_list (Symbol s) ts'
      | Some RightAssocNil t_nil ->
        begin match ts with
        | [_; Symbol s'] when prm_has_attr s' List ps ->
          app_ho_list (Symbol s) ts'
        | _ ->
          L.fold_right g ts' (elab ctx t_nil)
        end
      | Some LeftAssocNil t_nil ->
        begin match ts with
        | [_; Symbol s'] when prm_has_attr s' List ps ->
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
          (L.map (fun w -> app_ho_list (Symbol s) [v; w]) vs)
          (aux vs)
        | [] -> []
      in
        elab ctx (Apply (op, aux ts))
    | Some RightAssocNilNSN t_nil -> L.fold_right g ts' (elab ctx t_nil)
    | Some LeftAssocNilNSN t_nil -> L.fold_left h (elab ctx t_nil) ts'
    | Some RightAssocNSN t_nil -> L.fold_right g ts' (elab ctx t_nil)
    | Some LeftAssocNSN t_nil -> L.fold_left h (elab ctx t_nil) ts'
    | Some (Binder _) -> app_ho_list (Symbol s) ts'
      (* Printf.ksprintf failwith
      "Cannot elaborate application of `%s` to `%s`.
       Binder attribute should be handled by elab_binder" *)
       (* s (term_list_str ts) *)
    | Some (ArgList _) -> app_ho_list (Symbol s) ts'
    | Some (LetBinder _) -> app_ho_list (Symbol s) ts'
    end

(* ==== elaboration of binder syntax. ====  *)
and elab_binder
  (ctx : context)
  (s, k, xs, t : string * const * var list * term)
  : term =
  match k with
  | Decl (_,_, Some Binder t_cons) ->
      let mk_var (s, t) =
        Apply ("eo::var", [Literal (String s); t])
      in
      Apply (s, [Apply (t_cons, L.map mk_var xs); elab ctx t])
  | _ ->
    failwith "No :binder attribute."

and elab_prm (ctx : context) : param list -> param list =
  L.map (fun (s, t, ao) -> (s, elab ctx t, ao))

and elab_cs (ctx : context) : case list -> case list =
  L.map (fun (t, t') -> (elab ctx t, elab ctx t'))

and elab_const (ctx : context) : const -> const =
  function
  | Decl (m, t, ao) ->
    Decl (m, elab ctx t, ao)
  | Defn (ps, t) ->
    let ps' = elab_prm ctx ps in
    let sgn, _ = ctx in
    let ctx' = (sgn, ps') in
    Defn (ps', elab ctx' t)
  | Prog ((ps, ty), (qs, cs)) ->
    let sgn, outer_ps = ctx in
    let ps' = elab_prm ctx ps in
    let ctx_ty = (sgn, outer_ps @ ps') in
    let ty' = elab ctx_ty ty in
    let qs' = elab_prm ctx qs in
    let ctx_cs = (sgn, outer_ps @ ps' @ qs') in
    let cs' = elab_cs ctx_cs cs in
    Prog ((ps', ty'), (qs', cs'))

let elab_hook : (string -> (unit -> 'a) -> 'a) ref = ref (fun _ f -> f ())

let elab_sig (sgn : signature) : signature =
  let rec aux sgn_acc sgn_rem =
    match sgn_rem with
    | [] -> List.rev sgn_acc
    | (s, c) :: sgn_rest ->
      (* if !debug then
        Printf.printf "      + %s\n" s; *)
      let ctx = (sgn_acc @ sgn_rem, []) in
      let c' = !elab_hook s (fun () -> elab_const ctx c) in

      aux ((s, c') :: sgn_acc) sgn_rest
  in
  aux [] sgn

(* Elaborate a local signature with an external context.
   ctx_sig: the full signature from dependencies (already elaborated)
   local_sig: the local signature to elaborate *)
let elab_sig_with_ctx (ctx_sig : signature) (local_sig : signature) : signature =
  let rec aux sgn_acc sgn_rem =
    match sgn_rem with
    | [] -> List.rev sgn_acc
    | (s, c) :: sgn_rest ->
      (* Context includes: external context + already elaborated locals + remaining locals *)
      let ctx = (ctx_sig @ sgn_acc @ sgn_rem, []) in
      let c' = !elab_hook s (fun () -> elab_const ctx c) in
      aux ((s, c') :: sgn_acc) sgn_rest
  in
  aux [] local_sig
