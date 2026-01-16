open Syntax_eo
(* ============================================================
   Elaboration with Overloading Resolution

   This module elaborates Eunoia terms, handling:
   - N-ary operators (:right-assoc-nil, :left-assoc-nil, etc.)
   - Binders (:binder attribute)
   - Defined symbol expansion
   - Overloading resolution via LambdaPi typechecking
   ============================================================ *)
let debug = ref false

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
function
(* ---- literals, `Type`, and `->`. ---- *)
| Literal _ | Symbol "Type" | Symbol "->" as t -> t
(* ---- symbols. ----  *)
| Symbol s ->
  begin match L.assoc_opt s sgn with
  | Some Defn (qs, t) ->
    if qs = [] then elab ctx t
    else Printf.ksprintf failwith
      "Lingering parameters from defined symbol %s." s
  | _ -> Symbol s
  end
(* ---- applications. ---- *)
| Apply (s, ts) ->
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
          | _ -> None
          )
        with
        | t' :: _ -> t'
        | [] -> Printf.ksprintf failwith
          "Symbol `%s` not found in context." s
      end
    end
(* ---- eo::define as local let-binding. ---- *)
| Bind ("eo::define", xs, t') ->
    let ys = xs |> L.map (fun (s,t) -> (s, elab ctx t)) in
    Bind ("eo::define", ys, elab ctx t')
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
  (* program constants. *)
  | Prog _ -> app_ho_list (Symbol s) (L.map (elab ctx) ts)
  (* defined constants. *)
  | Defn (qs,t) ->
    let t',ts' = (elab ctx t, L.map (elab ctx) ts) in
    let (qs',t'',ts'') = splice (qs,t',ts') in
    if qs' = [] then
      elab ctx (app_raw t'' ts'')
    else
      Printf.ksprintf failwith
        "Lingering parameters from defined symbol %s." s
  (* declared constants. *)
  | Decl (_,_,ao) ->
    let g x y = glue (ps, Symbol s) x y in
    let h y x = glue (ps, Symbol s) y x in
    let ts' = (L.map (elab ctx) ts) in
    begin match ao with
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

let elab_sig (sgn : signature) : signature =
  let rec aux sgn_acc sgn_rem =
    match sgn_rem with
    | [] -> List.rev sgn_acc
    | (s, c) :: sgn_rest ->
      if !debug then
        Printf.printf "Elaborating:\n%s\n" (const_str (s,c));
      let ctx = (sgn_acc @ sgn_rem, []) in
      let c' = elab_const ctx c in
      if !debug then
        Printf.printf "Done:\n%s\n\n" (const_str (s,c'));

      aux ((s, c') :: sgn_acc) sgn_rest
  in
  aux [] sgn
