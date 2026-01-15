open Syntax_eo
(* ============================================================
   Elaboration with Overloading Resolution

   This module elaborates Eunoia terms, handling:
   - N-ary operators (:right-assoc-nil, :left-assoc-nil, etc.)
   - Binders (:binder attribute)
   - Defined symbol expansion
   - Overloading resolution via LambdaPi typechecking
   ============================================================ *)

let wt : term -> bool = fun t -> true
let glue (ps, f : param list * term)
  : term -> term -> term =
  (fun t1 t2 ->
    match t1 with
    | Symbol s when prm_has_attr s List ps ->
      Apply ("eo::list_concat", [f; t1; t2])
    | _ -> app_ho_list f [t1; t2]
  )

(* ==== elaboration entry points ==== *)
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
(* ---- higher-order application. ---- *)
| Apply ("_", ts) ->
  begin match ts with
  | [t1;t2] -> Apply ("_",[elab ctx t1; elab ctx t2])
  | _ -> failwith "Invalid number of parameters for `_`."
  end
(* ---- first-order application. ---- *)
| Apply (s, ts) ->
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
    (* No attribute: curried HO application *)
    | None -> app_ho_list (Symbol s) ts'

    (* :right-assoc-nil *)
    | Some RightAssocNil t_nil ->
      begin match ts with
      | [_; Symbol s'] when prm_has_attr s' List ps ->
        app_ho_list (Symbol s) ts'
      | _ ->
        L.fold_right g ts' (elab ctx t_nil)
      end

    (* :left-assoc-nil *)
    | Some LeftAssocNil t_nil ->
      begin match ts with
      | [_; Symbol s'] when prm_has_attr s' List ps ->
        app_ho_list (Symbol s) ts'
      | _ ->
        L.fold_left h (elab ctx t_nil) ts'
      end

    (* :right-assoc *)
    | Some RightAssoc ->
      let (init, last) = L.chop ts' in
      L.fold_right g init last

    (* :left-assoc *)
    | Some LeftAssoc ->
      L.fold_left h (L.hd ts') (L.tl ts')

    (* :chainable. *)
    | Some Chainable op ->
    (* e.g., (< a b c) => (and (< a b) (< b c)) *)
      let rec aux = function
        | v :: w :: vs ->
          (app_ho_list (Symbol s) [v; w]) :: aux (w :: vs)
        | _ -> []
      in
        elab ctx (Apply (op, aux ts))

    (* :pairwise *)
    | Some Pairwise op ->
    (* e.g., (distinct a b c) => (and (!= a b) (and (!= a c) (!= b c))) *)
      let rec aux = function
      | v :: vs ->
        L.append
          (L.map (fun w -> app_ho_list (Symbol s) [v; w]) vs)
          (aux vs)
        | [] -> []
      in
        elab ctx (Apply (op, aux ts))

    (* Non-singleton nil variants - treat like regular nil for now *)
    | Some RightAssocNilNSN t_nil ->
      L.fold_right g ts' (elab ctx t_nil)

    | Some LeftAssocNilNSN t_nil ->
      L.fold_left h (elab ctx t_nil) ts

    (* Other attributes *)
    | Some (Binder _) ->
      failwith "Binder attribute should be handled by elab_binder"

    | Some (ArgList _) ->
      failwith "ArgList attribute not yet implemented"
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
      Apply (s, [Apply (t_cons, L.map mk_var xs); t])

  | _ ->
    failwith "No :binder attribute."

(* ============================================================
   Helper Functions for Parameters and Cases
   ============================================================ *)

let elab_prm (ctx : context) : param list -> param list =
  L.map (fun (s, t, ao) -> (s, elab ctx t, ao))

let elab_cs (ctx : context) : case list -> case list =
  L.map (fun (t, t') -> (elab ctx t, elab ctx t'))
