(* elaborate.ml
   Elaboration with overloading resolution

   Handles:
   - N-ary operators (assoc-nil attributes)
   - Binders (:binder attribute)
   - Defined symbol expansion
   - Overloading resolution via LambdaPi *)

open Syntax_eo

(* Global signature for elaboration *)
let global_sig : signature ref = ref empty_sig

let set_signature s = global_sig := s

(* Lookup a symbol by name in the global signature or core prelude *)
let lookup_symbol name : symbol option =
  match sig_find_by_name !global_sig name with
  | sid :: _ ->
    (match sig_find !global_sig sid with
     | Some entry -> Some entry.se_def
     | None -> None)
  | [] ->
    (* Fall back to core prelude *)
    L.assoc_opt name !core_prelude

(* Find all symbols with a given name *)
let find_all_symbols name : (string * symbol) list =
  let from_sig = sig_find_by_name !global_sig name
    |> L.filter_map (fun sid ->
         match sig_find !global_sig sid with
         | Some entry -> Some (sid.sid_name, entry.se_def)
         | None -> None)
  in
  if from_sig <> [] then from_sig
  else
    (* Fall back to core prelude *)
    match L.assoc_opt name !core_prelude with
    | Some def -> [(name, def)]
    | None -> []

(* Error handling with context *)
let current_symbol = ref ""

let fail msg =
  if !current_symbol = "" then failwith msg
  else failwith (Printf.sprintf "[elaborate:%s] %s" !current_symbol msg)

let failf fmt = Printf.ksprintf fail fmt

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

let rec elab (ps : context) t =
  elab_inner ps t

and elab_inner (ps : context) = function
  (* literals, Type, -> *)
  | Literal _ | Symbol "Type" | Symbol "->" as t ->
    t

  (* symbols *)
  | Symbol s ->
    begin match lookup_symbol s with
    | Some (Defn ([], Symbol s', _)) ->
      elab ps (Symbol s')
    | _ ->
      Symbol s
    end

  (* eo::typeof x -> expand to the type of x from context *)
  | Apply ("eo::typeof", [Symbol s]) ->
    begin match prm_find s ps with
    | Some (_, ty, _) -> ty  (* Return the type directly *)
    | None ->
      (* Variable not in context - keep as-is for later resolution *)
      Apply ("eo::typeof", [Symbol s])
    end

  (* applications *)
  | Apply (s, ts) ->
    if is_builtin s then
      (* Handle n-ary builtins like eo::add, eo::mul by folding to binary *)
      if is_nary_binop s && L.length ts > 2 then
        let ts' = L.map (elab ps) ts in
        L.fold_left (fun acc t -> Apply (s, [acc; t])) (L.hd ts') (L.tl ts')
      else
        Apply (s, L.map (elab ps) ts)
    else begin
      match prm_find s ps with
      | Some (s, ty, ao) ->
        app_ho_list (Symbol s) (L.map (elab ps) ts)
      | None ->
        begin match
          find_all_symbols s |> L.filter_map (fun (s', k) ->
            if s = s' then
              let t' = elab_nary ps (s, k, ts) in
              if wt t' then Some t' else None
            else None)
        with
        | t' :: _ -> t'
        | [] ->
          failf "Symbol `%s` not found" s
        end
    end

  (* eo::define as local let-binding *)
  | Bind ("eo::define", xs, t') ->
    begin match xs with
    | [] ->
      elab ps t'
    | (x, tx) :: ys ->
      let tx' = elab ps tx in
      let ps' = (x, Symbol "NONE", []) :: ps in
      Bind ("eo::define", [(x, tx')],
        elab ps' (Bind ("eo::define", ys, t')))
    end

  (* binder application *)
  | Bind (s, xs, t) ->
    begin match
      find_all_symbols s |> L.filter_map (fun (s', k) ->
        if s = s' then
          let t' = elab_binder ps (s, k, xs, t) in
          if wt t' then Some t' else None
        else None)
    with
    | t' :: _ -> t'
    | [] ->
      failf "Binder `%s` not found" s
    end

(* N-ary application elaboration *)

and elab_nary (ps : context) (s, k, ts) =
  match k with
  (* program constants: shallow application. *)
  | Prog _ ->
    Apply (s, (L.map (elab ps) ts))

  (* nullary macro - expand *)
  | Defn ([], body, _) ->
    begin match body with
    | Symbol s' when ts = [] ->
      elab ps (Symbol s')
    | Symbol s' ->
      elab ps (Apply (s', ts))
    | _ when ts = [] ->
      elab ps body
    | _ ->
      Apply (s, L.map (elab ps) ts)
    end

  | Defn (qs, t, _) ->
    Apply (s, L.map (elab ps) ts)

  (* object-level constants. deep application using `_`. *)
  | Decl (_, ty, ao) ->
    let ts' = L.map (elab ps) ts in
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
          L.fold_right g ts' (elab ps t_nil)
        end

      | Some LeftAssocNil t_nil ->
        begin match ts with
        | [Symbol s'; _] when prm_has_attr s' List ps ->
          app_ho_list (Symbol s) ts'
        | _ ->
          L.fold_left h (elab ps t_nil) ts'
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
        elab ps (Apply (op, aux ts))

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
        elab ps (Apply (op, aux ts))

      | Some RightAssocNilNSN t_nil ->
        L.fold_right g ts' (elab ps t_nil)

      | Some LeftAssocNilNSN t_nil ->
        L.fold_left h (elab ps t_nil) ts'

      | Some RightAssocNSN t_nil ->
        L.fold_right g ts' (elab ps t_nil)

      | Some LeftAssocNSN t_nil ->
        L.fold_left h (elab ps t_nil) ts'

      | Some (Binder _) ->
        app_ho_list (Symbol s) ts'

      | Some (ArgList _) ->
        app_ho_list (Symbol s) ts'

      | Some (LetBinder _) ->
        app_ho_list (Symbol s) ts'
    end

  | Ltrl _ | Rule _ ->
    fail "Cannot elaborate Ltrl/Rule as nary"

(* Binder elaboration *)

and elab_binder (ps : context) (s, k, xs, t) =
  match k with
  | Decl (_, _, Some Binder t_cons) ->
    let mk_var (s, t) =
      Apply ("eo::var", [Literal (String s); t])
    in
    let bound_params =
      L.map (fun (n, ty) -> (n, ty, [])) xs
    in
    let ps' = ps @ bound_params in
    Apply (s, [Apply (t_cons, L.map mk_var xs); elab ps' t])
  | _ ->
    failf "No :binder attribute for `%s`" s

(* Auxiliary elaborators *)

and elab_prm ps =
  L.map (fun (s, t, ao) -> (s, elab ps t, ao))

and elab_cs ps =
  L.map (fun (t, t') -> (elab ps t, elab ps t'))

and elab_symbol (ps : context) = function
  | Decl (m, t, ao) ->
    Decl (m, elab ps t, ao)

  | Defn (params, t, ty_opt) ->
    let params' = elab_prm ps params in
    let ps' = params' in
    Defn (params', elab ps' t, Option.map (elab ps') ty_opt)

  | Prog (params, doms, ran, cs) ->
    let params' = elab_prm ps params in
    let ps' = ps @ params' in
    let doms' = L.map (elab ps') doms in
    let ran' = elab ps' ran in
    let cs' = elab_cs ps' cs in
    Prog (params', doms', ran', cs')

  | Ltrl (cat, ty) ->
    Ltrl (cat, elab ps ty)

  | Rule (params, assm, prems, args, reqs, conc) ->
    let params' = elab_prm ps params in
    let ps' = ps @ params' in
    Rule (params', elab ps' assm,
          L.map (elab ps') prems,
          L.map (elab ps') args,
          elab_cs ps' reqs,
          elab ps' conc)

  | Assume formula ->
    Assume (elab ps formula)

  | Step (rule_name, prems, args, conc_opt) ->
    Step (rule_name,
          L.map (elab ps) prems,
          L.map (elab ps) args,
          Option.map (elab ps) conc_opt)

(* Signature elaboration *)

let elab_hook : (string -> (unit -> 'a) -> 'a) ref =
  ref (fun _ f -> f ())

(* Elaborate all symbols in the global signature *)
let elab_sig () : (string * symbol) list =
  let order = sig_topo_sort !global_sig in
  L.map (fun sid ->
    current_symbol := sid.sid_name;
    match sig_find !global_sig sid with
    | None -> failwith ("Symbol not found: " ^ SymbolId.to_string sid)
    | Some entry ->
      let c' = !elab_hook sid.sid_name (fun () -> elab_symbol [] entry.se_def) in
      current_symbol := "";
      (sid.sid_name, c')
  ) order

(* Elaborate symbols for a specific module *)
let elab_module (mod_path : path) : (string * symbol) list =
  let syms = sig_module_symbols !global_sig mod_path in
  L.map (fun (name, def) ->
    current_symbol := name;
    let c' = !elab_hook name (fun () -> elab_symbol [] def) in
    current_symbol := "";
    (name, c')
  ) syms
