(* elaborate.ml
   Eunoia elaboration: normalize the Eunoia AST so that encode.ml
   can translate it to LambdaPi without consulting the Eunoia
   signature or parameter context.

   This module owns the Eunoia signature state and all decision
   logic: nullary define expansion, overload resolution, variable
   vs symbol dispatch, :list detection, n-ary attribute dispatch.

   Elaboration maps EO terms to EO terms. *)

module EO = Syntax_eo

(* ============================================================
   Eunoia signature state
   ============================================================ *)

let global_sig : EO.signature ref = ref []

(* Hash-based index for fast symbol lookup.
   sig_index maps name -> list of (name, symbol) pairs (for overloads).
   sig_single maps name -> first symbol (for single-match lookups).
   base_* tables cache the CPC portion, so per-proof rebuilds only
   process the proof-specific symbols (overlay). *)
let sig_index : (string, (string * EO.symbol) list) Hashtbl.t = Hashtbl.create 256
let sig_single : (string, EO.symbol) Hashtbl.t = Hashtbl.create 256
let base_index : (string, (string * EO.symbol) list) Hashtbl.t = Hashtbl.create 256
let base_single : (string, EO.symbol) Hashtbl.t = Hashtbl.create 256
let base_sig : EO.signature ref = ref []

let build_index_from sig_ tbl_index tbl_single =
  let rev_index : (string, (string * EO.symbol) list) Hashtbl.t =
    Hashtbl.create (max 16 (List.length sig_))
  in
  List.iter (fun (name, sym) ->
    if not (Hashtbl.mem tbl_single name) then Hashtbl.add tbl_single name sym;
    let prev = Option.value ~default:[] (Hashtbl.find_opt rev_index name) in
    Hashtbl.replace rev_index name ((name, sym) :: prev)
  ) sig_;
  Hashtbl.iter (fun name rev_list ->
    Hashtbl.replace tbl_index name (List.rev rev_list)
  ) rev_index

let rebuild_index () =
  Hashtbl.reset sig_index;
  Hashtbl.reset sig_single;
  build_index_from !global_sig sig_index sig_single

(* Snapshot the current index as the base (CPC) portion.
   After this, set_signature_overlay can cheaply add proof symbols. *)
let snapshot_base_sig () =
  base_sig := !global_sig;
  Hashtbl.reset base_index;
  Hashtbl.reset base_single;
  Hashtbl.iter (fun k v -> Hashtbl.replace base_index k v) sig_index;
  Hashtbl.iter (fun k v -> Hashtbl.replace base_single k v) sig_single

let set_signature s =
  global_sig := s;
  rebuild_index ()

(* Set signature by overlaying proof symbols on top of the cached base.
   Avoids re-indexing the ~1000 CPC symbols for each proof. *)
let set_signature_overlay (proof_sig : EO.signature) =
  global_sig := !base_sig @ proof_sig;
  (* Start from a copy of the base tables *)
  Hashtbl.reset sig_index;
  Hashtbl.reset sig_single;
  Hashtbl.iter (fun k v -> Hashtbl.replace sig_index k v) base_index;
  Hashtbl.iter (fun k v -> Hashtbl.replace sig_single k v) base_single;
  (* Add proof-specific symbols on top *)
  List.iter (fun (name, sym) ->
    if not (Hashtbl.mem sig_single name) then Hashtbl.add sig_single name sym;
    let prev = Option.value ~default:[] (Hashtbl.find_opt sig_index name) in
    Hashtbl.replace sig_index name (prev @ [(name, sym)])
  ) proof_sig

let get_signature () = !global_sig

let lookup_eo_symbol name : EO.symbol option =
  Hashtbl.find_opt sig_single name

let find_all_eo_symbols name : (string * EO.symbol) list =
  match Hashtbl.find_opt sig_index name with
  | Some l -> l
  | None -> []

(* ============================================================
   Helpers
   ============================================================ *)

(* Debug logging — delegates to Api_lp severity logging *)
let dbg fmt =
  Printf.ksprintf (fun s ->
    Api_lp.with_phase "elab" (fun () -> Api_lp.log_info "%s" s)
  ) fmt

(* Check if a symbol is an n-ary builtin that needs folding to binary *)
let is_nary_binop = function
  | s when s = EO.Builtin.eo_and || s = EO.Builtin.eo_or
        || s = EO.Builtin.eo_xor || s = EO.Builtin.eo_add
        || s = EO.Builtin.eo_mul -> true
  | _ -> false

(* Resolve a symbol name through nullary define chains *)
let rec resolve_sym_name s =
  match lookup_eo_symbol s with
  | Some (EO.Defn ([], EO.Symbol s', _)) -> resolve_sym_name s'
  | _ -> s

let take_drop n xs =
  let rec go n = function
    | x :: rest when n > 0 -> let (t, d) = go (n - 1) rest in (x :: t, d)
    | xs -> ([], xs)
  in go n xs

let split_last xs =
  match List.rev xs with
  | last :: rev_init -> (List.rev rev_init, last)
  | [] -> failwith "split_last: empty list"

(* Overload-resolved name: raw EO name with _N suffix for overload index > 0 *)
let overload_name s idx =
  if idx = 0 then s
  else Printf.sprintf "%s_%d" s idx

(* ============================================================
   Core elaboration: EO.term -> EO.term
   ============================================================ *)

(* Elaborate an Eunoia term given the parameter context.
   Returns a normalized EO term with all signature-level decisions resolved.
   subst_lit_aliases is applied once at the top level; inner recursive
   calls go directly to elab_inner to avoid O(n^2) re-traversal. *)
let rec elab (ps : EO.param list) (t : EO.term) : EO.term =
  elab_inner ps (EO.subst_lit_aliases t)

and elab_inner ps = function
  | EO.Symbol s when s = EO.Builtin.ty_type ->
    EO.Symbol EO.Builtin.ty_type

  | EO.Symbol "String" ->
    EO.Symbol "string"

  | EO.Symbol s ->
    begin match lookup_eo_symbol s with
    | Some (EO.Defn ([], EO.Symbol s', _)) ->
      dbg "define: %s -> %s" s s';
      elab_inner ps (EO.Symbol s')
    | _ -> EO.Symbol s
    end

  | EO.Literal lit ->
    EO.Literal lit

  (* Arrow types: elaborate each segment *)
  | EO.Apply (s, args) when s = EO.Builtin.ty_arrow ->
    EO.Apply (EO.Builtin.ty_arrow, elab_arrow ps args)

  (* Type cast *)
  | EO.Apply (s, [ty; tm]) when s = EO.Builtin.ty_as || s = EO.Builtin.eo_as ->
    EO.Apply (EO.Builtin.eo_as, [elab_inner ps ty; elab_inner ps tm])

  (* HOL application: (_ f x) *)
  | EO.Apply (s, [f; x]) when s = EO.Builtin.ty_app ->
    EO.Apply (EO.Builtin.ty_app, [elab_inner ps f; elab_inner ps x])

  (* eo::typeof x -> type of x from context *)
  | EO.Apply (op, [EO.Symbol s]) when op = EO.Builtin.eo_typeof ->
    begin match EO.prm_find s ps with
    | Some (_, ty, _) when ty <> EO.Symbol "NONE" -> ty
    | _ -> EO.Apply (EO.Builtin.eo_typeof, [elab_inner ps (EO.Symbol s)])
    end

  (* Builtin applications *)
  | EO.Apply (s, ts) when EO.is_builtin s ->
    elab_builtin ps s ts

  (* Non-builtin applications: dispatch through signature *)
  | EO.Apply (s, ts) ->
    elab_apply ps s ts

  (* eo::define and let as local let-binding *)
  | EO.Bind (op, xs, body) when op = EO.Builtin.eo_define || op = "let" ->
    elab_let ps xs body

  (* Binder application (forall, exists, etc.) *)
  | EO.Bind (s, xs, body) ->
    elab_binder ps s xs body

(* Elaborate builtin applications *)
and elab_builtin ps s ts =
  if is_nary_binop s && List.length ts > 2 then begin
    (* Fold n-ary builtins to right-associative binary *)
    match List.rev ts with
    | [] | [_] -> EO.Apply (s, List.map (elab_inner ps) ts)
    | last :: rev_init ->
      let folded = List.fold_left
        (fun acc t -> EO.Apply (s, [t; acc])) last rev_init in
      elab_inner ps folded
  end
  else if s = EO.Builtin.eo_list_cons then begin
    (* eo::List::cons: expand :list params eagerly *)
    match ts with
    | [x; xs] when not (match x with EO.Symbol s' -> EO.prm_has_attr s' EO.List ps | _ -> false)
                 && (match xs with EO.Symbol s' -> EO.prm_has_attr s' EO.List ps
                                 | EO.Apply _ -> true | _ -> false) ->
      EO.Apply (s, List.map (elab_inner ps) ts)
    | _ ->
      let nil = EO.Symbol EO.Builtin.eo_list_nil in
      List.fold_right (fun t acc ->
        let t' = elab_inner ps t in
        let is_list = match t with
          | EO.Symbol s' -> EO.prm_has_attr s' EO.List ps
          | _ -> false
        in
        if is_list then
          EO.Apply (EO.Builtin.eo_list_concat, [t'; acc])
        else
          EO.Apply (EO.Builtin.eo_list_cons, [t'; acc])
      ) ts nil
  end
  else
    EO.Apply (s, List.map (elab_inner ps) ts)

(* Elaborate non-builtin applications *)
and elab_apply ps s ts =
  match EO.prm_find s ps with
  | Some _ ->
    (* Variable application: use HOL app *)
    EO.app_ho_list (EO.Symbol s) (List.map (elab_inner ps) ts)
  | None ->
    let eo_type_arity = function
      | EO.Apply (s, ts) when s = EO.Builtin.ty_arrow && ts <> [] ->
        List.length ts - 1
      | _ -> 0
    in
    let all_eo = find_all_eo_symbols s in
    begin match
      all_eo |> List.mapi (fun i (s', k) -> (i, s', k))
      |> List.filter_map (fun (i, s', k) ->
        if s <> s' then None
        else match k with
        | EO.Decl (decl_ps, ty, ao) ->
          let n_opaque = List.length (List.filter
            (fun (_, _, atts) -> List.mem EO.Opaque atts) decl_ps) in
          let n_args = List.length ts - n_opaque in
          (* Count non-implicit, non-opaque params: these appear in the
             arrow type as explicit term-level arguments *)
          let n_explicit_ps = List.length (List.filter
            (fun (_, _, atts) ->
              not (List.mem EO.Implicit atts) &&
              not (List.mem EO.Opaque atts)) decl_ps) in
          let compat = match ao with
            | Some (EO.LeftAssoc | EO.RightAssoc
                   | EO.Chainable _ | EO.Pairwise _) ->
              n_args >= 2
            | Some (EO.LeftAssocNil _ | EO.RightAssocNil _
                   | EO.LeftAssocNilNSN _ | EO.RightAssocNilNSN _
                   | EO.LeftAssocNSN _ | EO.RightAssocNSN _) ->
              n_args >= 1
            | None ->
              n_args = eo_type_arity ty - n_explicit_ps
            | _ -> true
          in
          if not compat then None
          else Some (elab_nary ~overload_idx:i ps s k ts)
        | _ -> Some (elab_nary ~overload_idx:i ps s k ts))
    with
    | t' :: _ -> t'
    | [] ->
      (* Symbol not in Eunoia signature — direct application *)
      EO.Apply (s, List.map (elab_inner ps) ts)
    end

(* Elaborate an n-ary application *)
and elab_nary ?(overload_idx=0) ps s k ts =
  let name = overload_name s overload_idx in
  match k with
  | EO.Prog _ ->
    EO.Apply (name, List.map (elab_inner ps) ts)

  | EO.Defn ([], EO.Symbol s', _) ->
    dbg "define: %s -> %s" s s';
    if ts = [] then
      elab_inner ps (EO.Symbol s')
    else
      elab_inner ps (EO.Apply (s', ts))

  | EO.Defn ([], _body, _) ->
    (* Non-alias nullary define: keep as a symbol reference *)
    if ts = [] then
      EO.Symbol name
    else
      EO.Apply (name, List.map (elab_inner ps) ts)

  | EO.Defn _ ->
    EO.Apply (name, List.map (elab_inner ps) ts)

  | EO.Decl (decl_ps, ty, ao) ->
    if EO.returns_type ty then
      EO.Apply (name, List.map (elab_inner ps) ts)
    else
      elab_nary_decl ~overload_idx ps s decl_ps ty ao ts

  | _ -> failwith (Printf.sprintf "Cannot elaborate %s as nary" s)

(* Elaborate a Decl application with attribute dispatch *)
and elab_nary_decl ?(overload_idx=0) ps s decl_ps ty ao ts =
  let n_opaque =
    List.length (List.filter (fun (_, _, atts) -> List.mem EO.Opaque atts) decl_ps)
  in
  if n_opaque > 0 then
    dbg "opaque: %s n_opaque=%d n_args=%d" s n_opaque (List.length ts);
  let opaque_args, rest_ts =
    if n_opaque > 0 && n_opaque <= List.length ts then take_drop n_opaque ts
    else ([], ts)
  in
  let name = overload_name s overload_idx in
  dbg "overload: %s idx=%d -> %s" s overload_idx name;
  (* Elaborate nil term following the Ethos manual:
     - Ground nil: use nil term directly
     - Non-ground nil (references type params): use (eo::nil f (eo::typeof t1))
       where t1 is the first argument, per the Ethos spec. *)
  let elab_nil_eo t_nil =
    let impl_names =
      List.filter_map (fun (n, t, _) ->
        if t = EO.Symbol EO.Builtin.ty_type then Some n else None) decl_ps
    in
    let nil_has_params = List.exists (fun n ->
      EO.term_contains_symbol n t_nil) impl_names in
    if not nil_has_params then t_nil
    else
      match rest_ts with
      | t1 :: _ ->
        EO.Apply (EO.Builtin.eo_nil, [EO.Symbol name; EO.Apply (EO.Builtin.eo_typeof, [t1])])
      | [] -> t_nil
  in
  (* EO-level fold helpers *)
  let glue_eo is_list arg acc =
    if is_list then
      EO.Apply (EO.Builtin.eo_list_concat_old, [EO.Symbol name; arg; acc])
    else
      EO.app_ho (EO.app_ho (EO.Symbol name) arg) acc
  in
  let is_list_of t = match t with
    | EO.Symbol s' -> EO.prm_has_attr s' EO.List ps
    | _ -> false
  in
  let n_rest = List.length rest_ts in
  (* Direct application: HOL-app chain with opaque args prepended *)
  let mk_direct () =
    let opaque_elab = List.map (elab_inner ps) opaque_args in
    let rest_elab = List.map (elab_inner ps) rest_ts in
    let head =
      if opaque_elab = [] then EO.Symbol name
      else EO.Apply (name, opaque_elab)
    in
    EO.app_ho_list head rest_elab
  in
  (* Factored fold helpers for associativity attributes.
     ~check_boundary: when true, check if the boundary arg (last for right,
     first for left) is a :list param, and if a 2-arg form has a list param
     in the boundary position, use direct application instead. *)
  let fold_right_nil ?(check_boundary=false) label t_nil =
    dbg "%s: %s(%d args)" label s n_rest;
    if check_boundary then begin
      match rest_ts with
      | [_; EO.Symbol s'] when EO.prm_has_attr s' EO.List ps ->
        mk_direct ()
      | _ ->
        let last_is_list = match List.rev rest_ts with
          | EO.Symbol s' :: _ when EO.prm_has_attr s' EO.List ps -> true
          | _ -> false
        in
        if last_is_list then
          let init, last = split_last rest_ts in
          elab_inner ps (List.fold_right (fun t acc -> glue_eo (is_list_of t) t acc) init last)
        else
          let nil = elab_nil_eo t_nil in
          elab_inner ps (List.fold_right (fun t acc -> glue_eo (is_list_of t) t acc) rest_ts nil)
    end else begin
      let nil = elab_nil_eo t_nil in
      elab_inner ps (List.fold_right (fun t acc -> glue_eo (is_list_of t) t acc) rest_ts nil)
    end
  in
  let fold_left_nil ?(check_boundary=false) label t_nil =
    dbg "%s: %s(%d args)" label s n_rest;
    if check_boundary then begin
      match rest_ts with
      | [EO.Symbol s'; _] when EO.prm_has_attr s' EO.List ps ->
        mk_direct ()
      | _ ->
        let first_is_list = match rest_ts with
          | EO.Symbol s' :: _ when EO.prm_has_attr s' EO.List ps -> true
          | _ -> false
        in
        if first_is_list then
          match rest_ts with
          | [] -> failwith "left-assoc-nil: empty args"
          | acc :: tail ->
            elab_inner ps (List.fold_left (fun acc t -> glue_eo (is_list_of t) acc t) acc tail)
        else
          let nil = elab_nil_eo t_nil in
          elab_inner ps (List.fold_left (fun acc t -> glue_eo (is_list_of t) acc t) nil rest_ts)
    end else begin
      let nil = elab_nil_eo t_nil in
      elab_inner ps (List.fold_left (fun acc t -> glue_eo (is_list_of t) acc t) nil rest_ts)
    end
  in
  match ao with
  | None ->
    mk_direct ()

  | Some (EO.RightAssocNil t_nil) ->
    fold_right_nil ~check_boundary:true "right-assoc-nil" t_nil

  | Some (EO.LeftAssocNil t_nil) ->
    fold_left_nil ~check_boundary:true "left-assoc-nil" t_nil

  | Some EO.RightAssoc ->
    dbg "right-assoc: %s(%d args)" s n_rest;
    let init, last = split_last rest_ts in
    elab_inner ps (List.fold_right (fun t acc -> glue_eo (is_list_of t) t acc) init last)

  | Some EO.LeftAssoc ->
    dbg "left-assoc: %s(%d args)" s n_rest;
    begin match rest_ts with
    | [] -> failwith "left-assoc: empty args"
    | acc :: tail ->
      elab_inner ps (List.fold_left (fun acc t -> glue_eo (is_list_of t) acc t) acc tail)
    end

  | Some (EO.Chainable op) ->
    if List.length rest_ts <= 2 then mk_direct ()
    else begin
      dbg "chainable: %s(%d args), op=%s" s n_rest op;
      let rec aux = function
        | v :: w :: vs ->
          (EO.app_ho_list (EO.Symbol s) [v; w]) :: aux (w :: vs)
        | _ -> []
      in
      elab_inner ps (EO.Apply (op, aux rest_ts))
    end

  | Some (EO.Pairwise op) ->
    if List.length rest_ts <= 2 then mk_direct ()
    else begin
      dbg "pairwise: %s(%d args), op=%s" s n_rest op;
      let rec aux = function
        | v :: vs ->
          List.append
            (List.map (fun w -> EO.app_ho_list (EO.Symbol s) [v; w]) vs)
            (aux vs)
        | [] -> []
      in
      elab_inner ps (EO.Apply (op, aux rest_ts))
    end

  | Some (EO.RightAssocNilNSN t_nil) ->
    fold_right_nil "right-assoc-nil-nsn" t_nil

  | Some (EO.LeftAssocNilNSN t_nil) ->
    fold_left_nil "left-assoc-nil-nsn" t_nil

  | Some (EO.RightAssocNSN t_nil) ->
    fold_right_nil "right-assoc-nsn" t_nil

  | Some (EO.LeftAssocNSN t_nil) ->
    fold_left_nil "left-assoc-nsn" t_nil

  | Some (EO.ArgList cons_name) ->
    begin match rest_ts with
    | [EO.Symbol s'] when EO.prm_has_attr s' EO.List ps ->
      mk_direct ()
    | _ ->
      dbg "arg-list: %s(%d args), cons=%s" s n_rest cons_name;
      let list_term = EO.Apply (cons_name, rest_ts) in
      let list_elab = elab_inner ps list_term in
      let head =
        if opaque_args = [] then EO.Symbol name
        else EO.Apply (name, List.map (elab_inner ps) opaque_args)
      in
      EO.app_ho head list_elab
    end

  | Some (EO.Binder _ | EO.LetBinder _
         | EO.Implicit | EO.Opaque | EO.List
         | EO.Syntax _ | EO.Restrict _) ->
    mk_direct ()

(* Elaborate arrow type segments — preserve eo::var and eo::quote forms *)
and elab_arrow ps = function
  | [] -> []
  | [t] -> [elab_inner ps t]
  | EO.Apply (op, [ty; EO.Symbol s]) :: rest when op = EO.Builtin.eo_var ->
    EO.Apply (EO.Builtin.eo_var, [elab_inner ps ty; EO.Symbol s]) :: elab_arrow ps rest
  | EO.Apply (op, [EO.Symbol s]) :: rest when op = EO.Builtin.eo_quote ->
    EO.Apply (EO.Builtin.eo_quote, [EO.Symbol s]) :: elab_arrow ps rest
  | t :: rest ->
    elab_inner ps t :: elab_arrow ps rest

(* Elaborate eo::define let-bindings *)
and elab_let ps xs body =
  match xs with
  | [] -> elab_inner ps body
  | (name, rhs) :: rest ->
    let rhs' = elab_inner ps rhs in
    let ps' = (name, EO.Symbol "NONE", []) :: ps in
    let body' = elab_let ps' rest body in
    EO.Bind (EO.Builtin.eo_define, [(name, rhs')], body')

(* Elaborate binder applications *)
and elab_binder ps s xs body =
  match
    find_all_eo_symbols s |> List.filter_map (fun (s', k) ->
      if s = s' then Some (elab_binder_one ps s k xs body)
      else None)
  with
  | t' :: _ -> t'
  | [] -> failwith (Printf.sprintf "Binder `%s` not found" s)

and elab_binder_one ps s k xs body =
  match k with
  | EO.Decl (_, _, Some (EO.Binder t_cons_name)) ->
    let t_cons_name = resolve_sym_name t_cons_name in
    let mk_var_eo (name, ty) =
      EO.Apply (EO.Builtin.eo_var, [EO.Literal (Literal.String name); ty])
    in
    (* Substitute bound variable occurrences in the body with eo::var form *)
    let body' = List.fold_left (fun acc (n, ty) ->
      EO.subst acc n (mk_var_eo (n, ty))) body xs
    in
    let bound_params = List.map (fun (n, ty) -> (n, ty, [])) xs in
    let ps' = ps @ bound_params in
    let var_terms = List.map (fun v -> elab_inner ps (mk_var_eo v)) xs in
    let cons_elab = EO.Apply (t_cons_name, var_terms) in
    let body_elab = elab_inner ps' body' in
    EO.Apply (s, [cons_elab; body_elab])
  | _ ->
    failwith (Printf.sprintf "No :binder attribute for `%s`" s)
