(* elaborate.ml
   Eunoia elaboration: resolve the Eunoia AST into an annotated
   intermediate form that encode.ml can translate to LambdaPi
   without consulting the Eunoia signature or parameter context.

   This module owns the Eunoia signature state and all decision
   logic: nullary define expansion, overload resolution, variable
   vs symbol dispatch, :list detection, n-ary attribute dispatch. *)

module EO = Syntax_eo

(* ============================================================
   Annotated term type
   ============================================================ *)

type elab_term =
  | ELit of Literal.literal
  | EType                                    (* eo::Type *)
  | EVar of string                           (* resolved as a bound variable *)
  | ESym of string                           (* resolved as a global LP symbol *)
  | EAs of elab_term * elab_term             (* type cast: (as ty tm) *)
  | EHolApp of elab_term * elab_term list    (* variable application via APP *)
  | EBuiltinNary of string * elab_term list  (* n-ary builtin folded to binary *)
  | EBuiltin of string * elab_term list      (* other builtin application *)
  | EListCons of elab_arg list               (* eo::List::cons with :list annotations *)
  | ENary of nary_info * elab_arg list       (* resolved n-ary decl application *)
  | EApp of string * elab_term list          (* direct application (prog, defn, type-returning) *)
  | EArrow of arrow_seg list                 (* arrow type segments *)
  | EBinder of binder_info                   (* resolved binder application *)
  | ELet of string * elab_term * elab_term   (* eo::define *)
  | ETypeof of typeof_info                   (* eo::typeof *)

and elab_arg = {
  arg : elab_term;
  is_list : bool;     (* true if this arg is a :list parameter *)
}

and nary_info = {
  head : string;           (* LP symbol name for the head *)
  opaque_args : elab_term list;
  rest_args : elab_arg list;
  fold : fold_kind;
}

and fold_kind =
  | FoldNone                           (* no folding, direct hol_app *)
  | FoldRightNil of elab_term          (* right-assoc-nil with nil term *)
  | FoldLeftNil of elab_term           (* left-assoc-nil with nil term *)
  | FoldRight                          (* right-assoc without nil *)
  | FoldLeft                           (* left-assoc without nil *)
  | FoldChainable of string * EO.term list * EO.param list  (* op, original args, ps *)
  | FoldPairwise of string * EO.term list * EO.param list   (* op, original args, ps *)
  | FoldArgList of string * EO.term list * EO.param list    (* cons, original args, ps *)
  | FoldRightNilNSN of elab_term       (* right-assoc-nil-non-singleton-nil *)
  | FoldLeftNilNSN of elab_term        (* left-assoc-nil-non-singleton-nil *)
  | FoldRightNSN of elab_term          (* right-assoc-non-singleton-nil *)
  | FoldLeftNSN of elab_term           (* left-assoc-non-singleton-nil *)

and arrow_seg =
  | APlain of elab_term
  | ADepVar of string * elab_term * elab_term  (* name, eo_ty, rest elaborated in context *)
  | ADepQuote of string                         (* quoted variable name *)
  | AResult of elab_term                        (* final result type *)

and binder_info = {
  binder_head : string;        (* LP name for the binder symbol *)
  cons_term : elab_term;       (* elaborated cons application *)
  body : elab_term;            (* elaborated body with var substitutions *)
}

and typeof_info =
  | TypeofParam of EO.term     (* param type from ps, needs encoding *)
  | TypeofFallback of elab_term (* fallback: encode eo::typeof application *)

(* ============================================================
   Eunoia signature state
   ============================================================ *)

let global_sig : EO.signature ref = ref []

(* Hash-based index for fast symbol lookup.
   sig_index maps name -> list of (name, symbol) pairs (for overloads).
   sig_single maps name -> first symbol (for single-match lookups). *)
let sig_index : (string, (string * EO.symbol) list) Hashtbl.t = Hashtbl.create 256
let sig_single : (string, EO.symbol) Hashtbl.t = Hashtbl.create 256

let rebuild_index () =
  Hashtbl.clear sig_index;
  Hashtbl.clear sig_single;
  List.iter (fun (name, sym) ->
    (* sig_single: keep first occurrence (List.assoc_opt semantics) *)
    if not (Hashtbl.mem sig_single name) then
      Hashtbl.add sig_single name sym;
    (* sig_index: accumulate all occurrences *)
    let prev = match Hashtbl.find_opt sig_index name with
      | Some l -> l | None -> [] in
    Hashtbl.replace sig_index name (prev @ [(name, sym)])
  ) !global_sig

let set_signature s =
  global_sig := s;
  rebuild_index ()

let get_signature () = !global_sig

let lookup_eo_symbol name : EO.symbol option =
  Hashtbl.find_opt sig_single name

let find_all_eo_symbols name : (string * EO.symbol) list =
  match Hashtbl.find_opt sig_index name with
  | Some l -> l
  | None -> []

(* ============================================================
   Helpers (moved from encode.ml)
   ============================================================ *)

(* Debug logging — delegates to Api_lp severity logging *)
let dbg fmt =
  let saved = !Api_lp.current_phase in
  Api_lp.current_phase := "elab";
  Printf.ksprintf (fun s ->
    Api_lp.log_info "%s" s;
    Api_lp.current_phase := saved
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

(* Infer substitutions for a declaration's implicit type params from actual
   argument types. Returns a list of (param_name, actual_type) pairs. *)
let infer_nil_subst decl_ps ty ts ps =
  let impl_names =
    List.filter_map (fun (n, t, _) ->
      if t = EO.Symbol EO.Builtin.ty_type then Some n else None) decl_ps
  in
  if impl_names = [] then []
  else
    let declared_arg_tys = match ty with
      | EO.Apply (s, args) when s = EO.Builtin.ty_arrow && args <> [] ->
        let n = List.length args in
        List.filteri (fun i _ -> i < n - 1) args
      | _ -> []
    in
    let actual_arg_tys =
      List.filter_map (fun t ->
        match t with
        | EO.Symbol s ->
          (match EO.prm_find s ps with
           | Some (_, ty, _) -> Some ty
           | None -> None)
        | _ -> None) ts
    in
    let bindings = Hashtbl.create 4 in
    let rec match_ty pat act =
      match pat, act with
      | EO.Symbol s, _ when List.mem s impl_names ->
        if not (Hashtbl.mem bindings s) then
          Hashtbl.add bindings s act
      | EO.Apply (f1, args1), EO.Apply (f2, args2)
        when f1 = f2 && List.length args1 = List.length args2 ->
        List.iter2 match_ty args1 args2
      | _ -> ()
    in
    List.iter2 match_ty
      (List.filteri (fun i _ -> i < List.length actual_arg_tys) declared_arg_tys)
      (List.filteri (fun i _ -> i < List.length declared_arg_tys) actual_arg_tys);
    Hashtbl.fold (fun k v acc -> (k, v) :: acc) bindings []

(* Apply a list of substitutions to an Eunoia term *)
let apply_substs substs t =
  List.fold_left (fun acc (s, t') -> EO.subst acc s t') t substs

(* ============================================================
   Core elaboration
   ============================================================ *)

(* Elaborate an Eunoia term given the parameter context.
   ps = Eunoia param context (for :list checks, variable detection, etc.)
   Returns an elab_term with all signature-consulting decisions resolved. *)
let rec elab_term (ps : EO.param list) (t : EO.term) : elab_term =
  elab_term_inner ps (EO.subst_lit_aliases t)

and elab_term_inner ps = function
  | EO.Symbol s when s = EO.Builtin.ty_type ->
    EType

  | EO.Symbol "String" ->
    ESym "string"

  (* Symbol: check for nullary define expansion, then context/global lookup *)
  | EO.Symbol s ->
    begin match lookup_eo_symbol s with
    | Some (EO.Defn ([], body, _)) ->
      dbg "define: %s → %s" s (Pp_eo.term_str body);
      elab_term ps body
    | _ ->
      if EO.prm_mem s ps then EVar s
      else ESym s
    end

  | EO.Literal lit ->
    ELit lit

  (* Arrow types *)
  | EO.Apply (s, args) when s = EO.Builtin.ty_arrow ->
    EArrow (elab_arrow ps args)

  (* Type cast: (as T x) or (eo::as T x) *)
  | EO.Apply (s, [ty; tm]) when s = EO.Builtin.ty_as || s = EO.Builtin.eo_as ->
    EAs (elab_term ps ty, elab_term ps tm)

  (* HOL application: (_ f x) — already elaborated form *)
  | EO.Apply (s, [f; x]) when s = EO.Builtin.ty_app ->
    EHolApp (elab_term ps f, [elab_term ps x])

  (* eo::typeof x → type of x from context *)
  | EO.Apply (op, [EO.Symbol s]) when op = EO.Builtin.eo_typeof ->
    begin match EO.prm_find s ps with
    | Some (_, ty, _) -> ETypeof (TypeofParam ty)
    | None -> ETypeof (TypeofFallback (elab_term ps (EO.Symbol s)))
    end

  (* Builtin applications *)
  | EO.Apply (s, ts) when EO.is_builtin s ->
    elab_builtin ps s ts

  (* Non-builtin applications: dispatch through signature *)
  | EO.Apply (s, ts) ->
    elab_apply ps s ts

  (* eo::define as local let-binding *)
  | EO.Bind (op, xs, body) when op = EO.Builtin.eo_define ->
    elab_let ps xs body

  (* Binder application (forall, exists, etc.) *)
  | EO.Bind (s, xs, body) ->
    elab_binder ps s xs body

(* Elaborate builtin applications *)
and elab_builtin ps s ts =
  if is_nary_binop s && List.length ts > 2 then begin
    (* Fold n-ary builtins (eo::and, eo::or, etc.) to binary *)
    EBuiltinNary (s, List.map (elab_term ps) ts)
  end
  else if s = EO.Builtin.eo_list_cons then begin
    (* eo::List::cons: handle :list params *)
    let annotated = List.map (fun t ->
      let is_list = match t with
        | EO.Symbol s' -> EO.prm_has_attr s' EO.List ps
        | _ -> false
      in
      { arg = elab_term ps t; is_list }
    ) ts in
    EListCons annotated
  end
  else begin
    (* Other builtins: encode normally *)
    EBuiltin (s, List.map (elab_term ps) ts)
  end

(* Elaborate non-builtin applications *)
and elab_apply ps s ts =
  match EO.prm_find s ps with
  | Some _ ->
    (* Variable application: use HOL app *)
    let head = if EO.prm_mem s ps then EVar s else ESym s in
    EHolApp (head, List.map (elab_term ps) ts)
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
          let compat = match ao with
            | Some (EO.LeftAssoc | EO.RightAssoc
                   | EO.Chainable _ | EO.Pairwise _) ->
              n_args >= 2
            | Some (EO.LeftAssocNil _ | EO.RightAssocNil _
                   | EO.LeftAssocNilNSN _ | EO.RightAssocNilNSN _
                   | EO.LeftAssocNSN _ | EO.RightAssocNSN _) ->
              n_args >= 1
            | None ->
              n_args = eo_type_arity ty - List.length decl_ps
            | _ -> true
          in
          if not compat then None
          else Some (elab_nary ~overload_idx:i ps s k ts)
        | _ -> Some (elab_nary ~overload_idx:i ps s k ts))
    with
    | t' :: _ -> t'
    | [] ->
      (* Symbol not in Eunoia signature — direct LP symbol *)
      let head = if EO.prm_mem s ps then EVar s else ESym s in
      EApp (Api_lp.esc s, List.map (elab_term ps) ts)
    end

(* Elaborate an n-ary application *)
and elab_nary ?(overload_idx=0) ps s k ts =
  match k with
  (* Program constants: direct application *)
  | EO.Prog _ ->
    EApp (Api_lp.esc s, List.map (elab_term ps) ts)

  (* Nullary define: expand head, keep args *)
  | EO.Defn ([], body, _) ->
    begin match body with
    | EO.Symbol s' when ts = [] ->
      dbg "define: %s → %s" s s';
      elab_term ps (EO.Symbol s')
    | EO.Symbol s' ->
      dbg "define: %s(%d args) → %s(%d args)" s (List.length ts) s' (List.length ts);
      elab_term ps (EO.Apply (s', ts))
    | _ when ts = [] ->
      dbg "define: %s → %s" s (Pp_eo.term_str body);
      elab_term ps body
    | _ ->
      EApp (Api_lp.esc s, List.map (elab_term ps) ts)
    end

  (* Parametric define: encode normally *)
  | EO.Defn _ ->
    EApp (Api_lp.esc s, List.map (elab_term ps) ts)

  (* Declarations: dispatch on associativity attribute *)
  | EO.Decl (decl_ps, ty, ao) ->
    if EO.returns_type ty then
      EApp (Api_lp.esc s, List.map (elab_term ps) ts)
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
  let take_drop n xs =
    let rec go n = function
      | x :: rest when n > 0 -> let (t, d) = go (n - 1) rest in (x :: t, d)
      | xs -> ([], xs)
    in go n xs
  in
  let opaque_args, rest_ts =
    if n_opaque > 0 && n_opaque <= List.length ts then take_drop n_opaque ts
    else ([], ts)
  in
  let opaque_elab = List.map (elab_term ps) opaque_args in
  (* Annotate rest args with :list status *)
  let rest_annotated = List.map (fun t ->
    let is_list = match t with
      | EO.Symbol s' -> EO.prm_has_attr s' EO.List ps
      | _ -> false
    in
    { arg = elab_term ps t; is_list }
  ) rest_ts in
  (* Compute LP head name from overload index *)
  let lp_name =
    if overload_idx = 0 then Api_lp.esc s
    else Printf.sprintf "%s_%d" (Api_lp.esc s) overload_idx
  in
  dbg "overload: %s idx=%d -> LP %s" s overload_idx lp_name;
  (* Elaborate nil term with type param substitution *)
  let elab_nil t_nil =
    let subs = infer_nil_subst decl_ps ty ts ps in
    if subs = [] then elab_term ps t_nil
    else elab_term ps (apply_substs subs t_nil)
  in
  let fold = match ao with
    | None -> FoldNone
    | Some (EO.RightAssocNil t_nil) ->
      (* Check for special :list cases *)
      begin match rest_ts with
      | [_; EO.Symbol s'] when EO.prm_has_attr s' EO.List ps ->
        FoldNone  (* single explicit + :list → direct hol_app *)
      | _ ->
        let last_is_list = match List.rev rest_ts with
          | EO.Symbol s' :: _ when EO.prm_has_attr s' EO.List ps -> true
          | _ -> false
        in
        if last_is_list then FoldRightNil (EVar "__last_is_list__")
        else FoldRightNil (elab_nil t_nil)
      end
    | Some (EO.LeftAssocNil t_nil) ->
      begin match rest_ts with
      | [EO.Symbol s'; _] when EO.prm_has_attr s' EO.List ps ->
        FoldNone
      | _ ->
        let first_is_list = match rest_ts with
          | EO.Symbol s' :: _ when EO.prm_has_attr s' EO.List ps -> true
          | _ -> false
        in
        if first_is_list then FoldLeftNil (EVar "__first_is_list__")
        else FoldLeftNil (elab_nil t_nil)
      end
    | Some EO.RightAssoc -> FoldRight
    | Some EO.LeftAssoc -> FoldLeft
    | Some (EO.Chainable op) ->
      if List.length rest_ts <= 2 then FoldNone
      else FoldChainable (op, rest_ts, ps)
    | Some (EO.Pairwise op) ->
      if List.length rest_ts <= 2 then FoldNone
      else FoldPairwise (op, rest_ts, ps)
    | Some (EO.RightAssocNilNSN t_nil) -> FoldRightNilNSN (elab_nil t_nil)
    | Some (EO.LeftAssocNilNSN t_nil) -> FoldLeftNilNSN (elab_nil t_nil)
    | Some (EO.RightAssocNSN t_nil) -> FoldRightNSN (elab_nil t_nil)
    | Some (EO.LeftAssocNSN t_nil) -> FoldLeftNSN (elab_nil t_nil)
    | Some (EO.ArgList cons_name) ->
      (* Check if single :list arg *)
      begin match rest_ts with
      | [EO.Symbol s'] when EO.prm_has_attr s' EO.List ps ->
        FoldNone  (* single :list → direct hol_app *)
      | _ -> FoldArgList (cons_name, rest_ts, ps)
      end
    | Some (EO.Binder _ | EO.LetBinder _
           | EO.Implicit | EO.Opaque | EO.List
           | EO.Syntax _ | EO.Restrict _) ->
      FoldNone
  in
  let n_rest = List.length rest_ts in
  (match fold with
   | FoldNone -> ()
   | FoldRightNil _ -> dbg "right-assoc-nil: %s(%d args)" s n_rest
   | FoldLeftNil _ -> dbg "left-assoc-nil: %s(%d args)" s n_rest
   | FoldRight -> dbg "right-assoc: %s(%d args)" s n_rest
   | FoldLeft -> dbg "left-assoc: %s(%d args)" s n_rest
   | FoldChainable (op, _, _) -> dbg "chainable: %s(%d args), op=%s" s n_rest op
   | FoldPairwise (op, _, _) -> dbg "pairwise: %s(%d args), op=%s" s n_rest op
   | FoldArgList (cons, _, _) -> dbg "arg-list: %s(%d args), cons=%s" s n_rest cons
   | FoldRightNilNSN _ -> dbg "right-assoc-nil-nsn: %s(%d args)" s n_rest
   | FoldLeftNilNSN _ -> dbg "left-assoc-nil-nsn: %s(%d args)" s n_rest
   | FoldRightNSN _ -> dbg "right-assoc-nsn: %s(%d args)" s n_rest
   | FoldLeftNSN _ -> dbg "left-assoc-nsn: %s(%d args)" s n_rest);
  ENary ({ head = lp_name; opaque_args = opaque_elab;
           rest_args = rest_annotated; fold }, rest_annotated)

(* Elaborate arrow type segments *)
and elab_arrow ps = function
  | [] -> [AResult EType]  (* shouldn't happen *)
  | [t] -> [AResult (elab_term ps t)]
  | EO.Apply (op, [ty; EO.Symbol s]) :: rest when op = EO.Builtin.eo_var ->
    ADepVar (s, elab_term ps ty, elab_term ps ty) :: elab_arrow ps rest
  | EO.Apply (op, [EO.Symbol s]) :: rest when op = EO.Builtin.eo_quote ->
    ADepQuote s :: elab_arrow ps rest
  | t :: rest ->
    APlain (elab_term ps t) :: elab_arrow ps rest

(* Elaborate eo::define let-bindings *)
and elab_let ps xs body =
  match xs with
  | [] -> elab_term ps body
  | (name, rhs) :: rest ->
    let rhs_elab = elab_term ps rhs in
    let ps' = (name, EO.Symbol "NONE", []) :: ps in
    let body_elab = elab_let ps' rest body in
    ELet (name, rhs_elab, body_elab)

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
    let var_terms = List.map (fun v -> elab_term ps (mk_var_eo v)) xs in
    (* Build cons application as an EO term and elaborate it *)
    let cons_elab =
      EApp (Api_lp.esc t_cons_name, var_terms)
    in
    let body_elab = elab_term ps' body' in
    EBinder {
      binder_head = Api_lp.esc s;
      cons_term = cons_elab;
      body = body_elab;
    }
  | _ ->
    failwith (Printf.sprintf "No :binder attribute for `%s`" s)
