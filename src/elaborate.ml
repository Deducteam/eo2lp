module EO = Syntax_eo
module LF = Syntax_lf
module LP = Syntax_lp

module API = Api_lp

module M = EO.M
module L = EO.L

let is_well_typed : LF.term -> bool =
  fun _ -> true

let rec elab (sgn,ps as ctx : EO.context)
  : EO.term -> LF.term
= function
  (* ---- *)
  | Literal l -> Lit l
  (* ---- *)
  | Symbol "Type" -> Const ("TYPE", [])
  | Symbol "Kind" -> Const ("KIND", [])
  | Symbol "->" -> Const ("->", [])
  | Symbol s ->
    if L.mem_assoc s sgn then
      Const (s,[])
    else if L.exists (EO._pn s) ps then
      Var s
    else
      Printf.ksprintf failwith
      "Symbol %s not found in context" s
  (* ---- *)
  | Bind ("eo::define", xs, t) ->
    L.fold_right
      (fun (s,x) acc -> LF.Let (s, elab ctx x, acc))
      xs (elab ctx t)
  (* ---- *)
  | Bind (s,xs,t) ->
    elab ctx @@
      EO.app_binder (Symbol s,xs,t) (EO.att_of s sgn)
  (* ---- *)
  | Apply ("_",ts) -> (
    match ts with
    | [t1;t2] ->
      let (t1',t2') = elab ctx t1, elab ctx t2 in
      LF.App (t1',t2')
    | _ -> failwith "Invalid HO application."
  )
  (* ---- *)
  | Apply ("->",ts) ->
      EO.app_nary ps (Symbol "->", ts) (Some RightAssoc)
      |> elab ctx
  (* ---- *)
  | Apply (s,ts) -> (
    match L.find_opt (EO._pn s) ps with
    | Some _ ->
      if ts = []
        then Var s
        else EO.app_ho_list (Symbol s) ts |> elab ctx
    | None -> (
        match L.assoc_opt s sgn with
        | None ->
          Printf.ksprintf failwith
            "Symbol %s not in context." s
        | Some Dcl (_,_,ao,_) ->
          if ts = [] then
            Const (s,[])
          else
            EO.app_nary ps (Symbol s, ts) (EO.att_of s sgn)
            |> elab ctx
        | Some Prg (_,_,_,_) ->
            let f = LF.Const (s,[]) in
            if ts = [] then f
            else LF.app_list (f :: L.map (elab ctx) ts)
        | Some Dfn (qs,t) ->
            let (qs',t',ts') = EO.splice (qs,t,ts) in
            if qs' = [] then
              elab ctx (EO.app_raw t' ts')
            else
              failwith "Partially applied definition."
        )
      )

let elab_prm (ctx : EO.context)
  : EO.param list -> LF.param list =
  L.map (fun (s,t,ao) ->
    match ao with
    | Some EO.Implicit -> (s, elab ctx t, LF.Implicit)
    | _ -> (s, elab ctx t, LF.Explicit)
  )

let elab_cs (ctx : EO.context)
  : EO.case list -> LF.case list =
  L.map (fun (t,t') -> elab ctx t, elab ctx t')

let elab_sym (sgn,ps as ctx: EO.context)
  : string * EO.symbol -> string * LF.symbol =
  function
  | (s, Dcl (qs,t,_,_)) ->
    Printf.printf "Elaborating symbol `%s`.\n" s;
    (s, Decl (
      elab_prm ctx ps,
      elab (sgn, L.append qs ps) t
      )
    )
  | (s, Prg (ps', ty, cs, _)) ->
    let (qs,rs) = (
      EO.prog_ty_params ty ps,
      EO.prog_cs_params cs ps)
    in
      (s, Prog (
        (elab_prm ctx qs, elab (sgn, L.append qs ps) ty),
        (elab_prm ctx rs, elab_cs (sgn, L.append rs ps) cs)
      )
    )

let elab_sig (sgn : EO.signature)
  : EO.signature -> LF.signature
=
  L.map (elab_sym (sgn,[]))
