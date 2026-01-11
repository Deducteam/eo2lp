module EO = Syntax_eo
module LF = Syntax_lf
module LP = Syntax_lp

module API = Api_lp

module M = EO.M
module L = EO.L

let last (xs : 'a list) : ('a list * 'a) =
  let ys = List.rev xs in
  (List.rev (List.tl ys), List.hd ys)

let is_well_typed : LF.term -> bool =
  fun _ -> true

let cut_when
  (p : 'a -> bool) (xs : 'a list)
  : ('a list * 'a list)
=
  (L.take_while p xs, L.drop_while p xs)

let rec elab
  (sgn,ps as ctx : EO.context)
  : EO.term -> LF.term =
  function
  | Symbol s -> failwith ""
  | Literal l -> Lit l
  | Bind (s, vs, t) -> failwith ""
  | Apply (s,ts) ->
    begin match M.find s sgn with
    (* --- *)
    | [] ->
      Printf.ksprintf failwith
      "%s has no instances in signature." s
    (* --- *)
    | k :: ks ->
      begin match k with
      | Dcl (ps,_,ao,lv) ->
        let mvs =
          ps |> L.take_while (EO._pa Implicit)
             |> L.map (fun (_,ty,_) -> MVar ty)
        in
        let ops =
          ps |> L.drop (L.length mvs)
             |> L.take_while (EO._pa Opaque)
             |>

        elab_nary ctx (ao,lv) (f,ts)
      | Prg (ps,t,_,lv) ->
        elab_prog ctx (s,ts,lv)
      | Dfn (ps,t) ->
        let f = EO.splice (ps,t) ts in
        elab ctx f
      end
  end
and elab_const
  (s,ps,ts : string * EO.param list * EO.term list) : LF.term * EO.term list =
=



and elab_nary
  (sgn,ps as ctx : EO.context)
  (ao,lv : EO.const_attr option * EO.level)
  (t, ts : EO.term * EO.term list) : LF.term
=
  let g x y = EO.glue (ps,f) (x,y) in
  let h y x = EO.glue (ps,f) (y,x) in
  let f',ts' = elab ctx f, L.map (elab ctx) ts in
  begin match att_opt with
  (* ---- *)
  | None -> App (f', ts')
  (* ---- *)
  | Some RightAssocNil t_nil -> (
    match ts with
    | [t1; Symbol s] when EO.__pa (s,List) ps -> App (f', ts')
    | _ -> elab ctx (L.fold_right g ts t_nil)
    )
  (* ---- *)
  | Some LeftAssocNil t_nil -> (
    match ts with
    | [t1; Symbol s] when EO.__pa (s,List) ps -> App (f', ts')
    | _ -> elab ctx (L.fold_left h f ts)
    )
  (* ---- *)
  | Some RightAssoc ->
    let (xs, x) = last ts in
    elab ctx (L.fold_right g xs x)
  (* ---- *)
  | Some LeftAssoc ->
    elab ctx (L.fold_left h (List.hd ts) (List.tl ts))
  (* ---- *)
  | Some Chainable op ->
    let rec aux =
      function
      | v :: w :: vs -> (EO.app (f,[v;w])) :: aux vs
      | _ -> []
    in
      elab ctx (Apply (op, aux ts))
  (* ---- *)
  | Some Pairwise op ->
    let rec aux =
      function
      | v :: vs -> L.append
        (L.map (fun w -> EO.app (f,[v;w])) vs)
        (aux vs)
      | [] -> []
    in
      elab ctx (Apply (op, aux ts))
  (* ---- *)
  | Some _ ->
    failwith "unimplemented strategy"
  (* ---- *)
  end
