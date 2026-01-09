module EO = Syntax_eo
module LF = Syntax_lf

module M = EO.M
module L = EO.L


let split_last (xs : 'a list) : ('a list * 'a) =
  let ys = List.rev xs in
  (List.rev (List.tl ys), List.hd ys)

let rec elab
  (sgn,ps as ctx : EO.context)
  (t : EO.term) : LF.term = failwith ""


let rec elab_app
  (sgn,ps as ctx : EO.context)
  (f,att_opt,lv : EO.term * EO.const_attr option * EO.level)
  (ts : EO.term list) : LF.term
=
  let g x y = EO.glue (ps,f) (x,y) in
  let h y x = EO.glue (ps,f) (y,x) in
  begin match att_opt with
  (* ---- *)
  | None -> LF.app (lv, elab ctx f, L.map (elab ctx) ts)
  (* ---- *)
  | Some RightAssocNil t_nil ->
    begin match ts with
    | [t1; Symbol s] when EO.is_param_attr_list s ps ->
      LF.app (lv, elab ctx f, L.map (elab ctx) ts)

    | _ -> elab ctx (L.fold_right g ts t_nil)
    end
  (* ---- *)
  | Some LeftAssocNil t_nil ->
    begin match ts with
    | [t1; Symbol s] when is_param_attr_list s ps ->
      app (f,ts)
    | _ -> L.fold_left h t_nil ts
    end
  (* ---- *)
  | Some RightAssoc ->
    let (xs, x) = split_last ts in
    L.fold_right g xs x
  (* ---- *)
  | Some LeftAssoc ->
    L.fold_left h (List.hd ts) (List.tl ts)
  (* ---- *)
  | Some Chainable op ->
    let rec aux =
      function
      | v :: w :: vs -> (app (f,[v;w])) :: aux vs
      | _ -> []
    in
      desugar_app ps (op, aux ts)
  (* ---- *)
  | Pairwise op ->
    let f' = desugar ctx mvs (Symbol op) in
    let rec aux = function
      | v :: vs ->
        List.append
          (List.map (fun w -> mk_app O f [v;w]) vs)
          (aux vs)
      | [] -> []
    in
      mk_list_app ctx mvs f' (aux ts)
  (* ---- *)
  | RightAssocNilNSN _
  | LeftAssocNilNSN _
  | ArgList _ | Binder _ ->
    failwith "unimplemented strategy"
  (* ---- *)
  end
