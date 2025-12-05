open List

module EO = struct
  include Syntax_eo
  include Context_eo
end

module M = EO.M

let split_last (xs : 'a list) : ('a list * 'a) =
  let ys = List.rev xs in
  (List.rev (List.tl ys), List.hd ys)

(* post-elaboration terms *)
type param_attr =
  | Implicit
  | Explicit
  | Opaque

type term =
  | Literal of EO.literal
  | Symbol of string
  | App of term * term
  | Meta of term * term
  | Let of var list * term
and param =
  string * term * param_attr
and var =
  string * term
and case =
  term * term

let mk_app (t : term) (ts : term list) : term =
  fold_left (fun t_acc t' -> App (t_acc, t')) t ts

let mk_app_binop_right (cons, nil : term * term) (ts : term list) =
  let app_bin f t1 t2 = App (App (f, t1), t2) in
  fold_right (fun t_acc t' -> app_bin cons t_acc t') ts nil

let mk_meta_app (t : term) (ts : term list) : term =
  fold_left (fun t_acc t' -> Meta (t_acc, t')) t ts

let mk_eo_list_concat
  (f, t1,t2 : term * term * term) : term =
  mk_meta_app (Symbol "eo::list_concat") [f;t1;t2]

let mk_eo_var (s,t : string * term) : term =
  mk_meta_app (Symbol "eo::var") [Literal (String s); t]

(* auxillary function used in elaboration of f-lists. *)
let glue (ps : EO.param list)
  (f,t1,t2 : term * term * term) : term
=
  match t1 with
  | Symbol s when EO.is_list_param s ps ->
    mk_eo_list_concat (f,t1,t2)
  | _ -> mk_app f [t1;t2]

let rec elab_tm
  (sgn, ps as ctx : EO.signature * EO.param list)
  (t : EO.term) : term
=
  match t with
  (* ------------------------ *)
  | Literal l -> Literal l
  (* ------------------------ *)
  | Symbol s -> Symbol s
  (* ------------------------ *)
  | Bind (s, vs, t) ->
    if s = "eo::define" then
      Let (map (elab_var ctx) vs, elab_tm ctx t)
    else
      elab_binder_app ctx (s,vs,t)
  (* ------------------------ *)
  | Apply (s, ts) ->
    (* refactor to `EO.is_meta` *)
    if EO.is_builtin s || EO.is_program s || M.mem s sgn.def || s = "->" then
      mk_meta_app (Symbol s) (map (elab_tm ctx) ts)
    else
      elab_const_app ctx s ts
and
  elab_const_app
    (sgn,ps as ctx : EO.signature * EO.param list)
    (s : string) (ts : EO.term list) : term
  =
    let
      ts' = map (elab_tm ctx) ts       and
      g x y = glue ps (Symbol s, x, y) and
      h y x = glue ps (Symbol s, y, x)
    in
      match M.find_opt s sgn.att with
      | Some (RightAssocNil t_nil) ->
        fold_right g ts' (elab_tm ctx t_nil)
      | Some (LeftAssocNil t_nil) ->
        fold_left h (elab_tm ctx t_nil) ts'
      | Some (RightAssoc) ->
        let (xs, x) = split_last ts' in
        List.fold_right g xs x
      | Some (LeftAssoc) ->
        List.fold_left h (List.hd ts') (List.tl ts')
      | Some (att) ->
        Printf.printf
          "WARNING: naive application of constant %s with attribute %s.\n"
          s (EO.const_attr_str att);
        mk_app (Symbol s) ts'
      | None ->
        mk_app (Symbol s) ts'
and
  elab_binder_app
    (sgn,ps as ctx : EO.signature * EO.param list)
    (s,vs,t : string * EO.var list * EO.term) : term
  =
    match M.find_opt s sgn.att with
    | Some (Binder t_cons) ->
      let vs' = map (fun v -> mk_eo_var (elab_var ctx v)) vs in
      let vlist = elab_tm ctx (Apply (t_cons, ts)) in
      (* TODO. lookup params of binder symbol? *)
      let c = Const (s,[]) in
      mk_app s
      App (App (c, ts'), elab_tm ctx t)
    | _ -> failwith "error: unregistered binder."
and
  elab_param
    (sgn : EO.signature) (s,t,xs : EO.param) : param
  =
    let t' = elab_tm (sgn,[]) t in
    let fl =
      if List.mem (Attr ("implicit", None)) xs then
        Implicit
      else if List.mem (Attr ("opaque", None)) xs then
        Opaque
      else
        Explicit
    in
      (s,t',fl)
and
  elab_var (ctx : EO.signature * EO.param list)
    (s,t : EO.var) : var =
    (s, elab_tm ctx t)

let elab_case (ctx : EO.signature * EO.param list)
  (t,t' : EO.case) : case
=
  (elab_tm ctx t, elab_tm ctx t')

let rec free_in (t : term) (s : string) =
  match t with
  | Const (_,_) -> false
  | Var s' -> s = s'
  | Literal l -> false
  | App (t1,t2)   -> free_in t1 s || free_in t2 s
  | Meta (s', ts) -> List.exists (fun t' -> free_in t' s) ts
  | Let (xs, t') ->
      let b = List.exists
        (fun (s',t') ->
          if s = s' then failwith "error: variable capture in eo::define"
          else free_in t' s
        ) xs
      in
        b || free_in t' s

let free_params (ps : eparam list) (t : term) : (string * term) list =
  let f (s,ty,flg) =
    if free_in t s then Some (s,ty) else None
  in
    List.filter_map f ps

(* --------- pretty printing ---------- *)
let rec term_str : term -> string =
  function
  | Const (s,qs) ->
      let qs_str = String.concat " " (map eparam_str qs) in
      Printf.sprintf "%s⟦%s⟧" s qs_str
  | Var s -> s
  | Literal l -> literal_str l
  | App (t1,t2) ->
    Printf.sprintf "(_ %s %s)"
      (term_str t1)
      (term_str t2)
  | Let (xs, t) ->
    let xs_str = String.concat " " (List.map evar_str xs) in
    Printf.sprintf "(eo::define (%s) %s)" xs_str (term_str t)
  | Meta (s, ts) ->
    let ts_str = String.concat " " (List.map term_str ts) in
    Printf.sprintf "(%s %s)" s ts_str
and evar_str : (string * term) -> string =
  fun (s,t) ->
    Printf.sprintf "(%s %s)" s (term_str t)
and eparam_str : eparam -> string =
  fun (s,t,flag) ->
    match flag with
    | Explicit ->
        Printf.sprintf "(%s : %s)" s (term_str t)
    | Implicit ->
        Printf.sprintf "[%s : %s]" s (term_str t)
    | Opaque ->
        Printf.sprintf "⟬%s : %s⟭" s (term_str t)


    (* let rec subst ((s,t) : string * term) =
  let f = subst (s,t) in
  function
  | Symbol s' -> if s = s' then t else Symbol s'
  | Literal l -> Literal l
  | App (t1,t2) -> App (f t1, f t2)
  | Let (xs, t') ->
      let ys =
        List.map (fun (x,d) -> (x, f d)) xs
      in
        Let (ys, f t')
  | Meta (s, ts) -> Meta (s,List.map f ts)

let rec splice (t : term)
  (ps : params) (ts : term list) : term
=
  match ps with
  | [] -> t
  | Param (s, _, xs) :: ps' ->
    if List.mem (Attr ("implicit", None)) xs then
      splice t ps' ts
    else
      let t' = subst (s, List.hd ts) t in
      splice t' ps' (List.tl ts) *)

      let lcat_of : literal -> lit_category =
  function
  | Numeral _  -> NUM
  | Decimal _  -> DEC
  | Rational _ -> RAT
  | Binary _   -> BIN
  | Hexadecimal _ -> HEX
  | String _      -> STR
