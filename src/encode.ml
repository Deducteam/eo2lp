module EO = Syntax_eo
open Syntax_lp

let encode_hook = ref (fun _ f -> f ())

let rec eo_name : string -> string =
  function
  | "Type" -> eo_name "eo::Type"
  | s when S.starts_with ~prefix:"$" s ->
    "!" ^ eo_name (strip_prefix s "$")
  | s when S.starts_with ~prefix:"@@" s ->
    "_" ^ eo_name (strip_prefix s "@@")
  (* | s when S.starts_with ~prefix:"eo::" s ->
    "eo." ^ safe_name (strip_prefix s "eo::") *)
  | s ->
    let s' = s |> replace ('.',"⋅") |> replace (':', "⋅") in
    if is_forbidden s'
      then Printf.sprintf "{|%s|}" s
      else s'

let rec eo_tm : EO.term -> term =
  function
  | Symbol s -> Var (eo_name s)
  | Literal l -> Lit l
  | Apply (s,ts) ->
    begin match s,ts with
    | "_", [t1;t2] -> App (eo_tm t1, eo_tm t2)
    | "->", _ -> arr_list (L.map eo_tm ts)
    | _ -> app_list (Var (eo_name s)) (L.map eo_tm ts)
    end

  | Bind ("eo::define",xs,t) ->
    begin match xs with
    | [] -> eo_tm t
    | (x,tx) :: ys ->
      let t' = EO.Bind ("eo::define",ys,t) in
      Let (eo_name x, eo_tm tx, eo_tm t')
    end

  | _ as t -> Printf.ksprintf failwith
    "Term not fully elaborated: %s" (EO.term_str t)


let eo_att (atts : EO.attr list) : attr =
  if L.mem EO.Implicit atts
  then Implicit else Explicit

let eo_prm (ps : EO.param list) : param list =
  L.map (fun (s,t,atts) ->
    (eo_name s, tau_of (eo_tm t), eo_att atts)) ps

let eo_const (s,k : string * EO.const) : command list =
  !encode_hook s (fun () ->
    match k with
    | Decl (ps,ty,_) ->
    [
      Symbol (
        Some Constant, eo_name s,
        eo_prm ps,
        Some (tau_of @@ eo_tm ty),
        None
      )
    ]

    | Prog ((ps,ty),(qs,cs)) ->
    [
      Symbol (
        Some Sequential, eo_name s,
        eo_prm ps,
        Some (tau_of @@ eo_tm ty),
        None
      );

      Rule (
        let f t = bind_pvars qs (eo_tm t) in
        L.map (fun (t,t') -> (f t, f t')) cs
      )
    ]

    | Defn (ps,t) ->
    [
      Symbol (None, eo_name s, eo_prm ps, None, Some (eo_tm t))
    ]

    | Rule _ -> []
  )

let eo_sig : EO.signature -> signature =
  L.concat_map eo_const
