module EO = Syntax_eo
open Syntax_lp

let rec eo_tm : EO.term -> term =
  function
  | Symbol "Type" -> Var (safe_name "eo::Type")
  | Symbol "->" -> Var "⤳"
  | Symbol s -> Var (safe_name s)
  | Apply ("_",[t1;t2]) ->
      App (eo_tm t1, eo_tm t2)
  | Apply (s,ts) ->
      app_list (Var (safe_name s)) (L.map eo_tm ts)
  | Bind ("eo::define",xs,t) ->
      List.fold_right
        (fun (x,d) acc -> Let (safe_name x, eo_tm d, acc))
        xs (eo_tm t)
  | _ as t -> Printf.ksprintf failwith
    "Term not fully elaborated: %s" (EO.term_str t)

let eo_prm (ps : EO.param list) : param list =
  L.map (fun (s,t,atts) ->
    (safe_name s, tau_of (eo_tm t),
      (if L.mem EO.Implicit atts
        then Implicit else Explicit)
    )
  ) ps

let eo_const (s,k : string * EO.const) : command list =
  match k with
  | Decl (ps,ty,_) ->
  [
    Symbol (
      Some Constant, safe_name s,
      eo_prm ps,
      Some (tau_of @@ eo_tm ty),
      None)
  ]

  | Prog ((ps,ty),(qs,cs)) ->
  [
    Symbol (Some Sequential, safe_name s,
      eo_prm ps,
      Some (tau_of @@ eo_tm ty),
      None);

    Rule (
      let f t = bind_pvars qs (eo_tm t) in
      L.map (fun (t,t') -> (f t, f t')) cs)
  ]

  | Rule _ -> []
  | Defn _ -> []

let eo_sig : EO.signature -> signature =
  L.concat_map eo_const
