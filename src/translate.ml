(* importing Eunoia stuff. *)
module EO = struct
  include Syntax_eo
  include Interface_eo
end

(* importing LambdaPi stuff. *)
module LP = Syntax_lp

let is_lp_iden (s : string) : bool =
  true

let translate_symbol (s : string) : string =
  if is_lp_iden s then s else
    Printf.sprintf "{|%s|}" s

let mk_lp_set_arrow_typ : LP.term -> LP.term =
  

let translate_tm : EO.term -> LP.term =
  function
  | Symbol s -> Var (translate_symbol s)
  | Apply (s, ts) ->
    if s = "->" then
