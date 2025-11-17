open Syntax_eo

type defn =
  | Term of term
  | Cases of (term * term) list

type judgement =
  | TypeJ of symbol * param list * term
  | DefnJ of symbol * param list * defn
  | AttrJ of symbol * param list * attr

module SMap = Map.Make(String)
type eo_sig = judgement SMap.t

module Judgement = struct
  type t = judgement
  let compare = compare
end

module JSet = Set.Make(Judgement)
type jset = JSet.t

let proc_common_command : common_command -> JSet.t =
  function
  | DeclareConst     (s,t,xs)  -> failwith ""
  | DeclareDatatype  (s,dt)    -> failwith ""
  | DeclareDatatypes (sts,dts) -> failwith ""
  | Echo             (str_opt) -> failwith ""
  | Exit                       -> failwith ""
  | Reset                      -> failwith ""
  | SetOption        (a)       -> failwith ""
