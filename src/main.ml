module EO = struct
  include Syntax_eo
  include Elaborate_eo
end

module LP = struct
  include Syntax_lp
end

module SMap = Map.Make(String)

type 'a pmap = (EO.params * 'a) SMap.t

type signature =
  {
    mutable atts : EO.attr pmap;
    mutable typs : EO.term pmap;
    mutable defs : EO.term pmap;
    mutable prgs : EO.cases pmap;
  }

let _sig : signature =
  {
    atts = SMap.of_list [];
    typs = SMap.of_list [];
    defs = SMap.of_list [];
    prgs = SMap.of_list [];
  }

(* find eo files in dir *)
let find_eo_files (dir : string) : string list =
  Array.fold_left
    (fun acc name ->
      if Filename.check_suffix name ".eo" then
        (Filename.concat dir name) :: acc
      else
        acc
    )
    [] (Sys.readdir dir)


let atts_pmap
  (s : string) (ps : EO.params) (xs : EO.attr list) : EO.attr pmap
=
  SMap.of_list
    (List.map (fun x -> (s, (ps,x))) xs)

let proc_common_command : EO.common_command -> unit =
  function
  | DeclareConst (s,t,xs)  ->
    _sig.typs <- SMap.add s ([],t) _sig.typs;
    _sig.atts <- atts_pmap s [] xs

  | DeclareDatatype  (_s,_dt)    -> ()
  | DeclareDatatypes (_sts,_dts) -> ()
  | Echo             (_str_opt)  -> ()
  | Exit                         -> ()
  | Reset                        -> ()
  | SetOption        (_a)        -> ()

let proc_ruledec : EO.rule_dec -> unit  =



let proc_eo_file (fp : string) : unit =
  List.iter
    (fun cmd ->
      (* Printf.printf "Processing:\n%s\n" (command_str cmd); *)
      let js = proc_command cmd in
      Printf.printf "\n%s\n" (jlist_str js);
      js)
    (parse_eo_file fp)
