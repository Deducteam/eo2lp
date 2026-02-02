(* test_util.ml — Shared test framework for eo2lp tests *)

let pass_count = ref 0
let fail_count = ref 0

let green s = "\027[32m" ^ s ^ "\027[0m"
let red s = "\027[31m" ^ s ^ "\027[0m"
let bold s = "\027[1m" ^ s ^ "\027[0m"
let _dim s = "\027[2m" ^ s ^ "\027[0m"

let check_eq pp name ~input ~expected ~actual =
  if expected = actual then begin
    incr pass_count;
    Printf.printf "%s %s\n    %s\n    => %s\n" (green "PASS") name input (pp expected)
  end else begin
    incr fail_count;
    Printf.printf "%s %s\n    %s\n    expected: %s\n    actual:   %s\n"
      (red "FAIL") name input (pp expected) (pp actual)
  end

let check_true name ok =
  if ok then begin
    incr pass_count;
    Printf.printf "%s %s\n" (green "PASS") name
  end else begin
    incr fail_count;
    Printf.printf "%s %s\n" (red "FAIL") name
  end

let section name =
  Printf.printf "\n%s\n" (bold ("=== " ^ name ^ " ==="))

let subsection name =
  Printf.printf "\n--- %s ---\n" name

let summary () =
  Printf.printf "\n%s\n"
    (bold (Printf.sprintf "%d passed, %d failed" !pass_count !fail_count));
  if !fail_count > 0 then exit 1
