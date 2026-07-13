(* A tiny standalone driver that exercises the dirty-directory sink (plugin/fido_sink.ml) directly, so
   the §17 filesystem algorithm can be tested against dirty/adversarial trees without the Rocq layer.
   It syncs a fixed one-file header-owned image into argv.(1).  An optional argv.(2) selects a fault,
   injected through the REAL algorithm via the sink's operation PARAMETERS (no ambient environment branch):
     "fail-recovery-unlink"  — [unlink] fails on any staging entry, so recovery aborts fail-loud;
     "crash-mid-staging"     — [after_stage] raises after the real staging code creates a real temp,
                               modelling a process stopped mid-staging (a real temp is left in staging). *)
let header = "// fido generated.  do not edit."
let content = header ^ "\n\npackage main\n\nfunc main() {}\n"

let has_sub hay needle =                       (* is [needle] a substring of [hay]? *)
  let hl = String.length hay and nl = String.length needle in
  let rec go i = i + nl <= hl && (String.sub hay i nl = needle || go (i + 1)) in
  nl = 0 || go 0

let () =
  let root = Sys.argv.(1) in
  let mode = if Array.length Sys.argv > 2 then Sys.argv.(2) else "" in
  let unlink p =
    if mode = "fail-recovery-unlink" && has_sub p "/.fido/staging/"
    then raise (Unix.Unix_error (Unix.EACCES, "unlink", p))
    else Unix.unlink p in
  let after_stage _ =
    if mode = "crash-mid-staging" then raise (Fido_sink.Fail "simulated crash mid-staging") in
  match (try `Ok (Fido_sink.sync ~unlink ~after_stage root [ ("main.go", content) ])
         with Fido_sink.Fail m -> `Fail m) with
  | `Ok n -> Printf.printf "sink_test: synced %d file(s) into %s\n" n root
  | `Fail m -> prerr_endline ("sink_test: refused: " ^ m); exit 1
