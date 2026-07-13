(* A tiny standalone driver that exercises the dirty-directory sink (plugin/fido_sink.ml) directly, so
   the §17 filesystem algorithm can be tested against dirty/adversarial trees without the Rocq layer.
   It syncs a fixed one-file header-owned image into argv.(1).  An optional argv.(2) = "fail-recovery-unlink"
   injects a cleanup failure by passing an [unlink] that fails on any staged temp file — through the REAL
   recovery algorithm, with no ambient environment branch or destructive behaviour in the production path. *)
let header = "// fido generated.  do not edit."
let content = header ^ "\n\npackage main\n\nfunc main() {}\n"

let () =
  let root = Sys.argv.(1) in
  let fault = Array.length Sys.argv > 2 && Sys.argv.(2) = "fail-recovery-unlink" in
  let unlink p =
    if fault && Fido_sink.contains_sub (Filename.basename p) ".fido-tmp-"
    then raise (Unix.Unix_error (Unix.EACCES, "unlink", p))
    else Unix.unlink p in
  match (try `Ok (Fido_sink.sync ~unlink root [ ("main.go", content) ]) with Fido_sink.Fail m -> `Fail m) with
  | `Ok n -> Printf.printf "sink_test: synced %d file(s) into %s\n" n root
  | `Fail m -> prerr_endline ("sink_test: refused: " ^ m); exit 1
