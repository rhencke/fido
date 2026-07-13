(* A tiny standalone driver that exercises the dirty-directory sink (plugin/fido_sink.ml) directly, so
   the §17 filesystem algorithm can be tested against dirty/adversarial trees without the Rocq layer.
   It syncs a fixed one-file header-owned image into argv.(1).  An optional argv.(2) selects a fault or
   input, injected through the REAL algorithm via the sink's operation PARAMETERS (no ambient env branch):
     "fail-recovery-unlink" — [unlink] always fails, so recovery (its first unlink caller) aborts fail-loud;
     "crash-mid-staging"    — [after_stage] TERMINATES the process (Unix._exit) after the real staging code
                              creates a real temp: a true crash, no finalizer, the lock stays held;
     "reserved-path"        — the desired image targets a path inside the reserved .fido/ namespace. *)
let header = "// fido generated.  do not edit."
let content = header ^ "\n\npackage main\n\nfunc main() {}\n"

let () =
  let root = Sys.argv.(1) in
  let mode = if Array.length Sys.argv > 2 then Sys.argv.(2) else "" in
  let image = match mode with
    | "reserved-path" -> [ (".fido/staging/foo.go", content) ]
    | _ -> [ ("main.go", content) ] in
  let unlink p =
    if mode = "fail-recovery-unlink" then raise (Unix.Unix_error (Unix.EACCES, "unlink", p))
    else Unix.unlink p in
  let after_stage _ =
    if mode = "crash-mid-staging" then Unix._exit 137 in
  match (try `Ok (Fido_sink.sync ~unlink ~after_stage root image) with Fido_sink.Fail m -> `Fail m) with
  | `Ok n -> Printf.printf "sink_test: synced %d file(s) into %s\n" n root
  | `Fail m -> prerr_endline ("sink_test: refused: " ^ m); exit 1
