(* A tiny standalone driver that exercises the dirty-directory sink (plugin/fido_sink.ml) directly, so
   the §17 filesystem algorithm can be tested against dirty/adversarial trees without the Rocq layer.
   It syncs a fixed one-file header-owned image into argv.(1). *)
let header = "// fido generated.  do not edit."
let content = header ^ "\n\npackage main\n\nfunc main() {}\n"

let () =
  let root = Sys.argv.(1) in
  match (try `Ok (Fido_sink.sync root [ ("main.go", content) ]) with Fido_sink.Fail m -> `Fail m) with
  | `Ok n -> Printf.printf "sink_test: synced %d file(s) into %s\n" n root
  | `Fail m -> prerr_endline ("sink_test: refused: " ^ m); exit 1
