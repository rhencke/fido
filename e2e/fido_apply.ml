(* fido_apply — the tiny INTERNAL publication adapter for the `make regenerate` / `sync` workflow.  It reads the
   fixed pristine source [/generated] (the certified generated-module layer — materialized by `Fido Materialize`
   and validated by the go-e2e Docker stage) and synchronizes it into the destination through [Fido_sink.sync].
   It is not a public product API: it runs no Go, hashes nothing, inspects no validation evidence, and accepts no
   arbitrary source root.  Validate-before-publish ordering is owned by the Docker build graph (the `sync` image
   depends on a successful go-e2e), not by this adapter. *)

let src = "/generated"

let read_whole p =
  let ic = open_in_bin p in
  let n = in_channel_length ic in
  let s = really_input_string ic n in close_in ic; s

(* enumerate every [.go] file under [/generated] as (canonical forward-slash relative path, exact bytes). *)
let rec go_files rel acc =
  let dir = if rel = "" then src else Filename.concat src rel in
  Array.fold_left (fun acc name ->
    let child_rel = if rel = "" then name else rel ^ "/" ^ name in
    let p = Filename.concat dir name in
    match (Unix.lstat p).Unix.st_kind with
    | Unix.S_DIR -> go_files child_rel acc
    | Unix.S_REG when Filename.check_suffix name ".go" -> (child_rel, read_whole p) :: acc
    | _ -> acc)
    acc (Sys.readdir dir)

let () =
  let dst = if Array.length Sys.argv >= 2 then Sys.argv.(1) else "/dest" in
  let go_mod = read_whole (Filename.concat src "go.mod") in
  let entries = List.rev (go_files "" []) in
  match (try `Ok (Fido_sink.sync dst go_mod entries) with Fido_sink.Fail m -> `Fail m) with
  | `Ok n -> Printf.printf "fido apply: synced %d file(s) into %s\n" n dst
  | `Fail m -> prerr_endline ("fido apply: refused: " ^ m); exit 1
