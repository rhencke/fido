(* fido_apply — a tiny FILESYSTEM-ONLY production CLI.  It reads a PRISTINE generated module directory (a
   root [go.mod] plus recursive [.go] files, e.g. the `generated-module` Buildx layer) and synchronizes it
   into a destination through the SAME [Fido_sink] the plugin uses.  It inspects no Rocq term and no AST; it
   compiles nothing, renders nothing, alters no bytes, and chooses no semantic path — it only enumerates the
   already-final module tree and hands (go.mod bytes, (relative .go path, bytes) list) to the sink.

   Usage: fido-apply <src-generated-dir> <dest-root>. *)

let read_whole p =
  let ic = open_in_bin p in
  let n = in_channel_length ic in
  let s = really_input_string ic n in close_in ic; s

(* enumerate every [.go] file under [src] as (canonical forward-slash relative path, exact bytes). *)
let rec go_files src rel acc =
  let dir = if rel = "" then src else Filename.concat src rel in
  Array.fold_left (fun acc name ->
    let child_rel = if rel = "" then name else rel ^ "/" ^ name in
    let p = Filename.concat dir name in
    match (Unix.lstat p).Unix.st_kind with
    | Unix.S_DIR -> go_files src child_rel acc
    | Unix.S_REG when Filename.check_suffix name ".go" -> (child_rel, read_whole p) :: acc
    | _ -> acc)
    acc (Sys.readdir dir)

let () =
  if Array.length Sys.argv <> 3 then (prerr_endline "usage: fido-apply <src-generated-dir> <dest-root>"; exit 2);
  let src = Sys.argv.(1) and dst = Sys.argv.(2) in
  let go_mod = read_whole (Filename.concat src "go.mod") in
  let entries = List.rev (go_files src "" []) in
  match (try `Ok (Fido_sink.sync dst go_mod entries) with Fido_sink.Fail m -> `Fail m) with
  | `Ok n -> Printf.printf "fido apply: synced %d file(s) into %s\n" n dst
  | `Fail m -> prerr_endline ("fido apply: refused: " ^ m); exit 1
