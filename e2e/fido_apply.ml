(* fido_apply — a tiny FILESYSTEM-ONLY CLI: the publish (SINK) STEP of the ONE validate-then-publish workflow
   (§5).  It reads a PRISTINE generated-module directory (a root [go.mod] plus recursive [.go] files — any
   materialized image, e.g. the `generated-module` Buildx layer) and synchronizes it into a destination through
   the SAME [Fido_sink] the plugin uses.  It is IMAGE-AGNOSTIC (it transports whatever validated pristine it is
   pointed at, not a hard-coded canonical program) and it inspects no Rocq term and no AST; it compiles nothing,
   renders nothing, alters no bytes, and chooses no semantic path — it only enumerates the already-final module
   tree and hands (go.mod bytes, (relative .go path, bytes) list) to the sink.

   STRUCTURAL publication gate (§5): this CLI REFUSES to publish any source that does not carry the fresh-build
   VALIDATION MARKER [.fido-build-validated].  That marker is produced ONLY by the go-e2e stage, which writes it
   after the pinned one-shot `go build ./...` over the exact content-addressed pristine layer SUCCEEDS; the
   `sync` image obtains it from go-e2e through a Docker-DAG dependency over the SAME content-addressed layer, so
   a not-yet-built or FAILED validation leaves the marker absent and this CLI refuses.  Publication is therefore
   NOT merely make-ordered — the sink is un-runnable on unvalidated bytes even when this binary is invoked
   directly, which is the real internal boundary that a comment or a Make prerequisite cannot provide.
   (Assurance level: reasonable protection against ACCIDENTAL publication of unvalidated output for a
   cooperating developer — the same level the pre-commit hook documents — NOT resistance to deliberate local
   forgery of the marker file.)  The marker is never itself published (only [go.mod] + [.go] are transported).

   Usage: fido-apply <src-generated-dir> <dest-root>. *)

let validation_marker = ".fido-build-validated"

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
  (* STRUCTURAL publication gate: refuse unless this exact pristine carries the fresh-build validation marker. *)
  let marker = Filename.concat src validation_marker in
  if not (Sys.file_exists marker) then
    (prerr_endline ("fido apply: REFUSED — the source carries no fresh-build validation marker (" ^ marker
      ^ "): publication requires a successful pinned `go build ./...` over these exact bytes first"); exit 3);
  let go_mod = read_whole (Filename.concat src "go.mod") in
  let entries = List.rev (go_files src "" []) in
  match (try `Ok (Fido_sink.sync dst go_mod entries) with Fido_sink.Fail m -> `Fail m) with
  | `Ok n -> Printf.printf "fido apply: synced %d file(s) into %s\n" n dst
  | `Fail m -> prerr_endline ("fido apply: refused: " ^ m); exit 1
