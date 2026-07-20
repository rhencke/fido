(* fido_apply — a tiny FILESYSTEM-ONLY CLI: the publish (SINK) STEP of the ONE validate-then-publish workflow
   (§5).  It reads a PRISTINE generated-module directory (a root [go.mod] plus recursive [.go] files — any
   materialized image, e.g. the `generated-module` Buildx layer) and synchronizes it into a destination through
   the SAME [Fido_sink] the plugin uses.  It is IMAGE-AGNOSTIC (it transports whatever validated pristine it is
   pointed at, not a hard-coded canonical program) and it inspects no Rocq term and no AST; it compiles nothing,
   renders nothing, alters no bytes, and chooses no semantic path — it only enumerates the already-final module
   tree and hands (go.mod bytes, (relative .go path, bytes) list) to the sink.

   STRUCTURAL, BYTE-BOUND publication gate (§5): this CLI REFUSES to publish unless the source carries a
   fresh-build VALIDATION MANIFEST [.fido-build-validated] — a REGULAR (non-symlink) file listing `<md5> <path>`
   for EXACTLY the go.mod + every .go of the validated tree.  fido-apply recomputes the md5 of each file it is
   about to publish and requires a byte-exact bijection with the manifest (every published file attested with a
   matching digest, and the manifest attesting no more and no fewer files).  The manifest is produced ONLY by the
   go-e2e stage, AFTER the pinned one-shot `go build ./...` over the exact content-addressed pristine layer
   SUCCEEDS, and reaches the `sync` image over a Docker-DAG dependency.  So the sink is un-runnable on bytes that
   were not build-validated — an arbitrary tree plus a copied/stale manifest fails the digest bijection, and a
   failed/absent validation leaves the manifest absent.  Publication is thus NOT merely make-ordered, and the
   binding is to the BYTES, not to mere marker presence.  (This binds publication to the validated content; it is
   integrity binding, not a keyed signature — deliberate local forgery of BOTH the tree and its manifest is a
   separate concern.)  The manifest is never itself published (only [go.mod] + [.go] are transported).

   Usage: fido-apply <src-generated-dir> <dest-root>. *)

module SM = Map.Make (String)

let validation_manifest = ".fido-build-validated"
let refuse msg = prerr_endline ("fido apply: REFUSED — " ^ msg); exit 3

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

(* parse the manifest (one newline-terminated line per file, each md5hex then a space then the relpath)
   into a path->md5 map and its non-empty line count. *)
let parse_manifest s =
  List.fold_left (fun (m, n) line ->
    if String.trim line = "" then (m, n)
    else match String.index_opt line ' ' with
      | None -> refuse ("malformed validation-manifest line: " ^ line)
      | Some i ->
        let md5  = String.sub line 0 i in
        let path = String.trim (String.sub line (i + 1) (String.length line - i - 1)) in
        (SM.add path md5 m, n + 1))
    (SM.empty, 0) (String.split_on_char '\n' s)

let () =
  if Array.length Sys.argv <> 3 then (prerr_endline "usage: fido-apply <src-generated-dir> <dest-root>"; exit 2);
  let src = Sys.argv.(1) and dst = Sys.argv.(2) in
  (* STRUCTURAL gate — a REGULAR (non-symlink) validation manifest must be present. *)
  let manifest_path = Filename.concat src validation_manifest in
  (match (try Some (Unix.lstat manifest_path) with Unix.Unix_error _ -> None) with
   | Some st when st.Unix.st_kind = Unix.S_REG -> ()
   | Some _ -> refuse (validation_manifest ^ " is not a regular file")
   | None   -> refuse ("no fresh-build validation manifest " ^ manifest_path
                ^ "; a successful pinned `go build ./...` over these exact bytes must attest them first"));
  let (want, want_n) = parse_manifest (read_whole manifest_path) in
  let go_mod  = read_whole (Filename.concat src "go.mod") in
  let entries = List.rev (go_files src "" []) in
  (* BYTE-BINDING — the published set (go.mod + every .go) must be a byte-exact bijection with the manifest. *)
  let published = ("go.mod", go_mod) :: entries in
  if List.length published <> want_n then
    refuse (Printf.sprintf "the validation manifest attests %d file(s) but %d are present — not the validated byte-set"
              want_n (List.length published));
  List.iter (fun (path, bytes) ->
    match SM.find_opt path want with
    | Some m when String.equal m (Digest.to_hex (Digest.string bytes)) -> ()
    | Some _ -> refuse ("file " ^ path ^ " differs from the validated bytes (md5 mismatch)")
    | None   -> refuse ("file " ^ path ^ " is not attested by the validation manifest")) published;
  match (try `Ok (Fido_sink.sync dst go_mod entries) with Fido_sink.Fail m -> `Fail m) with
  | `Ok n -> Printf.printf "fido apply: synced %d file(s) into %s\n" n dst
  | `Fail m -> prerr_endline ("fido apply: refused: " ^ m); exit 1
