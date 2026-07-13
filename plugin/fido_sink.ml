(* fido_sink — the ONLY handwritten filesystem logic: a GENERIC ownership-aware dirty-directory
   synchronizer.  It receives an already-final directory image ((on-disk relative path * exact bytes)
   list, decoded from a proved-Rocq DirectoryImage whose provenance the vernac bridge typechecks) and
   makes a target tree's Fido-generated files EQUAL that image, preserving foreign files.  It understands
   ONLY the filesystem: it decodes no program, renders nothing, parses no Go, walks no Rocq terms.

   OWNERSHIP is positive and rechecked immediately before every overwrite/delete.  A generated `.go` is
   Fido-owned iff its FIRST LINE is the exact header (DERIVED from the image bytes, never hardcoded); it
   is only touched/removed when that header is present.  A per-parent staging directory
   `.fido-stage-<rand>/` is owned via a DURABLE record `<root>/.fido/stage-<rand>` in the persistent
   control dir — the record, NOT any file inside the stage, is the ownership authority.  Because the
   record lives outside the stage it is removing, even a PARTIALLY removed stage (contents gone, `rmdir`
   failed) stays mechanically recognizable and is recovered on a later run; a foreign `.fido-stage-*`
   directory (no record) is never touched.  No symlink is followed (lstat everywhere; symlinked dirs are
   never descended).

   All files stage before any install; the body runs to an OUTCOME and a SINGLE finalizer then runs
   exactly once.  That finalizer is FAIL-LOUD on its correctness obligations — every invocation stage
   (and its record), the lock descriptor, and the lock pathname — aggregating all their failures, so
   success is never reported while any of them survives, and a body error is combined with (never
   replaced or hidden by) a cleanup error.  A stage whose removal fails keeps its record, so ownership
   is preserved for recovery.  Removing an EMPTY new parent directory is the one deliberately best-effort
   step (a leftover empty dir is not stale state).

   The fallible directory-removal operation is a PARAMETER (`?rmdir`, default the real `Unix.rmdir`), so
   the standalone test driver can inject a cleanup failure through the real algorithm without any ambient
   environment branch or destructive behaviour in the production call graph; the plugin always links the
   real operation.

   HONEST GUARANTEE (threat model): a git-style index.lock coordinates COOPERATING Fido emitters, and
   every PRE-EXISTING foreign entry (file/dir/symlink) is preserved.  It is NOT a transactional whole-tree
   commit (a crash mid-install may leave a mixed generation; the next run converges after recovering
   recorded stale stages), and — like git's index.lock, and because this OCaml `Unix` exposes no
   openat/renameat/O_NOFOLLOW — it is NOT hardened against a concurrent NON-cooperating process racing
   symlink swaps into the target between check and use; the intended use (a single emit process writing a
   build tree) has no such adversary. *)

let control_dir   = ".fido"
let marker_name   = "marker"
let marker_bytes  = "fido-control-directory.  do not edit.\n"
let lock_name     = "index.lock"      (* git-style: created O_EXCL, removed at end *)
let stage_prefix  = ".fido-stage-"    (* a per-parent staging directory *)
let record_prefix = "stage-"          (* its durable ownership record, in the control dir *)
let skip_dirs     = [ ".git"; ".hg"; ".svn"; control_dir ]

exception Fail of string
let fail fmt = Printf.ksprintf (fun s -> raise (Fail s)) fmt

(* ---- lstat-based helpers (never follow a symlink implicitly) ---- *)
let lstat_opt p = try Some (Unix.lstat p) with Unix.Unix_error _ -> None
let kind_opt p = match lstat_opt p with Some st -> Some st.Unix.st_kind | None -> None
let is_real_dir p = kind_opt p = Some Unix.S_DIR
let is_symlink p = kind_opt p = Some Unix.S_LNK
let has_prefix pfx name =
  String.length name >= String.length pfx && String.sub name 0 (String.length pfx) = pfx
let has_stage_prefix name = has_prefix stage_prefix name

let first_line path =
  match (try Some (open_in_bin path) with Sys_error _ -> None) with
  | None -> None
  | Some ic -> let l = (try Some (input_line ic) with End_of_file -> None) in close_in ic; l

let first_line_of s = match String.index_opt s '\n' with Some i -> String.sub s 0 i | None -> s

let dir_has_marker dir name bytes =
  is_real_dir dir &&
  (let m = Filename.concat dir name in
   kind_opt m = Some Unix.S_REG && (try
     let ic = open_in_bin m in let n = in_channel_length ic in
     let s = really_input_string ic n in close_in ic; s = bytes
   with _ -> false))

let write_exact path bytes =
  let oc = open_out_bin path in output_string oc bytes; close_out oc

(* recursively remove OUR OWN directory: flat contents via unlink + rmdir (the fallible rmdir is a
   parameter so tests can inject a cleanup failure through the real algorithm); never follows a symlink
   (lstat + unlink drops the link itself). *)
let rec rm_rf rmdir path =
  match lstat_opt path with
  | None -> ()
  | Some st ->
    if st.Unix.st_kind = Unix.S_DIR then begin
      Array.iter (fun n -> rm_rf rmdir (Filename.concat path n)) (Sys.readdir path);
      rmdir path
    end else Unix.unlink path

let components rel =
  if not (Filename.is_relative rel) then fail "unsafe absolute path from image: %s" rel;
  let parts = String.split_on_char '/' rel in
  if parts = [] || List.exists (fun c -> c = "" || c = "." || c = ".." || String.contains c '\000') parts
  then fail "unsafe path from image: %s" rel;
  parts

(* a stage's root-relative path, as recorded in the control dir, is safe to remove: relative, no
   traversal, and its basename is a stage directory. *)
let valid_stage_rel rel =
  match String.split_on_char '/' rel with
  | [] -> false
  | parts ->
    List.for_all (fun c -> c <> "" && c <> "." && c <> ".." && not (String.contains c '\000')) parts
    && has_stage_prefix (List.nth parts (List.length parts - 1))

let strip_root root p =                       (* the path of p (under root) relative to root *)
  let rl = String.length root in
  if String.length p > rl && String.sub p 0 rl = root then
    let rest = String.sub p rl (String.length p - rl) in
    if String.length rest > 0 && rest.[0] = '/' then String.sub rest 1 (String.length rest - 1) else rest
  else p

let rec walk_real_dirs root f =
  Array.iter (fun name ->
    let p = Filename.concat root name in
    f p name;
    if is_real_dir p && not (List.mem name skip_dirs) && not (has_stage_prefix name)
    then walk_real_dirs p f)
    (try Sys.readdir root with Sys_error _ -> [||])

let () = Random.self_init ()

(* create a fresh per-parent stage dir AND a DURABLE ownership record (root/.fido/stage-<rand>, naming the
   stage's root-relative path) in the control dir.  Register (stage, record) for cleanup immediately after
   mkdir, then write the record; the record — living OUTSIDE the stage — is the ownership authority. *)
let rec make_stage root ctrl parent created tries =
  if tries <= 0 then fail "could not create a unique stage directory in %s" parent;
  let rand = Printf.sprintf "%06x" (Random.int 0xffffff) in
  let dir = Filename.concat parent (stage_prefix ^ rand) in
  match (try Unix.mkdir dir 0o755; true with Unix.Unix_error (Unix.EEXIST, _, _) -> false) with
  | false -> make_stage root ctrl parent created (tries - 1)
  | true ->
    let record = Filename.concat ctrl (record_prefix ^ rand) in
    created := (dir, record) :: !created;
    write_exact record (strip_root root dir ^ "\n");
    dir

let ensure_real_dir_parents root parts created =
  let rec go cur = function
    | [] | [ _ ] -> ()
    | c :: rest ->
      let nxt = Filename.concat cur c in
      (match kind_opt nxt with
       | None -> Unix.mkdir nxt 0o755; created := nxt :: !created; go nxt rest
       | Some Unix.S_DIR -> go nxt rest
       | Some _ -> fail "a path component is not a real directory: %s" nxt)
  in go root parts

(* ---- the synchronization (algorithm §17 A..G) ---- *)
let sync ?(rmdir = Unix.rmdir) root entries =
  (* the ownership header is DERIVED from the Rocq-rendered bytes (the first line of every generated
     file), not hardcoded — one authority (GoRender). *)
  let gen_header = match entries with (_, b) :: _ -> first_line_of b | [] -> "" in
  let is_generated_go path =
    Filename.check_suffix path ".go"
    && kind_opt path = Some Unix.S_REG && first_line path = Some gen_header in
  (* (A.1) validate / create the marked control directory *)
  (match kind_opt root with
   | None -> Unix.mkdir root 0o755
   | Some Unix.S_DIR -> ()
   | Some _ -> fail "target root is not a real directory: %s" root);
  let ctrl = Filename.concat root control_dir in
  (match kind_opt ctrl with
   | None -> Unix.mkdir ctrl 0o755; write_exact (Filename.concat ctrl marker_name) marker_bytes
   | Some Unix.S_DIR ->
     if not (dir_has_marker ctrl marker_name marker_bytes)
     then fail "%s exists without the exact Fido control marker — refusing to touch it" ctrl
   | Some _ -> fail "%s exists and is not a directory — refusing to touch it" ctrl);
  (* (A.2) exclusive lock — a git-style index.lock: created ATOMICALLY with O_EXCL (so a second
     cooperating emitter is excluded), removed at the end.  A crashed run leaves it; the next run reports
     it clearly and refuses (like git's index.lock), rather than racing. *)
  let lock_path = Filename.concat ctrl lock_name in
  let lock_fd =
    try Unix.openfile lock_path [ Unix.O_CREAT; Unix.O_EXCL; Unix.O_WRONLY ] 0o644
    with Unix.Unix_error (Unix.EEXIST, _, _) ->
      fail "%s already exists — another Fido emission holds it, or a crashed run left it (remove it to proceed)" lock_path in
  let created_parents = ref [] and created_stages = ref [] in
  (* Run the body to an OUTCOME (never finalizing inside it), then finalize EXACTLY ONCE, then combine. *)
  let body =
    try
      (* (A.3) recover stale stages left by a crashed run: read each control-dir ownership record, remove
         the stage it names (record = authority), then the record.  Best-effort: a record whose stage
         cannot be removed now is LEFT for a later run (convergence); a foreign .fido-stage-* has no
         record and is never touched. *)
      Array.iter (fun rn ->
        if has_prefix record_prefix rn then begin
          let record = Filename.concat ctrl rn in
          match first_line record with
          | Some rel when valid_stage_rel (String.trim rel) ->
            let stage = Filename.concat root (String.trim rel) in
            if not (is_symlink stage) then
              (try rm_rf rmdir stage; Unix.unlink record with _ -> ())
          | _ -> ()   (* malformed/foreign-looking record: leave it (we never write such) *)
        end)
        (try Sys.readdir ctrl with _ -> [||]);
      (* (B) desired set + existing generated .go files *)
      let targets = List.map (fun (rel, bytes) ->
        let parts = components rel in (Filename.concat root rel, parts, bytes)) entries in
      let desired = List.map (fun (t, _, _) -> t) targets in
      let existing_go = ref [] in
      walk_real_dirs root (fun p _ -> if is_generated_go p then existing_go := p :: !existing_go);
      (* (C) preflight every desired path (symlinks/foreign/collisions) BEFORE any change *)
      List.iter (fun (target, parts, _) ->
        let rec no_symlink cur = function
          | [] -> () | c :: rest ->
            let nxt = Filename.concat cur c in
            if is_symlink nxt then fail "refusing a symlink in path: %s" nxt else
            if kind_opt nxt = None then () else no_symlink nxt rest in
        no_symlink root parts;
        (match lstat_opt target with
         | None -> ()
         | Some st when st.Unix.st_kind = Unix.S_REG && first_line target = Some gen_header -> ()
         | Some _ -> fail "refusing to overwrite a foreign entry: %s" target))
        targets;
      (* (D) stage every file completely into a per-parent owned stage before any install *)
      let stage_of = Hashtbl.create 8 in
      let staged = List.map (fun (target, parts, bytes) ->
        ensure_real_dir_parents root parts created_parents;
        let parent = Filename.dirname target in
        let stage = match Hashtbl.find_opt stage_of parent with
          | Some s -> s
          | None -> let s = make_stage root ctrl parent created_stages 64 in Hashtbl.add stage_of parent s; s in
        let sp = Filename.concat stage (Filename.basename target) in
        write_exact sp bytes; (sp, target)) targets in
      (* (E) install by per-file atomic rename, rechecking ownership immediately before replacement *)
      List.iter (fun (sp, target) ->
        (match lstat_opt target with
         | None -> ()
         | Some st when st.Unix.st_kind = Unix.S_REG && first_line target = Some gen_header -> ()
         | Some _ -> fail "ownership/type of %s changed under us — aborting" target);
        Sys.rename sp target) staged;
      (* (F) stale cleanup: delete previously-generated .go no longer desired, rechecking ownership *)
      List.iter (fun p ->
        if not (List.mem p desired) then
          (match lstat_opt p with
           | Some st when st.Unix.st_kind = Unix.S_REG && first_line p = Some gen_header -> Unix.unlink p
           | _ -> ()))
        !existing_go;
      Ok (List.length targets)
    with e -> Error e in
  (* (G) FINALIZE ONCE.  Fail-loud on the correctness obligations — every invocation stage (removed via the
     injectable rmdir; its record is deleted ONLY after the stage is gone, so a failed removal keeps the
     stage durably owned), the lock descriptor, and the lock pathname — aggregating ALL their failures.
     Removing an EMPTY new parent is the one deliberately best-effort step. *)
  let cleanup_errs = ref [] in
  let add fmt = Printf.ksprintf (fun s -> cleanup_errs := s :: !cleanup_errs) fmt in
  List.iter (fun (stage, record) ->
    match (try rm_rf rmdir stage; None with ex -> Some (Printexc.to_string ex)) with
    | Some e -> add "stage %s: %s" stage e            (* keep the record: durable ownership for recovery *)
    | None -> (try Unix.unlink record with
               | Unix.Unix_error (Unix.ENOENT, _, _) -> ()   (* already gone / never written: fine *)
               | ex -> add "record %s: %s" record (Printexc.to_string ex)))
    !created_stages;
  List.iter (fun d -> match (try Sys.readdir d with _ -> [||]) with       (* best-effort empty-parent tidy *)
    | [||] -> (try Unix.rmdir d with _ -> ()) | _ -> ()) !created_parents;
  (try Unix.close lock_fd with ex -> add "close lock fd: %s" (Printexc.to_string ex));
  (try Unix.unlink lock_path with ex -> add "unlink %s: %s" lock_path (Printexc.to_string ex));
  let cleanup = match !cleanup_errs with [] -> None | l -> Some (String.concat "; " l) in
  (match body, cleanup with
   | Ok n, None -> n
   | Ok _, Some cm -> fail "installed the tree but cleanup FAILED (a retry recovers it): %s" cm
   | Error e, None -> raise e
   | Error e, Some cm ->
     let em = (match e with Fail m -> m | _ -> Printexc.to_string e) in
     raise (Fail (em ^ " — AND cleanup FAILED: " ^ cm)))
