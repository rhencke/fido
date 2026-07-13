(* fido_sink — the ONLY handwritten filesystem logic: a GENERIC ownership-aware dirty-directory
   synchronizer.  It receives an already-final directory image ((on-disk relative path * exact bytes)
   list, decoded from a proved-Rocq DirectoryImage whose provenance the vernac bridge typechecks) and
   makes a target tree's Fido-generated files EQUAL that image, preserving foreign files.  It understands
   ONLY the filesystem: it decodes no program, renders nothing, parses no Go, walks no Rocq terms.

   ONE OWNERSHIP AUTHORITY: a regular file is Fido-owned iff its FIRST LINE is the exact generated header
   (DERIVED from the image bytes, never hardcoded).  That single rule covers BOTH installed `.go` files
   AND the temporary files used to stage them — there is no separate marker or record.  Ownership is
   rechecked immediately before every overwrite/delete, always via lstat (a symlink is S_LNK, not S_REG,
   so it is never followed, read, or removed).

   STAGING is per-file and marker-free: each target's bytes are written to a fresh temp file
   `<target>.fido-tmp-<rand>` NEXT TO the target, created with O_CREAT|O_EXCL (so it never clobbers or
   follows an existing file/symlink; a collision just retries), then atomically renamed into place.  There
   are no staging directories, no inner markers, and no control-directory records — so there is no
   marker-that-is-deleted-before-its-directory husk, and no forgeable record path.

   RECOVERY runs FIRST, before any synchronization effect, and is recover-all-or-REJECT: it unlinks every
   owned stale temp (a regular file whose basename carries the temp infix and whose first line is the
   header — left by a crashed or failed run), aggregating failures; if ANY owned temp cannot be removed it
   aborts before staging.  A foreign `*.fido-tmp-*` that is not header-owned, a symlink, or a directory is
   preserved untouched.  The FINALIZER's sole obligation is releasing the lock (close + unlink), fail-loud
   and exactly once; a body error is combined with (never hidden by) a lock-release error.  A stage temp
   left by a failed body is itself owned, so the next run's recovery removes it.

   HONEST GUARANTEE (threat model): a git-style index.lock coordinates COOPERATING Fido emitters, and
   every PRE-EXISTING foreign entry (file/dir/symlink) is preserved (a foreign file forging the exact
   header is indistinguishable — the accepted limit of header ownership, identical for `.go` and temps).
   It is NOT a transactional whole-tree commit: a partial run may install some targets and leave owned
   temps, which the next run's recovery removes.  A CRASH (not a handled failure) leaves the index.lock;
   the next run REFUSES until that stale lock is deliberately removed, then recovers.  Only a HANDLED
   cleanup failure — where the finalizer already released the lock — permits an immediately converging
   rerun.  Like git's index.lock, and because this OCaml `Unix` exposes no openat/renameat/O_NOFOLLOW, it
   is NOT hardened against a concurrent NON-cooperating process racing symlink swaps between check and use;
   the intended use (a single emit process writing a build tree) has no such adversary. *)

let control_dir  = ".fido"
let marker_name  = "marker"
let marker_bytes = "fido-control-directory.  do not edit.\n"
let lock_name    = "index.lock"       (* git-style: created O_EXCL, removed at end *)
let tmp_infix    = ".fido-tmp-"       (* a staged temp file: <target-basename>.fido-tmp-<rand> *)
let skip_dirs    = [ ".git"; ".hg"; ".svn"; control_dir ]

exception Fail of string
let fail fmt = Printf.ksprintf (fun s -> raise (Fail s)) fmt

(* ---- lstat-based helpers (never follow a symlink implicitly) ---- *)
let lstat_opt p = try Some (Unix.lstat p) with Unix.Unix_error _ -> None
let kind_opt p = match lstat_opt p with Some st -> Some st.Unix.st_kind | None -> None
let is_real_dir p = kind_opt p = Some Unix.S_DIR
let is_symlink p = kind_opt p = Some Unix.S_LNK

let contains_sub hay needle =
  let hl = String.length hay and nl = String.length needle in
  if nl = 0 then true else
    let rec go i = i + nl <= hl && (String.sub hay i nl = needle || go (i + 1)) in go 0

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

let components rel =
  if not (Filename.is_relative rel) then fail "unsafe absolute path from image: %s" rel;
  let parts = String.split_on_char '/' rel in
  if parts = [] || List.exists (fun c -> c = "" || c = "." || c = ".." || String.contains c '\000') parts
  then fail "unsafe path from image: %s" rel;
  parts

let rec walk_real_dirs root f =
  Array.iter (fun name ->
    let p = Filename.concat root name in
    f p name;
    if is_real_dir p && not (List.mem name skip_dirs) then walk_real_dirs p f)
    (try Sys.readdir root with Sys_error _ -> [||])

let ensure_real_dir_parents root parts =
  let rec go cur = function
    | [] | [ _ ] -> ()
    | c :: rest ->
      let nxt = Filename.concat cur c in
      (match kind_opt nxt with
       | None -> Unix.mkdir nxt 0o755; go nxt rest
       | Some Unix.S_DIR -> go nxt rest
       | Some _ -> fail "a path component is not a real directory: %s" nxt)
  in go root parts

let () = Random.self_init ()

(* write [bytes] to a fresh O_CREAT|O_EXCL temp NEXT TO [target] (unique per target, never clobbers or
   follows an existing file/symlink; a name collision just retries) and return its path.  On a write
   failure the partial temp is removed so no un-owned residue leaks. *)
let stage_temp target bytes =
  let rec go tries =
    if tries <= 0 then fail "could not create a unique temp file next to %s" target;
    let tmp = target ^ tmp_infix ^ Printf.sprintf "%06x" (Random.int 0xffffff) in
    match (try Some (Unix.openfile tmp [ Unix.O_CREAT; Unix.O_EXCL; Unix.O_WRONLY ] 0o644)
           with Unix.Unix_error (Unix.EEXIST, _, _) -> None) with
    | None -> go (tries - 1)
    | Some fd ->
      let oc = Unix.out_channel_of_descr fd in
      (try output_string oc bytes; close_out oc
       with e -> (try close_out oc with _ -> ()); (try Unix.unlink tmp with _ -> ()); raise e);
      tmp
  in go 64

(* ---- the synchronization (algorithm §17) ---- *)
(* [unlink] is a PARAMETER (default the real Unix.unlink) so the standalone test driver can inject a
   cleanup failure through the real recovery algorithm — no ambient environment branch, no destructive
   behaviour, in the production call graph; the plugin always links the real operation. *)
let sync ?(unlink = Unix.unlink) root entries =
  let gen_header = match entries with (_, b) :: _ -> first_line_of b | [] -> "" in
  (* a Fido-owned REGULAR file: lstat S_REG (so a symlink is never followed) then header first line *)
  let is_owned_regular path =
    match lstat_opt path with
    | Some st when st.Unix.st_kind = Unix.S_REG -> first_line path = Some gen_header
    | _ -> false in
  let is_generated_go path = Filename.check_suffix path ".go" && is_owned_regular path in
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
  (* (A.2) exclusive lock — a git-style index.lock created ATOMICALLY with O_EXCL; a crashed run leaves
     it and the next run REFUSES (like git), rather than racing. *)
  let lock_path = Filename.concat ctrl lock_name in
  let lock_fd =
    try Unix.openfile lock_path [ Unix.O_CREAT; Unix.O_EXCL; Unix.O_WRONLY ] 0o644
    with Unix.Unix_error (Unix.EEXIST, _, _) ->
      fail "%s already exists — another Fido emission holds it, or a crashed run left it (remove it to proceed)" lock_path in
  let body =
    try
      (* (R) RECOVER owned stale temps FIRST — recover-all-or-REJECT before any synchronization effect.
         A temp is an owned regular file whose basename carries the temp infix; a foreign (non-header)
         file, a symlink, or a directory is preserved.  Aggregate failures; abort before staging. *)
      let rerr = ref [] in
      walk_real_dirs root (fun p name ->
        if contains_sub name tmp_infix && is_owned_regular p then
          (try unlink p with ex -> rerr := Printf.sprintf "%s: %s" p (Printexc.to_string ex) :: !rerr));
      (match !rerr with [] -> () | l ->
        fail "recovery FAILED (owned temp residue could not be removed): %s" (String.concat "; " l));
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
      (* (D) stage each target to an O_EXCL temp, then (E) install by atomic rename, rechecking ownership
         immediately before replacement (a foreign/type change since preflight aborts, leaving the temp for
         recovery). *)
      List.iter (fun (target, parts, bytes) ->
        ensure_real_dir_parents root parts;
        let tmp = stage_temp target bytes in
        (match lstat_opt target with
         | None -> ()
         | Some st when st.Unix.st_kind = Unix.S_REG && first_line target = Some gen_header -> ()
         | Some _ -> fail "ownership/type of %s changed under us — aborting" target);
        Sys.rename tmp target)
        targets;
      (* (F) stale cleanup: remove owned generated .go no longer desired, rechecking ownership *)
      List.iter (fun p -> if not (List.mem p desired) && is_generated_go p then unlink p) !existing_go;
      Ok (List.length targets)
    with e -> Error e in
  (* FINALIZE ONCE: release the lock — its sole obligation — fail-loud, aggregating close + unlink, and
     combining a body error with (never hiding it behind) a lock-release error. *)
  let lerr = ref [] in
  let add fmt = Printf.ksprintf (fun s -> lerr := s :: !lerr) fmt in
  (try Unix.close lock_fd with ex -> add "close lock fd: %s" (Printexc.to_string ex));
  (try Unix.unlink lock_path with ex -> add "unlink %s: %s" lock_path (Printexc.to_string ex));
  (match body, (match !lerr with [] -> None | l -> Some (String.concat "; " l)) with
   | Ok n, None -> n
   | Ok _, Some cm -> fail "installed the tree but releasing the lock FAILED: %s" cm
   | Error e, None -> raise e
   | Error e, Some cm ->
     let em = (match e with Fail m -> m | _ -> Printexc.to_string e) in
     raise (Fail (em ^ " — AND releasing the lock FAILED: " ^ cm)))
