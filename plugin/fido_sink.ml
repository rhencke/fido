(* fido_sink — the ONLY handwritten filesystem logic: a GENERIC ownership-aware dirty-directory
   synchronizer.  It receives an already-final directory image ((on-disk relative path * exact bytes)
   list, decoded from a proved-Rocq DirectoryImage whose provenance the vernac bridge typechecks) and
   makes a target tree's Fido-generated files EQUAL that image, preserving foreign files OUTSIDE the
   reserved control namespace.  It understands ONLY the filesystem — no program, no Go, no Rocq terms.

   VALIDATED ROOT + RESERVED NAMESPACE (both before ANY filesystem effect, since the sink is generic over
   raw strings and cannot trust the caller): (a) every proper ancestor of `root` must be an existing REAL
   directory — a symlink in ANY prefix component is rejected, because ordinary pathname resolution would
   otherwise follow it and redirect every subsequent effect (lstat only spares the FINAL component); and
   (b) `<root>/.fido/` is Fido-controlled, NOT part of the preserved foreign area — a desired path inside
   `.fido/` is rejected.  Foreign preservation is scoped to the tree OUTSIDE `.fido/`.

   TWO DISTINCT ownership authorities, for two distinct concerns:
   - INSTALLED `.go` (in the tree): a regular file is Fido-owned iff its first line is the exact generated
     header (DERIVED from the image bytes, never hardcoded).  Ownership is rechecked immediately before
     every overwrite/delete, via lstat (a symlink is S_LNK, never S_REG, so it is never followed).  A
     foreign `.go` forging the header is the accepted limit of this authority (a header is public).
   - TRANSIENT staging: the sink stages into `<root>/.fido/staging/`, a RESERVED location it alone manages;
     ownership there is a NAMESPACE POLICY (it rests on `.fido/` being reserved), not the location being
     unforgeable.

   STAGING: the sync loop stages each target and RENAMES it out before staging the next, so there is never
   more than ONE staging temp — a single fixed slot `.fido/staging/tmp`, no counter or allocator.  Each
   target's bytes go to that slot (O_CREAT|O_EXCL, fails closed if occupied), which is then atomically
   renamed into place; the preflight rejects a cross-filesystem target (a rename can't be atomic across
   devices).  RECOVERY runs FIRST, recover-all-or-REJECT and fail-CLOSED: staging must be empty or the ONE
   regular slot; any other basename, or a non-regular entry at the slot (directory, symlink, special file —
   a state the builder cannot create), is REFUSED, never traversed or deleted (so a nested tree or a mount
   is refused, not recursively removed), and any enumeration/lstat/removal error but a confirmed ENOENT
   aborts before any effect; it never scans the tree, so a foreign file (even one forging the header) is
   untouched.

   The FINALIZER's sole obligation is releasing the lock (close + unlink), fail-loud and once, combining a
   body error with a lock-release error (never hiding either).

   The fallible ops are PARAMETERS (`?unlink`/`?after_stage`, default real/no-op) so the test driver can
   inject a recovery failure or a mid-staging crash through the real algorithm — no ambient branch, no
   destructive default in the production call graph; the plugin always uses the defaults.

   HONEST GUARANTEE (threat model): a git-style index.lock coordinates COOPERATING Fido emitters.  Every
   pre-existing foreign entry OUTSIDE `.fido/` is preserved, WITH ONE ACCEPTED LIMIT: a `.go` forging the
   exact header is indistinguishable from a stale generated file, so it is overwritten (at a target) or
   deleted (when not desired) — the header is public and IS the ownership; likewise a `.fido/` forging the
   marker.  It is NOT a transactional whole-tree commit (a partial run may leave temps in `staging/`, which
   the next run removes).  NORMAL completion (success or a handled body failure, incl. a recovery failure)
   runs the finalizer and releases the lock, so an immediate rerun can proceed; a CRASH (process killed,
   finalizer not run) or a lock-release failure leaves the index.lock and the next run REFUSES until it is
   deliberately removed.  Like git's index.lock, and because this OCaml `Unix` exposes no
   openat/renameat/O_NOFOLLOW, it is NOT hardened against a concurrent NON-cooperating process racing
   symlink swaps between check and use; the intended single-emit-process use has no such adversary. *)

let control_dir  = ".fido"
let marker_name  = "marker"
let marker_bytes = "fido-control-directory.  do not edit.\n"
let lock_name    = "index.lock"       (* git-style: created O_EXCL, removed at end *)
let staging_name = "staging"          (* <root>/.fido/staging/ — the reserved staging namespace *)
let temp_name    = "tmp"              (* the ONE staging slot: <root>/.fido/staging/tmp *)
let skip_dirs    = [ ".git"; ".hg"; ".svn"; control_dir ]

exception Fail of string
let fail fmt = Printf.ksprintf (fun s -> raise (Fail s)) fmt

(* ---- lstat-based helpers (never follow a symlink implicitly) ---- *)
let lstat_opt p = try Some (Unix.lstat p) with Unix.Unix_error _ -> None
let kind_opt p = match lstat_opt p with Some st -> Some st.Unix.st_kind | None -> None
let is_real_dir p = kind_opt p = Some Unix.S_DIR
let is_symlink p = kind_opt p = Some Unix.S_LNK

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

(* validate that EVERY proper ancestor of [root] (from the filesystem root or cwd down to root's parent)
   is an existing REAL directory — reject a symlink or non-directory in ANY prefix component.  Otherwise
   ordinary pathname resolution follows a prefix symlink and redirects every subsequent effect into the
   referent tree (lstat only spares the FINAL component).  [root] itself may be absent (A.1 creates it);
   its parent chain must be real. *)
let validate_root_chain root =
  let rec chain p acc = let d = Filename.dirname p in if d = p then p :: acc else chain d (p :: acc) in
  let rec go = function
    | [] | [ _ ] -> ()                             (* the last element is root itself, checked by A.1 *)
    | a :: rest ->
      (match lstat_opt a with
       | Some st when st.Unix.st_kind = Unix.S_DIR -> go rest
       | Some _ -> fail "a component of the target root is a symlink or non-directory: %s" a
       | None -> fail "a parent directory of the target root does not exist: %s" a)
  in go (chain root [])

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

(* the device of the nearest EXISTING ancestor of a target (its eventual parent inherits that device); a
   later component created under it is on the same filesystem, so this decides whether an atomic rename
   into the target is possible.  All ancestors are real dirs (the preflight rejects a symlink in the path). *)
let ancestor_device root parts =
  let rec go cur = function
    | [] | [ _ ] -> (Unix.stat cur).Unix.st_dev
    | c :: rest ->
      let nxt = Filename.concat cur c in
      (match kind_opt nxt with Some Unix.S_DIR -> go nxt rest | _ -> (Unix.stat cur).Unix.st_dev)
  in go root parts

(* write [bytes] to THE staging slot (one fixed basename) and return its path.  The sync loop stages a
   target and renames it OUT before staging the next, so there is never more than one staging temp — no
   counter, no allocator.  O_CREAT|O_EXCL fails CLOSED if the slot is already occupied (recovery empties it
   first, so in normal operation it is not). *)
let stage_temp staging bytes =
  let tmp = Filename.concat staging temp_name in
  let fd = Unix.openfile tmp [ Unix.O_CREAT; Unix.O_EXCL; Unix.O_WRONLY ] 0o644 in
  let oc = Unix.out_channel_of_descr fd in
  (try output_string oc bytes; close_out oc with e -> (try close_out oc with _ -> ()); raise e);
  tmp

(* ---- the synchronization (algorithm §17) ---- *)
let sync ?(unlink = Unix.unlink) ?(after_stage = fun _ -> ()) ?(readdir = Sys.readdir) root entries =
  let gen_header = match entries with (_, b) :: _ -> first_line_of b | [] -> "" in
  let is_generated_go path =
    Filename.check_suffix path ".go"
    && (match lstat_opt path with Some st -> st.Unix.st_kind = Unix.S_REG | None -> false)
    && first_line path = Some gen_header in
  (* (A.-1) validate the ROOT's whole existing path chain (no prefix symlink may redirect effects) and
     (A.0) RESERVE the control namespace: refuse any desired path inside <root>/.fido (and reject unsafe
     ones).  BOTH run BEFORE any filesystem effect or recovery.  The plugin's FilePath excludes hidden
     components and its root is fixed, but the sink is generic over raw strings, so it enforces both itself
     — otherwise a prefix-symlinked root would redirect all effects, or a desired `.fido/staging/<x>` could
     be installed and then deleted by the next recovery. *)
  validate_root_chain root;
  List.iter (fun (rel, _) ->
    match components rel with
    | c :: _ when c = control_dir -> fail "refusing a desired path inside the reserved %s namespace: %s" control_dir rel
    | _ -> ())
    entries;
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
  (* (A.1b) the structured staging namespace, inside the marked control dir *)
  let staging = Filename.concat ctrl staging_name in
  (match kind_opt staging with
   | None -> Unix.mkdir staging 0o755
   | Some Unix.S_DIR -> ()
   | Some _ -> fail "%s exists and is not a directory — refusing to touch it" staging);
  (* (A.2) exclusive lock — a git-style index.lock created ATOMICALLY with O_EXCL; a crashed run leaves it
     and the next run REFUSES (like git), rather than racing. *)
  let lock_path = Filename.concat ctrl lock_name in
  let lock_fd =
    try Unix.openfile lock_path [ Unix.O_CREAT; Unix.O_EXCL; Unix.O_WRONLY ] 0o644
    with Unix.Unix_error (Unix.EEXIST, _, _) ->
      fail "%s already exists — another Fido emission holds it, or a crashed run left it (remove it to proceed)" lock_path in
  let body =
    try
      (* (R) RECOVER — staging holds AT MOST the ONE fixed slot (a regular file): the sync renames each
         staged file out before the next, so no other state is reachable.  Recovery is TWO-PHASE so that no
         effect precedes a rejection: it first validates the COMPLETE state (every entry must be the slot,
         absent or regular), then removes the slot only if validation fully passed — so a mixed state (the
         slot plus a foreign basename, in any order) is refused with NOTHING removed.  Any other basename or
         a non-regular entry at the slot (directory, symlink, special file — a state the builder cannot
         create) is REJECTED (fail-loud), never traversed or deleted, so a nested tree or a mount cannot be
         recursively removed.  Fail-CLOSED: enumeration / lstat / removal errors (other than a confirmed
         ENOENT) abort before any synchronization effect. *)
      let residue =
        try readdir staging               (* the enumeration order is an injectable seam (default Sys.readdir)
                                             so a test can force either order through the REAL two-phase path *)
        with ex -> fail "recovery FAILED: cannot enumerate %s: %s" staging (Printexc.to_string ex) in
      (* PHASE 1 — validate the COMPLETE staging state with NO effect: every entry must be the ONE slot,
         absent or a regular file; record whether the regular slot is present.  A forbidden basename or a
         non-regular slot aborts here, so a mixed state (e.g. the slot plus a foreign name, in any readdir
         order) is rejected BEFORE anything is removed. *)
      let slot_present = ref false in
      Array.iter (fun n ->
        let p = Filename.concat staging n in
        if n <> temp_name then
          fail "recovery FAILED: %s is not the Fido staging slot — refusing an impossible staging state" p;
        match (try Some (Unix.lstat p)
               with Unix.Unix_error (Unix.ENOENT, _, _) -> None            (* raced away: fine *)
                  | ex -> fail "recovery FAILED: cannot lstat %s: %s" p (Printexc.to_string ex)) with
        | None -> ()
        | Some s when s.Unix.st_kind = Unix.S_REG -> slot_present := true
        | Some _ -> fail "recovery FAILED: %s is not a regular file — refusing to remove a non-file staging entry" p)
        residue;
      (* PHASE 2 — validation passed: NOW remove the one slot (if present). *)
      if !slot_present then
        (let p = Filename.concat staging temp_name in
         try unlink p with ex -> fail "recovery FAILED: cannot remove %s: %s" p (Printexc.to_string ex));
      (* (B) desired set + existing generated .go files *)
      let targets = List.map (fun (rel, bytes) ->
        let parts = components rel in (Filename.concat root rel, parts, bytes)) entries in
      let desired = List.map (fun (t, _, _) -> t) targets in
      let existing_go = ref [] in
      walk_real_dirs root (fun p _ -> if is_generated_go p then existing_go := p :: !existing_go);
      (* (C) preflight every desired path (symlinks/foreign/cross-filesystem) BEFORE any change *)
      let staging_dev = (Unix.stat staging).Unix.st_dev in
      List.iter (fun (target, parts, _) ->
        let rec no_symlink cur = function
          | [] -> () | c :: rest ->
            let nxt = Filename.concat cur c in
            if is_symlink nxt then fail "refusing a symlink in path: %s" nxt else
            if kind_opt nxt = None then () else no_symlink nxt rest in
        no_symlink root parts;
        if ancestor_device root parts <> staging_dev then
          fail "%s is on a different filesystem than the staging area — atomic rename unsupported" target;
        (match lstat_opt target with
         | None -> ()
         | Some st when st.Unix.st_kind = Unix.S_REG && first_line target = Some gen_header -> ()
         | Some _ -> fail "refusing to overwrite a foreign entry: %s" target))
        targets;
      (* (D) stage each target through the ONE slot, then (E) install by atomic rename, rechecking ownership
         immediately before replacement (a foreign/type change since preflight aborts, leaving the slot in
         staging for recovery).  The rename empties the slot before the next target stages. *)
      List.iter (fun (target, parts, bytes) ->
        ensure_real_dir_parents root parts;
        let tmp = stage_temp staging bytes in
        after_stage tmp;
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
