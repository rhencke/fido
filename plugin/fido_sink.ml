(* fido_sink — the ONLY handwritten filesystem logic: a GENERIC ownership-aware dirty-directory
   synchronizer.  It receives an already-final directory image ((on-disk relative path * exact bytes)
   list, decoded from a proved-Rocq DirectoryImage whose provenance the vernac bridge typechecks) and
   makes a target tree's Fido-generated files EQUAL that image, preserving foreign files.  It understands
   ONLY the filesystem: it decodes no program, renders nothing, parses no Go, walks no Rocq terms.

   TWO DISTINCT ownership authorities, for two distinct concerns:
   - INSTALLED `.go`: a regular file in the tree is Fido-owned iff its first line is the exact generated
     header (DERIVED from the image bytes, never hardcoded).  Ownership is rechecked immediately before
     every overwrite/delete, via lstat (a symlink is S_LNK, never S_REG, so it is never followed).
   - TRANSIENT staging: everything inside the STRUCTURED namespace `<root>/.fido/staging/` is Fido-owned
     BY LOCATION — it lives inside the marked control dir, so it is ours whatever its bytes.  This is
     unforgeable (a foreign lookalike in the tree is never in our namespace) and ATOMIC (a partially
     written temp is already owned by being in `staging/`), so no crash prefix can orphan it.

   STAGING: each target's bytes are written to a fresh `<root>/.fido/staging/<seq>` created O_CREAT|O_EXCL,
   then atomically renamed into place.  Because a rename is atomic only within one filesystem, the
   preflight REJECTS (before any effect) a target whose nearest existing ancestor is on a different device
   than `staging/`.  RECOVERY runs FIRST and is recover-all-or-REJECT: it removes EVERY entry in
   `staging/` (all ours, by location) and is fail-CLOSED — any enumeration/lstat/removal error other than a
   confirmed ENOENT aborts before any synchronization effect.  It never scans the tree for temps, so a
   foreign file anywhere in the tree (even one forging the header) is untouched.  A temp left by a failed
   run stays in `staging/` and is removed by the next run's recovery.

   The FINALIZER's sole obligation is releasing the lock (close + unlink), fail-loud and once, combining a
   body error with a lock-release error (never hiding either).

   The fallible operations are PARAMETERS (`?unlink`, default the real Unix.unlink; `?after_stage`, default
   a no-op) so the standalone test driver can inject a recovery failure or an in-real-staging abort through
   the real algorithm — no ambient environment branch, no destructive behaviour, in the production call
   graph; the plugin always uses the defaults.

   HONEST GUARANTEE (threat model): a git-style index.lock coordinates COOPERATING Fido emitters, and every
   PRE-EXISTING foreign entry (file/dir/symlink) is preserved.  It is NOT a transactional whole-tree commit
   (a partial run may install some targets and leave owned temps in `staging/`, which the next run removes).
   NORMAL completion — success or a handled body failure (including a recovery failure) — runs the finalizer
   and releases the lock, so an immediate rerun can proceed; but a CRASH (the process killed, finalizer not
   run) or a failure of the lock release itself leaves the index.lock, and the next run REFUSES until it is
   deliberately removed.  Like git's index.lock, and because this OCaml `Unix` exposes no
   openat/renameat/O_NOFOLLOW, it is NOT hardened against a concurrent NON-cooperating process racing
   symlink swaps between check and use; the intended use (a single emit process writing a build tree) has
   no such adversary. *)

let control_dir  = ".fido"
let marker_name  = "marker"
let marker_bytes = "fido-control-directory.  do not edit.\n"
let lock_name    = "index.lock"       (* git-style: created O_EXCL, removed at end *)
let staging_name = "staging"          (* <root>/.fido/staging/ — the structured owned staging namespace *)
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

(* remove a staging entry (owned by LOCATION).  Fail-CLOSED: only a confirmed ENOENT means "already gone";
   any other lstat / readdir / removal error propagates so recovery aborts.  A symlink is unlinked (never
   followed); a directory is removed recursively (staging normally holds flat regular files). *)
let rec remove_staged unlink p =
  match (try Some (Unix.lstat p) with Unix.Unix_error (Unix.ENOENT, _, _) -> None) with
  | None -> ()
  | Some st ->
    if st.Unix.st_kind = Unix.S_DIR then begin
      Array.iter (fun n -> remove_staged unlink (Filename.concat p n)) (Sys.readdir p);
      Unix.rmdir p
    end else unlink p

let () = Random.self_init ()

(* write [bytes] to a fresh O_CREAT|O_EXCL temp inside the owned staging dir and return its path.  A
   collision (the sequence is fresh after recovery empties staging, so only a race) just advances. *)
let stage_temp staging seq bytes =
  let rec go tries =
    if tries <= 0 then fail "could not create a unique staging temp in %s" staging;
    let tmp = Filename.concat staging (string_of_int !seq) in incr seq;
    match (try Some (Unix.openfile tmp [ Unix.O_CREAT; Unix.O_EXCL; Unix.O_WRONLY ] 0o644)
           with Unix.Unix_error (Unix.EEXIST, _, _) -> None) with
    | None -> go (tries - 1)
    | Some fd ->
      let oc = Unix.out_channel_of_descr fd in
      (try output_string oc bytes; close_out oc with e -> (try close_out oc with _ -> ()); raise e);
      tmp
  in go 64

(* ---- the synchronization (algorithm §17) ---- *)
let sync ?(unlink = Unix.unlink) ?(after_stage = fun _ -> ()) root entries =
  let gen_header = match entries with (_, b) :: _ -> first_line_of b | [] -> "" in
  let is_generated_go path =
    Filename.check_suffix path ".go"
    && (match lstat_opt path with Some st -> st.Unix.st_kind = Unix.S_REG | None -> false)
    && first_line path = Some gen_header in
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
      (* (R) RECOVER — empty the staging namespace (every entry is ours, by location, whatever its bytes),
         fail-CLOSED before any synchronization effect: enumeration or removal errors abort. *)
      let residue =
        try Sys.readdir staging
        with ex -> fail "recovery FAILED: cannot enumerate %s: %s" staging (Printexc.to_string ex) in
      Array.iter (fun n ->
        let p = Filename.concat staging n in
        try remove_staged unlink p
        with ex -> fail "recovery FAILED: cannot remove staging residue %s: %s" p (Printexc.to_string ex))
        residue;
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
      (* (D) stage each target into the owned namespace, then (E) install by atomic rename, rechecking
         ownership immediately before replacement (a foreign/type change since preflight aborts, leaving
         the temp in staging for recovery). *)
      let seq = ref 0 in
      List.iter (fun (target, parts, bytes) ->
        ensure_real_dir_parents root parts;
        let tmp = stage_temp staging seq bytes in
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
