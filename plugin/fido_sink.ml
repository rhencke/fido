(* fido_sink — the ONLY handwritten filesystem logic: a small, auditable, ownership-aware dirty-directory
   synchronizer.  It receives an already-final directory image — the exact root [go.mod] bytes plus an
   ((on-disk relative .go path * exact bytes) list), decoded from a proved-Rocq DirectoryImage whose
   provenance the vernac bridge typechecks — and makes a target tree's Fido-generated module EQUAL that
   image, while REFUSING to run in the presence of any foreign Go/module input or nested control name.  It
   understands ONLY the filesystem — no program, no Go, no Rocq terms.

   OWNERSHIP + FOREIGN REJECTION.  Installed `.go` files and the root `go.mod` are Fido-owned iff their
   first line is the exact generated header (DERIVED from the go.mod bytes) AND they are regular non-symlink
   files — RE-checked immediately before every overwrite/delete.  A foreign `.go` (anywhere in the
   Go-DISCOVERED namespace — the traversal skips the opaque dot/underscore/testdata/vendor directory trees
   `go build ./...` itself ignores, so it neither inspects nor rejects because of anything beneath them), a
   foreign/nested `go.mod`, or a nested `.fido` REJECTS the whole emission before any generated-file
   mutation; foreign NON-Go files, and everything under the skipped opaque trees, are preserved untouched.

   SIBLING-TEMP STAGING (no records, no nonce, no stage directory, no parser).  `<root>/.fido/` holds the
   exact marker and, during an active run or after a crash, one git-style O_EXCL `index.lock` — nothing else.
   Each final output is staged into its RESERVED sibling temporary `<final>.fido-tmp-v1`; because the lock
   serializes cooperating emitters, the name needs no nonce and recovery needs no record — the final path is
   already known to the live sync.  Since temp and target are SIBLINGS, install is an atomic same-device
   rename (nested mounts inside root work; EXDEV fails loud, no copy).  A regular non-symlink file whose
   basename ends in `.fido-tmp-v1` is, by PUBLIC (and forgeable) CONVENTION, an abandoned Fido temp ONLY IF
   its suffix-stripped path maps to a Fido FINAL path (the root `go.mod` or an intrinsic FilePath `.go`); a
   non-mappable suffixed entry, or a symlink/directory/special with that suffix, is NOT owned (refuse +
   preserve).  Forgeability of the mapped suffix is an accepted tradeoff under the single-owner /
   cooperating-process threat model — no transaction log is built to avoid it.

   TWO-PHASE, FAIL-CLOSED.  After acquiring the lock: PHASE 1 inspects the whole Go-discovered namespace once (validating
   foreign-Go/module/control rules and COLLECTING every VALID abandoned temp — a regular reserved-suffix file
   whose suffix-stripped path maps to a Fido final path) and deletes nothing; only a confirmed ENOENT is
   "missing" — every other fs error aborts and preserves.  If any path is invalid or uninspectable the run
   rejects before any mutation.  PHASE 2 deletes each collected temp after re-lstat (must still be a regular
   reserved-suffix file mapping to a final path).  Then the complete image stages into sibling temps before
   any install; each final installs by rename; stale owned `.go` is removed.  Binding order: validate the
   root chain and reject a reserved-namespace desired path BEFORE any effect; ensure/roll-back .fido; lock;
   inspect; delete abandoned temps; preflight; stage complete; install by rename; remove stale; release.

   HONEST GUARANTEE (Linux/amd64 scope).  GoProgram acceptance, SafeProgram certification, and DirectoryImage
   creation are semantically all-or-nothing.  Dirty-directory installation is locked for cooperating
   emitters, rejects foreign Go/module inputs and nested `.fido` in the Go-discovered namespace (skipping the
   opaque dot/underscore/testdata/vendor trees `go build ./...` ignores), inspects that namespace fail-closed,
   stages the complete image into reserved sibling temporary files before installation, uses per-file rename
   in the ordinary same-filesystem case, cleans handled-failure temps immediately, removes validated
   abandoned suffix-owned temps (whose suffix-stripped path maps to a Fido final path) on a later run, and
   converges when the directory namespace remains stable.
   It is NOT a portable transactional multi-file filesystem commit, NOT hardened against malicious concurrent
   mutation, and does NOT model arbitrary unmount/remount/backing-store replacement between runs.

   Fallible/nondeterministic ops are PARAMETERS (checkpoint/unlink/rename/before_install/before_write/
   before_delete) so the driver injects faults through the REAL algorithm; the plugin always uses defaults. *)

(* C1A §11: identity-keyed / membership-only collections use the OCaml runtime's mature [Map]/[Set] — the
   sink authors no hash/tree.  [SMap] keys the desired outputs by their relative path (rejecting a duplicate
   before any effect; [bindings] gives a canonical path-sorted iteration independent of transport order);
   [SSet] holds the unordered-unique desired-target set (stale-file membership) and abandoned-temp set.
   Lists remain ONLY where order is meaningful (the [created_dirs]/[created_temps] rollback stacks). *)
module SMap = Map.Make (String)
module SSet = Set.Make (String)

let control_dir  = ".fido"
let marker_name  = "marker"
let marker_bytes = "fido-control-directory.  do not edit.\n"
let lock_name    = "index.lock"                (* git-style: created O_EXCL, removed at end *)
let gomod_name   = "go.mod"
let temp_suffix  = ".fido-tmp-v1"              (* reserved sibling temp; the lock serializes, so no nonce *)

exception Fail of string
let fail fmt = Printf.ksprintf (fun s -> raise (Fail s)) fmt

(* ---- fail-closed filesystem observation: only a confirmed ENOENT is "missing" ---- *)
type obs = Missing | Present of Unix.stats
let lstat_obs p =
  try Present (Unix.lstat p)
  with Unix.Unix_error (Unix.ENOENT, _, _) -> Missing
     | Unix.Unix_error (e, _, _) -> fail "cannot lstat %s: %s" p (Unix.error_message e)

let ends_with suf s =
  let ls = String.length s and lf = String.length suf in
  ls >= lf && String.sub s (ls - lf) lf = suf

(* first line of a regular file, FAIL-CLOSED (a read error is never "no header"). *)
let read_first_line p =
  let ic = try open_in_bin p with Sys_error m -> fail "cannot open %s: %s" p m in
  (try let l = (try input_line ic with End_of_file -> "") in close_in ic; l
   with Sys_error m -> close_in_noerr ic; fail "cannot read %s: %s" p m)

let read_whole p =
  let ic = try open_in_bin p with Sys_error m -> fail "cannot open %s: %s" p m in
  (try let n = in_channel_length ic in let s = really_input_string ic n in close_in ic; s
   with Sys_error m -> close_in_noerr ic; fail "cannot read %s: %s" p m)

let first_line_of_string s =
  match String.index_opt s '\n' with Some i -> String.sub s 0 i | None -> s

(* a path is a Fido-owned regular file with the exact header first line (rechecked before every mutation). *)
let owned_regular p header = match lstat_obs p with
  | Present st -> st.Unix.st_kind = Unix.S_REG && read_first_line p = header
  | Missing -> false

let write_all fd bytes =
  let len = String.length bytes in
  let rec loop off =
    if off < len then
      let w = Unix.write_substring fd bytes off (len - off) in
      if w <= 0 then fail "short write" else loop (off + w) in
  loop 0

(* create a NEW file exclusively and write it completely (fails closed if the path is occupied); a
   descriptor-close error on the failure path is surfaced, not swallowed. *)
let write_new p bytes =
  let fd = try Unix.openfile p [Unix.O_CREAT; Unix.O_EXCL; Unix.O_WRONLY] 0o644
           with Unix.Unix_error (e, _, _) -> fail "cannot create %s: %s" p (Unix.error_message e) in
  (try write_all fd bytes; Unix.close fd
   with e ->
     let close_msg = (try Unix.close fd; None with Unix.Unix_error (ce,_,_) -> Some (Unix.error_message ce)) in
     let base = match e with Fail m -> m | _ -> Printexc.to_string e in
     fail "cannot write %s: %s%s" p base (match close_msg with Some c -> " | fd close failed: " ^ c | None -> ""))

(* ---- the formal output domain: the sink's defensive path validator accepts EXACTLY the canonical strings
   emitted from the intrinsic [FilePath] for a `.go` file (it does not broaden the domain, and it faithfully
   MIRRORS `FilePath.path_ok` — a weaker check would let a noncanonical path, a `go build`-ignored dir, or a
   nested control name through, and `ensure_dir_chain` would then materialize it).  Kept in exact
   correspondence with `FilePath.v`: `is_lower`/`is_lower_digit`/`component_ok`/`reserved_dir`/
   `dir_component_ok`/`filename_ok`/`path_ok`. ---- *)
let is_lower c = c >= 'a' && c <= 'z'
let is_lower_digit c = (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9')
let component_ok s =
  String.length s > 0 && is_lower s.[0]
  && (let ok = ref true in String.iteri (fun i c -> if i > 0 && not (is_lower_digit c) then ok := false) s; !ok)
let reserved_dir s = s = "testdata" || s = "vendor"            (* dirs `go build ./...` IGNORES *)
let dir_component_ok s = component_ok s && not (reserved_dir s)
let filename_ok s =
  let n = String.length s in
  n >= 3 && String.sub s (n - 3) 3 = ".go" && component_ok (String.sub s 0 (n - 3))
(* the whole `.go` path: ARBITRARY LENGTH (no cap — mirrors `FilePath.path_ok`, which has none; a numeric
   bound is not a correctness invariant); every directory component admissible and not `go build`-ignored;
   the last segment an admissible `.go` filename.  A leading dot (`.fido`), `..`, `_`, upper-case, `vendor`/
   `testdata`, a NUL, an empty/absolute/repeated-slash segment, or a non-`.go` basename all FAIL here. *)
let filepath_ok rel =
  match List.rev (String.split_on_char '/' rel) with
  | last :: rdirs -> List.for_all dir_component_ok rdirs && filename_ok last
  | [] -> false

let split_parent parts =
  match List.rev parts with
  | base :: rrest -> (String.concat "/" (List.rev rrest), base)
  | [] -> fail "empty path"

(* validate that EVERY proper ancestor of [root] is an existing REAL directory — reject a symlink or
   non-directory in ANY prefix component (ordinary resolution would otherwise follow it and redirect every
   effect into the referent; lstat only spares the FINAL component). *)
let validate_root_chain root =
  let rec chain p acc = let d = Filename.dirname p in if d = p then p :: acc else chain d (p :: acc) in
  let rec go = function
    | [] | [ _ ] -> ()
    | a :: rest ->
      (match lstat_obs a with
       | Present st when st.Unix.st_kind = Unix.S_DIR -> go rest
       | Present _ -> fail "a component of the target root is a symlink or non-directory: %s" a
       | Missing -> fail "a parent directory of the target root does not exist: %s" a)
  in go (chain root [])

let ensure_dir_chain root parent_rel created =
  if parent_rel = "" then ()
  else
    let cur = ref root in
    List.iter (fun c ->
      cur := Filename.concat !cur c;
      match lstat_obs !cur with
      | Present st -> if st.Unix.st_kind <> Unix.S_DIR then fail "%s is not a directory" !cur
      | Missing ->
        (try Unix.mkdir !cur 0o755
         with Unix.Unix_error (e,_,_) -> fail "cannot create directory %s: %s" !cur (Unix.error_message e));
        created := !cur :: !created)
      (String.split_on_char '/' parent_rel)

(* ---- the Go-discovered namespace: `go build ./...` IGNORES a directory (and a file) whose basename begins
   with `.` or `_`, and the directories `testdata`/`vendor`.  Those trees — `.git`/`.hg`/`.svn`, editor
   caches, underscore-private dirs, Go-ignored testdata/vendor — are OPAQUE foreign non-Go state: the sink
   neither recurses into, inspects, classifies, cleans, nor rejects because of anything beneath them (this is
   what keeps Fido out of `.git`).  It does NOT over-skip an ordinary visible directory merely because its
   name is outside Fido's narrow generated grammar (an uppercase/hyphenated foreign dir may still hold Go
   input `go build ./...` discovers).  The control name `.fido` is handled separately by the caller (root =
   control, nested = error), BEFORE this test. ---- *)
let go_ignored_name name = name <> "" && (name.[0] = '.' || name.[0] = '_')
let go_ignored_dir name = go_ignored_name name || name = "testdata" || name = "vendor"

(* a reserved-suffix regular file is Fido-owned as an abandoned temp ONLY if removing the suffix yields a
   path Fido could actually have STAGED: exactly the root `go.mod`, or a `.go` path in the intrinsic FilePath
   output domain (the SAME [filepath_ok]).  A suffix entry that maps to neither is NOT Fido state — it is
   preserved and makes the run refuse clearly rather than being silently adopted or deleted. *)
let temp_maps_to_final final = final = gomod_name || filepath_ok final

(* ---- PHASE 1: ONE fail-closed inspection of the Go-discovered namespace.  Validate foreign-Go/module/
   control rules and COLLECT (never delete) every VALID abandoned Fido temp; any invalid/uninspectable path
   rejects the whole run before any generated-file mutation.  Opaque Go-ignored trees are not entered. ---- *)
let rec inspect root header rel temps =
  let dir = if rel = "" then root else Filename.concat root rel in
  let names =
    try Sys.readdir dir
    with Sys_error m -> fail "cannot inspect %s: %s — refusing without a complete tree scan" dir m in
  Array.iter (fun name ->
    let child_rel = if rel = "" then name else rel ^ "/" ^ name in
    let p = Filename.concat dir name in
    if name = control_dir then
      (* the EXACT root .fido is the owned control dir (validated separately by [ensure_root_and_control],
         not descended); a NESTED .fido in the traversed namespace is an error of any filesystem type *)
      (if rel <> "" then fail "a nested %s control name is present (%s) — refusing" control_dir child_rel)
    else match lstat_obs p with
      | Missing -> ()
      | Present st ->
        let k = st.Unix.st_kind in
        if k = Unix.S_DIR && go_ignored_dir name then ()
          (* an OPAQUE Go-ignored DIRECTORY tree (.git/dot/underscore/testdata/vendor): never entered,
             classified, or rejected — this keeps Fido out of `.git`.  Checked FIRST so a Go-ignored directory
             whose name ALSO ends in the reserved suffix (`.cache.fido-tmp-v1`/`_x.fido-tmp-v1`) or `.go` is
             skipped, not rejected.  (Only DIRECTORY TREES are opaque — a dot/underscore FILE in the traversed
             namespace is still classified below.) *)
        else if ends_with temp_suffix name then begin
          (* a reserved-suffix entry IN THE TRAVERSED NAMESPACE (an ignored dir TREE was already skipped above,
             so anything here is NOT beneath a skipped directory) — classified BEFORE the dot/underscore-name
             skip below, so a non-mappable dot/underscore file/symlink/special (e.g. root `_notes.fido-tmp-v1`)
             still REFUSES fail-closed.  Owned (collected) only as a REGULAR file whose suffix-stripped path is
             a possible Fido final path; Fido's own final paths are never dot/underscore, so a dot/underscore
             suffix entry is never mappable → refuses. *)
          let final = String.sub child_rel 0 (String.length child_rel - String.length temp_suffix) in
          if not (temp_maps_to_final final) then
            fail "a reserved-suffix entry %s does not map to a Fido final path (root go.mod or an intrinsic FilePath .go) — refusing (preserved)" child_rel
          else if k = Unix.S_REG then temps := SSet.add p !temps
          else fail "a reserved-suffix entry %s is a symlink/directory/special, not a regular temp — refusing" child_rel
        end
        else if name = gomod_name then
          (* a `go.mod` of ANY filesystem kind (regular/dir/symlink/special) is classified BEFORE generic
             directory recursion — otherwise a DIRECTORY named `go.mod` would be traversed instead of rejected:
             a nested one rejects; a root one must be a regular Fido-headed file. *)
          (if rel <> "" then fail "a nested go.mod is present (%s) — refusing" child_rel
           else if not (k = Unix.S_REG && read_first_line p = header)
           then fail "a foreign root go.mod is present — refusing to touch it")
        else if ends_with ".go" name && not (go_ignored_name name) then
          (* a VISIBLE `*.go` of ANY filesystem kind is classified BEFORE recursion — otherwise a DIRECTORY
             named `foreign.go` would be traversed instead of rejected: it must be a regular Fido-headed file,
             else it is foreign (a `.go` DIRECTORY / symlink / special all reject here).  A dot/underscore `.go`
             file is Go-ignored and falls through to the skip below. *)
          (if not (k = Unix.S_REG && read_first_line p = header)
           then fail "a foreign .go file is present (%s) — refusing" child_rel)
        else if go_ignored_name name then ()
          (* a remaining Go-ignored dot/underscore NON-directory name that is NOT a reserved-suffix / go.mod /
             `.go` (e.g. `.gitignore`, a dot/underscore `.go` file): `go build ./...` ignores it, so it is
             opaque foreign state — preserved. *)
        else if k = Unix.S_DIR then inspect root header child_rel temps
          (* a visible directory NOT named `go.mod` or `*.go`: recurse into the Go-discovered namespace *)
        (* other foreign non-Go files/symlinks/specials: preserved *))
    names

(* ---- PHASE 2: after the COMPLETE scan succeeds, delete each validated abandoned temp (re-lstat: still a
   regular non-symlink reserved-suffix file); fail loud on any mismatch or deletion error. ---- *)
let delete_temps unlink temps =
  SSet.iter (fun p ->
    match lstat_obs p with
    | Present st when st.Unix.st_kind = Unix.S_REG && ends_with temp_suffix p ->
        (try unlink p with Unix.Unix_error (e,_,_) -> fail "cannot remove abandoned temp %s: %s" p (Unix.error_message e))
    | Present _ -> fail "abandoned temp %s changed type before removal — refusing" p
    | Missing -> fail "abandoned temp %s vanished before removal — refusing" p)
    temps

(* ---- remove stale Fido-owned .go NOT in the desired set (ownership RE-checked immediately before delete),
   over the SAME Go-discovered namespace: opaque Go-ignored trees (.git/dot/underscore/testdata/vendor) and
   Go-ignored `.go` files are never entered or touched. ---- *)
let rec remove_stale_go unlink before_delete root header desired rel =
  let dir = if rel = "" then root else Filename.concat root rel in
  let names =
    try Sys.readdir dir
    with Sys_error m -> fail "cannot scan %s for stale generated files: %s" dir m in
  Array.iter (fun name ->
    begin
      let child_rel = if rel = "" then name else rel ^ "/" ^ name in
      let p = Filename.concat dir name in
      match lstat_obs p with
      | Missing -> ()
      | Present st ->
        if st.Unix.st_kind = Unix.S_DIR then
          (if go_ignored_dir name then () else remove_stale_go unlink before_delete root header desired child_rel)
        else if ends_with ".go" name && not (go_ignored_name name) && st.Unix.st_kind = Unix.S_REG
                && read_first_line p = header && not (SSet.mem p desired)
        then begin
          before_delete p;                          (* test seam: a race can mutate p here *)
          (* recheck ownership IMMEDIATELY before delete and ABORT fail-closed on ANY mismatch/error (the
             target became missing, nonregular, symlinked, unreadable, or no longer Fido-headed) — never
             delete a file that is no longer provably ours; preserve it. *)
          if owned_regular p header then
            (try unlink p
             with Unix.Unix_error (e,_,_) -> fail "cannot remove stale generated %s: %s" p (Unix.error_message e))
          else fail "stale generated %s changed and is no longer Fido-owned — refusing to touch it" p
        end
    end)
    names

(* ---- root + the owned control directory: <root>/.fido/ = exact marker (+ optional lock), nothing else ---- *)
let ensure_root_and_control root control_abs =
  (match lstat_obs root with
   | Present st -> if st.Unix.st_kind <> Unix.S_DIR then fail "target root is not a real directory: %s" root
   | Missing -> (try Unix.mkdir root 0o755
                 with Unix.Unix_error (e,_,_) -> fail "cannot create root %s: %s" root (Unix.error_message e)));
  match lstat_obs control_abs with
  | Missing ->
    (* FIRST-TIME: create the control dir + marker.  If the marker fails, ROLL BACK exactly what this
       invocation created so a partial .fido never strands the target (the next run starts fresh). *)
    (try Unix.mkdir control_abs 0o755
     with Unix.Unix_error (e,_,_) -> fail "cannot create %s: %s" control_abs (Unix.error_message e));
    let mk = Filename.concat control_abs marker_name in
    (try write_new mk marker_bytes
     with e ->
       let base = match e with Fail m -> m | _ -> Printexc.to_string e in
       let errs = ref [] in
       let step what f =
         match (try f (); None with Fail m -> Some m | Unix.Unix_error (er,_,_) -> Some (Unix.error_message er) | ex -> Some (Printexc.to_string ex)) with
         | None -> () | Some m -> errs := (what ^ ": " ^ m) :: !errs in
       step "marker" (fun () -> match lstat_obs mk with Present _ -> Unix.unlink mk | Missing -> ());
       step "control dir" (fun () -> Unix.rmdir control_abs);
       (match !errs with
        | [] -> fail "first-time %s init failed and was rolled back: %s" control_abs base
        | es -> fail "first-time %s init failed: %s | rollback also failed: %s" control_abs base (String.concat "; " (List.rev es))))
  | Present st ->
    (* EXISTING: an owned .fido must be exactly the marker (+ optional transient lock); any other entry, a
       wrong/absent marker, or a non-directory rejects WITHOUT modification. *)
    if st.Unix.st_kind <> Unix.S_DIR then fail "%s exists but is not a directory — refusing" control_abs;
    let mk = Filename.concat control_abs marker_name in
    (match lstat_obs mk with
     | Present mst when mst.Unix.st_kind = Unix.S_REG && read_whole mk = marker_bytes -> ()
     | _ -> fail "%s exists without the exact Fido control marker — refusing to touch it" control_abs);
    let names = try Sys.readdir control_abs
                with Sys_error m -> fail "cannot inspect %s: %s — refusing" control_abs m in
    Array.iter (fun n ->
      if not (n = marker_name || n = lock_name)
      then fail "%s contains an unexpected entry %s — refusing to touch it" control_abs n)
      names

(* ============================================================================================================
   PRISTINE MATERIALIZE — the AUTHORITATIVE pre-publication image write.  It writes the EXACT decoded
   DirectoryImage (go.mod bytes + (relative .go path, bytes) entries) into a FRESH, EMPTY target directory,
   with NO `.fido` control state, NO foreign-input rejection, and NO sibling-temp staging: the target is a
   DISPOSABLE build-VALIDATION root created fresh for exactly this one image, NEVER a user directory.  The
   pinned `go build ./...` validates THESE bytes, and the canonical committed artifact is copied from THIS
   materialization — never from a sink/published directory.  [sync] publishes the SAME image bytes to a real
   destination only AFTER this has build-validated (validation-before-publication).  Fresh + empty + O_EXCL is
   fail-closed: a duplicate transport path, an occupied name, or a pre-existing non-empty root all FAIL rather
   than overwrite. *)
let materialize dir go_mod entries =
  validate_root_chain dir;
  (match lstat_obs dir with
   | Missing ->
       (try Unix.mkdir dir 0o755
        with Unix.Unix_error (e,_,_) -> fail "cannot create materialization root %s: %s" dir (Unix.error_message e))
   | Present st when st.Unix.st_kind = Unix.S_DIR ->
       (match (try Sys.readdir dir with Sys_error m -> fail "cannot read %s: %s" dir m) with
        | [||] -> ()
        | _ -> fail "materialization root %s is not empty — refusing (a FRESH disposable build-validation root is required)" dir)
   | Present _ -> fail "materialization root %s exists and is not a directory" dir);
  write_new (Filename.concat dir gomod_name) go_mod;
  List.iter (fun (rel, bytes) ->
    let (parent_rel, _base) = split_parent (String.split_on_char '/' rel) in
    ensure_dir_chain dir parent_rel (ref []);
    write_new (Filename.concat dir rel) bytes) entries;
  1 + List.length entries

let sync ?(checkpoint = fun _ -> ()) ?(unlink = Unix.unlink) ?(rename = Unix.rename)
         ?(before_install = fun _ -> ()) ?(before_write = fun _ -> ()) ?(before_delete = fun _ -> ())
         dir go_mod entries =
  let header = first_line_of_string go_mod in
  let control_abs = Filename.concat dir control_dir in
  let lock_abs    = Filename.concat control_abs lock_name in
  (* A. validate the root chain (prefix symlinks) — before any effect *)
  validate_root_chain dir;
  (* B. compute the desired outputs (go.mod at root + every .go); [filepath_ok] enforces the EXACT intrinsic
        FilePath `.go` domain (lowercase canonical components, no `.fido`/`..`/`_`/upper, no `vendor`/
        `testdata` dir, `.go` basename, arbitrary length) — so a noncanonical path or a nested control name is
        rejected BEFORE any effect and can never be materialized by [ensure_dir_chain] *)
  (* immediately validate the transport entries into a desired-output MAP keyed by relative path — REJECTING
     a duplicate relative path BEFORE any filesystem effect (a standard map's [add] would silently overwrite),
     and deriving a CANONICAL path-sorted iteration ([SMap.bindings]) that does NOT depend on transport order:
     permuted entries produce the same map and hence the same final directory (C1A §11.1).  The transport list
     itself stays a list — it is a certified enumeration, not the identity/membership authority. *)
  let desired_map =
    let add m rel v =
      if SMap.mem rel m then fail "refusing a duplicate output path: %s" rel;
      SMap.add rel v m in
    let m0 = add SMap.empty gomod_name (Filename.concat dir gomod_name, "", gomod_name, go_mod) in
    List.fold_left (fun m (rel, bytes) ->
      if not (filepath_ok rel) then fail "refusing a path outside the intrinsic FilePath `.go` domain: %s" rel;
      let (parent_rel, base) = split_parent (String.split_on_char '/' rel) in
      add m rel (Filename.concat dir rel, parent_rel, base, bytes)) m0 entries in
  let desired = List.map snd (SMap.bindings desired_map) in
  (* the unordered-unique set of desired TARGET paths — for O(log n) stale-file membership (not List.mem). *)
  let desired_targets = List.fold_left (fun s (t,_,_,_) -> SSet.add t s) SSet.empty desired in
  (* C. ensure root + the owned control directory (marker only — NO records/stage dirs) *)
  ensure_root_and_control dir control_abs;
  (* D. acquire the emission lock (git-style O_EXCL) *)
  let lockfd =
    try Unix.openfile lock_abs [Unix.O_CREAT; Unix.O_EXCL; Unix.O_WRONLY] 0o644
    with Unix.Unix_error (Unix.EEXIST, _, _) ->
           fail "%s already exists — another Fido emission holds it, or a crashed run left it (remove it to proceed)" lock_abs
       | Unix.Unix_error (e, _, _) -> fail "cannot create lock %s: %s" lock_abs (Unix.error_message e) in
  let created_dirs = ref [] and created_temps = ref [] in
  let temp_of (target,_,_,_) = target ^ temp_suffix in
  let body () =
    (* E. PHASE 1 — inspect the Go-discovered namespace fail-closed, collecting VALID mapped abandoned temps
          into an unordered-unique SET (no deletion) *)
    let temps = ref SSet.empty in
    inspect dir header "" temps;
    (* F. PHASE 2 — delete the validated abandoned temps *)
    delete_temps unlink !temps;
    (* G. preflight the complete desired image: every final target absent or Fido-owned, every sibling temp
          path absent after recovery, and every needed parent directory created (recorded for cleanup) *)
    List.iter (fun ((target, parent_rel, _, _) as d) ->
      (match lstat_obs target with
       | Missing -> ()
       | Present _ -> if not (owned_regular target header)
                      then fail "%s exists and is not Fido-owned — refusing to overwrite" target);
      (match lstat_obs (temp_of d) with
       | Missing -> ()
       | Present _ -> fail "the sibling temp path %s is occupied after recovery — refusing" (temp_of d));
      ensure_dir_chain dir parent_rel created_dirs) desired;
    (* H. STAGE the complete image into sibling temps BEFORE any install.  Create each temp EXCLUSIVELY, then
          REGISTER it for cleanup IMMEDIATELY (before writing), so an ENOSPC/short-write/close failure OR a
          crash after creation leaves a temp the handled-failure path still removes. *)
    List.iteri (fun i ((_, _, _, bytes) as d) ->
      let tp = temp_of d in
      before_write tp;                               (* test seam: a later-stage failure can fire here *)
      let fd = try Unix.openfile tp [Unix.O_CREAT; Unix.O_EXCL; Unix.O_WRONLY] 0o644
               with Unix.Unix_error (e, _, _) -> fail "cannot create %s: %s" tp (Unix.error_message e) in
      created_temps := tp :: !created_temps;         (* registered the instant it exists on disk *)
      checkpoint "after-create";                     (* a crash here leaves a created-but-empty (partial) temp *)
      (try write_all fd bytes; Unix.close fd
       with e ->
         let close_msg = (try Unix.close fd; None with Unix.Unix_error (ce,_,_) -> Some (Unix.error_message ce)) in
         let base = match e with Fail m -> m | _ -> Printexc.to_string e in
         fail "cannot write %s: %s%s" tp base (match close_msg with Some c -> " | fd close failed: " ^ c | None -> ""));
      if i = 0 then checkpoint "after-first-payload") desired;
    checkpoint "after-staging";
    (* I. install each file by SIBLING RENAME: recheck ownership immediately before overwrite, then rename
          (sibling; atomic; EXDEV fails loud with NO copy fallback) *)
    List.iteri (fun i ((target, _, _, _) as d) ->
      before_install target;                         (* test seam: a race can mutate the target here *)
      (match lstat_obs target with
       | Missing -> ()
       | Present _ -> if not (owned_regular target header)
                      then fail "%s changed and is no longer Fido-owned — refusing to overwrite" target);
      let tp = temp_of d in
      (try rename tp target
       with Unix.Unix_error (Unix.EXDEV, _, _) ->
              fail "cross-device install %s -> %s (a sibling temp must be on the target filesystem; no copy fallback)" tp target
          | Unix.Unix_error (e, _, _) -> fail "cannot install %s: %s" target (Unix.error_message e));
      if i = 0 then checkpoint "after-first-install") desired;
    (* J. remove stale Fido-owned .go not in the desired target SET (empty program removes them all) *)
    remove_stale_go unlink before_delete dir header desired_targets "";
    List.length desired in
  (* handled-failure cleanup (§14): remove every sibling temp this invocation created that is STILL a regular
     reserved-suffix file (an already-installed one is Missing at its temp path — skip); then remove
     newly-created empty parents.  Aggregate every error; never hide the initiating one. *)
  let cleanup_errors = ref [] in
  let cleanup_on_failure () =
    List.iter (fun tp ->
      (* observe each temp under its OWN error guard so an lstat failure on one collects an error and does
         NOT abort cleanup of the remaining temps/dirs (§14 attempts every temp). *)
      match (try `Obs (lstat_obs tp) with Fail m -> `Err m) with
      | `Err m -> cleanup_errors := Printf.sprintf "cannot observe temp %s: %s" tp m :: !cleanup_errors
      | `Obs Missing -> ()
      | `Obs (Present st) when st.Unix.st_kind = Unix.S_REG && ends_with temp_suffix tp ->
        (match (try unlink tp; None with Unix.Unix_error (e,_,_) -> Some (Unix.error_message e)) with
         | None -> () | Some m -> cleanup_errors := Printf.sprintf "cannot remove temp %s: %s" tp m :: !cleanup_errors)
      | `Obs (Present _) -> cleanup_errors := Printf.sprintf "temp %s changed type — preserving it" tp :: !cleanup_errors)
      !created_temps;
    (* newly-created parents (deepest first): a non-empty dir (ENOTEMPTY/EEXIST) is benign (preserve it);
       any OTHER removal error is an operational failure and is reported. *)
    List.iter (fun d ->
      match (try Unix.rmdir d; None
             with Unix.Unix_error ((Unix.ENOTEMPTY | Unix.EEXIST | Unix.ENOENT), _, _) -> None
                | Unix.Unix_error (e,_,_) -> Some (Unix.error_message e)) with
      | None -> () | Some m -> cleanup_errors := Printf.sprintf "cannot remove created dir %s: %s" d m :: !cleanup_errors)
      !created_dirs in
  (* releasing the lock collects (never hides) both a descriptor-close error and the unlink error. *)
  let lock_errors = ref [] in
  let release_lock () =
    (match (try Unix.close lockfd; None with Unix.Unix_error (e,_,_) -> Some (Unix.error_message e)) with
     | None -> () | Some m -> lock_errors := ("close: " ^ m) :: !lock_errors);
    (match (try Unix.unlink lock_abs; None with Unix.Unix_error (e,_,_) -> Some (Unix.error_message e)) with
     | None -> () | Some m -> lock_errors := ("unlink: " ^ m) :: !lock_errors) in
  match (try `Ok (body ()) with e -> `Err e) with
  | `Ok n ->
    release_lock ();
    (match !lock_errors with [] -> n
     | es -> raise (Fail ("lock release FAILED: " ^ String.concat "; " (List.rev es))))
  | `Err e ->
    let body_msg = match e with Fail m -> m | _ -> Printexc.to_string e in
    (try cleanup_on_failure ()
     with ex -> cleanup_errors := ("cleanup routine raised: " ^ Printexc.to_string ex) :: !cleanup_errors);
    release_lock ();
    let parts = body_msg
                :: (List.rev_map (fun m -> "cleanup FAILED: " ^ m) !cleanup_errors
                    @ List.rev_map (fun m -> "lock release FAILED: " ^ m) !lock_errors) in
    (match parts with
     | [ single ] -> raise (Fail single)
     | _ -> raise (Fail (String.concat " | " parts)))
