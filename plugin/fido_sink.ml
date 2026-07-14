(* fido_sink — the ONLY handwritten filesystem logic: a small, auditable, ownership-aware dirty-directory
   synchronizer.  It receives an already-final directory image — the exact root [go.mod] bytes plus an
   ((on-disk relative .go path * exact bytes) list), decoded from a proved-Rocq DirectoryImage whose
   provenance the vernac bridge typechecks — and makes a target tree's Fido-generated module EQUAL that
   image, while REFUSING to run in the presence of any foreign Go/module input or nested control name.  It
   understands ONLY the filesystem — no program, no Go, no Rocq terms.

   OWNERSHIP + FOREIGN REJECTION.  Installed `.go` files and the root `go.mod` are Fido-owned iff their
   first line is the exact generated header (DERIVED from the go.mod bytes) AND they are regular non-symlink
   files — RE-checked immediately before every overwrite/delete.  A foreign `.go` (anywhere beneath root), a
   foreign/nested `go.mod`, or a nested `.fido` REJECTS the whole emission before any generated-file
   mutation; foreign NON-Go files are preserved.

   SIBLING-TEMP STAGING (no records, no nonce, no stage directory, no parser).  `<root>/.fido/` holds the
   exact marker and, during an active run or after a crash, one git-style O_EXCL `index.lock` — nothing else.
   Each final output is staged into its RESERVED sibling temporary `<final>.fido-tmp-v1`; because the lock
   serializes cooperating emitters, the name needs no nonce and recovery needs no record — the final path is
   already known to the live sync.  Since temp and target are SIBLINGS, install is an atomic same-device
   rename (nested mounts inside root work; EXDEV fails loud, no copy).  A regular non-symlink file whose
   basename ends in `.fido-tmp-v1` is, by PUBLIC (and forgeable) CONVENTION, an abandoned Fido temp; a
   symlink/directory/special with that suffix is NOT owned (refuse + preserve).  Forgeability is an accepted
   tradeoff under the single-owner / cooperating-process threat model — no transaction log is built to avoid
   it.

   TWO-PHASE, FAIL-CLOSED.  After acquiring the lock: PHASE 1 inspects the WHOLE target tree once (validating
   foreign-Go/module/control rules and COLLECTING every regular reserved-suffix temp) and deletes nothing;
   only a confirmed ENOENT is "missing" — every other fs error aborts and preserves.  If any path is invalid
   or uninspectable the run rejects before any mutation.  PHASE 2 deletes each collected temp after re-lstat
   (must still be a regular reserved-suffix file).  Then the complete image stages into sibling temps before
   any install; each final installs by rename; stale owned `.go` is removed.  Binding order: validate the
   root chain and reject a reserved-namespace desired path BEFORE any effect; ensure/roll-back .fido; lock;
   inspect; delete abandoned temps; preflight; stage complete; install by rename; remove stale; release.

   HONEST GUARANTEE (Linux/amd64 scope).  GoProgram acceptance, SafeProgram certification, and DirectoryImage
   creation are semantically all-or-nothing.  Dirty-directory installation is locked for cooperating
   emitters, rejects foreign Go/module inputs and nested `.fido`, inspects the complete tree fail-closed,
   stages the complete image into reserved sibling temporary files before installation, uses per-file rename
   in the ordinary same-filesystem case, cleans handled-failure temps immediately, removes validated
   abandoned suffix-owned temps on a later run, and converges when the directory namespace remains stable.
   It is NOT a portable transactional multi-file filesystem commit, NOT hardened against malicious concurrent
   mutation, and does NOT model arbitrary unmount/remount/backing-store replacement between runs.

   Fallible/nondeterministic ops are PARAMETERS (checkpoint/unlink/rename/before_install/before_write/
   before_delete) so the driver injects faults through the REAL algorithm; the plugin always uses defaults. *)

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

(* ---- path safety + the reserved control namespace + the formal output domain ---- *)
let components rel =
  if not (Filename.is_relative rel) then fail "unsafe absolute path from image: %s" rel;
  let parts = String.split_on_char '/' rel in
  if parts = [] || List.exists (fun c -> c = "" || c = "." || c = ".." || String.contains c '\000') parts
  then fail "unsafe path from image: %s" rel;
  (match parts with
   | c :: _ when c = control_dir ->
       fail "refusing a desired path inside the reserved %s namespace: %s" control_dir rel
   | _ -> ());
  parts

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

(* ---- PHASE 1: ONE fail-closed inspection of the whole target tree.  Validate foreign-Go/module/control
   rules and COLLECT (never delete) every regular reserved-suffix temp; any invalid/uninspectable path
   rejects the whole run before any generated-file mutation. ---- *)
let rec inspect root header rel temps =
  let dir = if rel = "" then root else Filename.concat root rel in
  let names =
    try Sys.readdir dir
    with Sys_error m -> fail "cannot inspect %s: %s — refusing without a complete tree scan" dir m in
  Array.iter (fun name ->
    let child_rel = if rel = "" then name else rel ^ "/" ^ name in
    let p = Filename.concat dir name in
    if name = control_dir then
      (* the EXACT root .fido is the owned control dir (not descended); a NESTED .fido is an error of any type *)
      (if rel <> "" then fail "a nested %s control name is present (%s) — refusing" control_dir child_rel)
    else match lstat_obs p with
      | Missing -> ()
      | Present st ->
        let k = st.Unix.st_kind in
        if ends_with temp_suffix name then
          (if k = Unix.S_REG then temps := p :: !temps
           else fail "a reserved-suffix entry %s is a symlink/directory/special, not a regular temp — refusing" child_rel)
        else if name = gomod_name then
          (if rel <> "" then fail "a nested go.mod is present (%s) — refusing" child_rel
           else if not (k = Unix.S_REG && read_first_line p = header)
           then fail "a foreign root go.mod is present — refusing to touch it")
        else if ends_with ".go" name then
          (if not (k = Unix.S_REG && read_first_line p = header)
           then fail "a foreign .go file is present (%s) — refusing" child_rel)
        else if k = Unix.S_DIR then inspect root header child_rel temps
        (* other foreign non-Go files / symlinks / specials: preserved *))
    names

(* ---- PHASE 2: after the COMPLETE scan succeeds, delete each validated abandoned temp (re-lstat: still a
   regular non-symlink reserved-suffix file); fail loud on any mismatch or deletion error. ---- *)
let delete_temps unlink temps =
  List.iter (fun p ->
    match lstat_obs p with
    | Present st when st.Unix.st_kind = Unix.S_REG && ends_with temp_suffix p ->
        (try unlink p with Unix.Unix_error (e,_,_) -> fail "cannot remove abandoned temp %s: %s" p (Unix.error_message e))
    | Present _ -> fail "abandoned temp %s changed type before removal — refusing" p
    | Missing -> fail "abandoned temp %s vanished before removal — refusing" p)
    temps

(* ---- remove stale Fido-owned .go NOT in the desired set (ownership RE-checked immediately before delete) ---- *)
let rec remove_stale_go unlink before_delete root header desired rel =
  let dir = if rel = "" then root else Filename.concat root rel in
  let names =
    try Sys.readdir dir
    with Sys_error m -> fail "cannot scan %s for stale generated files: %s" dir m in
  Array.iter (fun name ->
    if not (rel = "" && name = control_dir) then begin
      let child_rel = if rel = "" then name else rel ^ "/" ^ name in
      let p = Filename.concat dir name in
      match lstat_obs p with
      | Missing -> ()
      | Present st ->
        if st.Unix.st_kind = Unix.S_DIR then remove_stale_go unlink before_delete root header desired child_rel
        else if ends_with ".go" name && st.Unix.st_kind = Unix.S_REG
                && read_first_line p = header && not (List.mem p desired)
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

let sync ?(checkpoint = fun _ -> ()) ?(unlink = Unix.unlink) ?(rename = Unix.rename)
         ?(before_install = fun _ -> ()) ?(before_write = fun _ -> ()) ?(before_delete = fun _ -> ())
         dir go_mod entries =
  let header = first_line_of_string go_mod in
  let control_abs = Filename.concat dir control_dir in
  let lock_abs    = Filename.concat control_abs lock_name in
  (* A. validate the root chain (prefix symlinks) — before any effect *)
  validate_root_chain dir;
  (* B. compute the desired outputs (go.mod at root + every .go); [components] rejects a desired path inside
        .fido, and each source entry must be a `.go` in the formal output domain — all before any effect *)
  let desired =
    (Filename.concat dir gomod_name, "", gomod_name, go_mod)
    :: List.map (fun (rel, bytes) ->
         let (parent_rel, base) = split_parent (components rel) in
         if not (ends_with ".go" base) then fail "refusing a non-.go output path (outside the formal domain): %s" rel;
         (Filename.concat dir rel, parent_rel, base, bytes)) entries in
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
    (* E. PHASE 1 — inspect the whole tree fail-closed, collecting abandoned temps (no deletion) *)
    let temps = ref [] in
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
    (* H. STAGE the complete image into sibling temps BEFORE any install *)
    List.iteri (fun i ((_, _, _, bytes) as d) ->
      let tp = temp_of d in
      before_write tp;                               (* test seam: a later-stage write can fail here *)
      write_new tp bytes;
      created_temps := tp :: !created_temps;
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
    (* J. remove stale Fido-owned .go not in the desired set (empty program removes them all) *)
    remove_stale_go unlink before_delete dir header (List.map (fun (t,_,_,_) -> t) desired) "";
    List.length desired in
  (* handled-failure cleanup (§14): remove every sibling temp this invocation created that is STILL a regular
     reserved-suffix file (an already-installed one is Missing at its temp path — skip); then remove
     newly-created empty parents.  Aggregate every error; never hide the initiating one. *)
  let cleanup_errors = ref [] in
  let cleanup_on_failure () =
    List.iter (fun tp ->
      match lstat_obs tp with
      | Missing -> ()
      | Present st when st.Unix.st_kind = Unix.S_REG && ends_with temp_suffix tp ->
        (match (try unlink tp; None with Unix.Unix_error (e,_,_) -> Some (Unix.error_message e)) with
         | None -> () | Some m -> cleanup_errors := Printf.sprintf "cannot remove temp %s: %s" tp m :: !cleanup_errors)
      | Present _ -> cleanup_errors := Printf.sprintf "temp %s changed type — preserving it" tp :: !cleanup_errors)
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
