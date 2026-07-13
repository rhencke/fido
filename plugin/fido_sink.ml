(* fido_sink — the ONLY handwritten filesystem logic: a GENERIC ownership-aware dirty-directory
   synchronizer.  It receives an already-final directory image — the exact root [go.mod] bytes plus an
   ((on-disk relative .go path * exact bytes) list), decoded from a proved-Rocq DirectoryImage whose
   provenance the vernac bridge typechecks — and makes a target tree's Fido-generated module EQUAL that
   image, while REFUSING to run in the presence of any foreign Go/module input.  It understands ONLY the
   filesystem — no program, no Go, no Rocq terms.

   OWNERSHIP + FOREIGN REJECTION.  Installed `.go` files and the root `go.mod` are Fido-owned iff their
   first line is the exact generated header (DERIVED from the go.mod bytes) AND they are regular non-symlink
   files — RE-checked immediately before every overwrite/delete.  A foreign `.go` (anywhere beneath root) or
   a foreign/nested `go.mod` REJECTS the whole emission before any generated-file mutation (a dirty foreign
   Go input would silently change what `go build ./...` compiles); foreign NON-Go files are preserved.

   LOCAL STAGING (no central staging dir).  `<root>/.fido/` holds the exact marker, one git-style O_EXCL
   lock, and `stage-records/` (records ONLY, never payloads).  For each distinct final PARENT (root for
   `go.mod`/root-level `.go`; a subdir for a nested `.go`) one local stage `<parent>/.fido-stage-<nonce>`
   (OS /dev/urandom nonce) is created, OWNED BY A ROOT-OWNED RECORD — never a name/marker/header: the record
   is created atomic O_CREAT|O_EXCL and fully written+validated BEFORE its stage dir, and removed only AFTER
   the stage dir is gone.  Because stage and target are SIBLINGS, per-file install is an atomic same-device
   rename (nested mounts inside root work; no central cross-device compare; EXDEV fails loud, no copy).
   Binding order: validate the root chain and reject a reserved-namespace desired path (a target inside
   .fido) BEFORE any effect; then ensure/roll-back .fido; acquire the lock; record-driven recovery; reject
   foreign Go/module inputs — after the lock/recovery but BEFORE any generated-file MUTATION (no stage or
   install has happened yet); stage the COMPLETE image; install each by rename; remove stale owned `.go`;
   remove each stage then its record; release the lock.

   FAIL-CLOSED.  Only a confirmed ENOENT is "missing"; every other fs error (EACCES/EIO/ELOOP/ENOTDIR/…)
   aborts; discovery never turns a readdir/lstat failure into "empty"/"no header".  On a handled failure the
   run cleans its OWN stages/records/newly-empty parents immediately and AGGREGATES body + cleanup +
   lock-release errors (a record is removed only once its stage is CONFIRMED gone — never orphaned).  An
   existing `.fido` is validated (marker + stage-records/ + a transient lock, nothing else) and NEVER
   modified; a failed first-time init rolls back what it created.

   HONEST GUARANTEE (Linux/amd64 scope).  GoProgram acceptance, SafeProgram certification, and DirectoryImage
   creation are semantically all-or-nothing.  Installation is locked for COOPERATING emitters, rejects
   foreign Go/module inputs, stages the complete image locally beside target parents before installation,
   uses per-file atomic rename in the ordinary same-filesystem case, cleans handled-failure residue
   immediately, recovers record-owned abandoned stages before future mutation, and converges on rerun.  It
   is NOT a portable transactional multi-file filesystem commit, NOT crash-proof against SIGKILL/power loss,
   and — no openat/O_NOFOLLOW in this OCaml Unix — NOT hardened against a malicious concurrent process; the
   single-emit-process use has no such adversary.  A foreign lookalike without a valid root-owned record is
   never treated as owned.

   Fallible/nondeterministic ops are PARAMETERS (rand_hex/checkpoint/unlink/rename/before_install/before_write/
   before_delete) so the driver injects faults through the REAL algorithm; the plugin always uses defaults. *)

let control_dir  = ".fido"
let marker_name  = "marker"
let marker_bytes = "fido-control-directory.  do not edit.\n"
let lock_name    = "index.lock"                (* git-style: created O_EXCL, removed at end *)
let records_dir  = "stage-records"             (* <root>/.fido/stage-records/ — records ONLY, no payloads *)
let stage_prefix = ".fido-stage-"              (* <parent>/.fido-stage-<nonce> local stage dirs *)
let gomod_name   = "go.mod"
let record_tag   = "fido-stage-record v1"
let nonce_bytes  = 16                          (* /dev/urandom bytes per stage nonce *)
let nonce_hexlen = 2 * nonce_bytes             (* its exact hex length (a strict record field) *)

exception Fail of string
let fail fmt = Printf.ksprintf (fun s -> raise (Fail s)) fmt

(* a local stage tracked for cleanup: its durable record (created first) + its stage dir once created.
   Registered the moment the record exists, so any later failure routes to the one aggregating cleanup. *)
type tracked = { record : string; mutable dir : string option }

(* ---- fail-closed filesystem observation: only a confirmed ENOENT is "missing" ---- *)
type obs = Missing | Present of Unix.stats

let lstat_obs p =
  try Present (Unix.lstat p)
  with Unix.Unix_error (Unix.ENOENT, _, _) -> Missing
     | Unix.Unix_error (e, _, _) -> fail "cannot lstat %s: %s" p (Unix.error_message e)

let is_kind p k = match lstat_obs p with Present st -> st.Unix.st_kind = k | Missing -> false

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

(* ---- path safety + the reserved control namespace ---- *)

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

(* ---- recursive removal that never follows a symlink (unlink removes the link itself) ---- *)
let rec rm_rf_no_follow unlink p =
  match lstat_obs p with
  | Missing -> ()
  | Present st ->
    (match st.Unix.st_kind with
     | Unix.S_DIR ->
        let names =
          try Sys.readdir p
          with Sys_error m -> fail "recovery FAILED: cannot read %s: %s" p m in
        Array.iter (fun n -> rm_rf_no_follow unlink (Filename.concat p n)) names;
        (try Unix.rmdir p with Unix.Unix_error (e,_,_) -> fail "recovery FAILED: cannot rmdir %s: %s" p (Unix.error_message e))
     | _ ->
        (try unlink p with Unix.Unix_error (e,_,_) -> fail "recovery FAILED: cannot unlink %s: %s" p (Unix.error_message e)))

(* ---- default OS nonce: high-entropy hex from /dev/urandom (never OCaml Random) ---- *)
let default_rand_hex n =
  let ic = try open_in_bin "/dev/urandom" with Sys_error m -> fail "cannot open /dev/urandom: %s" m in
  let b = Bytes.create n in
  (try really_input ic b 0 n with End_of_file -> close_in_noerr ic; fail "short read from /dev/urandom");
  close_in ic;
  let buf = Buffer.create (2 * n) in
  Bytes.iter (fun c -> Buffer.add_string buf (Printf.sprintf "%02x" (Char.code c))) b;
  Buffer.contents buf

let is_hex s = s <> "" &&
  String.for_all (fun c -> (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f')) s

(* a recorded stage's parent-relative path must be safe and stay under root. *)
let safe_rel r =
  r = "" ||
  (let parts = String.split_on_char '/' r in
   not (List.exists (fun c -> c = "" || c = "." || c = ".." || String.contains c '\000') parts))

(* ---- record-driven recovery of abandoned local stages (fail-closed) ---- *)

(* STRICT: exactly the versioned tag line + nonce + parent + stage + a single trailing newline — any
   missing field, extra trailing data, or wrong tag is a malformed record (fail-closed, never accepted). *)
let parse_record p =
  match String.split_on_char '\n' (read_whole p) with
  | [tag; nonce; parent; stage; ""] when tag = record_tag -> (nonce, parent, stage)
  | _ -> fail "recovery FAILED: malformed record %s" p

let valid_nonce n = is_hex n && String.length n = nonce_hexlen

(* validate that every RECORDED-PARENT component of a stage rel path is a REAL non-symlink directory (lstat
   per component under root).  Otherwise a symlinked ancestor (e.g. a crash record naming sub/.fido-stage-N
   where sub later became a symlink out of root) would let the final lstat/rm_rf follow it OUTSIDE the root.
   The final component (the stage dir itself) is validated by its own lstat at the call site. *)
let validate_stage_ancestors root stage_rel =
  let rec go cur = function
    | [] | [ _ ] -> ()
    | c :: rest ->
      let nxt = Filename.concat cur c in
      (match lstat_obs nxt with
       | Present st when st.Unix.st_kind = Unix.S_DIR -> go nxt rest
       | Present _ -> fail "recovery FAILED: recorded-stage parent %s is a symlink or non-directory — refusing" nxt
       | Missing -> ())   (* a missing parent ⇒ the stage is missing too ⇒ handled as a stale record below *)
  in go root (String.split_on_char '/' stage_rel)

let recover_stages unlink root records_abs =
  match lstat_obs records_abs with
  | Missing -> ()
  | Present st ->
    if st.Unix.st_kind <> Unix.S_DIR then fail "recovery FAILED: %s is not a directory" records_abs;
    let names =
      try Sys.readdir records_abs
      with Sys_error m -> fail "recovery FAILED: cannot enumerate %s: %s" records_abs m in
    Array.iter (fun recname ->
      let record_abs = Filename.concat records_abs recname in
      match lstat_obs record_abs with
      | Missing -> ()
      | Present rst ->
        if rst.Unix.st_kind <> Unix.S_REG then
          fail "recovery FAILED: %s is not a regular record file — refusing" record_abs;
        let (nonce, parent_rel, stage_rel) = parse_record record_abs in
        if nonce <> recname then fail "recovery FAILED: record %s nonce mismatch" record_abs;
        if not (valid_nonce nonce) then fail "recovery FAILED: record %s has an invalid nonce" record_abs;
        if not (safe_rel parent_rel) then fail "recovery FAILED: record %s parent escapes root" record_abs;
        let expected = (if parent_rel = "" then "" else parent_rel ^ "/") ^ stage_prefix ^ nonce in
        if stage_rel <> expected then fail "recovery FAILED: record %s stage path inconsistent" record_abs;
        validate_stage_ancestors root stage_rel;   (* no symlinked parent may redirect rm_rf out of root *)
        let stage_abs = Filename.concat root stage_rel in
        (match lstat_obs stage_abs with
         | Missing ->
            (try unlink record_abs
             with Unix.Unix_error (e,_,_) -> fail "recovery FAILED: cannot remove stale record %s: %s" record_abs (Unix.error_message e))
         | Present sst ->
            if sst.Unix.st_kind = Unix.S_DIR then begin
              rm_rf_no_follow unlink stage_abs;
              (try unlink record_abs
               with Unix.Unix_error (e,_,_) -> fail "recovery FAILED: cannot remove record %s: %s" record_abs (Unix.error_message e))
            end else
              fail "recovery FAILED: recorded stage %s is not a directory — refusing" stage_abs))
      names

(* ---- foreign-Go / foreign-or-nested-go.mod scan (fail-closed): prove no foreign build input ---- *)
let rec scan_foreign root header rel =
  let dir = if rel = "" then root else Filename.concat root rel in
  let names =
    try Sys.readdir dir
    with Sys_error m -> fail "cannot inspect %s: %s — refusing without proving absence of foreign Go" dir m in
  Array.iter (fun name ->
    if not (rel = "" && name = control_dir) then begin       (* the owned root control dir is not scanned *)
      let child_rel = if rel = "" then name else rel ^ "/" ^ name in
      let p = Filename.concat dir name in
      match lstat_obs p with
      | Missing -> ()
      | Present st ->
        let k = st.Unix.st_kind in
        if name = gomod_name then begin
          if rel <> "" then fail "a nested go.mod is present (%s) — refusing" child_rel
          else if not (k = Unix.S_REG && read_first_line p = header)
          then fail "a foreign root go.mod is present — refusing to touch it"
        end
        else if ends_with ".go" name then begin
          if not (k = Unix.S_REG && read_first_line p = header)
          then fail "a foreign .go file is present (%s) — refusing" child_rel
        end
        else if k = Unix.S_DIR then scan_foreign root header child_rel
        (* other (non-.go, non-go.mod) regular files, symlinks, specials: foreign but harmless — preserved *)
    end)
    names

(* ---- one recorded local stage per parent (record BEFORE stage dir; retry on collision).  [stages] is the
   shared cleanup registry (tracked added when the record exists, dir set when the stage exists), so any
   later failure routes to the single aggregating cleanup — make_stage never self-cleans nor orphans. *)
let make_stage rand_hex unlink checkpoint stages root records_abs parent_rel =
  let parent_abs = if parent_rel = "" then root else Filename.concat root parent_rel in
  let rec attempt tries =
    if tries <= 0 then fail "could not create a unique local stage under %s" parent_abs;
    let nonce = rand_hex nonce_bytes in
    if not (valid_nonce nonce) then fail "the nonce source did not return a %d-char hex nonce" nonce_hexlen;
    let stage_name = stage_prefix ^ nonce in
    let stage_abs = Filename.concat parent_abs stage_name in
    let stage_rel = (if parent_rel = "" then "" else parent_rel ^ "/") ^ stage_name in
    let record_abs = Filename.concat records_abs nonce in
    match lstat_obs stage_abs with
    | Present _ -> attempt (tries - 1)          (* a pre-existing lookalike occupies the path: new nonce *)
    | Missing ->
      (match (try `Fd (Unix.openfile record_abs [Unix.O_CREAT; Unix.O_EXCL; Unix.O_WRONLY] 0o644)
              with Unix.Unix_error (Unix.EEXIST, _, _) -> `Collide
                 | Unix.Unix_error (e, _, _) -> fail "cannot create stage record %s: %s" record_abs (Unix.error_message e)) with
       | `Collide -> attempt (tries - 1)
       | `Fd fd ->
         let content = Printf.sprintf "%s\n%s\n%s\n%s\n" record_tag nonce parent_rel stage_rel in
         (try write_all fd content; Unix.close fd
          with e ->
            let close_msg = (try Unix.close fd; None with Unix.Unix_error (ce,_,_) -> Some (Unix.error_message ce)) in
            let base = match e with Fail m -> m | _ -> Printexc.to_string e in
            let rm_msg = (try unlink record_abs; None with Unix.Unix_error (re,_,_) -> Some (Unix.error_message re)) in
            fail "cannot write stage record %s: %s%s%s" record_abs base
              (match close_msg with Some c -> " | fd close failed: " ^ c | None -> "")
              (match rm_msg with Some r -> " | record cleanup failed: " ^ r | None -> ""));
         (* the record now exists on disk — REGISTER it before anything else can fail *)
         let t = { record = record_abs; dir = None } in
         stages := t :: !stages;
         (let (n', p', s') = parse_record record_abs in    (* §13.6 validate the CLOSED record *)
          if not (n' = nonce && p' = parent_rel && s' = stage_rel)
          then fail "stage record %s did not validate after write" record_abs);
         checkpoint "after-record";
         (match (try `Ok (Unix.mkdir stage_abs 0o755)
                 with Unix.Unix_error (Unix.EEXIST, _, _) -> `Collide
                    | Unix.Unix_error (e, _, _) -> fail "cannot create local stage %s: %s" stage_abs (Unix.error_message e)) with
          | `Ok () -> t.dir <- Some stage_abs; checkpoint "after-mkdir"; stage_abs
          | `Collide ->                          (* a raced foreign entry at the slot: drop OUR record, retry *)
            (match (try unlink record_abs; None with Unix.Unix_error (e,_,_) -> Some (Unix.error_message e)) with
             | None -> stages := List.filter (fun x -> x != t) !stages; attempt (tries - 1)
             | Some m -> fail "cannot remove stage record %s after a slot collision: %s" record_abs m)))
  in attempt 8

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
          (* §17 recheck ownership IMMEDIATELY before delete and ABORT fail-closed on ANY mismatch/error
             (the target became missing, nonregular, symlinked, unreadable, or no longer Fido-headed) —
             never delete a file that is no longer provably ours; preserve it. *)
          if owned_regular p header then
            (try unlink p
             with Unix.Unix_error (e,_,_) -> fail "cannot remove stale generated %s: %s" p (Unix.error_message e))
          else fail "stale generated %s changed and is no longer Fido-owned — refusing to touch it" p
        end
    end)
    names

let ensure_root_and_control root control_abs records_abs =
  (match lstat_obs root with
   | Present st -> if st.Unix.st_kind <> Unix.S_DIR then fail "target root is not a real directory: %s" root
   | Missing -> (try Unix.mkdir root 0o755
                 with Unix.Unix_error (e,_,_) -> fail "cannot create root %s: %s" root (Unix.error_message e)));
  match lstat_obs control_abs with
  | Missing ->
    (* FIRST-TIME: create the whole owned control namespace (marker + records dir).  If any step after the
       control dir fails, ROLL BACK exactly the entries this invocation created, so a partial .fido never
       strands the target (the next run starts fresh and converges — §12,15). *)
    (try Unix.mkdir control_abs 0o755
     with Unix.Unix_error (e,_,_) -> fail "cannot create %s: %s" control_abs (Unix.error_message e));
    let mk = Filename.concat control_abs marker_name in
    (try
       write_new mk marker_bytes;
       (try Unix.mkdir records_abs 0o755
        with Unix.Unix_error (e,_,_) -> fail "cannot create %s: %s" records_abs (Unix.error_message e))
     with e ->
       let base = match e with Fail m -> m | _ -> Printexc.to_string e in
       let errs = ref [] in
       (* each step catches ANY exception (incl. the [Fail] lstat_obs raises) so all steps run and aggregate. *)
       let step what f =
         match (try f (); None with Fail m -> Some m | Unix.Unix_error (er,_,_) -> Some (Unix.error_message er) | ex -> Some (Printexc.to_string ex)) with
         | None -> () | Some m -> errs := (what ^ ": " ^ m) :: !errs in
       step "records dir" (fun () -> match lstat_obs records_abs with Present _ -> Unix.rmdir records_abs | Missing -> ());
       step "marker" (fun () -> match lstat_obs mk with Present _ -> Unix.unlink mk | Missing -> ());
       step "control dir" (fun () -> Unix.rmdir control_abs);
       (match !errs with
        | [] -> fail "first-time %s init failed and was rolled back: %s" control_abs base
        | es -> fail "first-time %s init failed: %s | rollback also failed: %s" control_abs base (String.concat "; " (List.rev es))))
  | Present st ->
    (* EXISTING: VALIDATE the exact ownership marker AND directory shape; abort WITHOUT modifying on any
       deviation (§12 — an existing .fido is Fido-owned by location; it must be marker + stage-records/ (+ a
       transient index.lock), nothing else). *)
    if st.Unix.st_kind <> Unix.S_DIR then fail "%s exists but is not a directory — refusing" control_abs;
    let mk = Filename.concat control_abs marker_name in
    (match lstat_obs mk with
     | Present mst when mst.Unix.st_kind = Unix.S_REG && read_whole mk = marker_bytes -> ()
     | _ -> fail "%s exists without the exact Fido control marker — refusing to touch it" control_abs);
    (match lstat_obs records_abs with
     | Present rst when rst.Unix.st_kind = Unix.S_DIR -> ()
     | _ -> fail "%s lacks the expected %s/ directory — refusing to touch it" control_abs records_dir);
    let names = try Sys.readdir control_abs
                with Sys_error m -> fail "cannot inspect %s: %s — refusing" control_abs m in
    Array.iter (fun n ->
      if not (n = marker_name || n = records_dir || n = lock_name)
      then fail "%s contains an unexpected entry %s — refusing to touch it" control_abs n)
      names

let uniq l = List.rev (List.fold_left (fun acc x -> if List.mem x acc then acc else x :: acc) [] l)

let sync ?(rand_hex = default_rand_hex) ?(checkpoint = fun _ -> ()) ?(unlink = Unix.unlink)
         ?(rename = Unix.rename) ?(before_install = fun _ -> ()) ?(before_write = fun _ -> ())
         ?(before_delete = fun _ -> ())
         dir go_mod entries =
  let header = first_line_of_string go_mod in
  let control_abs = Filename.concat dir control_dir in
  let lock_abs    = Filename.concat control_abs lock_name in
  let records_abs = Filename.concat control_abs records_dir in
  (* A. validate the root chain (prefix symlinks) — before any effect *)
  validate_root_chain dir;
  (* B. compute the desired outputs (go.mod at root + every .go); the reserved-namespace check in
        [components] rejects a desired path inside .fido BEFORE any effect *)
  let desired =
    (Filename.concat dir gomod_name, "", gomod_name, go_mod)
    :: List.map (fun (rel, bytes) ->
         let (parent_rel, base) = split_parent (components rel) in
         (Filename.concat dir rel, parent_rel, base, bytes)) entries in
  (* C. ensure root + the owned control namespace (marker/records) *)
  ensure_root_and_control dir control_abs records_abs;
  (* D. acquire the emission lock (git-style O_EXCL) *)
  let lockfd =
    try Unix.openfile lock_abs [Unix.O_CREAT; Unix.O_EXCL; Unix.O_WRONLY] 0o644
    with Unix.Unix_error (Unix.EEXIST, _, _) ->
           fail "%s already exists — another Fido emission holds it, or a crashed run left it (remove it to proceed)" lock_abs
       | Unix.Unix_error (e, _, _) -> fail "cannot create lock %s: %s" lock_abs (Unix.error_message e) in
  let created_dirs = ref [] and stages = ref [] in
  let body () =
    (* E. record-driven recovery of abandoned stages (fail-closed) *)
    recover_stages unlink dir records_abs;
    (* F. foreign-Go / foreign-or-nested go.mod scan (fail-closed) *)
    scan_foreign dir header "";
    (* G. one recorded local stage per distinct final parent (creating parent dirs as needed) *)
    let stage_of = Hashtbl.create 8 in
    List.iter (fun pr ->
      ensure_dir_chain dir pr created_dirs;
      let stage_abs = make_stage rand_hex unlink checkpoint stages dir records_abs pr in
      Hashtbl.replace stage_of pr stage_abs)
      (uniq (List.map (fun (_,pr,_,_) -> pr) desired));
    (* H. STAGE THE COMPLETE IMAGE before any install *)
    List.iteri (fun i (_, pr, base, bytes) ->
      let sp = Filename.concat (Hashtbl.find stage_of pr) base in
      before_write sp;                               (* test seam: a later-stage write can fail here *)
      write_new sp bytes;
      if i = 0 then checkpoint "after-first-payload") desired;
    checkpoint "after-staging";
    (* I. install each file: recheck ownership IMMEDIATELY before overwrite, then rename (sibling; atomic;
          EXDEV fails loud with NO copy fallback) *)
    List.iter (fun (target, pr, base, _) ->
      before_install target;                       (* test seam: a race can mutate the target here *)
      (match lstat_obs target with
       | Missing -> ()
       | Present _ -> if not (owned_regular target header)
                      then fail "%s changed and is no longer Fido-owned — refusing to overwrite" target);
      let src = Filename.concat (Hashtbl.find stage_of pr) base in
      (try rename src target
       with Unix.Unix_error (Unix.EXDEV, _, _) ->
              fail "cross-device install %s -> %s (a local stage must be on the target filesystem; no copy fallback)" src target
          | Unix.Unix_error (e, _, _) -> fail "cannot install %s: %s" target (Unix.error_message e)))
      desired;
    (* J. remove stale Fido-owned .go not in the desired set (empty program removes them all) *)
    remove_stale_go unlink before_delete dir header (List.map (fun (t,_,_,_) -> t) desired) "";
    (* K. cleanup: remove each now-empty stage, then its record *)
    List.iter (fun t ->
      (match t.dir with
       | Some stage_abs ->
         (try Unix.rmdir stage_abs
          with Unix.Unix_error (e,_,_) -> fail "cannot remove local stage %s: %s" stage_abs (Unix.error_message e))
       | None -> ());
      (try unlink t.record
       with Unix.Unix_error (e,_,_) -> fail "cannot remove stage record %s: %s" t.record (Unix.error_message e)))
      !stages;
    stages := [];
    List.length desired in
  (* handled-failure cleanup (§15): remove this run's stages then their records + newly-empty parents.  The
     record is removed ONLY when its stage is CONFIRMED gone — a failed stage removal keeps the record so the
     stage stays RECOVERABLE (never orphaned).  Every cleanup error is collected, not hidden. *)
  let cleanup_errors = ref [] in
  let cleanup_on_failure () =
    List.iter (fun t ->
      (* a stage that could not be removed keeps its record (recoverable); a record with no stage yet is
         removed directly.  Both cases collect any removal error rather than hiding it. *)
      let rm_record () =
        match (try unlink t.record; None with Unix.Unix_error (e,_,_) -> Some (Unix.error_message e)) with
        | None -> () | Some m -> cleanup_errors := Printf.sprintf "cannot remove record %s: %s" t.record m :: !cleanup_errors in
      match t.dir with
      | None -> rm_record ()
      | Some stage_abs ->
        let stage_gone =
          (try rm_rf_no_follow unlink stage_abs; (match lstat_obs stage_abs with Missing -> true | _ -> false)
           with Fail m -> cleanup_errors := m :: !cleanup_errors; false
              | e -> cleanup_errors := Printexc.to_string e :: !cleanup_errors; false) in
        if stage_gone then rm_record ()
        else cleanup_errors := Printf.sprintf "stage %s not removed — preserving record %s for recovery" stage_abs t.record :: !cleanup_errors)
      !stages;
    (* newly-created empty parents: a non-empty dir (ENOTEMPTY/EEXIST) is benign (preserve it); any OTHER
       removal error is an operational failure and is reported. *)
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
