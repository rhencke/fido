(* The ONLY handwritten OCaml: a GENERIC dirty-directory FILESYSTEM synchronizer.  It receives an
   already-final directory image (relative path * exact bytes) — computed and extracted from proved
   Rocq, together with the ownership header (the SOLE authority; the sink hardcodes no header) — and
   makes a target directory's Fido-owned files EQUAL that image: new files written, changed files
   replaced, stale Fido files removed, while every FOREIGN file and directory is left untouched.  It
   decodes no program, renders nothing, parses no Go, and walks no Rocq terms: it understands ONLY the
   filesystem.  A file is Fido-owned iff its first line is the exact generated header.  Installation is
   crash-safe: bytes are written to a hidden staging directory INSIDE the target, then moved into place
   by per-file atomic rename (for the current one-file image, a single atomic rename); an exclusive lock
   serializes concurrent syncs.  Two hidden names inside the target are RESERVED for the sink. *)

let (header, image_entries) = Emit_out.emit_image   (* header + (path, bytes) list, both from Rocq *)
let staging_name = ".fido-staging"                   (* reserved: our staging directory *)
let lock_name = ".fido-sync.lock"                    (* reserved: our exclusive lock file *)

let die msg = prerr_endline ("fido writer: " ^ msg); exit 1

(* ---- small filesystem helpers (lstat everywhere: never follow a symlink implicitly) ---- *)
let lstat_opt p = try Some (Unix.lstat p) with Unix.Unix_error _ -> None
let kind_opt p = match lstat_opt p with Some st -> Some st.Unix.st_kind | None -> None

let rec mkdir_p dir =
  if not (Sys.file_exists dir) then begin
    let parent = Filename.dirname dir in
    if parent <> dir then mkdir_p parent;
    (try Unix.mkdir dir 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ())
  end

let rec rm_rf path =
  match lstat_opt path with
  | None -> ()
  | Some st ->
    if st.Unix.st_kind = Unix.S_DIR then begin
      Array.iter (fun n -> rm_rf (Filename.concat path n)) (Sys.readdir path);
      Unix.rmdir path
    end else Unix.unlink path

let write_file path bytes =
  let oc = open_out_bin path in
  output_string oc bytes; close_out oc

let first_line path =
  match (try Some (open_in_bin path) with Sys_error _ -> None) with
  | None -> None
  | Some ic -> let l = (try Some (input_line ic) with End_of_file -> None) in close_in ic; l

(* a REGULAR file (never a symlink or dir) whose first line is the ownership marker *)
let is_fido_owned path = kind_opt path = Some Unix.S_REG && first_line path = Some header

(* recursively collect Fido-owned regular files under dir, skipping our own reserved control entries *)
let rec discover dir acc =
  Array.fold_left (fun acc name ->
    if name = staging_name || name = lock_name then acc
    else
      let p = Filename.concat dir name in
      match kind_opt p with
      | Some Unix.S_DIR -> discover p acc
      | Some Unix.S_REG when first_line p = Some header -> p :: acc
      | _ -> acc)
    acc (Sys.readdir dir)

(* a relative path split into safe components (non-absolute; no empty/"."/".." parts) *)
let checked_components rel =
  if not (Filename.is_relative rel) then None
  else
    let parts = String.split_on_char '/' rel in
    if parts <> [] && List.for_all (fun c -> c <> "" && c <> "." && c <> "..") parts
    then Some parts else None

(* every EXISTING parent component under root must be a real directory (this refuses symlinked or
   file-shaped parents, so no traversal and no mid-install failure on a bad parent) *)
let rec check_parents cur = function
  | [] | [ _ ] -> ()
  | c :: rest ->
    let nxt = Filename.concat cur c in
    (match kind_opt nxt with
     | None -> check_parents nxt rest              (* absent: will be created as a real directory *)
     | Some Unix.S_DIR -> check_parents nxt rest
     | Some _ -> die ("a path component is not a directory: " ^ nxt))

let () =
  let root = Sys.argv.(1) in
  mkdir_p root;
  (* (1) exclusive lock.  Refuse a foreign non-regular entry at the reserved lock name (an lstat
     ownership check — so a symlink is caught and never followed), then take the lock; the whole-file
     lockf auto-releases when this process exits. *)
  let lock_path = Filename.concat root lock_name in
  (match kind_opt lock_path with
   | Some k when k <> Unix.S_REG -> die "the reserved lock name is occupied by a non-regular entry"
   | _ -> ());
  let lock_fd =
    try Unix.openfile lock_path [ Unix.O_CREAT; Unix.O_RDWR ] 0o644
    with Unix.Unix_error _ -> die "cannot open the sync lock" in
  (try Unix.lockf lock_fd Unix.F_TLOCK 0
   with Unix.Unix_error _ -> die "another sync holds the lock");
  (* (2) the staging name is reserved and is always a directory we create; clean our own abandoned
     staging, but REFUSE (never delete) a foreign non-directory squatting the reserved name. *)
  let staging = Filename.concat root staging_name in
  (match kind_opt staging with
   | None -> ()
   | Some Unix.S_DIR -> rm_rf staging
   | Some _ -> die "the reserved staging name is occupied by a foreign non-directory");
  (* (3) discover the files Fido currently owns (by header), before touching anything *)
  let owned = discover root [] in
  (* (4) preflight EVERY desired path: safe components, real-directory parents, no foreign collision *)
  let targets = List.map (fun (rel, contents) ->
    match checked_components rel with
    | None -> die ("unsafe relative path: " ^ rel)
    | Some parts ->
      check_parents root parts;
      let target = List.fold_left Filename.concat root parts in
      (* only our own regular file may be replaced; refuse ANY other existing entry, including a
         (possibly dangling) symlink — lstat, so we never follow it *)
      (match lstat_opt target with
       | None -> ()
       | Some st when st.Unix.st_kind = Unix.S_REG && first_line target = Some header -> ()
       | Some _ -> die ("refusing to overwrite a foreign entry: " ^ target));
      (target, parts, contents))
    image_entries in
  (* (5)+(6) stage all bytes inside root (same filesystem, so the later renames are atomic) *)
  Unix.mkdir staging 0o755;
  List.iter (fun (_, parts, contents) ->
    let sp = List.fold_left Filename.concat staging parts in
    mkdir_p (Filename.dirname sp);
    write_file sp contents)
    targets;
  (* (7) install by per-file atomic rename, replacing only existing Fido-owned files *)
  List.iter (fun (target, parts, _) ->
    let sp = List.fold_left Filename.concat staging parts in
    mkdir_p (Filename.dirname target);
    Sys.rename sp target)
    targets;
  (* (8)+(9) delete Fido-owned files no longer desired; never a foreign file, never a directory *)
  let desired = List.map (fun (t, _, _) -> t) targets in
  List.iter (fun p -> if not (List.mem p desired) then Unix.unlink p) owned;
  rm_rf staging;
  (* (10) release the lock; (11) report success only after a COMPLETE sync *)
  Unix.close lock_fd;
  Printf.printf "fido writer: synced %d file(s) into %s\n" (List.length targets) root
