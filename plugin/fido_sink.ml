(* fido_sink — the ONLY handwritten filesystem logic: a GENERIC ownership-aware dirty-directory
   synchronizer.  It receives an already-final directory image ((on-disk relative path * exact bytes)
   list, decoded from a proved-Rocq DirectoryImage) and makes a target tree's Fido-generated files EQUAL
   that image, while leaving every FOREIGN file, directory, and symlink untouched.  It understands ONLY
   the filesystem: it decodes no program, renders nothing, parses no Go, walks no Rocq terms.

   Ownership is POSITIVE and rechecked immediately before every overwrite/delete:
     - a persistent control directory  <root>/.fido/  holds an exact ownership marker and the lock;
     - a generated .go file is Fido-owned iff its first line is exactly the generated header;
     - per-parent stage directories  <parent>/.fido-stage-<random>/  hold an exact stage marker;
   nothing at a control/stage/lookalike name is deleted unless its exact marker is present, and no
   symlink is ever followed.  Installation stages every file first, then per-file atomic-renames; on any
   handled failure all invocation stages are removed and existing generated files are left untouched.
   It is convergent on rerun but NOT a transactional whole-tree commit (documented honestly). *)

let control_dir   = ".fido"
let marker_name   = "marker"
let marker_bytes  = "fido-control-directory.  do not edit.\n"
let lock_name     = "lock"
let stage_prefix  = ".fido-stage-"
let stage_marker  = ".fido-stage-marker"
let stage_bytes   = "fido-stage-directory.  do not edit.\n"
let gen_header    = "// fido generated.  do not edit."          (* first-line ownership of generated .go *)
let skip_dirs     = [ ".git"; ".hg"; ".svn"; control_dir ]      (* metadata trees never scanned/touched *)

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

let is_generated_go path =
  Filename.check_suffix path ".go"
  && kind_opt path = Some Unix.S_REG
  && first_line path = Some gen_header

let dir_has_marker dir name bytes =
  is_real_dir dir &&
  (let m = Filename.concat dir name in
   kind_opt m = Some Unix.S_REG && (try
     let ic = open_in_bin m in let n = in_channel_length ic in
     let s = really_input_string ic n in close_in ic; s = bytes
   with _ -> false))

let write_exact path bytes =
  let oc = open_out_bin path in output_string oc bytes; close_out oc

let rec rm_rf path =
  match lstat_opt path with
  | None -> ()
  | Some st ->
    if st.Unix.st_kind = Unix.S_DIR then begin
      Array.iter (fun n -> rm_rf (Filename.concat path n)) (Sys.readdir path);
      Unix.rmdir path
    end else Unix.unlink path

(* split an intrinsic relative path into components (already canonical, but re-guarded defensively) *)
let components rel =
  if not (Filename.is_relative rel) then fail "unsafe absolute path from image: %s" rel;
  let parts = String.split_on_char '/' rel in
  if parts = [] || List.exists (fun c -> c = "" || c = "." || c = ".." || String.contains c '\000') parts
  then fail "unsafe path from image: %s" rel;
  parts

(* ---- recursive discovery (never following directory symlinks) ---- *)
let rec walk_real_dirs root f =
  Array.iter (fun name ->
    let p = Filename.concat root name in
    f p name;
    if is_real_dir p && not (List.mem name skip_dirs) && not (has_stage_prefix name)
    then walk_real_dirs p f)
    (try Sys.readdir root with Sys_error _ -> [||])
and has_stage_prefix name =
  String.length name >= String.length stage_prefix
  && String.sub name 0 (String.length stage_prefix) = stage_prefix

let discover_owned_go root =
  let acc = ref [] in
  walk_real_dirs root (fun p _ -> if is_generated_go p then acc := p :: !acc);
  !acc

let discover_stale_stages root =
  let acc = ref [] in
  walk_real_dirs root (fun p name -> if has_stage_prefix name && is_real_dir p then acc := p :: !acc);
  !acc

(* a unique owned stage directory created atomically inside [parent] (random name, O_EXCL mkdir loop) *)
let rec make_stage parent tries =
  if tries <= 0 then fail "could not create a unique stage directory in %s" parent;
  let name = Printf.sprintf "%s%06x" stage_prefix (Random.int 0xffffff) in
  let dir = Filename.concat parent name in
  match (try Unix.mkdir dir 0o755; Some dir with Unix.Unix_error (Unix.EEXIST, _, _) -> None) with
  | Some d -> write_exact (Filename.concat d stage_marker) stage_bytes; d
  | None -> make_stage parent (tries - 1)

(* create required real-directory parents, refusing to descend through a symlink; record new ones *)
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

let () = Random.self_init ()

(* ---- the synchronization (algorithm §17 A..G) ---- *)
let sync root entries =
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
  (* (A.2) exclusive lock on the persistent control lock file (auto-released on process exit) *)
  let lock_path = Filename.concat ctrl lock_name in
  let lock_fd = Unix.openfile lock_path [ Unix.O_CREAT; Unix.O_RDWR ] 0o644 in
  (try Unix.lockf lock_fd Unix.F_TLOCK 0
   with Unix.Unix_error _ -> fail "another Fido emission holds the lock on %s" root);
  let created_parents = ref [] and created_stages = ref [] in
  let cleanup_stages () =
    List.iter (fun d -> try rm_rf d with _ -> ()) !created_stages;
    List.iter (fun d -> match (try Sys.readdir d with _ -> [||]) with
      | [||] -> (try Unix.rmdir d with _ -> ()) | _ -> ()) !created_parents in
  try
    (* (A.3-6) remove only marked, non-symlink, non-active stale stage directories *)
    List.iter (fun d ->
      if dir_has_marker d stage_marker stage_bytes && not (is_symlink d)
      then (try rm_rf d with _ -> fail "could not remove stale stage %s" d))
      (discover_stale_stages root);
    (* (B) desired set + existing generated .go files *)
    let targets = List.map (fun (rel, bytes) ->
      let parts = components rel in (Filename.concat root rel, parts, bytes)) entries in
    let desired = List.map (fun (t, _, _) -> t) targets in
    let existing_go = discover_owned_go root in
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
        | Some s -> s | None -> let s = make_stage parent 64 in Hashtbl.add stage_of parent s; s in
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
         | _ -> ()))          (* ownership changed → leave it, never delete foreign *)
      existing_go;
    (* (G) remove invocation stages, release lock, report success *)
    cleanup_stages ();
    Unix.close lock_fd;
    List.length targets
  with e ->
    cleanup_stages ();
    (try Unix.close lock_fd with _ -> ());
    raise e
