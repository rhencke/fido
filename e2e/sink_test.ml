(* A tiny standalone driver that exercises the dirty-directory sink (plugin/fido_sink.ml) directly, so
   the §17 filesystem algorithm can be tested against dirty/adversarial trees without the Rocq layer.
   It syncs a fixed one-file header-owned image into argv.(1).  An optional argv.(2) selects a fault, an
   input, or a boundary self-test, injected through the REAL algorithm via the sink's operation PARAMETERS
   (no ambient env branch):
     "fail-recovery-unlink" — [unlink] always fails, so recovery (its first unlink caller) aborts fail-loud;
     "crash-mid-staging"    — [after_stage] TERMINATES the process (Unix._exit) after the real staging code
                              creates a real temp: a true crash, no finalizer, the lock stays held;
     "reserved-path"        — the desired image targets a path inside the reserved .fido/ namespace;
     "selftest"             — boundary check of the sealed staging allocator, including the REAL stage_temp
                              allocation transition at max_int (uses argv.(1) as a scratch directory). *)
let header = "// fido generated.  do not edit."
let content = header ^ "\n\npackage main\n\nfunc main() {}\n"

module A = Fido_sink.Alloc

let () =
  let mode = if Array.length Sys.argv > 2 then Sys.argv.(2) else "" in
  if mode = "selftest" then begin
    let check name b = if not b then (prerr_endline ("sink_test: selftest FAILED: " ^ name); exit 1) in
    let raises f = try ignore (f ()); false with Fido_sink.Fail _ -> true in
    (* a negative cursor is UNCONSTRUCTIBLE, and recognition = exactly the emitted name language *)
    check "negative unconstructible"  (A.of_index (-1) = None);
    check "recognize -1"       (not (A.recognize "-1"));
    check "recognize empty"    (not (A.recognize ""));
    check "recognize 007"      (not (A.recognize "007"));
    check "recognize oversized"(not (A.recognize "99999999999999999999999999"));
    let get i = match A.of_index i with Some c -> c | None -> failwith "of_index" in
    let cmax = get max_int and cmax1 = get (max_int - 1) in
    check "recognize max_int"        (A.recognize (A.name cmax));
    check "next max_int-1 = max_int" (A.name (A.next cmax1) = A.name cmax);
    check "next max_int exhausts"    (raises (fun () -> A.next cmax));
    (* the REAL stage_temp allocation transition at the upper boundary: it EMITS the max_int file, then the
       next allocation fails (exhaustion) without wrapping, and recovery recognizes exactly that name. *)
    let scratch = Sys.argv.(1) in
    (try Unix.mkdir scratch 0o755 with _ -> ());
    let staging = Filename.concat scratch "staging" in
    (try Unix.mkdir staging 0o755 with _ -> ());
    let cursor = ref cmax in
    check "stage_temp at max_int emits then exhausts" (raises (fun () -> Fido_sink.stage_temp staging cursor content));
    check "max_int file really emitted" (Sys.file_exists (Filename.concat staging (A.name cmax)));
    print_string "sink_test: allocator selftest OK\n"
  end else begin
    let root = Sys.argv.(1) in
    let image = match mode with
      | "reserved-path" -> [ (".fido/staging/foo.go", content) ]
      | _ -> [ ("main.go", content) ] in
    let unlink p =
      if mode = "fail-recovery-unlink" then raise (Unix.Unix_error (Unix.EACCES, "unlink", p))
      else Unix.unlink p in
    let after_stage _ =
      if mode = "crash-mid-staging" then Unix._exit 137 in
    match (try `Ok (Fido_sink.sync ~unlink ~after_stage root image) with Fido_sink.Fail m -> `Fail m) with
    | `Ok n -> Printf.printf "sink_test: synced %d file(s) into %s\n" n root
    | `Fail m -> prerr_endline ("sink_test: refused: " ^ m); exit 1
  end
