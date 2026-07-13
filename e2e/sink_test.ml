(* A tiny standalone driver that exercises the dirty-directory sink (plugin/fido_sink.ml) directly, so the
   local-staging / record-recovery / foreign-rejection algorithm can be tested against dirty/adversarial
   trees without the Rocq layer.  It syncs a fixed module image (a go.mod whose first line is the exact
   ownership header, plus zero or more .go files) into argv.(1) and, on success, verifies each installed
   file equals — byte for byte — the very bytes it handed the sink (no duplicate expected-bytes authority).
   An optional argv.(2) selects the image shape and/or a fault, injected through the REAL algorithm via the
   sink's operation PARAMETERS (no ambient env branch):
     "empty"    — an EMPTY source map (go.mod only): the module-only program;
     "multi"    — files in two parents (root main.go + sub/main.go): two local stages;
     "reserved" — a desired .go inside the reserved .fido/ namespace (rejected before any effect);
     "collide"  — a FIXED nonce, so a pre-seeded record/stage forces the collision/retry path;
     "unlink-fail"           — [unlink] always fails (recovery / cleanup / stale-removal failure);
     "exdev"                 — [rename] raises EXDEV (a cross-device install must fail loud, no copy fallback);
     "foreign-before-install" — [before_install] makes the target foreign right before its ownership recheck
                  (an overwrite race): the recheck must abort rather than overwrite;
     "foreign-before-delete" — [before_delete] makes a stale owned .go foreign right before its stale-delete
                  recheck (a deletion race): the recheck must NOT delete the now-foreign file;
     "fail-write-sub"        — [before_write] raises a HANDLED failure at a LATER stage (the sub/ file):
                  cleanup must run immediately and leave prior FINAL files untouched;
     "fail-after-first-payload" — [checkpoint] raises a HANDLED failure after the first staged file: cleanup
                  must run immediately and leave prior FINAL files untouched;
     "crash-after-record" / "crash-after-mkdir" / "crash-after-first-payload" / "crash-after-staging"
                — [checkpoint] TERMINATES the process (Unix._exit) at that exact point: a true crash, no
                  finalizer, the lock stays held, and record/stage residue is left for the next run. *)
let header = "// fido generated.  do not edit."
let go_mod = header ^ "\n\nmodule fido.local/generated\n\ngo 1.23\n"
(* distinctive, binary-sensitive .go bytes (control chars + tab, no final newline) with the header first
   line so the byte-equality check catches any transformation.  These dirs are never go-built. *)
let mk tag = header ^ "\n\npackage main\n\nfunc main() {}\n// " ^ tag ^ " \001\002\003\tend"

let read_all path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in close_in ic; s

let () =
  let root = Sys.argv.(1) in
  (* argv.(2) = the image selector; argv.(3) (if present) = the fault selector, else the same token does
     both — so `sink_test dir multi crash-after-staging` freezes a multi image at a fault point. *)
  let image = if Array.length Sys.argv > 2 then Sys.argv.(2) else "" in
  (* argv.(3) may be a '+'-separated set of faults (e.g. "fail-after-staging+unlink-fail") applied together *)
  let faults = String.split_on_char '+' (if Array.length Sys.argv > 3 then Sys.argv.(3) else image) in
  let has f = List.mem f faults in
  let entries = match image with
    | "empty"    -> []
    | "multi"    -> [ ("main.go", mk "ROOT"); ("sub/main.go", mk "SUB") ]
    | "reserved" -> [ (".fido/x.go", mk "X") ]
    | _          -> [ ("main.go", mk "ROOT") ] in
  let rand_hex =
    if has "collide" then (fun _ -> "00112233445566778899aabbccddeeff")   (* fixed → forces collision *)
    else Fido_sink.default_rand_hex in
  let checkpoint label =
    if has ("crash-" ^ label) then
      (Printf.eprintf "sink_test: crashing at %s\n%!" label; Unix._exit 137)
    else if has ("fail-" ^ label) then
      raise (Fido_sink.Fail ("injected handled failure at " ^ label)) in
  let unlink =
    if has "unlink-fail" then (fun p -> raise (Unix.Unix_error (Unix.EACCES, "unlink", p)))
    else Unix.unlink in
  let rename src dst =
    if has "exdev" then raise (Unix.Unix_error (Unix.EXDEV, "rename", dst)) else Unix.rename src dst in
  let make_foreign p = let oc = open_out_bin p in output_string oc "FOREIGN not a fido file\n"; close_out oc in
  let has_sub p =                                (* plain substring search for "/sub/" — no Str dependency *)
    let n = String.length p and m = 5 in
    let rec go i = i + m <= n && (String.sub p i m = "/sub/" || go (i + 1)) in go 0 in
  let before_install target =
    if has "foreign-before-install" && Filename.basename target = "main.go" then make_foreign target in
  let before_write sp =
    if has "fail-write-sub" && has_sub sp then raise (Fido_sink.Fail "injected later-stage write failure") in
  let before_delete p =
    if has "foreign-before-delete" && has_sub p then make_foreign p in
  match (try `Ok (Fido_sink.sync ~rand_hex ~checkpoint ~unlink ~rename ~before_install ~before_write
                    ~before_delete root go_mod entries)
         with Fido_sink.Fail m -> `Fail m) with
  | `Ok n ->
    let check rel bytes =
      let inst = read_all (Filename.concat root rel) in
      if inst <> bytes then
        (Printf.eprintf "sink_test: %s installed %d bytes != staged %d bytes (byte mismatch)\n"
           rel (String.length inst) (String.length bytes); exit 1) in
    check "go.mod" go_mod;
    List.iter (fun (rel, bytes) -> check rel bytes) entries;
    Printf.printf "sink_test: synced %d file(s) into %s\n" n root
  | `Fail m -> prerr_endline ("sink_test: refused: " ^ m); exit 1
