(* The ONLY handwritten OCaml: a filesystem exhaust pipe.  It receives the Rocq-computed,
   Rocq-extracted final image (relative path * exact contents) and writes it — atomically via a
   staging directory + rename.  It decodes nothing, chooses nothing, understands no program. *)

let write_file dir (rel, contents) =
  let oc = open_out_bin (Filename.concat dir rel) in
  output_string oc contents;
  close_out oc

let () =
  let dest = Sys.argv.(1) in
  let stage = dest ^ ".staging" in
  Unix.mkdir stage 0o755;
  List.iter (write_file stage) Emit_out.demo_pairs;
  Sys.rename stage dest
