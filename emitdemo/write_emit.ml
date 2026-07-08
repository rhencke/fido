(* Writes the certified emitter's output to spine_demo.go.  [Emit_demo.demo_emit] is the OCaml extraction of
   GoEmit.demo_emit (= emit_compiled demo_cert); its bytes are exactly GoEmit.demo_emit_bytes, machine-checked
   in GoEmit.v.  Run by `make emit-demo` from the repo root; the produced file is then validated with the Go
   toolchain (gofmt + go build + go vet). *)
let () =
  let oc = open_out "emitdemo/spine_demo.go" in
  output_string oc Emit_demo.demo_emit;
  close_out oc
