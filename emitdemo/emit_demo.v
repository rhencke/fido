(** Extraction driver for `make emit-demo` (NOT part of the Fido dune theory — it lives in this subdir, so
    dune never compiles it; `make emit-demo` compiles it standalone).  It extracts the CERTIFIED program text
    [GoEmit.demo_emit] (= [emit_supported demo_cert]; its exact bytes are machine-checked by
    [GoEmit.demo_emit_bytes]) to OCaml as a NATIVE string, so a tiny writer ([write_emit.ml]) can emit the
    actual `spine_demo.go` and the Go toolchain (gofmt + go build + go vet) can confirm the blessed emitter's output is
    real, accepted Go — the end-to-end check connecting the proven bytes to the Go compiler. *)
From Fido Require Import GoEmit.
From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlNativeString.   (* Coq [string] -> OCaml native [string] *)
Extraction Language OCaml.
Set Extraction Output Directory "emitdemo".
Extraction "emit_demo.ml" GoEmit.demo_emit.
