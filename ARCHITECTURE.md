# Fido — Architecture Charter (binding)

Read before any structural change. This governs. The AST is the IR: there is **one** program
representation — an intrinsic `ModuleSpec` (module path + Go version) paired with a (possibly EMPTY)
verified finite map from intrinsic `FilePath` keys to one raw `GoFileAST` per file. `GoCompile`/`GoSafe`
are EVIDENCE and facts over that same program (never copies), the generated module file (`go.mod`) is
RENDERED in Rocq, and the only handwritten OCaml is the Fido Emit transport boundary (a term-decoding
bridge + a filesystem sink), which understands filesystems, not programs.

## The law of this repository

Ruthless correctness or ruthless deletion — no middle state. Incomplete scope is acceptable; incorrect,
approximate, duplicated, transitional, fail-open, or half-built foundations are not. Every retained
component must be complete and correct in itself and may build only on foundations that are already complete
and correct. Cut representable scope before weakening a proof. A green boolean checker is not a compile
authority; a printer's own inverse is not a Go-semantics theorem; a functional-lookup theorem is not proof
of key uniqueness; regex source scanning is not a sound zero-axiom gate; axiom-free is not correct.

## The pipeline

```
  GoProgram      the ONE program representation: { prog_module : ModuleSpec ; prog_files : fmap FilePath
                 GoFileAST } (FMap).  The file map MAY be EMPTY (a module-only program — a go.mod and no
                 packages).  Keys are unique BY CONSTRUCTION (a NoDup-keys proof — fm_keys_nodup); lookup is
                 deterministic; enumeration is finite; SEMANTIC equality is extensional-by-lookup
                 (fm_Equal), distinct from Rocq record =.  A GoFileAST is RAW top-level declarations only
                 (a list of GoDecl; today only DMain = a `func main()` decl).  It carries NO package clause,
                 entry-point flag, imports, symbols, or types — those are COMPILATION RESULTS.  The path is
                 the map KEY and is not stored in the file.

  ModuleSpec     an intrinsic fact about the GENERATED module (NOT environment config, NOT a TargetConfig):
                 { module_path : ModulePath ; module_go_version : GoVersion }.  ModulePath is an INTRINSIC
                 narrow canonical module path (slash-separated lowercase segments [a-z][a-z0-9.]* ending
                 a-z0-9, no `..`/leading-trailing/repeated slash, length-bounded; accepted by go 1.23 as a
                 `module` directive; invalid paths UNREPRESENTABLE).  GoVersion is a SINGLETON today
                 (Go1_23, renders exactly "1.23"); adding a later constructor is a reviewed semantic
                 milestone.  The exact compiler binary/toolchain pin is operational, off the theorems.

  FilePath       an INTRINSIC canonical relative source path (not a raw string): slash-separated
                 lowercase-ASCII directory components + an ordinary lowercase-ASCII `.go` basename, with
                 no empty/`.`/`..` component, no absolute/leading/trailing/repeated slash, no leading dot
                 or underscore (so no hidden/`_test`/`_GOOS` file, no control-name collision).  Every
                 representable path is safe to materialize (Linux/amd64 operational scope) AND discovered
                 by `go build ./...`.  Validity is a carried proof; equality is decidable.  (`go.mod` is
                 NOT a FilePath — a distinct root field carries it.)

  GoCompile      EXACT WHOLE-PROGRAM admissibility over the whole map, plus derived CompilationFacts.
                 Files are grouped by parent directory ([fp_parent]); each directory is one package; the
                 derived package name is `main`; every package has EXACTLY ONE `main` declaration (zero or
                 more than one rejects the WHOLE program); every declaration is integer-representable; one
                 invalid package rejects the whole program (all-or-nothing).  go_compile : GoProgram ->
                 result CompileError CompilableProgram, proved sound + complete against the declarative
                 judgment (prog_ok_iff).  CompilationFacts p carries the compiler-derived facts the
                 renderer consumes (today: the package clause name) — decorating the SAME program.

  GoSafe         the safety capability SafeProgram over CompilableProgram, plus a PER-FILE abstract
                 println-trace with REAL values (VBool/VInt Z).  GoSafe := True TODAY (the fragment has no
                 unsafe op), documented honestly; the PERMANENT extension point for guarantees beyond
                 compiler acceptance.  There is no whole-PROGRAM execution semantics yet (multi-package is
                 a compile-time concept — go build ./... — and only the witness package is executed vs
                 goldens); a per-package program semantics arrives when a construct needs it.

  GoRender       the direct renderer.  It renders each GoFileAST to bytes (the package clause from the
                 derived CompilationFacts name, each DMain as a `func main()`) AND renders the go.mod from
                 the ModuleSpec (`module <path>` + `go <version>`).  Every rendered file — go.mod and every
                 .go — begins with the exact header `// fido generated.  do not edit.` as its FIRST LINE.
                 Proved: all-ASCII; render_expr_denotes (the rendered primitive spelling denotes exactly its
                 value); decimal-faithful, no leading zero, header-first-line; go.mod exact bytes / header
                 first line / ASCII.

  DirectoryImage the COMPLETE module: exact root go.mod bytes (di_go_mod) + a finite map from FilePath to
                 exact final .go bytes (di_go_files), PROVENANCE-GATED: a value carries a proof BOTH came
                 from rendering ONE SafeProgram (di_prov).  A CLOSED proof witnesses that; but a proof can be
                 POSTULATED (axiom/variable), so the type alone is not sufficient — the live Fido Emit
                 boundary is the real gate (it rejects an assumption-dependent proof).  The .go map MAY be
                 empty; there is NO nonemptiness claim.  mkImage is public but demands the proof;
                 render_program is the canonical closed construction.  di_transport projects it to the
                 (exact go.mod bytes, (on-disk path, bytes) list) transport.

  Fido Emit      the ONE general transport command (a Rocq vernac): `Fido Emit <image-term> To "<root>"`.
                 Before ANY effect it guards provenance two ways: it typechecks its argument's di_transport
                 as a DirectoryImage projection (rejecting a raw transport), and it rejects any argument
                 whose assumption closure contains an axiom (rejecting a same-typed image built from a forged
                 proof).  Only then does it decode ONLY the final (go.mod bytes, (path, bytes) list)
                 transport (exact constructors of prod/list/string/ascii/bool, fail-loud otherwise) and hand
                 it to the sink.  Not witness-specific; no recompile for a different SafeProgram.

  sink           the generic ownership-aware dirty-directory synchronizer: it REJECTS foreign Go/module
                 inputs, then stages the complete image into random per-parent local dirs owned by
                 root-owned records and installs by atomic rename.  Filesystem ONLY.

  pinned Go      `go build ./...` over the WHOLE emitted tree + witness run.  Integration only.
```

**There is no second tree, no separate/typed/target/text IR, no tokenizer/lexer/parser, no
AST->output->AST round-trip authority, no copied compiled AST, no handwritten OCaml language semantics.**
`GoCompile` produces facts + a proof over the one `GoProgram`; the renderer traverses it directly.

## Two honest claims (never conflate)

- **(A) KERNEL-internal exactness — PROVED.** The executable `go_compile` succeeds exactly for the
  declarative `GoCompile` judgment (`prog_ok_iff`; sound + complete), and the renderer/semantics facts
  hold. Asserted axiom-free every build by `gate/axiom_gate.v`.
- **(B) EXTERNAL adequacy target — the GOAL, not a kernel theorem.** The declarative `GoCompile` judgment
  matches `go build ./...` acceptance for every representable rendered program. We model the acceptance
  semantics independently; `cmd/go` is used for DIFFERENTIAL experiments and the e2e, never as the formal
  decision procedure. A representable program `go build ./...` accepts but GoCompile rejects is a MODEL
  BUG (fix the model or narrow the representation), never a "permanent limitation"; a program GoCompile
  accepts but `go build ./...` rejects means no emission should have been possible — a correctness failure.

## Responsibility table (does / does NOT)

| Layer | Does | Does NOT |
|---|---|---|
| **FilePath** | the intrinsic canonical relative-path domain; decidable eq; `fp_parent` (package key); safe + `go build ./...`-discoverable by construction | admit raw strings, absolute/`..`/hidden/`_test`/GOOS-suffixed/non-`.go` paths |
| **FMap** | key-generic finite map; THE invariant `fm_keys_nodup`; `dup_key_unrepresentable`; deterministic `fm_MapsTo_fun` (distinct, weaker); `fm_Equal` (semantic eq ≠ record `=`) | present `fm_MapsTo_fun` as the uniqueness invariant; impose order; list+dedup |
| **ModuleSpec** | intrinsic module facts: narrow `ModulePath` (decidable eq, canonical render) + singleton `GoVersion` (Go1_23 → "1.23") | be a `TargetConfig`; carry GOOS/GOARCH/ABI/scheduler/point-release; admit an invalid module path (unrepresentable) |
| **GoAST** | `ModuleSpec` + a possibly-EMPTY program map + raw `GoDecl` (a `func main` form); key-uniqueness intrinsic | carry a package clause / entry flag / imports / a raw path in the file; a nonemptiness restriction; a second tree |
| **GoCompile** | whole-program directory→package + exactly-one-main + int-representability; `go_compile` sound/complete; populated `CompilationFacts` | be a boolean; accept per-file partially; hide package grouping / entry status in a raw node |
| **GoSafe** | real `GoValue`; abstract `eval_file`; `SafeProgram` (0 = -0); honest `GoSafe := True` | observe spelling as value; keep an unused panic placeholder; circularly reference compilation |
| **GoRender** | render decls + the derived package clause; render go.mod from the ModuleSpec; header exact first line (go.mod and .go); `render_expr_denotes` | tokenize/lex/parse/round-trip; deduce packages/entry; invoke a formatter; add require/replace/toolchain to go.mod |
| **DirectoryImage** | the complete module (exact go.mod bytes + a possibly-empty .go map), provenance-gated (`di_prov` proves BOTH came from `render_program`; `mkImage` demands that proof); `Fido Emit` typechecks its argument's `di_transport` AND rejects any argument with an axiomatic assumption closure | be an arbitrary-map escape that bypasses SafeProgram; invent go.mod in the sink; make a nonemptiness claim; accept a raw transport, or a same-typed image built from a forged (axiomatic) proof, at the emit boundary |
| **Fido Emit + sink** | a four-step boundary — typecheck the image, reject a non-empty assumption closure (kernel provenance queries), decode ONLY the final (go.mod, entries) transport with exact constructors, then a foreign-Go-rejecting local-staging dirty-directory sync | inspect the program/AST/behaviour/semantics; emit without both provenance guards; merge/preserve a foreign `.go`/`go.mod`; delete/overwrite/follow foreign state |

## The handwritten-OCaml boundary (hard)

**All semantic work is proved Rocq.** The ONLY handwritten OCaml is the Fido Emit TRANSPORT boundary:
- `plugin/g_fido.mlg` — the transport bridge, a four-step boundary: (1) typecheck the argument's
  `di_transport` projection as the certified image type; (2) reject a non-empty assumption closure (a kernel
  provenance query that descends Qed proof bodies — the SAME `closure_assums`/`assums_disallowed` mechanism
  the whole-theory audit uses); (3) reduce and STRUCTURALLY decode ONLY the final `string * list
  (string*string)` transport — the exact go.mod bytes and the (path, bytes) list (exact constructors,
  fail-loud); (4) call the sink. It does no semantic program/AST/behaviour inspection. That both provenance
  guards stay live is a mutation-sensitive REGRESSION gate, not a proof: the emit stage's negative fixtures
  (a raw transport + TRANSIENTLY-generated axiom/variable-backed images) execute forged inputs and, if
  either guard were removed, the corresponding `Fido Emit` would succeed and create a target — failing the
  e2e (a spoofable source grep would not).
- `plugin/fido_sink.ml` + `e2e/sink_test.ml` — the generic dirty-directory synchronizer + its driver.
  Filesystem ONLY: they walk no Rocq terms.

`tools/ocaml-origin-gate.sh` enforces exactly these three files, filesystem-only for the sink,
transport-only for the bridge, bounded sizes, and no deleted-backend hallmarks. **Never reintroduce a
handwritten OCaml backend / lowering / renderer / semantic decoder, or a bridge that decodes anything but
the final transport type.** If the transport boundary cannot be met correctly, delete the e2e — a false
transport foundation is worse than no integration.

### Dirty-directory synchronization (honest guarantee)

`GoCompile`, `GoSafe`, and DirectoryImage production are whole-program ALL-OR-NOTHING. Installation into an
existing dirty tree is locked (a persistent `<root>/.fido/` control dir with an exact marker + a git-style
`index.lock`). Before any effect the sink (generic over raw strings, so it trusts no caller) VALIDATES the
`root` (every proper ancestor must be an existing real directory — a symlink in ANY prefix component is
rejected, else ordinary resolution would follow it and redirect all effects) and REJECTS a desired path
inside the RESERVED `<root>/.fido/` namespace.

**Foreign Go/module inputs REJECT the whole emission** (fail-closed scan, before any generated-file
mutation): any foreign `.go` anywhere beneath root (a regular file whose first line is not the header, or a
`.go` symlink/nonregular entry), a foreign root `go.mod`, a `go.mod` symlink, or any nested `go.mod`. A
dirty foreign Go input would silently change what `go build ./...` compiles, so it is not preserved-and-
merged — it aborts. Foreign NON-Go files/dirs are preserved. Installed `.go` files and the root `go.mod`
are Fido-owned iff their first line is the exact header AND they are regular non-symlink files (rechecked
by lstat immediately before every overwrite/delete; a symlink is S_LNK, never S_REG, so never followed); a
foreign `.go`/`go.mod` forging the header is the accepted limit (a header is public).

**Local staging (no central staging dir).** `<root>/.fido/` holds the marker, the lock, and
`stage-records/` (durable ownership records ONLY, never payloads). For each distinct final PARENT directory
receiving desired files (root for `go.mod` and root-level `.go`; a subdir for a nested `.go`) the sink
creates ONE local stage `<parent>/.fido-stage-<nonce>` with a high-entropy OS nonce (`/dev/urandom`, never
OCaml `Random`). A stage is owned by a ROOT-OWNED RECORD, never by name/marker/header: the record is
created atomically (`O_CREAT|O_EXCL`) and completely written BEFORE its stage directory, and removed only
AFTER the stage directory is gone. The sink stages the COMPLETE image (go.mod + every .go) before any
install, then installs each file by rename from its sibling stage — same filesystem, so nested mount points
inside root are supported without a central cross-device compare; EXDEV fails loud with no copy fallback.
Only then are stale Fido-owned `.go` files (owned, not desired) removed (the empty program removes them
all, keeping/updating the owned go.mod).

**Fail-closed.** Only a confirmed `ENOENT` means "missing"; every other filesystem error aborts. RECOVERY
runs first and is RECORD-DRIVEN (never a name scan): each record is parsed strictly and validated (version,
nonce = filename, canonical stage path under root, matching parent); a confirmed-missing stage → the stale
record is removed; a real non-symlink stage dir → removed recursively without following symlinks, then the
record; a symlink/file/inconsistent recorded stage → abort and preserve. A foreign lookalike
`.fido-stage-*` without a valid record is never treated as owned. A handled failure cleans this run's
stages/records/newly-empty parents immediately, aggregates body + cleanup + lock-release errors, and
releases the lock. It is **NOT** a transactional whole-tree commit; residue remains only after an
uncatchable CRASH or a cleanup/lock-release failure — the next run recovers it (record-driven) before any
generated-file mutation. It is **NOT** hardened against a concurrent non-cooperating process (this OCaml
`Unix` exposes no `openat`/`O_NOFOLLOW`); the honest model is COOPERATING emitters serialized by the lock,
in the Linux/amd64 operational scope. Ownership is by header + regular-file + desired-key-set, never
timestamps or a manifest. Git is a recovery backstop, not the primary safety mechanism.

**The exact guarantee.** *GoProgram acceptance, SafeProgram certification, and DirectoryImage creation are
semantically all-or-nothing. Dirty-directory installation is locked for cooperating emitters, rejects
foreign Go/module inputs, stages the complete image locally beside target parents before installation, uses
per-file atomic rename in the ordinary same-filesystem case, cleans handled-failure residue immediately,
recovers record-owned abandoned local stages before future mutation, and converges on rerun. It is not a
portable transactional multi-file filesystem commit and is not hardened against malicious concurrent
filesystem mutation.*

## Closed world

Imports are absent now, so the derived import set is empty for every file, and import syntax is
UNREPRESENTABLE. **Permanent contract:** when import declarations are added, `GoCompile` must resolve every
import to an owned package derived from the SAME `GoProgram`; any unresolved or external import rejects the
whole program. No package may come from the standard library, module cache, network, vendor tree,
workspace, or ambient filesystem unless a later reviewed foundation explicitly and completely models that
source.

## Growing the language

Every new AST constructor enters only when it has, COMPLETE at that time: exact whole-program `GoCompile`
rules matching `go build ./...` (constructor absent otherwise), exact operational meaning in `GoSafe`,
renderer support with its value/syntax proofs, and — where observable — a differential fixture + e2e
witness. Shrink the representable language before weakening `GoCompile`. Package clauses / entry status /
imports are compilation results, never raw metadata. Integer width has one authority (`Ints`, 64-bit);
there is no `TargetConfig`.

## Trust base (say it exactly)

Trusted: Rocq and its kernel; the digest-pinned Docker/Go images plus the opam-repo state and apt packages;
the Fido Emit **transport boundary** (the bridge typechecks the image type and rejects an axiomatic
assumption closure — both via Rocq's own kernel/assumptions machinery — then decodes only the final
transport constructors; the sink is filesystem-only — all trusted-not-proved); and the Go toolchain
(claim (B), the `go build ./...` adequacy, is exercised differentially by the e2e, not proved). Proved (axiom-free, asserted every build by
`gate/axiom_gate.v` PLUS the Rocq-native `Fido Audit Assumptions` command — a whole-certified-theory
assumption-closure audit that catches an external axiom reached transitively through any internal/opaque
lemma, and any unused Fido axiom): the Ints boundary values; ModulePath decidable eq + representable/
unrepresentable module-path fixtures; GoVersion's exact "1.23" rendering; FilePath decidable eq +
representable/unrepresentable path fixtures; FMap's key-NoDup invariant + duplicate-key unconstructibility +
deterministic lookup; GoCompile claim (A) — `prog_ok_iff`, `go_compile` sound + complete, rejection ⇒ no
CompilableProgram; GoSafe's zero-sign-agnostic fact; GoRender's `render_expr_denotes` + all-ASCII +
decimal-faithful + no-leading-zero + header-first-line + boundaries + the exact go.mod render (bytes /
header first line / ASCII); DirectoryImage's go.mod-and-.go header-first-line / ASCII / unique-paths over
EVERY image (NO nonemptiness claim — the empty program is valid). "No assumptions" is never evidence a
theorem's STATEMENT is right — the gated invariant must be the one advertised.

## What must never come back

A handwritten OCaml backend / lowering / renderer / semantic decoder, or a bridge decoding anything but the
final transport type; a SECOND program-AST hierarchy, a raw `GoPackage` tree, or a copied compiled AST;
package/import metadata in raw file values; `MainFile` (package/main/entry collapsed into one raw node);
raw `string` map keys; a nonemptiness restriction on the program/image; a handwritten `go.mod` (it is
RENDERED in Rocq) or `go.mod` smuggled into the FilePath map; central `<root>/.fido/staging/` or a
central cross-device rejection (staging is LOCAL, per-parent, record-owned); a foreign `.go`/`go.mod`
preserved-and-merged into the built tree; handled-failure residue left deliberately for the next run;
a `Undef`-body-only axiom check posing as a whole-theory audit; tracked axiom-bearing fixtures; `go vet`
as a blocking acceptance gate; single-file compiler semantics or a subset filter posing as compiler
admissibility; a witness-specific extracted emit executable or a hard-coded `main.go` Docker copy; a
fail-open regex axiom scanner; timestamps/manifests as ownership authority; a claimed transactional
whole-directory guarantee; a `TargetConfig`; a lexer/parser/tokenizer/round-trip/text-IR/target-IR in the
certified path; fuel. Git carries the history; re-admit a feature only when the roots make its proof
obligations natural.
