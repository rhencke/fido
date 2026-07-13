# Fido — Architecture Charter (binding)

Read before any structural change. This governs. The AST is the IR: there is **one** program
representation — a nonempty verified finite map from intrinsic `FilePath` keys to one raw `GoFileAST`
per file. `GoCompile`/`GoSafe` are EVIDENCE and facts over that same program (never copies), and the only
handwritten OCaml is the Fido Emit transport boundary (a term-decoding bridge + a filesystem sink), which
understands filesystems, not programs.

## The law of this repository

Ruthless correctness or ruthless deletion — no middle state. Incomplete scope is acceptable; incorrect,
approximate, duplicated, transitional, fail-open, or half-built foundations are not. Every retained
component must be complete and correct in itself and may build only on foundations that are already complete
and correct. Cut representable scope before weakening a proof. A green boolean checker is not a compile
authority; a printer's own inverse is not a Go-semantics theorem; a functional-lookup theorem is not proof
of key uniqueness; regex source scanning is not a sound zero-axiom gate; axiom-free is not correct.

## The pipeline

```
  GoProgram      the ONE program representation: a NONEMPTY finite map fmap FilePath GoFileAST (FMap).
                 Keys are unique BY CONSTRUCTION (a NoDup-keys proof — fm_keys_nodup); lookup is
                 deterministic; enumeration is finite; SEMANTIC equality is extensional-by-lookup
                 (fm_Equal), distinct from Rocq record =; nonempty is intrinsic.  A GoFileAST is RAW
                 top-level declarations only (a list of GoDecl; today only DMain = a `func main()` decl).
                 It carries NO package clause, entry-point flag, imports, symbols, or types — those are
                 COMPILATION RESULTS.  The path is the map KEY and is not stored in the file.

  FilePath       an INTRINSIC canonical relative source path (not a raw string): slash-separated
                 lowercase-ASCII directory components + an ordinary lowercase-ASCII `.go` basename, with
                 no empty/`.`/`..` component, no absolute/leading/trailing/repeated slash, no leading dot
                 or underscore (so no hidden/`_test`/`_GOOS` file, no control-name collision).  Every
                 representable path is safe to materialize AND discovered by `go build ./...` on any
                 target.  Validity is a carried proof; equality is decidable.

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

  GoRender       the direct GoFileAST -> bytes renderer.  It emits the package clause from the derived
                 CompilationFacts name and each DMain as a `func main()`.  Every file begins with the
                 exact header `// fido generated.  do not edit.` as its FIRST LINE.  Proved: all-ASCII;
                 render_expr_denotes (the rendered primitive spelling denotes exactly its value);
                 decimal-faithful, no leading zero, header-first-line.

  DirectoryImage a complete finite map from FilePath to exact final bytes, PROVENANCE-GATED: a value
                 carries a proof it came from rendering a SafeProgram (di_prov).  A CLOSED proof witnesses
                 that; but a proof can be POSTULATED (axiom/variable), so the type alone is not sufficient —
                 the live Fido Emit boundary is the real gate (it rejects an assumption-dependent proof).
                 mkImage is public but demands the proof; render_program is the canonical closed
                 construction.  directory_entries projects it to the (on-disk path, bytes) transport list.

  Fido Emit      the ONE general transport command (a Rocq vernac): `Fido Emit <image-term> To "<root>"`.
                 Before ANY effect it guards provenance two ways: it typechecks its argument as a
                 DirectoryImage (rejecting a raw transport), and it rejects any argument whose assumption
                 closure contains an axiom (rejecting a same-typed image built from a forged proof).  Only
                 then does it decode ONLY the final (path, bytes) transport data (exact constructors of
                 list/prod/string/ascii/bool, fail-loud otherwise) and hand it to the sink.  Not
                 witness-specific; no recompile for a different SafeProgram.

  sink           the generic ownership-aware dirty-directory filesystem synchronizer.  Filesystem ONLY.

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
| **GoAST** | the nonempty program map + raw `GoDecl` (a `func main` form); nonempty/uniqueness intrinsic | carry a package clause / entry flag / imports / a raw path in the file; a second tree |
| **GoCompile** | whole-program directory→package + exactly-one-main + int-representability; `go_compile` sound/complete; populated `CompilationFacts` | be a boolean; accept per-file partially; hide package grouping / entry status in a raw node |
| **GoSafe** | real `GoValue`; abstract `eval_file`; `SafeProgram` (0 = -0); honest `GoSafe := True` | observe spelling as value; keep an unused panic placeholder; circularly reference compilation |
| **GoRender** | render decls + the derived package clause; header exact first line; `render_expr_denotes` | tokenize/lex/parse/round-trip; deduce packages/entry; invoke a formatter |
| **DirectoryImage** | complete finite map, provenance-gated (`di_prov` proves it came from `render_program`; `mkImage` demands that proof); `Fido Emit` typechecks its argument as a `DirectoryImage` AND rejects any argument with an axiomatic assumption closure | be an arbitrary-map escape that bypasses SafeProgram; accept a raw transport list, or a same-typed image built from a forged (axiomatic) proof, at the emit boundary |
| **Fido Emit + sink** | a four-step boundary — typecheck the image, reject a non-empty assumption closure (kernel provenance queries), decode ONLY final (path, bytes) with exact constructors, then ownership-aware dirty-directory sync | inspect the program/AST/behaviour/semantics; emit without both provenance guards; delete/overwrite/follow foreign state |

## The handwritten-OCaml boundary (hard)

**All semantic work is proved Rocq.** The ONLY handwritten OCaml is the Fido Emit TRANSPORT boundary:
- `plugin/g_fido.mlg` — the transport bridge, a four-step boundary: (1) typecheck the argument as the
  certified image type; (2) reject a non-empty assumption closure (a kernel provenance query that descends
  Qed proof bodies); (3) reduce and STRUCTURALLY decode ONLY the final `list (string*string)` (exact
  constructors, fail-loud); (4) call the sink. It does no semantic program/AST/behaviour inspection. That
  both provenance guards stay live is a mutation-sensitive REGRESSION gate, not a proof: the emit stage's
  negative fixtures execute forged inputs and, if either guard were removed, the corresponding `Fido Emit`
  would succeed and create a target — failing the e2e (a spoofable source grep would not).
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
`index.lock`). There are TWO DISTINCT ownership authorities for two distinct concerns. INSTALLED `.go`:
a regular file in the tree is Fido-owned iff its first line is the exact header; ownership is rechecked
immediately before every overwrite/delete, always via lstat (a symlink is S_LNK, never S_REG, so it is
never followed/read/removed); foreign files/dirs/symlinks are preserved. TRANSIENT staging: everything
inside the STRUCTURED namespace `<root>/.fido/staging/` is Fido-owned BY LOCATION (it lives inside the
marked control dir), which is unforgeable (a foreign lookalike anywhere in the tree is never in that
namespace) and ATOMIC (a partially written temp is already owned by being there, so no crash prefix can
orphan it). Staging writes each target's bytes to a fresh `<root>/.fido/staging/<seq>` created
O_CREAT|O_EXCL, then atomically renames it into place; because a rename is atomic only within one
filesystem, the preflight REJECTS (before any effect) a target whose nearest existing ancestor is on a
different device than `staging/`. RECOVERY runs FIRST and is recover-all-or-**REJECT**: it removes every
entry in `staging/` (all ours, by location, whatever the bytes) and is fail-CLOSED — any enumeration/lstat/
removal error other than a confirmed `ENOENT` aborts before any synchronization effect; it never scans the
tree, so a foreign file (even one forging the header) is untouched. The FINALIZER's sole obligation is
releasing the lock (close + unlink), fail-loud and exactly once, combining a body error with a lock-release
error (never hiding either). It is **NOT** a transactional whole-tree commit — a partial run may install
some targets and leave owned temps in `staging/`, which the next run removes. NORMAL completion (success or
a handled body failure, including a recovery failure) runs the finalizer and releases the lock, so an
immediate rerun can proceed; a CRASH (process killed, finalizer not run) or a failure of the lock release
itself leaves the `index.lock`, and the next run REFUSES until it is deliberately removed. It is **NOT**
hardened against a concurrent non-cooperating process (this OCaml `Unix` exposes no `openat`/`O_NOFOLLOW`);
the honest model is cooperating emitters that preserve pre-existing foreign state (a foreign `.go` forging
the exact header is indistinguishable — the accepted limit of header ownership, which is why transient
staging uses location, not the header). Installed-`.go` ownership is by header + desired-key-set, never
timestamps or a manifest.
Git is a recovery backstop, not the primary safety mechanism.

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
`gate/axiom_gate.v`): the Ints boundary values; FilePath decidable eq + representable/unrepresentable path
fixtures; FMap's key-NoDup invariant + duplicate-key unconstructibility + deterministic lookup; GoCompile
claim (A) — `prog_ok_iff`, `go_compile` sound + complete, rejection ⇒ no CompilableProgram; GoSafe's
zero-sign-agnostic fact; GoRender's `render_expr_denotes` + all-ASCII + decimal-faithful + no-leading-zero +
header-first-line + boundaries; DirectoryImage's header-first-line / ASCII / nonempty / unique-paths over
EVERY image. "No assumptions" is never evidence a theorem's STATEMENT is right — the gated invariant must be
the one advertised.

## What must never come back

A handwritten OCaml backend / lowering / renderer / semantic decoder, or a bridge decoding anything but the
final transport type; a SECOND program-AST hierarchy, a raw `GoPackage` tree, or a copied compiled AST;
package/import metadata in raw file values; `MainFile` (package/main/entry collapsed into one raw node);
raw `string` map keys; single-file compiler semantics or a subset filter posing as compiler admissibility;
a witness-specific extracted emit executable or a hard-coded `main.go` Docker copy; a fail-open regex axiom
scanner; timestamps/manifests as ownership authority; a claimed transactional whole-directory guarantee; a
`TargetConfig`; a lexer/parser/tokenizer/round-trip/text-IR/target-IR in the certified path; fuel. Git
carries the history; re-admit a feature only when the roots make its proof obligations natural.
