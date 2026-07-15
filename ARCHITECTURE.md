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

**Binding contract, not advisory plan.** The current `.review/NEXT_STEPS.md` is binding for the active
milestone. If an objective defect cannot be repaired without changing its architecture, scope, guarantees,
threat model, responsibility boundaries, or selected algorithm, report an architectural conflict and stop.
Do not implement an alternative autonomously.

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
                 a-z0-9, no `..`/leading-trailing/repeated slash, length-bounded; FIRST element dotted (no
                 stdlib-colliding dotless prefix), NO `/vN` version-suffix tail, NO `gopkg.in/` — the two
                 Go-1.23 semantic-import-versioning reject classes; accepted by go 1.23 as a `module`
                 directive, exact one-way (valid `/v2`/gopkg modules are out of scope, excluded not narrowed);
                 invalid paths UNREPRESENTABLE).  GoVersion is a SINGLETON today
                 (Go1_23, renders exactly "1.23"); adding a later constructor is a reviewed semantic
                 milestone.  The exact compiler binary/toolchain pin is operational, off the theorems.

  FilePath       an INTRINSIC canonical relative source path (not a raw string): slash-separated
                 lowercase-ASCII directory components + an ordinary lowercase-ASCII `.go` basename, with
                 no empty/`.`/`..` component, no absolute/leading/trailing/repeated slash, no leading dot
                 or underscore (so no hidden/`_test`/`_GOOS` file, no control-name collision).  Every
                 representable path is safe to materialize (Linux/amd64 operational scope) AND discovered
                 by `go build ./...`.  Validity is a carried proof; equality is decidable.  (`go.mod` is
                 NOT a FilePath — a distinct root field carries it.)

  GoTypes        the ONE Go type-system authority — EVIDENCE over the raw GoAST, never a typed AST.  The
                 permanent type universe is EXACTLY { TBool, the integer family TInteger over the ten-member IntegerType, TFloat FloatType, TString }.  A raw literal denotes an EXACT
                 UNTYPED constant (GoConst := CBool bool | CInt Z | CFloat FloatConst | CString string — ints
                 arbitrary-precision, a bare float literal (EFloat) an EXACT canonical rational, strings exact
                 byte sequences) via the PARTIAL const_value (option GoConst): a bare literal is exact (a bare
                 float UNROUNDED) and a conversion routes through convert_const;
                 convert_const : GoType -> GoConst -> option GoConst is the ONE conversion authority (int←int
                 value-preserving + range-checked; int←float exact-integral + in-range; float←int/float rounds
                 ONCE at the destination; bool/string reject).  An EXPLICIT integer conversion (EIntConvert it e)
                 routes through it, yielding a value-preserving TYPED constant of the destination IntegerType,
                 repr-checked at EVERY nesting layer; a float conversion (EFloatConvert ft e) yields a TYPED
                 constant ROUNDED ONCE at the destination FloatType (F32 rounds DIRECTLY at binary32, never via
                 F64 — the double-round scar) (const_info — the untyped/typed constant-status analyzer).  A USE
                 CONTEXT (today UsePrintlnArg) resolves an UNTYPED constant by a DEFAULT TYPE (const_default_type
                 — an int defaults to TInteger IInt, a float to TFloat F64) and CHECKS
                 REPRESENTABILITY (ConstRepresentable — the PER-TYPE inclusive-range decision over the Ints
                 authority), while a TYPED constant keeps its own type + value and is TRUSTED (already validated
                 by convert_const, not re-defaulted).  ResolveExpr
                 u e t (reflected by resolve_expr, sound + complete + deterministic) is the resolved typing of
                 one expression; StmtTyped/DeclTyped/FileTyped/ProgramTyped lift it to the whole program (the
                 EMPTY file map is typed vacuously).  There is NO placeholder/unknown/raw type, NO second
                 numeric-width authority, and NO typed AST.

  GoCompile      EXACT WHOLE-PROGRAM admissibility over the whole map, plus derived CompilationFacts.
                 Files are grouped by parent directory ([fp_parent]); each directory is one package; the
                 derived package name is `main`; every package has EXACTLY ONE `main` declaration (zero or
                 more than one rejects the WHOLE program); the whole program is TYPED through GoTypes
                 (ProgramTyped — every println argument resolves; a typing failure is a constant fitting no
                 integer type, a non-integer conversion operand, or an invalid nested conversion, reported by
                 the honest ErrTyping); one invalid package rejects the whole program (all-or-nothing).
                 go_compile : GoProgram -> result CompileError CompilableProgram, proved
                 sound + complete against the declarative judgment (prog_ok_iff).  CompilationFacts p
                 carries the compiler-derived facts the renderer consumes (today: the package clause name)
                 and EXPOSES that the same p is typed via a canonical projection (compilable_program_typed),
                 not a stored typed copy — decorating the SAME program.

  GoSafe         the safety capability SafeProgram over CompilableProgram, plus a PER-FILE abstract
                 println-trace with REAL values (VBool/VInteger IntegerType Z/VFloat ft (FloatValue ft)/VString exact bytes; evaluation is PARTIAL, derived from const_info).  Runtime values use the SAME GoType
                 authority (value_type — VFloat ft carries TFloat ft) and are range-well-formed (ValueWF; a
                 FloatValue is a PROOF-CARRYING canonical Stdlib SpecFloat.spec_float — the image of the format
                 normalizer, future-compatible with finite/±0/inf/NaN, Flocq NOT used — so ValueWF(VFloat) := True
                 with canonicality in the type, and constant eval produces only finite/+0); evaluation is DERIVED from the one
                 constant-status analysis (const_info) and is PARTIAL (a compiler-invalid conversion has no
                 value — never a wrap), so a resolved expression evaluates to a well-formed value of its
                 resolved GoType (eval_expr_resolved).  GoSafe := True TODAY (the fragment has
                 no unsafe op), documented honestly; the PERMANENT extension point for guarantees beyond
                 compiler acceptance.  There is no whole-PROGRAM execution semantics yet (multi-package is
                 a compile-time concept — go build ./... — and only the witness package is executed vs
                 goldens); a per-package program semantics arrives when a construct needs it.

  GoRender       the direct renderer.  It renders each GoFileAST to bytes (the package clause from the
                 derived CompilationFacts name, each DMain as a `func main()`) AND renders the go.mod from
                 the ModuleSpec (`module <path>` + `go <version>`).  Every rendered file — go.mod and every
                 .go — begins with the exact header `// fido generated.  do not edit.` as its FIRST LINE.
                 An integer conversion renders as `<integer_keyword it>(<inner>)` (the exact Go keyword of each
                 of the ten IntegerType members) and a float conversion as `float32(<inner>)`/`float64(<inner>)`;
                 a float constant renders by ONE canonical decimal spelling (zero → `0.0`; nonzero →
                 `<signed-coeff>.0e<±exp>`) paired with an INDEPENDENT decoder proving `decode(render d) = Some d`
                 (the exact rational round trip).  Proved: all-ASCII (keywords + conversions included);
                 render_const_info_denotes (rendering an expression denotes exactly the ConstInfo GoTypes computes — a bare
                 integer/float is UNTYPED, an explicit conversion is a typed constant routed through convert_const —
                 via the ONE RenderedConstInfoDenotes relation, now with float cases), and that relation is FUNCTIONAL
                 (render_const_info_denotes_functional: a spelling denotes AT MOST ONE ConstInfo — the six recognisers
                 are pairwise disjoint, so no spelling carries two conflicting constant statuses);
                 render_resolved_expr_denotes (a resolved argument EVALUATES to a well-formed value of its
                 resolved GoType whose spelling denotes it — tying the three authorities); decimal-faithful, no
                 leading zero, header-first-line; go.mod exact bytes / header first line / ASCII.

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
                 inputs + nested .fido, then stages the complete image into reserved sibling temps
                 `<final>.fido-tmp-v1` and installs by atomic rename (two-phase recovery).  Filesystem ONLY.

  pinned Go      `go build ./...` over the WHOLE canonical `generated-module` tree + witness run.
                 Integration only.
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
| **GoAST** | `ModuleSpec` + a possibly-EMPTY program map + raw `GoDecl` (a `func main` form) over `EBool`/`EInt`/`ENeg`/`EString`/`EIntConvert` (explicit integer conversion to an intrinsic `IntegerType`)/`EFloat` (a bare float literal carrying an INTRINSIC bounded-canonical finite decimal `coeff·10^exp`, `\|coeff\|<10^40`, `\|exp\|≤4096`)/`EFloatConvert` (explicit conversion to a `FloatType`); key-uniqueness intrinsic | carry a package clause / entry flag / imports / a raw path in the file; a nonemptiness restriction; a second tree; a type on a raw literal; a raw type-name string in a conversion; arithmetic / complex / imaginary / NaN / Inf syntax |
| **GoTypes** | the ONE type authority — EVIDENCE over the raw AST: `GoType` = `TBool` \| `TInteger IntegerType` \| `TFloat FloatType` \| `TString`; exact untyped `GoConst` (bool / int / float / byte-string; a `CFloat` is an exact CANONICAL rational — numerator `Z` / positive coprime denominator, canonical zero, decidable eq, NOT a float/spec_float/decimal-string/rounded value); the ONE conversion authority `convert_const : GoType -> GoConst -> option GoConst`; PARTIAL `const_value` (int conversions value-preserving, float conversions ROUND ONCE at the destination — F32 direct at binary32); the `ConstInfo` analyzer (untyped vs typed constants, repr-checked at every nesting layer); one default-type (int → `TInteger IInt`, float → `TFloat F64`); the per-type inclusive-range representability decision over `Ints`; reflected `ResolveExpr` (untyped checked for representability, typed constants trusted + keep their type + value); `Stmt/Decl/File/ProgramTyped` | a typed AST / `TypedIR` / copied "resolved expression"; a placeholder/unknown/raw/opaque type ahead of its syntax; a second numeric-width or conversion authority; a `GoTypeTag`; a float stored as a rounded/spec_float/decimal-string constant; typing a literal outside a use context |
| **GoCompile** | whole-program directory→package + exactly-one-main + whole-program typing (`ProgramTyped` via GoTypes); `go_compile` sound/complete; `CompilationFacts` exposing typing by canonical projection | be a boolean; accept per-file partially; hide package grouping / entry status in a raw node; store a typed copy of the program |
| **GoSafe** | real `GoValue` (`VBool`/`VInteger IntegerType Z`/`VFloat ft (FloatValue ft)`/`VString`; a `FloatValue` is a PROOF-CARRYING canonical Stdlib `SpecFloat.spec_float`, Flocq unused); `value_type` over the SAME `GoType`; `ValueWF` range invariant (`ValueWF (VFloat …) := True` — canonicality in the type; constant eval only finite/+0); PARTIAL `eval_expr` derived from `const_info`; resolved-eval well-formedness + type preservation; abstract `eval_file`; `SafeProgram` (0 = -0); honest `GoSafe := True` | observe spelling as value; a separate runtime type universe; a per-width runtime record family / `GoTypeTag`; keep an unused panic placeholder; circularly reference compilation |
| **GoRender** | render decls + the derived package clause; render go.mod from the ModuleSpec; an integer conversion as `<integer_keyword it>(<inner>)` (the ten exact Go keywords) and a float conversion as `float32(…)`/`float64(…)`; ONE canonical float decimal spelling (`0.0`; else `<signed-coeff>.0e<±exp>`) with an INDEPENDENT decoder proving `decode(render d) = Some d`; header exact first line (go.mod and .go); `render_const_info_denotes` / `render_resolved_expr_denotes` (spelling ↔ ConstInfo ↔ value/resolved type; integer-conversion case via `convert_const`, now with float cases; all via the ONE `RenderedConstInfoDenotes`) | tokenize/lex/parse/round-trip; deduce packages/entry; invoke a formatter; add require/replace/toolchain to go.mod |
| **DirectoryImage** | the complete module (exact go.mod bytes + a possibly-empty .go map), provenance-gated (`di_prov` proves BOTH came from `render_program`; `mkImage` demands that proof); `Fido Emit` typechecks its argument's `di_transport` AND rejects any argument with an axiomatic assumption closure | be an arbitrary-map escape that bypasses SafeProgram; invent go.mod in the sink; make a nonemptiness claim; accept a raw transport, or a same-typed image built from a forged (axiomatic) proof, at the emit boundary |
| **Fido Emit + sink** | a four-step boundary — typecheck the image, reject a non-empty assumption closure (kernel provenance queries), decode ONLY the final (go.mod, entries) transport with exact constructors, then a foreign-Go-rejecting sibling-temp dirty-directory sync | inspect the program/AST/behaviour/semantics; emit without both provenance guards; merge/preserve a foreign `.go`/`go.mod`; delete/overwrite/follow foreign state; keep a stage-record/nonce/central-staging design |

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
- `plugin/fido_sink.ml` + `e2e/sink_test.ml` + `e2e/fido_apply.ml` — the generic dirty-directory
  synchronizer, its driver, and the `make regenerate` apply CLI (enumerate a pristine `/generated` tree and
  hand it to the sink). Filesystem ONLY: they walk no Rocq terms.

`tools/ocaml-origin-gate.sh` enforces exactly these four files (inspecting every source at every depth — a
repository-content gate, not the runtime sink, so it prunes only `.git`), filesystem-only for the
sink/driver/apply, transport-only for the bridge — there is NO source-line size cap (a numeric cap is not a
correctness invariant) and NO whole-repository historical-name scanner (the real boundary is this allowlist
plus the responsibility checks; repository prose may freely discuss deleted history). **Never reintroduce a
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
mutation): any foreign `.go` anywhere in the Go-DISCOVERED namespace (a regular file whose first line is not
the header, or a `.go` symlink/nonregular entry), a foreign root `go.mod`, a `go.mod` symlink, or any nested
`go.mod`. The traversal SKIPS the opaque dot/underscore/`testdata`/`vendor` directory trees `go build ./...`
itself ignores — it neither inspects nor rejects because of anything beneath them (so a foreign `.go` there
cannot corrupt the build, and `.git` stays untouched); everything under those trees is preserved. A dirty
foreign Go input in the discovered namespace would silently change what `go build ./...` compiles, so it is
not preserved-and-merged — it aborts. Foreign NON-Go files/dirs are preserved. Installed `.go` files and the root `go.mod`
are Fido-owned iff their first line is the exact header AND they are regular non-symlink files (rechecked
by lstat immediately before every overwrite/delete; a symlink is S_LNK, never S_REG, so never followed); a
foreign `.go`/`go.mod` forging the header is the accepted limit (a header is public).

**Sibling-temp staging (no records, no nonce, no stage directory, no parser).** `<root>/.fido/` holds
EXACTLY the marker and, during an active run or after a crash, the git-style `index.lock` — nothing else;
any other root-control entry rejects without modification. Each final output stages into its RESERVED
sibling temporary `<final>.fido-tmp-v1`; because the lock serializes cooperating emitters, the name needs no
nonce and recovery needs no record — the final path is already known to the live sync. The sink stages the
COMPLETE image (go.mod + every .go) before any install, then installs each file by rename from its sibling
temp — same filesystem, so nested mount points inside root are supported; EXDEV fails loud with no copy
fallback. Only then are stale Fido-owned `.go` files (owned, not desired) removed (the empty program removes
them all, keeping/updating the owned go.mod). A **regular non-symlink** file ending in `.fido-tmp-v1` is, by
PUBLIC (and forgeable) CONVENTION, an abandoned Fido temp ONLY IF its suffix-stripped path maps to a Fido
FINAL path (the root `go.mod` or an intrinsic FilePath `.go`); a non-mappable suffixed entry, or a
symlink/directory/special with that suffix, is NOT owned (refuse + preserve). A nested `.fido` (any type) in
the traversed Go-discovered namespace is an emission error and aborts. Forgeability of the mapped-suffix
convention is an accepted tradeoff under the single-owner threat model — no transaction log is built to avoid
it.

**Fail-closed, two-phase.** Only a confirmed `ENOENT` means "missing"; every other filesystem error aborts.
After the lock: PHASE 1 inspects the whole Go-discovered namespace once (validating foreign-Go/module/control rules and
COLLECTING every VALID abandoned temp — a regular reserved-suffix file whose suffix-stripped path maps to a
Fido final path), deleting nothing; if any path is invalid or uninspectable the run rejects before any
mutation, preserving every collected temp. PHASE 2 (only after the complete scan succeeds) re-`lstat`s each
collected temp, requires it is still a regular reserved-suffix file mapping to a final path, and deletes it
(fail-loud on any mismatch). A handled failure removes this run's created temps + newly-empty parents,
aggregates body + cleanup + lock-release errors, and releases the lock. It is **NOT** a transactional
whole-tree commit — install is a sequential rename loop, so a mid-install failure may leave earlier files
installed (nontransactional, stated honestly); residue remains only after an uncatchable CRASH or a
cleanup/lock-release failure — a rerun, after the stale lock is cleared, removes the temps and converges. It
is **NOT** hardened against a concurrent non-cooperating process (this OCaml `Unix` exposes no
`openat`/`O_NOFOLLOW`); the honest model is COOPERATING emitters serialized by the lock, in the Linux/amd64
operational scope. Ownership is by header + regular-file + desired-key-set (or the reserved suffix MAPPING to
a Fido final path, for temps), never timestamps, a manifest, records, or device/inode identity.

**The exact guarantee.** *GoProgram acceptance, SafeProgram certification, and DirectoryImage creation are
semantically all-or-nothing. Dirty-directory installation is locked for cooperating emitters, rejects
foreign Go/module inputs and nested `.fido` in the Go-discovered namespace (skipping the opaque
dot/underscore/testdata/vendor trees `go build ./...` ignores), inspects that namespace fail-closed, stages
the complete image into reserved sibling temporary files before installation, uses per-file rename in the
ordinary same-filesystem case, cleans handled-failure temps immediately, removes validated abandoned
suffix-owned temps (whose suffix-stripped path maps to a Fido final path) on a later run, and converges when
the directory namespace remains stable. It is not a portable
transactional multi-file filesystem commit, not hardened against malicious concurrent mutation, and does not
model arbitrary unmount/remount/backing-store replacement between runs.*

### Pristine generated-module layer + tracked artifact (prototype pre-commit)

One ordinary content-addressed Buildx stage, `generated-module`, holds EXACTLY the canonical generated
module (`/generated/go.mod` + recursive `.go` — the primary witness), assembled from the authoritative
generation inputs (certified `.v`, dune, plugin, pinned toolchain, canonical witness) and never from the
committed generated bytes, never a mutable cache mount. Every canonical-output workflow — the Go e2e,
`make regenerate`, and the pre-commit staged-index verification — consumes THAT one layer. The canonical
generated module (root `go.mod` + recursive `.go`) is a **tracked, reviewed derived artifact** (Fido-headed;
`.v`/proof sources remain authoritative; no `dist/`, no handwritten Go in the module, no nested `go.mod`).
`make regenerate` rewrites it into the repo through the SAME `Fido_sink`. Verification is split coherently:
`make check` verifies the **working tree** (it materializes the working-tree content of every relevant file —
`git ls-files --cached --others --exclude-standard` through tar: tracked files with their uncommitted edits
PLUS untracked non-gitignored files, so a rogue untracked `foreign.go`/`.ml` is caught, while the gitignored
local residue `.fido/`/`*.fido-tmp-v1`/`*.vo` is excluded — rebuilds the
pristine `generated-module`/`generated-artifact` from the same working-tree inputs, and byte-compares the
working-tree `go.mod` + recursive `.go` against it, path set + bytes both directions); the **pre-commit hook**
verifies the proposed **staged** commit (it exports the Git INDEX once, runs the SAME shared compare over that
staged snapshot, and never reads the unstaged working tree or auto-stages). This byte-compare is essential
because `.dockerignore` hides the committed `go.mod`/`.go` from the Buildx context, so the proof/e2e cannot
incidentally validate their bytes. The pre-commit hook is a PROTOTYPE boundary providing **reasonable
assurance** against accidental stale generated output for a cooperating developer using ordinary Git commands;
it is bypassable with `git commit --no-verify` and does NOT defend against deliberate modification of its own
verifier — local verifier tamper-resistance is explicitly OUT OF SCOPE (a future PR CI runs the same
comparison server-side as a stronger boundary).

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
imports are compilation results, never raw metadata. Integer width has one authority (`Ints`, 64-bit),
float precision + single-round conversion has one authority (`Floats` — the `F32`/`F64` leaf module next to
`Ints`), and the type universe has one authority (`GoTypes` — `TBool`, the integer family `TInteger` over the
ten-member `IntegerType`, `TFloat` over the two-member `FloatType`, and `TString`); `int`/`uint` are pinned
64-bit and DISTINCT from `int64`/`uint64`; there is no `TargetConfig`.
A new type constructor arrives ONLY with the syntax and complete semantic obligations that need it (as
`TString` did — together with `EString` + its value + canonical rendering + an independent decoder proving
the byte round trip `decode(render s) = Some s`, which may also accept semantically equivalent noncanonical
spellings and claims no source-spelling inverse), never a
speculative `unknown`/`opaque`/`raw` type, and never a typed AST. Raw literals stay UNTYPED
syntax: they denote exact untyped constants, and defaulting/representability happen in a use context.

## Static Type Universe Arc

The type universe grows in ONE reviewed order, each root landing COMPLETE with its static facts before the
next begins: (1) integers; (2) floats; (3) complex; (4) `uintptr` and the predeclared aliases (`byte` =
`uint8`, `rune` = `int32`); (5) unnamed structural types (arrays, slices, structs, pointers, function
signatures, maps, channels); (6) type aliases, defined named types, and valid recursion; (7) method
signatures and method sets as type-level facts; (8) non-generic value interfaces; (9) only THEN the
operations that consume those roots. **Integers and floats are DONE.**

**Types before operations.** Each root adds only STATIC facts — identity, underlying type, canonical
rendering, zero-value classification, nilability, comparability, map-key admissibility, recursive validity,
assignability, constant representability, function signatures, method signatures/sets. It does NOT yet build
runtime models (slice backing arrays, map heaps, channel queues, pointer heaps, function closures, interface
dynamic values), and it must NEVER resurrect a fake operational value merely to assert that a static type
exists (faithful-or-absent — a static-only type carries no runtime placeholder).

**Non-generic boundary.** This arc admits NO type parameters, generic types, generic aliases,
constraint-only interface semantics, instantiation/inference, or imports. The eventual
`any`/`error`/ordinary-interface story belongs to the non-generic value-interface phase (8), never earlier.

## Trust base (say it exactly)

Trusted: Rocq and its kernel; the digest-pinned Docker/Go images plus the opam-repo state and apt packages;
the Fido Emit **transport boundary** (the bridge typechecks the image type and rejects an axiomatic
assumption closure — both via Rocq's own kernel/assumptions machinery — then decodes only the final
transport constructors; the sink is filesystem-only — all trusted-not-proved); and the Go toolchain
(claim (B), the `go build ./...` adequacy, is exercised differentially by the e2e, not proved). Proved (axiom-free, asserted every build in the **prove** stage by
`gate/axiom_gate.v` PLUS the Rocq-native `Fido Audit Assumptions` command — a whole-certified-theory
assumption-closure audit seeded from every Fido CONSTANT, every Fido mutual INDUCTIVE (via `IndRef`), and
every surviving named assumption, that rejects every `Printer.Axiom` category (incl. assumed positivity /
guardedness / type-in-type / UIP) and `Printer.Variable` — catching an external axiom reached transitively
through any internal/opaque lemma, an unused Fido axiom, and an unreferenced assumption-bearing inductive,
with a module-coverage gate and adversarial self-tests A-E): the Ints boundary values; the Floats single-round `convert_const` boundary (F32 direct at binary32); ModulePath decidable eq + representable/
unrepresentable module-path fixtures; GoVersion's exact "1.23" rendering; FilePath decidable eq +
representable/unrepresentable path fixtures; FMap's key-NoDup invariant + duplicate-key unconstructibility +
deterministic lookup; GoTypes — the one type authority: zero-sign constant equality, default-type
exactness, representability reflection, expression resolution sound + complete + deterministic, statement +
program typing reflection, int max/min accepted, overflow/underflow rejected; GoCompile claim (A) —
`prog_ok_iff`, `go_compile` sound + complete, rejection ⇒ no CompilableProgram, the compiled evidence
exposes `ProgramTyped`, the empty program accepted; GoSafe's zero-sign-agnostic fact + resolved-type
preservation (`eval_expr_resolved_type`); GoRender's `render_const_info_denotes` + `render_resolved_expr_denotes`
+ all-ASCII + decimal-faithful + no-leading-zero + the canonical float decimal round trip + header-first-line + boundaries + the exact go.mod render
(bytes / header first line / ASCII); DirectoryImage's go.mod-and-.go header-first-line / ASCII / unique-paths over
EVERY image (NO nonemptiness claim — the empty program is valid). "No assumptions" is never evidence a
theorem's STATEMENT is right — the gated invariant must be the one advertised.

## What must never come back

A handwritten OCaml backend / lowering / renderer / semantic decoder, or a bridge decoding anything but the
final transport type; a SECOND program-AST hierarchy, a raw `GoPackage` tree, a copied compiled AST, or a
typed AST / `TypedIR` / copied "resolved-expression" tree beside the one raw `GoAST`; a type attached to a
raw literal, or a placeholder/unknown/opaque/raw/`TString` type constructor added ahead of the syntax that
needs it; a second numeric-width, float-precision, conversion, or type authority beside
`Ints`/`Floats`/`convert_const`/`GoTypes`; F32 rounded through F64 (the double-round scar); a float stored as
a rounded/spec_float/decimal-string constant;
package/import metadata in raw file values; `MainFile` (package/main/entry collapsed into one raw node);
raw `string` map keys; a nonemptiness restriction on the program/image; a handwritten `go.mod` (it is
RENDERED in Rocq) or `go.mod` smuggled into the FilePath map; central `<root>/.fido/staging/`, a central
cross-device rejection, or the deleted stage-record / nonce / local-stage-directory / record-driven-recovery
subsystem (staging is a RESERVED sibling temp `<final>.fido-tmp-v1`, the lock serializes so no nonce/record
is needed); device/inode/mount-identity ownership records; a foreign `.go`/`go.mod` preserved-and-merged
into the built tree, or a nested `.fido` skipped instead of rejected; handled-failure residue left
deliberately for the next run; a constant-only audit that skips certified inductives or surviving named
assumptions; a `Undef`-body-only axiom check posing as a whole-theory audit; tracked axiom-bearing fixtures;
`go vet` as a blocking acceptance gate; single-file compiler semantics or a subset filter posing as compiler
admissibility; a witness-specific extracted emit executable or a hard-coded `main.go` Docker copy; a
fail-open regex axiom scanner; a no-tracked-Go seal (the canonical generated module IS tracked and verified
byte-exact against the pristine Buildx layer); a `dist/` directory; handwritten Go in the canonical module;
a pre-commit that reads the unstaged working tree or auto-stages; timestamps/manifests as ownership
authority; a claimed transactional whole-directory guarantee; a `TargetConfig`; a
lexer/parser/tokenizer/round-trip/text-IR/target-IR in the certified path; fuel. Git carries the history; re-admit a feature only when the roots make its proof
obligations natural.
