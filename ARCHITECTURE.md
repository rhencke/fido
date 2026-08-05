# Architecture

The current semantic, proof, provenance, extraction and trust architecture, in dependency order. This
governs. Read it before any structural change.

---

## 1. Goal and closed universe

Fido emits Go that has been proved compile-admissible and safe **before** any bytes exist. An untrusted
proposer may write a program and arbitrary supporting lemmas; no Go is emitted unless Rocq first proves the
whole program admissible.

There is **one** program representation. The AST *is* the IR. `Admissible` and `Property` are evidence and
facts over that one program, never new trees.

```text
Syntax.Program → Typing → Admissible → Safe → Render → Emit.Image → Fido Materialize → pinned go build ./...
                                                                        → make regenerate publishes the SAME bytes
```

The universe is closed. Imports are **unrepresentable**, not rejected: `Syntax.ImportSpec` has no
constructors. When imports arrive, `Admissible` must resolve every import to a package owned by the same
`Syntax.Program`, or reject the whole program. Nothing may resolve to stdlib, module cache, network, vendor,
workspace or ambient filesystem.

**The law of this repository is ruthless correctness or ruthless deletion — no middle state.** Incomplete
scope is acceptable. Incorrect, approximate, duplicated, transitional, fail-open or half-built foundations
are not. Every retained component must be complete and correct in itself and may build only on foundations
that are already complete and correct. **Cut representable scope before weakening a proof:** if a construct
cannot be modelled exactly, remove it from the AST, never admit it with a conservative narrowing.

A green boolean checker is not a compile authority. A printer's own inverse is not a Go-semantics theorem. A
functional-lookup theorem is not proof of key uniqueness. Regex source scanning is not a sound zero-axiom
gate. **Axiom-free is not correct** — always check that the theorem's statement is the right one.

**One authority per fact.** `Integer` owns integer width, `Float` float format, `Complex` complex format,
`Names` the closed sixteen-name source type-name class, `Typing` the type universe, and `Admissible`'s
predeclared context is the one source-name → `Typing.SemanticType` resolver. There is no `TargetConfig`, no
`GoTypeTag`, no second width or conversion authority, no typed AST beside the one raw `Syntax`, and no
source-name table in `Syntax`, `Typing` or `Render`.

**Standard collections only.** Where a mature collection exists in the pinned Rocq stdlib (`FMapAVL`,
`FMapPositive`), the OCaml stdlib (`Map.Make`, `Set.Make`) or the Rocq runtime (`Names.GlobRef.Set`), Fido
uses it. A thin domain wrapper is encouraged: instantiate a standard functor with a domain key, enforce
stronger construction, prove project facts, seal an interface. Fido never implements collection storage or
generic algorithms — no project-authored map, set, table, hash, tree or trie; no `list + NoDup` as
identity-keyed storage; no reimplemented find/add/balance. Choose by semantic role: identity-keyed → map;
membership-only → set; ordered sequence or transport enumeration → `list`; duplicate-invalid source → a
duplicate-**rejecting** builder, never a silent overwrite. A map's `elements` is a derived enumeration, never
a second identity authority. A failed builder stays failed. If nothing fits, report the conflict and stop.

**No fuel, ever.** Totality comes from decreasing structure.

---

## 2. Source and program representation

A `Syntax.Program` is a `ModuleSpec` paired with a possibly-**empty** `Syntax.Files`.

`Syntax.Files` is a pinned-stdlib `FMapAVL` keyed by `FilePath.T`. **The path is the map key**, so duplicate
paths are unrepresentable by construction, lookup is deterministic, and `file_bindings` is a canonical
derived enumeration. Semantic equality is standard map `Equal` (`FilesEqual`), distinct from Rocq record
equality. The builder `Syntax.files_of_nodes` is sound, complete, exact and order-independent — each node
maps to its own source with no silent overwrite.

A `Syntax.FileNode` is a construction and view type: a `FilePath.T` plus a `Syntax.File`. The path is the key
and is **not** stored in the mapped value, so there is one path authority.

A `Syntax.File` is a source-owned package clause (`Syntax.MainPackage`), an intrinsically empty import
section, and a list of declarations — today only `Syntax.Main`, a `func main()`. **Entry-point status,
symbols and types are compilation results; the package clause is source syntax.**

`ModuleSpec` is an intrinsic fact about the *generated* module, not environment configuration: a
`ModulePath.T` and a `Version`. `ModulePath.T` is a narrow canonical path — slash-separated lowercase
segments, no `..`, no repeated or leading slash, arbitrary length, first element dotted, and neither a `/vN`
version suffix nor a `gopkg.in` form. Those two exclusions are exactly Go 1.23's semantic-import-versioning
reject classes. Invalid paths are unrepresentable. `Version` is a singleton today (`Go1_23`, rendering
`1.23`); a later constructor is a reviewed semantic milestone.

`FilePath.T` is an intrinsic canonical relative source path, not a raw string: lowercase-ASCII components and
an ordinary lowercase-ASCII `.go` basename, with no empty, `.` or `..` component, no absolute or trailing
slash, and no leading dot or underscore — so no hidden, `_test` or GOOS-suffixed file. **Length is unbounded
in the model, the grammar and the sink.** Platform host limits are not a Fido domain concern; an over-long
path fails loud at the OS during materialization, never silently in the model. `go.mod` is not a
`FilePath.T`; a distinct root field carries it.

The admitted fragment is small and grows only by proof. Each source file is a `package main` clause, empty
imports, and a `func main()` whose statements print primitive literals and one source-shaped explicit
conversion naming a **source** type. Anything else is unrepresentable, not rejected.

---

## 3. Static elaboration and retained facts

### Index — structural identity

`Index` is the one structural occurrence-identity and navigation authority, derived from one immutable
`Syntax.Program` snapshot. It imports only `Syntax`, `Collections` and `FilePath`; it knows no semantic types,
admissibility, rendering or diagnostics.

Each represented occurrence gets one canonical file-local `positive` id by deterministic preorder, file root
= 1. Its `Index.Meta` lives in a sealed per-file table over pinned `FMapPositive`.

An **independent, table-free** `source_occurrence_at` re-derives each occurrence's metadata straight from the
syntax, and the universal `index_file_source_exact` pins stored metadata equal to source-occurrence metadata
at every id, in **presence and absence**. A mislabeled table is therefore unprovable.

References are sealed and indexed by the exact `Syntax.Program`, minted only through validated
`file_of_path`/`ref_of_key`. Identity is `Index.Key` identity. A different-payload or different-`ModuleSpec`
snapshot yields non-interchangeable reference types even when the erased data is equal.

A conversion occupies two children: the source type-name occurrence at `Pos.succ me`, carrying its
`Index.TypeNameView`, then the operand subtree. `TypeNameRef` recovers the retained source `Syntax.TypeExpr`
through the reference.

The query API is **total by carried validity** — only `parent_of` is optional — never a semantic fallback.
Navigation is exact: parent via metadata, direct children by preorder interval jumps, ancestry by intervals,
one canonical enumeration, and the single-pass `visit_file` traversal that hands each original syntax
fragment to its validated `NodeRef` in one structural pass. No per-node search, no located or copied AST, no
second tree.

### Typing — the one type authority

`Typing` is evidence over the raw syntax, never a typed AST. The permanent type universe is exactly
`{ BoolType, IntegerType over the ten Integer kinds, FloatType, ComplexType, StringType }`.

A raw literal denotes an **exact untyped constant**: integers arbitrary-precision, a bare float literal an
exact canonical rational, a complex literal an exact pair of rationals, strings exact byte sequences.

`Typing.TypedConstant : SemanticType -> Type` is an intrinsic dependent family. **A mismatched or
out-of-range typed constant is unrepresentable, never merely rejected.**

`Typing.convert_constant` is the one conversion authority. Integer conversions are value-preserving and
range-checked. Float conversions round **once at the destination** — F32 directly at binary32, never via F64,
and a same-format float is returned unchanged. Complex conversions round each component once, and
scalar↔complex follows Go's zero-imaginary rule.

One source-shaped conversion `Syntax.Convert ts e` names a **source** type. Its semantic target is the
compiler-owned resolution of `ts`. The index-free typing spec is parameterized by that resolver, so `Typing`
never owns a source-name → semantic-type table.

`Typing.resolve_constant_info` is use-context resolution. An untyped constant **defaults** (int →
`IntegerType Int`, float → `FloatType F64`, complex → `ComplexType C128`); a typed constant **packs
unchanged**, because its validity is intrinsic — not re-defaulted, not re-checked.

`ConstantRepresentable` is derived from successful typing, routing numeric targets through
`convert_constant`, so representability and conversion can never disagree. There is no second range or
overflow checker, no placeholder type, and no typed AST.

### Admissible — exact whole-program acceptance

`Admissible` is **exact whole-program compiler admissibility** — the pinned one-shot `go build ./...`
acceptance — not a subset filter. It consumes the whole finite map.

```text
Admissible p := fresh_build_preflight_ok p  /\  SourceProgramValid p
SourceProgramValid := Typing.Program /\ PackageDeclsUnique /\ MainPackagesHaveEntry
```

Files group by parent directory into packages. One invalid package rejects the whole program: acceptance is
all-or-nothing. `fresh_build_preflight_ok` is cmd/go's default-**output** rule: a sole main package's default
executable name must not collide with an existing root directory. Zero or two-or-more packages write no
default output, and the empty program is accepted.

The one elaboration root `elaborate` builds one retained `Index.Program` and returns a `Compilable.Elaboration`.
`Compilable.compile` **projects** it — there is no second checker.

An accepted program yields `Compilable.Compiled` carrying a `Compilable.Program`, which retains the program,
its exact elaborated index, and its `Compilable.Facts`. A rejected program yields `Compilable.Rejected`
carrying exact structured diagnostics **and no `Compilable.Program`** — hence no `Safe.Program` and no image.

Diagnostics are structured values anchored in the exact snapshot: invalid conversion (primary = the innermost
failing conversion, with an outer-context field), default-not-representable, duplicate-main, missing-main and
build-output-directory. The three diagnostic layers each have an emptiness characterization, and a failed
preflight takes precedence over the sole package's semantic errors. **An outcome is a structured branch and
its exact diagnostic list, never a collapsed tag.**

### Retained causal objects

The production expression path is one phase built from one retained input, driven by one proof-carrying work
forest **object**. Its ordering, its per-file and flat structure, its key uniqueness and its
operand-in-suffix property are carried as fields — not rebuilt and not re-proved by consumers.

Work-member identity is a separate carried field: a standard `FMapAVL` index built **once** from the
already-built item list. It is total with no fallback precisely because it demands the key-uniqueness proof
as an argument, and it is overwrite-free. Domain and injectivity are **derived** from it, never stored, so
there is no second domain or uniqueness authority. **No `List.find`, `existsb` or recursive key scan exists
anywhere in the member-lookup path.**

The outcome table pairs its accumulator with the trace that built it, indexed by that accumulator, so a
foreign accumulator reproducing a head outcome cannot be attached. Each member's direct cause is a
**projection** of that trace, reading the operand outcome through the exact operand suffix member.

The phase retains the whole flow as a dependent chain of objects, each typed by the exact prior object it
consumes. There is no provenance-equality field: the causal chain **is** the dependent types, so a foreign
component is unrepresentable by type mismatch rather than rejected by a check.

**Equality to a recomputation is never provenance.** `Compilable.Program` retains the exact accepted core;
the index, facts, layout, plan and both diagnostic lists are projections of it, never a stored equality to a
rerun. The core, program, failure and facts records, their constructors and the core builder are all
**sealed**, so a client cannot assemble a peer core, and `Compilable.compile` is the only mint.

---

## 4. Safety, capabilities and provenance

`Safe.Program` is the permanent safety boundary over `Compilable.Program`. `Property := True` is honest
**today** — the fragment contains no unsafe operation. It is the extension point for guarantees beyond
compiler acceptance, not a circular claim, and it carries no unused panic or control placeholder.

Runtime values are real values carrying the **same** `Typing.SemanticType` authority as the constant
analysis. A `Float.Value` is a proof-carrying canonical Stdlib `spec_float` — the image of the format
normalizer, with Flocq unused — so its well-formedness is `True` with canonicality in the type. A runtime
`Complex.Value` is a pair of such components that **may** be −0, infinity or NaN, while constant evaluation
produces only finite values and +0.

Evaluation is **derived** from the one constant analysis and is **partial**: a compiler-invalid conversion
has no value, never a wrap. A resolved expression evaluates to a well-formed value of its resolved semantic
type. A typed float is rounded once at conversion and never re-rounded.

There is no whole-program execution semantics yet; only the witness package is executed against goldens. A
per-package program semantics arrives when a construct needs it.

**A compound typed constant is composed from already-coherent typed components.** A typed complex constant is
a pair of typed float components; a runtime complex value a pair of runtime floats. The component authority's
coherence and denotation proofs are reused, never duplicated at the aggregate layer. The untyped / typed /
runtime distinction holds at every level.

---

## 5. Rendering

`Render` traverses the one program directly. It renders each file's package clause from that file's **own**
`Syntax.package`, each declaration, and the `go.mod` from the `ModuleSpec`. Every rendered file — `go.mod`
and every `.go` — begins with the exact header `// fido was here.  woof woof.  do not edit.` as its first
line, and that is proved.

A conversion renders as `<source-name>(<inner>)`, reading the **retained source identifier**, not the
resolved semantic type. All sixteen source names render their own spelling, so `byte` and `rune` render as
themselves and never as `uint8` or `int32`.

A float constant renders by one canonical decimal spelling, paired with an **independent decoder** proving
the exact rational round trip. A complex constant renders as one canonical `complex(re, im)` with its own
independent decoder and semantic round trip.

Three denotation theorems tie the authorities together. `const_info_denotes`: a rendered expression denotes
exactly the constant status `Typing` computes. `const_info_denotes_functional`: a spelling denotes **at most
one** constant status, because the recognisers are pairwise disjoint. `resolved_expr_denotes`: a resolved
argument evaluates to a well-formed value of its resolved type, whose spelling denotes it.

There is no tokenizer, lexer, parser or round-trip authority, and no formatter is invoked.

---

## 6. Emission and the OCaml transport boundary

An `Emit.Image` is the complete module: exact root `go.mod` bytes plus a finite map from `FilePath.T` to
exact final `.go` bytes. It is provenance-gated — a value carries proof that both came from rendering one
`Safe.Program`. The `.go` map may be empty; **there is no nonemptiness claim**.

The raw mint token constructor is private and `Emit.Mint.issue` is the sole authority-producing operation.
The image is a reducible carrier retaining the exact `Safe.Program`, the exact bytes and that exact token, so
provenance is a projection. Its pack constructor is not a mint: what stops it authorizing foreign bytes is
that the token's indices force the payload.

**A proof can be postulated, so the type alone is not sufficient.** The live transport boundary is the real
gate.

### The handwritten-OCaml boundary (hard)

All semantic work is proved Rocq. The **only** handwritten OCaml is the transport boundary, and it
understands filesystems, not programs.

`plugin/materialize.mlg` is the bridge, a four-step boundary: typecheck the argument's transport projection
as the certified image type; **reject any argument whose assumption closure contains an axiom**, using the
same kernel mechanism as the whole-theory audit; reduce and structurally decode **only** the final
`(go.mod bytes, (path, bytes) list)` transport with exact constructors, failing loud otherwise; and hand the
result to `Fido Materialize`, the sole Rocq transport command. **There is no public `Fido Emit`.**

`plugin/sink.ml`, `e2e/sink_test.ml` and `e2e/apply.ml` are the pristine writer, the foreign-rejecting
publication sink, its test driver and the tiny `make regenerate` adapter. They walk no Rocq terms and run no
programs. `Sink.sync` is a **private** plugin module, so it is not independently usable as publication by any
OCaml consumer.

`tools/ocaml-origin-gate.sh` enforces exactly those four files with those boundaries, at every depth. **Never
reintroduce a handwritten backend, lowering, renderer or semantic decoder, or a bridge that decodes anything
but the final transport type.** If the transport boundary cannot be met correctly, delete the e2e — a false
transport foundation is worse than no integration.

That both provenance guards stay live is a mutation-sensitive regression gate, not a proof: the emit stage
executes forged inputs — a raw transport and transiently generated axiom- and variable-backed images — and if
either guard were removed the corresponding command would succeed and create a target, failing the e2e. A
source grep would be spoofable; this is not.

### Publication

`Fido Materialize` writes authoritative bytes directly into a fresh, empty, disposable validation root:
`O_EXCL`, fail-closed, no control state.

The publication sink is separate and installs into an existing dirty tree under a lock. Before any effect it
validates the root — every proper ancestor must be a real directory, and a symlink in any prefix component is
rejected — and refuses a desired path inside the reserved control namespace.

**Foreign Go or module inputs reject the whole emission**, fail-closed, before any generated-file mutation:
any foreign `.go` in the Go-discovered namespace, a foreign or symlinked root `go.mod`, or any nested
`go.mod`. The traversal skips the opaque dot, underscore, `testdata` and `vendor` trees that `go build ./...`
itself ignores, so `.git` stays untouched and foreign non-Go files are preserved.

Ownership is by **header plus regular-file status**, rechecked by `lstat` immediately before every overwrite
or delete, so a symlink is never followed. A foreign file forging the header is the accepted limit — a header
is public. Ownership is never by timestamp, manifest, record, or device and inode identity.

Staging is into reserved sibling temporaries and installation is by atomic rename on the same filesystem;
`EXDEV` fails loud with no copy fallback. The **complete** image stages before any install. Only then are
stale owned files removed. Phase 1 inspects the whole namespace once and deletes nothing; phase 2 runs only
after that scan succeeds. Only a confirmed `ENOENT` means "missing"; every other filesystem error aborts.

**The exact guarantee.** Program acceptance, certification and image creation are semantically
all-or-nothing. Dirty-directory installation is locked for **cooperating** emitters, rejects foreign inputs,
inspects fail-closed, stages completely before installing, and converges when the namespace remains stable.
It is *not* a portable transactional multi-file commit, *not* hardened against malicious concurrent mutation,
and does *not* model unmount or backing-store replacement between runs. This OCaml `Unix` exposes no
`openat`/`O_NOFOLLOW`.

**Validate before publish** is the Docker DAG, not a checksum: building the `sync` image copies the e2e's
fresh-build marker, so a failed pinned `go build ./...` makes `sync` unbuildable and prevents publication. A
checksum cannot prove a build succeeded. This is accidental-publication protection for a cooperating
developer; the project does not attempt to resist a deliberate local bypass, by design.

### The tracked generated artifact

One content-addressed Buildx stage holds exactly the pristine canonical module, assembled from the
authoritative generation inputs and **never** from the committed bytes. Every canonical-output workflow
consumes that one layer.

The canonical module is a **tracked, reviewed derived artifact** — Fido-headed, with the `.v` sources
authoritative. `make check` verifies the **working tree**; the pre-commit hook verifies the proposed
**staged** commit, exporting the Git index once and never reading the unstaged tree or auto-staging. These
are distinct source views and must stay distinct. The byte-compare is essential because `.dockerignore` hides
the committed bytes from Buildx, so the proof and e2e cannot incidentally validate them.

The hook is a prototype boundary giving reasonable assurance against accidental stale output for a
cooperating developer. It is bypassable with `--no-verify` and does not defend against modification of its own
verifier. Local verifier tamper-resistance is explicitly out of scope.

---

## 7. Trust boundary

**Trusted:** Rocq and its kernel; the digest-pinned images, opam state and apt packages; the Fido transport
boundary (typechecking and assumption-closure rejection via Rocq's own machinery, then decoding only the
final transport; the sink is filesystem-only); and the Go toolchain.

**Proved axiom-free, asserted every build** by the Rocq-native `Fido Audit Assumptions` — the one
zero-project-axiom authority. It is a whole-certified-theory assumption-closure audit seeded from every Fido
constant, every mutual inductive and every surviving named assumption, rejecting every axiom category and
every variable. It catches an external axiom reached transitively through an opaque lemma, which a
source-text scanner cannot do soundly. A module-coverage gate and adversarial self-tests prove it is not
fail-open. **It enumerates its own roots**, so nothing beside it has to be kept in step by hand.

**Zero project axioms.** Never `Axiom`, `Parameter`, `Admitted`, a kernel primitive, or functional
extensionality. Tracked axiom-bearing fixtures are forbidden; negatives are generated transiently.

### Two honest claims — never conflate

**(A) Kernel-internal exactness — PROVED.** The executable `Compilable.compile` succeeds exactly for the
declarative `Admissible` judgment: sound, complete, and the one elaboration root satisfies
`elaboration_accepted_iff_admissible`.

**(B) External adequacy — the GOAL, not a kernel theorem.** That the judgment matches `go build ./...` for
every representable rendered program is attacked by differential experiments and the e2e, never proved about
`cmd/go`. **A representable program `go build` accepts but `Admissible` rejects is a model bug**, never a
documented limitation. A program `Admissible` accepts but `go build` rejects is a correctness failure.

Integration tests are **alarms, not proofs**. A Go build or run failure for an emitted program is never an
expected test — it means `Admissible`, rendering, the derived facts or the transport is wrong. Negative
candidates fail in Rocq, before any bytes.

---

## 8. Boundaries

Every live scope restriction is one row in `.review/scope.tsv`: the pinned target, unmodelled platform
limits, the cooperating-developer threat boundary, buildx-only builds, module-path and file-naming
narrowings, imports on hold, the admitted fragment, and the bounded float-decimal domain. No restriction may
live only in a code comment.

Standing acceptance obligations are rows in `.review/acceptance.tsv`. Spec-closure and latitude rows are
`.review/closure.csv` and `.review/latitude.tsv`.

### What must never come back

A handwritten OCaml backend, lowering, renderer or semantic decoder, or a bridge decoding anything but the
final transport type. A second program-AST hierarchy, a copied compiled AST, or a typed AST beside the one
raw `Syntax`. A type attached to a raw literal, or a placeholder, unknown, opaque or raw type constructor
added ahead of the syntax that needs it. A second numeric-width, float-precision, complex, conversion or type
authority. F32 rounded through F64. A float stored as a rounded or decimal-string constant. Package or import
metadata in raw file values. Raw `string` map keys. A nonemptiness restriction on the program or image. A
handwritten `go.mod`, or a `go.mod` smuggled into the path map. A central staging directory, nonce, or
record-driven recovery subsystem. Device or inode ownership records. A foreign file preserved and merged into
the built tree, or a nested control directory skipped instead of rejected. A checksum posing as proof that a
build succeeded. A constant-only audit that skips inductives or named assumptions. A hand-maintained list of
assumption surfaces beside the whole-theory audit — a weaker subset with no rule deriving it, which drifts.
Tracked axiom-bearing fixtures. `go vet` as a blocking gate. Single-file compiler semantics, or a subset
filter posing as admissibility. A fail-open regex axiom scanner. A `dist/` directory. Handwritten Go in the
canonical module. A pre-commit that reads the unstaged tree or auto-stages. A claimed transactional
whole-directory guarantee. A `TargetConfig`. A lexer, parser, tokenizer, text IR or target IR in the
certified path. Fuel.

Git carries the history. Re-admit a feature only when the roots make its proof obligations natural.

---

## 9. Fixed points and proof contracts

Binding constraints on everything built from here. They are not restated per milestone; `ROADMAP.md` names
which milestone consumes which contract. IDs are stable and never renumbered, so a gap means a fixed point
was retired because another row already carried its obligation.

| id | fixed point |
|---|---|
| ARCH-01 | The deletion and generalization standard: retention tests and the prohibition list. |
| ARCH-02 | Minimal machine base — no Go feature defines a second run relation. |
| ARCH-03 | One owner per meaning; the opaque static capability and failure retain the exact compiler object by construction. Public fact, diagnostic, layout and plan interfaces are projections. **Equality to a rerun is never provenance.** |
| ARCH-04 | Expression fact/use split — the use builder never inspects the raw child again. |
| ARCH-05 | Single type algebra; aliases do not create identity; recursive named types refer to declarations. |
| ARCH-06 | Static slot versus dynamic place — source binding identity and runtime storage identity never collapse. |
| ARCH-07 | Stack-only panic, defer and recover; the named invariants justify direct recovery without tokens. |
| ARCH-08 | Resource-local origins — live state retains exact origins, and proofs connect them to run actions. |
| ARCH-09 | Finite bad-prefix safety; safety and liveness stay separate. |
| ARCH-10 | No vacuous library safety — an empty set of starts does not prove open-world safety. |
| ARCH-11 | Do-not-do-early: no state, feature or compatibility scaffold lands before its complete vertical feature. Narrowly reopened once, for the `Emit.Image` mint (§6). |
| ARCH-12 | Rob accepts only the exact reviewed green HEAD. |
| EVID-01 | Pinned spec and memory-model bytes. |
| EVID-02 | Reproducible extraction and audit outputs. |
| EVID-03 | Evaluation-order nondeterminism and deterministic specified-order fixtures. |
| EVID-04 | FMA both-branches model; target observation is adequacy evidence only. |
| EVID-05 | Select, map-iteration and scheduling nondeterminism; print adequacy demotion. |
| EVID-06 | Module, language and toolchain boundary; no-switch invocation. |
| EVID-07 | The terminal observation tuple (`TOOLCHAIN.md`). |
| EVID-08 | Applied-only provenance and the judgment split: a record names the change actually applied, and a mechanically checkable claim is kept separate from a human judgment, which is never certified. |
| EVID-10 | NaN map and struct-tag semantics, with fixtures. |
| EVID-11 | The proof-cost contract remains fixed. |
| EVID-12 | `uintptr` stays out unless a reviewed scope change lands. |

Frozen spec-closure proof contracts. Each row states the obligation a milestone must discharge to claim the
contract. `ROADMAP.md` names which milestone consumes which; `.review/closure.csv` and
`.review/latitude.tsv` name the exact rows, each carrying its `contract` and its owning `milestone`.

| id | contract | binding obligation |
|---|---|---|
| SC-00 | PIN-LEDGER-CLOSURE | Every pinned spec, memory-model, cmd/go and toolchain artifact is hash-recorded, and every heading, EBNF production, reserved keyword, operator, punctuation token, predeclared identifier and extracted latitude sentence it contains has exactly one ledger row — `IN` with an owner chain and a contract, or `OUT` with constructor-level unrepresentability and a written price. |
| SC-01 | SOURCE-LEXICAL-RENDER | Source representation, identifiers, tokens, semicolon insertion and canonical literal spelling encode exact source values, and comments, raw-string spelling, raw-source parsing, build constraints and directives have no constructors. |
| SC-02 | CONSTANTS-LITERALS | Every literal form, exact untyped constant, typed constant, `iota`, constant expression, representability, defaulting and overflow rule is covered, and no fixture bound stands in for a spec bound. |
| SC-03 | BINDINGS-DECLARATIONS-BLANK | Blocks, scopes, labels, declarations, per-iteration variables and closure capture keep static slot identity separate from dynamic place identity, and `_ = f()` evaluates `f` exactly once while creating no binding. |
| SC-04 | TYPES-PROPERTIES-GENERICS | One type algebra decides underlying type, identity, assignability, conversion, comparability and instantiation for every type form including generics — struct tags participating in identity — and no second type-identity system exists. |
| SC-05 | EXPR-FACT-USE-EVAL | One context-free fact per expression and one exact fact per use edge; the production path never re-analyses the raw child, absent use kinds are unrepresentable, and order is proved exactly where the spec fixes it while both permitted sibling orders stay runs where it does not. |
| SC-06 | SOURCE-ZIPPER-CONTROL | All control flow runs on a running focus continuation plus a finishing reason, with jump targets consuming retained continuation skeletons and no runtime source walk constructing one. |
| SC-07 | FUNCTIONS-CLOSURES-MULTIRESULT | Function declarations and literals, methods, variadics, closures, recursion, method values and expressions, and typed argument/result sequences have exact call and return continuations. |
| SC-08 | STORE-PLACES-CONVERSIONS | Composite objects, allocation, addressability and conversions forge no identity and reuse none, typed lookup is total on reachable states, strings are values rather than mutable objects, and append aliasing, fresh-capacity and zero-size-comparison latitude keep every permitted branch. |
| SC-09 | PANIC-DEFER-RECOVER | Defer, panic and recover use stack-only state — no recover token, panic monad, global panic state or second evaluator — and a non-defer push from `Finishing` is unrepresentable by constructor absence. |
| SC-10 | GOROUTINES-CHANNELS-SELECT | Goroutines, buffered, unbuffered and nil channels, send, receive, close, range and select are decided by `enabled_dec` and the one `step`, with no ready queue, waiter registry or second scheduler, and every permitted schedule remains a run. |
| SC-11 | MAP-ITERATION-NONDET | Every valid next-key choice is a `step` branch and every key order a valid run, the chosen order appears in `Action` labels, and no host map order or canonical sort decides semantics. |
| SC-12 | HB-RACE-CHANNEL-EDGES | The channel happens-before edge set is exhaustive and named — send-to-receive-completion, capacity, close-to-zero-receive, unbuffered receive-to-send-completion — each with a positive fixture and a negative fixture whose race result changes without it, and every trace event comes from `step`. |
| SC-13 | INTERFACE-GENERIC-CLOSURE | Method sets, promoted selectors, typed nil, dispatch, assertion and type switches close under substitution, with no runtime type registry and no re-derived conformance. |
| SC-14 | PACKAGES-INIT-STARTS-EXIT | Initialization follows every dependency edge and rejects cycles before `Compilable.Program`, multiple command roots produce independent starts, the emitted `go.mod` carries exactly the accepted module path and `go 1.23` with no `toolchain` directive, and final states have no steps. |
| SC-15 | BUILTINS | Every admitted predeclared built-in resolves through ordinary binding facts, receives exact use facts and executes through `step`; `print`/`println` output formatting is pinned-toolchain adequacy evidence, never a portable language theorem. |
| SC-16 | ERRORS-UNREPRESENTABILITY | Acceptance and rejection are decided over one retained whole-elaboration object and every diagnostic projects from the exact object that produced it; no rejected program mints `Compilable.Program`, `Safe.Program` or `Emit.Image`, and no broad "unsupported" catch-all stands where the ledger names distinct exclusions. |
| SC-17 | RENDER-ADEQUACY-MEMBERSHIP | Direct rendering covers every admitted constructor with no raw-text escape and one `Emit.Mint.issue` publication path; a deterministic program matches the pinned observation tuple exactly, and a nondeterministic one only through a sound-and-complete membership checker that consumes `enabled_dec` and defines no semantics. |
| SC-18 | ENABLEDNESS-DECISION | `enabled_dec` decides readiness for nil, buffered, unbuffered, closed, select-with-default, absorbing and deadlock states, and agrees exactly with relational `step` on reachable well-formed states. |
| SC-19 | OUT-BOUNDARIES | Every `OUT` row freezes its missing constructor, the valid Go it gives up, the reason, the future-inclusion price, and a proof that no host helper or generic fallback can reintroduce the behaviour. |
| SC-20 | EVAL-ORDER-LATITUDE | Every latitude row is owned by the one relational `step` with no generic choice authority, and no row adds a public machine field, a second evaluator, a scheduler object or a generic `Choice` action. |
| SC-21 | PROOF-COST-INTERNALS | The public base is fixed while internal forms stay disposable: an internal type or index is kept only when removing it admits a real invalid state, and a capability retaining only copied fields plus equality to a recomputation is a failed design even when its extensional theorems pass. |
| SC-22 | ACCEPTANCE-ALIGNMENT | `fido_accepts_subset_pinned_gc` is discharged incrementally by the checkpoint that makes each restriction representable, without making pinned gc a language-semantics authority — a finite probe set is evidence, never the global theorem. |
