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
                ┌ Compilable.compile → Safe ┐   Compilable is the sole Go static verdict; Safe refines it
Syntax.Program ─┤                           ├─ Emit.Image → Fido Materialize → pinned go build ./...
                └ Render ───────────────────┘   direct Syntax → canonical bytes
                                                → make regenerate publishes the SAME bytes
```

`Render` and static compilation are **sibling branches** over the one `Syntax.Program`; they share no import
and join only at `Emit`, which renders the exact `Safe.source` of a program the compilation branch admitted.

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

**One authority per fact.** Each module owns exactly what this table names, and never what another owns.

| owner | owns | does not own |
|---|---|---|
| `Collections` | standard maps and sets, and one tiny nonempty sequence type | a new collection framework |
| `Names` | lexical identifier validity, ordinary-name refinement, the complete pinned predeclared spelling identity catalog, and the byte-level ASCII predicate every rendered file is proved to satisfy | scope, binding, semantic type, call rules, or support policy |
| `Syntax` | source structure and source values | resolution, object identity, semantic type, diagnostics, variable identity, or behaviour |
| `Index` | exact source-occurrence identity, views, parents, children, and source roles | binding, typing, diagnostics, or semantic facts |
| `Compilable` | scopes, semantic objects, binding, the retained static analysis, type/expression/use/application facts, result plans, static variable identity, dependency objects, diagnostics, scope boundaries, and the three-way decision — its type forms, package identity, binding, analysis and report living in physical child modules (`Compilable.TypeResolution`, `Compilable.PackageIdentity`, `Compilable.Bindings`, `Compilable.Analysis`, `Compilable.Report`), never peer layers | runtime values, dynamic places or environments, rendering, or behaviour |
| `Machine` | the one behaviour relation and derived runs | static compilation or a second evaluator |
| `Safe` | only the safety property and the transparent certificate retaining the exact compiled capability | values, stores, evaluation, rendering, or static facts |
| `Render` | direct canonical source bytes | binding, typing, fact construction, or evaluation |
| `Runtime` | **introduced by C7**: values, the permanent object store, dynamic places, dynamic environments, and their intrinsic operations | static variable identity, name binding, static facts, safety, or a second run relation |
| `Emit` | the one image mint and exact emitted bytes | source or semantic authority |

`Integer` owns integer width, `Float` float format and `Complex` complex format. There is no `TargetConfig`,
no `GoTypeTag`, no second width or conversion authority, no typed AST beside the one raw `Syntax`, and no
source-name table in `Syntax`, `Compilable.TypeResolution` or `Render`.

One row is still the destination rather than today's tree: `Runtime` does not exist, and **C7 creates it**,
because no state or runtime scaffold lands before the complete vertical feature that consumes it (`ARCH-11`).
The pre-C7 `Float.Value`, `Complex.Value` and `Safe` evaluator/value route are deleted: float and complex
typed constants are purely static, and C7 creates the first runtime values.

The static rows now hold their contents, not merely their division. `Index` owns the intrinsic occurrence
identity and its refined position-selector references; `Compilable.TypeResolution` owns the type facts; the
retained binding phase resolves each ordinary source name; and `Compilable` owns the scope, object, boundary
and three-way `Compiled`/`Rejected`/`OutsideScope` decision over one retained phase, carried transparently by
the accepted `Program`. `Names` owns the ordinary-name refinement and the complete predeclared identity
catalog, seated in the outer scope where any declaration may shadow it.

The remaining type-system content is later C6 roots, not current fact. The type universe is still the bare
semantic forms, so named basic-type identity (`int` distinct from `int32`), defined and alias type meaning,
nonconstant conversions, and the program-indexed type environment are deferred; until they land, every
conversion the current fragment expresses is constant and a predeclared type-name denotes one of the sixteen
bare forms.

**Support that depends on binding is decided after binding.** Constructor absence owns every exclusion syntax
alone can identify. Where legality depends on which object a name resolves to, `Syntax` carries the ordinary
source form and `Compilable` reports an exact scope boundary over an exact unmet **semantic requirement** —
the exact site, the exact resolved object or target, and the exact argument profile where the missing rule
depends on one. That is a third outcome beside acceptance and rejection, never a claim that the source is
invalid Go.

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

### Physical structure follows semantic structure

One semantic owner may span several Rocq compilation units. Size alone never triggers a split; only a
permanent semantic root with a one-way dependency does. `Foo.v` is the composition and public-capability
boundary. `Foo/Bar.v` is a permanent internal layer named `Foo.Bar`, and it is named for the facts it owns —
never `Utils`, `Common` or `Helpers`.

Lower layers do not import higher layers, and production never imports an evidence layer. A split creates no
duplicate carrier, compatibility facade, callback registry or reconstructed provenance: the same fact keeps
the same single owner on both sides of the cut. A circular dependency is not an obstacle to route around; it
means the semantic cut is wrong, and it returns to review.

C6 decomposes `Compilable` on exactly this rule:

```text
Compilable/TypeResolution.v    the permanent type-form layer (`TypeForm`, constants, conversion forms) — form, never identity
Compilable/PackageIdentity.v   the retained package surface, `PackageRef` position selectors, and `package_of_file`
Compilable/Bindings.v          scopes, object-establishing binders, declaration-kind visibility, and the fixed-spelling
                               `func main()` occurrence qualified through PackageIdentity as `MainDeclRef s pr`, with
                               `MainMissing`/`MainOne`/`MainMultiple` multiplicity; the retained binding phase
Compilable/Analysis.v          the sole fact and issue authority: per-occurrence value/application/statement/type-use
                               outcomes with blocking over one retained fact phase, the selected-nonempty-package
                               fresh-output preflight, and the one canonical issue table (cause, class, subject, root, order)
Compilable/Report.v            projection only: it resolves and classifies nothing, projecting the canonical Analysis
                               issue table into ordered diagnostics and boundaries
Compilable.v                   the sole composer and sealed public surface: one retained abstract `Compilation` built once,
                               `compile` the sole `Decision` source, `inspect` its sole eliminator, `compiled_prog` the sole
                               payload-gated `Prog` projection, and the permanent three-way Compiled/Rejected/Outside decision
```

TypeResolution and PackageIdentity precede Bindings; Bindings precedes Analysis; Analysis precedes Report;
Report precedes `Compilable.v`. No child imports `Compilable.v`. Further C6 children (package dependency order,
runtime) stay prose-only and frozen until this milestone is accepted.

`Compilable.Analysis` owns the resolution facts and issues: the name-resolution meanings and the resolver over the
retained index and the once-gathered establishers (whose gathering already fixes the declare-then-use order a short
or grouped declaration needs), the per-occurrence outcomes, the fresh-output preflight, and the one canonical issue
table. `Compilable.Report` consumes the completed Analysis and owns only its projection into diagnostics,
requirements, boundaries and the canonical report lists — it selects no cause, order, or fallback. The dependency
runs one way — Report onto Analysis — and the layer gate confirms no cycle.

### Direct module dependencies are gated

The physical dependency graph is itself a checked artifact. The block below is the **sole** authority for which
direct `From Fido Require` edges may exist: it names every module in the Dune theory exactly once, with its
exact current direct Fido dependencies and nothing dormant. The layer gate in the prover build runs pinned
`rocq dep` over the same module universe Dune builds and requires the actual direct-edge relation to **equal**
this block. A forbidden edge fails whether or not any declaration from it is used; a listed edge with no
matching import fails as a dormant authorization; an unknown or unmapped module fails closed.

<!-- FIDO-LAYER-POLICY BEGIN -->
```text
Decimal:
Integer:
Float:
Complex: Float
FilePath:
ModulePath:
Version:
Collections: FilePath
Names:
Syntax: Collections FilePath Float ModulePath Names Version
Index: Collections FilePath Syntax
Compilable.TypeResolution: Complex Float Integer Names
Compilable.PackageIdentity: FilePath Index
Compilable.Bindings: Compilable.PackageIdentity Index Names Syntax
Compilable.Analysis: Compilable.Bindings Compilable.TypeResolution Complex FilePath Float Index Integer Names Syntax
Compilable.Report: Compilable.Analysis Compilable.Bindings Compilable.PackageIdentity Index Syntax
Compilable: Compilable.Analysis Compilable.Bindings Compilable.PackageIdentity Compilable.Report Compilable.TypeResolution Index Syntax
Machine:
Safe: Compilable Syntax
Render: Complex Decimal Float ModulePath Names Syntax Version
Emit: Collections FilePath Names Render Safe Syntax
```
<!-- FIDO-LAYER-POLICY END -->

The relation shows the sibling structure directly: `Render` lists no `Compilable.TypeResolution`, `Compilable` or `Safe`, `Emit`
lists no `Compilable`, and the two branches meet only at `Emit`. The gate's claim is exactly that the direct
edges `rocq dep` reports equal this relation and that every theory module is covered once. It does **not**
prove that a listed import is used, that a referenced owner is imported directly, that no forbidden name
arrives through notation, coercion, hint or transitive visibility, or that a theorem belongs semantically to
its module — those remain ownership-first review obligations.

---

### Two authorities, never two formal implementations

Two kinds of authority govern every milestone, and there are never two of the same kind. **Governing prose** —
this file, `ROADMAP.md`, `DECISIONS.md`, `.review/scope.tsv` and the active `.review/NEXT.md` — owns required
semantic meaning, checkpoint scope, supported and unsupported boundaries, downstream obligations, acceptance
and evidence gates, and dependency order. The **canonical Rocq implementation**, in its permanent production owner,
owns the exact inductive, record and index topology, the exact constructors, the exact theorem statements, the
exact definitions and proofs, and the formal object later layers consume.

Neither silently overrides the other. If canonical code fails a governing semantic obligation, the code is
wrong. If implementation or proof evidence shows the prose forces a wrong abstraction, the prose is wrong and
is amended in the same review. A mismatch is a defect to resolve, never a precedence shortcut. There is no
second executable or formal rendition of the same layer: no shadow `.v` subsystem, no independently elaborated
"contract surface", no duplicate theorem catalogue used as an implementation source, no peer formal model that
production is later reconstructed from, and no future-milestone implementation disguised as planning.

**The active milestone is formalized directly in its canonical modules**, once every milestone it depends on is
accepted. Work proceeds in dependency-closed semantic roots — never line-count, time or convenience slices. For
each root: establish public types and constructor topology first; secure exact provenance and impossible-state
exclusion; state only the guarantees the root exposes; complete definitions, proofs, tests, artifacts and
required document changes; delete every superseded representation and path in the same terminal change; and
review the whole current system before building a dependent root. No dependent root may use an unsettled one.

While a milestone still carries a prose rendition of its own formal surface, that rendition is migration input
only: non-authoritative, not independently elaborated, and true only of the portions not yet canonicalized. Each implementation commit canonicalizes one dependency-closed portion in its
permanent owner, deletes the corresponding rendition in the same commit, and deletes any superseded production
authority in the same commit, so no exact formal fact is ever authoritative in two places. The rendition
reaches zero at milestone completion; nothing is moved to another document, because Git owns history.

**Future milestones remain prose-only** until all their dependencies are accepted. Their prose is adversarial
downstream pressure — used to test whether the active lower abstraction is general enough — never permission to
implement the future, to add future state, fields, constructors or theorems early, or to keep compatibility
scaffolding.

**Shadow implementation is forbidden; scratch checks are narrow and disposable.** A permitted scratch check is
the smallest experiment that answers one isolated question cheaper to test in the pinned toolchain than to
settle by inspection — whether one constructor elaborates, whether one index introduces a cycle, whether one
impossible state stays unconstructible, whether the pinned toolchain accepts one namespace or parser fact. It
defines no alternate subsystem or public surface, carries no milestone-wide theorem catalogue, never becomes a
source production is reimplemented from, never enters the build or repository history, and is deleted before
terminal verification and reported with its question, result and the decision it informed. If scratch work
begins to carry load-bearing architecture, it stops: delete it and continue in the canonical owner. There is
no committed scratch directory and no retained scratch manifest.

**Dependency retreat (targeted causal).** If new evidence shows a load-bearing accepted fact is wrong — an
accepted public type or constructor topology, semantic meaning, retained provenance or causal identity, public
theorem guarantee, boundary, or an accepted fact a higher layer's correctness depends on — retreat is
**targeted and causal**, driven by the affected contract and its real dependents, never by Git ancestry or
milestone number:

1. Historical acceptance stays a historical fact. A repair never rewrites an accepted checkpoint as
   never-accepted, and invents no earlier checkpoint.
2. The evidence freezes exactly the work that causally depends on the wrong fact.
3. The retreat begins from the exact affected accepted contract or guarantee surface, not from ancestry or
   milestone order.
4. That earliest affected guarantee is repaired and reviewed on one immutable candidate.
5. Every later accepted claim with a real causal dependency on the changed guarantee is reopened and
   revalidated.
6. Every accepted checkpoint claimed unaffected requires explicit **negative causal closure** — positive
   theorem-type, constructor, computation, dependency, artifact or contract evidence that its accepted result
   does not depend on the changed guarantee. Silence is not closure, and absence of a current code consumer
   is not by itself closure; the burden is on the claimant to establish nondependence.
7. An unaffected checkpoint is not replayed merely because it is a chronological descendant.
8. Revalidation judges whether the surviving abstraction is still the correct one on the repaired
   foundation, not merely that it still compiles — simplifying, deleting or redesigning where warranted.
9. No invented pre-C0 checkpoint, history rewrite, status-commit ladder, or one-commit-per-old-checkpoint
   sequence.
10. Rob alone closes a targeted retreat and later accepts the affected frontier.

This refines dependency retreat, it does not delete it: a genuinely load-bearing downstream dependency still
reopens. A demonstrably internal proof refactor that changes no semantic, provenance, public-guarantee or
boundary dependency needs no retreat; uncertainty means freeze and report.

**Review and acceptance.** An exhaustive review is the archive-authoritative sixteen-pass Wirth whole-system
protocol. Sixteen criterion-isolated pass agents each answer one whole-system question — architecture,
ownership, simplicity, semantics, intrinsic correctness, provenance, single authority, guarantee strength,
boundary honesty, capability, execution path, proof integrity, foundational stability, retention, artifact
adequacy, and governance — over the same exact immutable candidate: a frozen source archive identified by its
ZIP-comment commit and archive SHA-256, not the live `HEAD`. Each inspects public types and constructor
topology before proof bodies, freezes one findings report, and grades it; the candidate's grade is the weakest
of the sixteen, never an average. A separate seventeenth synthesis role reads the sixteen frozen reports, maps
their convergence, conflict, asymmetry and silence, and produces one dependency-ordered implementation
contract. The submitted archive carries Rob's trusted attestation that its required gates passed before
handoff, so a review inspects gate definitions, coverage and retained artifacts but never reruns the pinned
toolchain and never treats local tool absence as missing evidence. Reviewers propose; no pass and no synthesis
accepts; Rob alone accepts, and no work is manufactured after the reviewed frontier has survived review.
`life.md` is outside this protocol and outside every actor's authority.

**Strict checkpoint scope.** Whole-system inspection remains mandatory, but a finding blocks the active
checkpoint only when it violates that checkpoint's accepted semantic, provenance, public-guarantee, production,
artifact, trust-boundary, or required-dependency contract, or when it makes a prerequisite fact on which the
next work relies unestablished. A tooling, gate-hardening, mutation-coverage, reporting, documentation,
performance, or repository-hygiene finding that does not undermine that foundation is mandatory concurrent
work, assigned to the earliest checkpoint that must consume or close it. It must remain visible and must close
before an acceptance whose evidence depends on it, but discovery alone does not expand the active checkpoint.
Concurrent treatment is forbidden — the finding is a hard blocker on the active checkpoint — for a wrong public
type, index, or constructor topology; lost, reconstructed, or ambiguous provenance; a theorem statement weaker
or stronger than the accepted guarantee; a duplicate semantic authority; an axiom, `Admitted`, unimplemented
assumption, trusted fallback, fuel, arbitrary bound, or semantic under-approximation presented as correctness;
changed source meaning, compiler decision, diagnostic, emitted byte, runtime behavior, capability, or trust
boundary outside the active contract; a gate defect that makes an unestablished semantic prerequisite appear
established; or any defect in an accepted lower fact that the next semantic root actually consumes. Every
concurrent finding carries a named earliest mandatory closure point; this is not permission to defer cleanup
indefinitely.

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

One transparent terminating fold (`flat`, over `file_occs`) builds each file's ordered occurrence list once,
assigning each represented occurrence its canonical file-local `nat` position by deterministic preorder, file
root = 0. `raw_index p` maps each file path to that list and `ProgramIndex p` is sealed to it (`{ l | l =
raw_index p }`); every consumer reads it through `prog_occs`, none re-folds the raw source.

A reference is a **dependent selector into that retained object, valid by its indices** — not a coordinate,
key, Boolean or table handle. A `NodeRef` is a `FileRef` plus a position `nr_pos` and a proof `nr_pos <
length (local_index idx nr_file)`; a malformed position has no inhabitant, so an out-of-range or foreign-file
reference cannot be constructed, and `le`-proof-irrelevance makes a reference's identity exactly its
file-and-position. `node_ref_cursor` projects the exact retained member by total `nth_lt` — never a fallback.
`BinderRef`/`BlockRef` refine a `NodeRef` with an erased `Prop` proof over the projected role/kind, so a
wrong-role reference is likewise unconstructible; the proof erases at `vm_compute`, so the id is byte-identical.
Transparency preserves `vm_compute`; unforgeability comes from the indices, not from opacity.

The query API is **total by carried validity** — only `parent_of` is optional — never a semantic fallback.
Navigation is exact: file/node/parent/member projections over the retained object, kind/role refinements over
the exact projection, and one canonical enumeration. No per-node search, no coordinate/equality/Boolean-backed
peer mint, no raw-source semantic enumeration, no located or copied AST, no second tree.

### Compilable.TypeResolution — the type authority

`Compilable.TypeResolution` is the type child of `Compilable`, evidence over the raw syntax, never a typed AST.
The type universe **today** is exactly `{ BoolType, IntegerType over the ten Integer kinds, FloatType,
ComplexType, StringType }` — bare forms with no identity of their own. A later C6 root will replace that with
the Go rule: each predeclared basic type becomes a **named identity**, so `int` and `int32` are distinct types
that merely share an integer form, and a defined type is a further identity carrying its exact declaration
reference. Form is what conversion and representability read; identity is what assignability reads, and the two
are never the same fact. `byte` and `rune` are aliases — they mint no identity and are identical to `uint8`
and `int32`. The universe grows only through reviewed milestones, never by a string, numeric tag or registry.

A raw literal denotes an **exact untyped constant**: integers arbitrary-precision, a bare float literal an
exact canonical rational, a complex literal an exact pair of rationals, strings exact byte sequences.

`Compilable.TypeResolution.TypedConstant : SemanticType -> Type` is an intrinsic dependent family. **A mismatched or
out-of-range typed constant is unrepresentable, never merely rejected.**

`Compilable.TypeResolution.convert_constant` is today's one conversion authority, and every conversion the current fragment can
express is constant. Integer conversions are value-preserving and range-checked. Float conversions round
**once at the destination** — F32 directly at binary32, never via F64, and a same-format float is returned
unchanged. Complex conversions round each component once, and scalar↔complex follows Go's zero-imaginary
rule.

A later C6 root makes conversion **two rules, because Go's are not one rule**: the constant authority above,
restated over a destination basic form, and beside it a **nonconstant** authority, strictly narrower —
identical types, types sharing an underlying form, scalar numeric to scalar numeric, and complex to complex.
It will admit no scalar↔complex crossing, so `complex128(i)` and `float64(c)` on variables are rejected exactly
as pinned `gc` rejects them, and a conversion site will read the constant rule when its operand is constant and
the value rule otherwise, neither a fallback for nor defined from the other.

A conversion is one `Application` whose head resolves through the retained binding phase to a **source** type;
its semantic target is the compiler-owned resolution of that name. The index-free typing spec is parameterized
by that resolver, so `Compilable.TypeResolution` owns no source-name → semantic-type table.

`Compilable.TypeResolution.resolve_constant_info` is use-context resolution. An untyped constant **defaults** (int →
`IntegerType Int`, float → `FloatType F64`, complex → `ComplexType C128`); a typed constant **packs
unchanged**, because its validity is intrinsic — not re-defaulted, not re-checked.

A float typed constant is purely static: it retains the exact post-rounding rational and the exact
destination-format rounded representation from the **same** one rounding as static proof data, and a complex
typed constant composes two such carriers. Neither projects a runtime value.

`ConstantRepresentable` is derived from successful typing, routing numeric targets through
`convert_constant`, so representability and conversion can never disagree. There is no second range or
overflow checker, no placeholder type, and no typed AST.

### Admissible — exact whole-program acceptance

`Admissible` is **exact whole-program compiler admissibility** — the pinned one-shot `go build ./...`
acceptance — not a subset filter, and a declarative characterization that mints nothing. It holds exactly when
the retained phase's reports are both empty:

```text
Admissible p := all_diags p = [] /\ all_boundaries p = []
```

`Compilable.diagnostics` aggregates the fresh-build preflight, package-rule and per-occurrence diagnostics;
`Compilable.boundaries` aggregates the out-of-scope boundaries — both are `Compilable.Report` projections of the
one retained fact and package-fact phase. Files group by parent directory into packages; one invalid package
rejects the whole program, so acceptance is all-or-nothing. The preflight is cmd/go's default-**output** rule:
a sole main package's default executable name must not collide with an existing root directory; zero or
two-or-more packages write no default output, and the empty program is accepted.

The private composer (a `Local` `elaborate`, never a public route) builds one retained `Compilation` — the
intrinsic index, the package surface, the binding phase, the package facts and the fact phase — computed once,
each field a dependent projection of the one before it. `Compilable.compile p` is the **sole first source** of a
`Decision p`; `inspect d` is the **sole eliminator**, revealing the exact retained `Compilation` and the exact
abstract branch payload of that supplied `d`. There is no public elaborator, no public decision constructor,
and no second checker. `Compilation`, `Decision`, every branch payload, and `Prog` are abstract to a client.

The one analysis computes two orthogonal sets — **definite diagnostics** and **exact scope boundaries** —
and the decision has three branches whose precedence is fixed: any diagnostic gives Rejected (which may retain
simultaneous boundaries); no diagnostic with any boundary gives Outside; both empty gives Compiled. **A boundary
never becomes a diagnostic.** `admissible_iff_reports` characterizes admissibility as exactly both lists empty.

The Compiled branch exposes the one `Prog` capability only through `compiled_prog` on the exact supplied compiled
payload; `Prog.Program` is an abstract type whose admissibility-gated maker `issue` is **private** to the
capability module, so no public theorem or transport turns an arbitrary `Compilation` plus `Admissible` into a
`Prog`. The rejected/outside payloads expose only their exact report lists (`rejected_diagnostics`,
`rejected_boundaries`, `outside_boundaries`). Only a compiled payload's `compiled_prog` reaches `Safe.Program` or
an `Emit.Image`. Public `Case` constructors are harmless: a caller must already hold the matching abstract payload.

Diagnostics are structured values anchored in the exact retained index: unresolved name, invalid identity,
type-as-value, not-a-type, non-callable object or expression head, conversion arity/overflow/not-representable,
complex arity/mismatch, unary mismatch, default-integer overflow, no-value-used, illegal statement, const
missing-initializer, result-count mismatch, short duplicate, and the package/main/output-collision issues. Each
is a canonical `Analysis` issue-table row with an exact subject, class, cause and source-order ordinal; `Report`
projects them into ordered diagnostics and boundaries and selects no cause, order, or fallback. **An outcome is a
structured branch and its exact issue list, never a collapsed tag.**

The three-way outcome is not owned exclusively by completed type resolution. An outside boundary is the exact
earliest unmet requirement at an exact retained site, so it arises from the earliest partial-phase fact that
establishes it: an established source object with no yet-modelled type, value, application, statement or unary
meaning is a boundary as much as a type-level one, and the outcome is live as soon as the phase retains scopes,
objects and bindings. Later semantic roots fill deeper requirements inside the same sealed retained phase; they
never replace the outcome/boundary root or reinterpret an established boundary as a diagnostic. The fixed
precedence above and the one-core provenance law below are unchanged.

### Retained causal objects

The production analysis is one retained `Compilation`: the intrinsic index, the package surface, the binding
phase, the package facts and the fact phase, each a field typed by the exact prior field it consumes. Nothing is
rebuilt or re-proved by a consumer — every downstream reading is a projection of a retained field.

Occurrence identity is intrinsic. A `NodeRef` is a key into one file's retained finite position map of shallow
cells, indexed by the exact `ProgramIndex` with an irrelevant membership proof; a `PackageRef` is a position into
the retained package surface; a `MainDeclRef s pr` qualifies the exact `MainOccurrenceRef` (a `VTop (Syntax.Main
body)` occurrence) through PackageIdentity, making membership in package `pr` intrinsic, and its multiplicity per
package is `MainMissing`/`MainOne`/`MainMultiple`, independent of the ordinary declaration group keyed by `main`.
A reference from a foreign index, surface, or package is unrepresentable by type, never rejected by a check.
There is no `List.find`/`existsb` scan or recomputed peer object in the read path.

The phase retains the whole flow as a dependent chain: the causal chain **is** the dependent types, so a foreign
component is unrepresentable by type mismatch rather than caught by a comparison.

**Equality to a recomputation is never provenance.** The retained `Compilation` holds each phase once; the index,
facts, package facts, diagnostics and boundaries are projections of it, never a stored equality to a rerun. The
compiled capability `Prog.Program` is abstract — sealed behind a module signature whose only maker `compiled_prog`
demands a compiled payload obtained by eliminating a supplied `Decision`, its admissibility-gated `issue` private —
so a client cannot forge one, and `compile`/`inspect` are the only route. `compile`, `inspect`, `Decision` and the
payloads stay reducible so witnesses materialize through them; only `Prog.Program` is opaque, and the byte path
projects it away (`Safe.source` is a primitive projection), so opacity never strands `vm_compute`.

From C6 the same rule binds the phase the core retains. The **exact type environment** built during the
phase, the **exact package dependency outcome**, and every accepted binding, object, expression, use,
application, result-plan and static-variable fact are projections of that one phase — not rebuilt by a
second call to the environment builder, and not declared as independent accepted-world families beside it.
The environment is not total over phases: the phase result is a sum, and a phase that found a type cycle
holds a cyclic result and therefore has no environment at all. The accepted environment is reached by
**dependent elimination** of that result, never by an equality bridge to a rerun.

### Structural progress and cost

Every load-bearing construction is **structural recursion over finite maps**, terminating by construction: no
fuel, gas, step budget, retry count, timeout, recursion limit, arbitrary maximum, or cached last-good result
appears anywhere in the certified theory. The numbering pass, the per-file position map, the package surface,
the binding phase, the fact phase, the issue table, and the report projection are each a single structural pass;
`fact_phase_one_pass` proves the retained fact phase is exactly one row per indexed occurrence.

The construction cost is charged in explicit parameters, with no unit-cost strings and no assumed physical
sharing: `F` source files, `N` indexed occurrences, `E` direct occurrence edges, `P` selected nonempty packages,
`B_n` named establishments, `M` fixed-main establishments, `B` total status rows, `G` canonical declaration
groups, `Q_o`/`Q_s`/`Q_b` name-use / statement / short-left incidences, `R` report members, `A` applicable fact
rows, `I` canonical issue rows, `D` diagnostics, `U` boundaries, `L_path` characters inspected for the singleton
default-output name, and per-stage `chi_*` character inspections, `J_X` reference incidences, `K_X` cells
constructed, and `S_X` retained copies. The stage bounds: Index is one preorder pass building `N` cells and `E`
edges (`O(N)` map inserts, each `chi_file`-bounded); PackageIdentity is `O(F·chi_file)` for the surface plus the
`P`-scan; Bindings is `O(B_n + Q_b)`; Analysis is one `O(N)` fact pass plus the `O(P·L_path)` preflight and the
issue-table fold `O(A + I)`; Report is an `O(R)` projection with no re-scan; Decision/Safe/Emit are `O(1)`
projections plus the `O(K_render)` byte traversal. Retained space is `O(N + B + G + I + R)` fields, each an exact
retained reference, never a duplicated source tree or repeated prefix scan.

### Machine — the abstract run base

`Machine.T` is the one labelled-transition base every later runtime milestone shares: opaque `State`,
`Start`, `Label` and `Result`, plus `initial`, a **relational** `step`, and `final`. Nothing else is a field.

`FiniteRun` is built only from real steps, so a trace is exactly the labels it consumed; `InfiniteRun` is
coinductive and observes one real step at a time. `Reachable`, `Enabled`, `Disabled`, `FinalAbsorbing` and
`Stuck` are derived from those, and `EnabledDecision` freezes the one decision shape later machines must
prove **from the same relational `step`** — it is not a second semantics.

**`Machine` fixes no Go feature, and this repository defines no concrete `Machine.T` value.** The record and
its constructor are public — its component types are abstract parameters of a value, not an opaque interface
— so a `Machine.T` is constructible by anyone who supplies the seven fields. What does not exist here is any
concrete Go state, label or result, any machine value, or any `EnabledDecision` inhabitant, and no module
imports `Machine` yet. Its product is the base itself; the first complete runtime vertical feature is what
consumes it. Adding a concrete machine early, merely to give it a consumer, would be exactly the scaffold
ARCH-11 forbids.

**There will be exactly one concrete machine, and C7 builds it.** C6 is entirely static: it supplies the
retained facts, compiler-owned variable identities and the initialization-dependency object a runtime
consumes, and adds no runtime module, value, place, store or environment. C7 introduces `Runtime` and the
machine together, as one vertical. C7 is the first `Machine.T` over the exact compiled capability (the retained
`Compilation` and its `Prog.Program`): it gives
the existing expression and `println` fragment one run relation and adds its own expression, output, order and
fatal-panic slice. Safety refines that same behavior later; the machine never depends on a `Safe` certificate. Every later
milestone extends that same machine's sealed internals — C8 adds control, C11 generalizes starts to imports
and package dependency order — and none replaces it with a peer. A second run relation is the failure this
base exists to prevent.

---

## 4. Safety, capabilities and provenance

`Safe.Program` is the permanent safety boundary over the compiled capability: `Safe.certify` retains the exact
`Compilation` and its `Prog.Program` plus a proof of `Property` over that capability. `Property := True` is honest
**today** — the fragment contains no unsafe operation. It is the extension point for guarantees beyond
compiler acceptance, not a circular claim, and it carries no unused panic or control placeholder.

Float and complex typed constants are purely static. A `Float.TypedConstant` retains the exact post-rounding
rational and the exact destination-format rounded `spec_float` from the **same** one rounding as static proof
data; the format index is load-bearing, and negative zero, infinity and NaN are unconstructible. C6 has no
runtime value, store or evaluator; **C7** owns runtime representation and execution.

There is no whole-program execution semantics yet; only the witness package is executed against goldens. A
per-package program semantics arrives when a construct needs it.

**A compound typed constant is composed from already-coherent typed components.** A typed complex constant is
a pair of typed float components, reusing each component's coherence rather than duplicating it at the
aggregate layer. The untyped / typed distinction holds at every level.

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

Rendering is a **sibling branch** of static compilation: `Render` traverses raw `Syntax` and imports no
`Compilable.TypeResolution`, `Compilable`, `Safe` or evidence authority. Each canonical spelling carries an **independent
renderer-local decoder** proving the exact source-value round trip — the integer, string, decimal and complex
inverses recover the exact lower source value those bytes encode. These are direct source-value inverses, not
a compiler-semantic denotation: any correspondence between a rendered spelling and the constant status
`Compilable.TypeResolution` computes belongs to a later downstream adequacy layer with an exact retained premise and a real
consumer, and is absent until then.

There is no tokenizer, lexer, parser or round-trip authority, and no formatter is invoked.

---

## 6. Emission and the OCaml transport boundary

An `Emit.Image` is a sole-constructor witness carrying only the certified `Safe.Program`; its bytes — the exact
root `go.mod` and a finite map from `FilePath.T` to exact final `.go` bytes — are obtained solely by projection
through `Emit.transport`, never stored. The `.go` map may be empty; **there is no nonemptiness claim**.

`Emit.of_safe : Safe.Program -> Image` is the sole image route. Because it is the only constructor and takes
only a certified program, there is no raw-byte, file-map, origin, token, or equality slot a client could fill
with foreign bytes: provenance is intrinsic to the constructor, not a separate mint. `transport (of_safe sp)`
reduces to `(module_file sp, entries sp)` — the bytes rendered from that one `Safe.Program`'s retained source.

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

**Proved axiom-free, asserted every build** by one three-part enforcement chain, no part of which is
sufficient alone:

```text
certified-module coverage → whole-theory Fido Audit Assumptions → adversarial controls A-E
```

The Rocq-native `Fido Audit Assumptions` owns assumption closure **over the certified environment actually
loaded**: it seeds every Fido constant, every mutual inductive and every surviving named assumption, rejects
every axiom category and every variable, and catches an external axiom reached transitively through an opaque
lemma, which a source-text scanner cannot do soundly. It enumerates its own roots, so no hand-maintained list
sits beside it. But it can only audit what is loaded — **certified-module coverage is what proves every
tracked root `.v` is in that environment**, by requiring tracked root `.v` to equal `dune (modules ...)`
exactly. Controls A-E then prove the audit is not fail-open. Drop module coverage and a module could leave
`dune` and be silently unaudited; drop the controls and the audit could pass by doing nothing.

**Zero project axioms.** Never `Axiom`, `Parameter`, `Admitted`, a kernel primitive, or functional
extensionality. Tracked axiom-bearing fixtures are forbidden; negatives are generated transiently.

### Two honest claims — never conflate

**(A) Kernel-internal exactness — PROVED.** The decision is three-way, and each branch is characterized exactly
over the exact retained `Compilation` revealed by `inspect`. `admissible_iff_reports` makes admissibility exactly
both report lists empty; `compiled_admissible` proves a compiled payload's revealed compilation is admissible, so a
Compiled outcome is unconditionally sound and completeness holds over the whole admissible (in-scope, boundary-free)
domain. `rejected_has_diagnostics` and `outside_reports` characterize the other branches exactly — Rejected carries
a non-empty diagnostic list, Outside empty diagnostics with a non-empty boundary — and `inspect_compile` decides
`compile`'s branch by exactly those report lists. `inspect` returns exactly one `Case`, and the payload disjointness
lemmas (`compiled_not_rejected`, `compiled_not_outside`, `rejected_not_outside`) prove the branches disjoint.
`compiled_prog_admissible` and the payload's indexing pin the capability to the exact supplied compiled payload and
its revealed compilation.

An `OutsideScope` outcome carries the exact unmet semantic requirement — a statement about Fido's reach, never
a claim that the program is invalid Go. Narrowing the domain to hide a rejection Fido gets wrong would launder
completeness, so the in-scope domain is a proved property of the program, never a residue of whatever the
checker failed on.

**(B) External adequacy — the GOAL, not a kernel theorem.** Adequacy is **bidirectional over the in-scope
domain**, and the domain is named rather than assumed:

```text
Fido accepts                            -> pinned go build ./... accepts
pinned go build accepts + no boundary   -> Fido accepts
```

**A program `Admissible` accepts but `go build` rejects is a correctness failure**, always. **A representable
program `go build` accepts, carrying no scope boundary, that Fido rejects is a model bug** — never a
documented limitation. Neither direction is proved about `cmd/go`; both are attacked by differential
experiments and the e2e.

What makes the second direction honest is that "outside the current semantic scope" is **not a rejection**.
Valid Go that Fido does not yet model leaves the compiler through `OutsideScope`, carrying the exact unmet
semantic requirement — site, resolved object or target, and argument profile where the rule needs one —
and asserting nothing about the source's validity. Syntax-identifiable exclusions stay unrepresentable
and are priced as `.review/scope.tsv` rows. Both sets shrink as milestones
land, and what remains at C16 is exactly the ledger's permanent `OUT` rows.

Integration tests are **alarms, not proofs**. A Go build or run failure for an emitted program is never an
expected test — it means `Admissible`, rendering, the derived facts or the transport is wrong. Negative
candidates fail in Rocq, before any bytes.

---

## 8. Boundaries

Every live **representability** restriction is one row in `.review/scope.tsv`: the pinned target, unmodelled
platform limits, the cooperating-developer threat boundary, buildx-only builds, module-path and file-naming
narrowings, imports on hold, ASCII-only identifiers, and the bounded float-decimal domain. A **scope
boundary** is not a restriction of this kind: it is a semantic outcome over an exact object and an exact
missing capability, and `.review/closure.csv` records which milestone owes that capability. Those are the two
mechanisms §7 (B) permits, and no restriction may live only in a code comment.

Standing acceptance obligations are rows in `.review/acceptance.tsv`. Spec-closure and latitude rows are
`.review/closure.csv` and `.review/latitude.tsv`.

### What must never come back

A handwritten OCaml backend, lowering, renderer or semantic decoder, or a bridge decoding anything but the
final transport type. A second program-AST hierarchy, a copied compiled AST, or a typed AST beside the one
raw `Syntax`. A type attached to a raw literal, or a placeholder, unknown, opaque or raw type constructor
added ahead of the syntax that needs it. A second numeric-width, float-precision, complex, conversion or type
authority. A type identity that is a string, a numeric `TypeId`, a registry entry or a tag rather than the
exact source declaration reference. F32 rounded through F64. A source literal or untyped constant stored as a
rounded or decimal-string value, or a typed exact value reconstructed by rerounding — though a *typed*
constant may retain its exact destination-format rounded representation beside the exact rational as static
evidence from the same one rounding. Package or import metadata in raw file values. Raw `string` map keys. A nonemptiness restriction on the program or image. A
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
| ARCH-03 | One owner per meaning; the static capability, its failure **and its outside-scope result** all retain the exact compiler object by construction (the accepted `Program` carries it transparently, the decision core stays sealed). Public fact, diagnostic, boundary, layout and plan interfaces are projections of that object, never independently minted peers. **Equality to a rerun is never provenance.** |
| ARCH-04 | Expression fact/use split — the use builder never inspects the raw child again. |
| ARCH-05 | Single type algebra; aliases do not create identity; recursive named types refer to declarations. |
| ARCH-06 | Static slot versus dynamic place — source binding identity and runtime storage identity never collapse. |
| ARCH-07 | Stack-only panic, defer and recover; the named invariants justify direct recovery without tokens. |
| ARCH-08 | Resource-local origins — live state retains exact origins, and proofs connect them to run actions. |
| ARCH-09 | Finite bad-prefix safety; safety and liveness stay separate. |
| ARCH-10 | No vacuous library safety — an empty set of starts does not prove open-world safety. |
| ARCH-11 | Do-not-do-early: no state, feature or compatibility scaffold lands before its complete vertical feature. Narrowly reopened once, for the `Emit.Image` mint (§6). |
| ARCH-12 | Rob accepts only the exact reviewed green HEAD. |
| ARCH-13 | Two authorities, never two formal: governing prose owns meaning, scope and boundaries, canonical Rocq owns exact formal realization, and a mismatch is a defect. The active milestone is formalized directly in its canonical owners with its prose rendition deleted in lockstep; future milestones stay prose-only; shadow implementations and committed scratch are forbidden; a falsified lower layer triggers targeted causal dependency retreat from the affected accepted contract. See §1 "Two authorities, never two formal implementations" and its "Dependency retreat (targeted causal)" rule. |
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
| SC-14 | PACKAGES-INIT-STARTS-EXIT | Initialization follows every dependency edge and rejects cycles before a compiled capability exists, multiple command roots produce independent starts, the emitted `go.mod` carries exactly the accepted module path and `go 1.23` with no `toolchain` directive, and final states have no steps. |
| SC-15 | BUILTINS | Every admitted predeclared built-in resolves through ordinary binding facts, receives exact use facts and executes through `step`; `print`/`println` output formatting is pinned-toolchain adequacy evidence, never a portable language theorem. |
| SC-16 | ERRORS-UNREPRESENTABILITY | One retained whole-elaboration object decides `Compiled`, `Rejected` and `OutsideScope`, and every diagnostic and every boundary projects from the exact object that produced it. **A scope boundary is never collapsed into a rejection**; only `Compiled` carries a `Prog.Program` capability — the sole route to `Safe.Program` and `Emit.Image` — and no broad "unsupported" catch-all stands where the ledger names distinct exclusions. |
| SC-17 | RENDER-ADEQUACY-MEMBERSHIP | Direct rendering covers every admitted constructor with no raw-text escape and one `Emit.of_safe` image path; a deterministic program matches the pinned observation tuple exactly, and a nondeterministic one only through a sound-and-complete membership checker that consumes `enabled_dec` and defines no semantics. |
| SC-18 | ENABLEDNESS-DECISION | `enabled_dec` decides readiness for nil, buffered, unbuffered, closed, select-with-default, absorbing and deadlock states, and agrees exactly with relational `step` on reachable well-formed states. Staged: **C5** freezes the generic `EnabledDecision`, `FinalAbsorbing` and `Stuck` shapes over abstract `Machine.T` and provides no decision inhabitant; **C8** closes ordinary control and absorbing-final readiness; **C14** closes nil, buffered, unbuffered and closed-channel readiness plus select readiness; **C15** closes deadlock classification and exact agreement with relational `step` on all reachable well-formed states. |
| SC-19 | OUT-BOUNDARIES | Every `OUT` row freezes the valid Go it gives up, the reason, the future-inclusion price, and a proof that no host helper or generic fallback can reintroduce the behaviour. Its boundary is established **either** by an exact missing source constructor **or** by an exact missing semantic capability over a resolved object; missing-constructor is not the only permitted form. |
| SC-20 | EVAL-ORDER-LATITUDE | Every latitude row is owned by the one relational `step` with no generic choice authority, and no row adds a public machine field, a second evaluator, a scheduler object or a generic `Choice` action. |
| SC-21 | PROOF-COST-INTERNALS | The public base is fixed while internal forms stay disposable: an internal type or index is kept only when removing it admits a real invalid state, and a capability retaining only copied fields plus equality to a recomputation is a failed design even when its extensional theorems pass. |
| SC-22 | ACCEPTANCE-ALIGNMENT | Exact compile acceptance is retained over the no-boundary domain: a program pinned gc accepts and that carries no scope boundary is accepted by Fido. The one-way `fido_accepts_subset_pinned_gc` theorem remains mandatory but is not the whole claim. Both are discharged incrementally by the checkpoint that makes each restriction representable, without making pinned gc a language-semantics authority — a finite probe set is evidence, never the global theorem. |
