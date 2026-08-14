# C6 — active task: the C4 exact-elaboration retreat repair (R1–R7)

Review: none

The active work is the **C4 exact-elaboration retreat repair**. Candidate `ac8bdd4` was reviewed by an
archive-authoritative sixteen-pass Wirth review (synthesis `3ac0246c`), graded **F**, `REVIEW_BLOCKED`, and its
findings deduplicated into **seven root causes R1–R7** — a compiler-interior rebuild. Everything past the
retreat stays frozen until Rob closes it; C5 stays historically accepted (`Machine.v` has no importer and no
causal edge from the repaired path). Rob alone closes and accepts; `IMPLEMENTED_NOT_ACCEPTED` until then.

This sheet is the self-contained active contract: what is required now, and nothing else. Superseded briefs and
repair narrative are Git history.

## Current truth vs. required outcome

RC-01's core landed (`e100f84`) and **R1–R5 have since landed**: the transparent `occ_file` fold's result is
retained as the compiler's one causal object; occurrence/reference identities are intrinsic position-selectors;
binding/diagnostics/boundaries read the retained index and package/scope objects; and the public decision
carries the exact `Program` through one transparent capability/provenance chain. **R6 (theorems + evidence) and
R7 (corpus) remain the required outcome below, not the current state.** Architecture prose keeps that distinction
until R7 finalizes. R4's concrete semantic partition landed; its deeper multi-issue causal chain is deferred as a
no-op in the current single-issue domain.

## The resolved sealing question — closed, not a choice

The A/B/C sealing fork is closed by adjudication. The answer is neither transparent-but-forgeable (A) nor
system-wide opaque sealing (B): make the occurrence/reference **intrinsic**. One transparent structural
computation stays (so `vm_compute` still reduces), but every public semantic constructor is valid by its
indices — a malformed identity has no inhabitant — and a reference is a dependent selector into the exact
retained work object whose member/view it projects. Transparency and unforgeability coexist; local opacity is
used only for a residual capability that intrinsic construction cannot close, never as an end in itself.
Recorded in `DECISIONS.md` (`RC01-INTRINSIC-TOPOLOGY`). No A/B churn, no further opaque-seal experiment over the
current carrier.

## The seven roots (required results)

- **R1 — one intrinsic retained occurrence/reference authority** (`Index`, BLOCKER). One transparent
  terminating fold builds each file's ordered work object once; metadata/lookup derived once from those exact
  members; a reference is a dependent selector projecting the exact member/view; total file/node/parent/member
  projections; kind/role refinements over the exact projection. No malformed public constructor, no
  coordinate/equality/Boolean-backed peer mint, no raw-source semantic enumeration, no linear peer scan, no
  silent fallback. `vm_compute` preserved through a transparent non-authoritative outcome-code/erasure of the
  same canonical computation if needed; no rich sealed handle on the VM reduction spine; no second checker.
- **R2 — exact package/binding/scope identity** (`Compilable.Bindings`, BLOCKER). One program/index-scoped
  package object from canonical files; exact binder/object/block/package-scope refinements; sealed or
  intrinsically valid establisher formation; phase-owned resolver input; declaration-kind-specific visibility.
  No free package strings, any-node objects, copied establisher fields, or missing-ref fallback.
- **R3 — one retained static phase + correct child cut** (`Compilable`, BLOCKER). One phase retains the R1
  object, the binding phase, type/application facts, package-rule + preflight results, diagnostics, boundaries,
  and causal edges. `TypeResolution` owns type decisions only; `Facts` owns one retained semantic fact per exact
  occurrence and does NOT import `Report`; `Report` consumes facts and owns projection/order; `Compilable`
  composes once and decides once. Import edge: `Facts → Report → Compilable`.
- **R4 — causal report algebra + exact semantic partition** (`Facts` then `Report`, BLOCKER). Phase/core-indexed
  structured causes/boundaries with exact site, target/object, profile, predecessor, root/blocked; public roots
  are the earliest unmet causal requirements only. Typed-`complex` branch-complete (no `CxDefer` erasure);
  reject known-invalid `iota`/`nil`/identity-known non-statement builtins; correct declaration
  visibility/precedence; no `None` conflating invalid/absent/unmodelled/deferred.
- **R5 — capability/provenance one chain** (`Compilable.CAPABILITY`, BLOCKER). `compile p`'s `Compiled` branch
  carries the exact `Program` over the exact phase; `Admissible` is an independent declarative characterization
  that mints nothing; every client eliminates one `Decision`; `Safe.certify` wraps that exact value;
  `Emit.of_safe` is the sole live image constructor. Delete `program_of : Admissible -> Program`, `compiled_of`,
  `program_of_source` plumbing, and `Emit.of_safe_at` + its bridge lemmas.
- **R6 — the accepted theorems + branch-complete evidence** (theorem surface + fixtures/gates, BLOCKER). Exact
  member/index/ref totality; independent declarative admissibility; unconditional compiled soundness;
  completeness over the exact in-scope/no-boundary domain; exact rejected/outside characterizations; branch
  exclusivity/exhaustiveness; exact decision/program identity. Add concrete exact-payload branch fixtures +
  joined Fido/Go cases; extend the assumption audit to proof-bearing fixtures.
- **R7 — truthful self-contained corpus** (`ARCHITECTURE.md` + ledgers, BLOCKER + AMENDMENT/DELETE). One
  archive-authoritative Wirth review rule; one self-contained active task; current truth distinguished from
  required outcome; the resolved RC01 outcome; accurate owner/dependency/ledger state; live-prose normal form;
  exact current toolchain evidence boundary. Normalize the active contract now, keep it truthful in lockstep,
  finalize after the code/evidence changes.

## Implementation order (dispatched)

1. Normalize the active governance contract (this sheet + the `RC01-INTRINSIC-TOPOLOGY` decision; correct the
   review-object rule; retire `.review/RC01_SEALING_CONFLICT.md`). No implementation/acceptance claim.
2. **R1** — the intrinsic, computationally-usable Index root; add R1 theorems + negative-client controls.
3. **Intentional Stop 1** — run the gates; audit the public surface against every R1 forbidden form; confirm the
   accepted witness bytes/path set are unchanged. Continue only if the fold is retained once, every semantic
   reference projects the exact member, invalid identities are unconstructible, and computation stays viable.
4. **R2** — exact package/binding/scope identity.
5. **R3** — one retained phase + the child cut.
6. **R4** — semantic partition + causal report algebra.
7. **R5** — capability/provenance one chain.
8. **Intentional Stop 2** — formal/public gates after R2–R5; confirm no second authority, raw-source rebuild,
   equality-to-rerun provenance, compatibility capability, or wrong-direction import; exact counterexample
   fixtures pass before broader evidence.
9. **R6** — universal theorems + branch-complete evidence.
10. Mandatory deletions + concurrent cleanup against the final graph.
11. **R7** finalization in live-prose normal form.
12. Full gate set; freeze a new archive (SHA-256 + ZIP-comment commit + reconstructed tree); submit for a fresh
    sixteen-pass review. Do not reuse this synthesis as the new verdict.

## Stop / status

`IMPLEMENTED_NOT_ACCEPTED`. Dispatched by Rob. Current: **R1–R5 landed** — intrinsic position-selector references
into the retained index (R1); exact package/binding/scope identity with declaration-kind visibility (R2); the
`Facts → Report → Compilable` cut over one retained phase (R3); the semantic partition — typed-`complex` →
OutsideScope, `iota`/`nil`/builtin-as-value → Rejected, no `None` conflation (R4 concrete; deeper causal chain
deferred as a domain no-op); and the transparent capability/provenance chain — `Compiled` carries the exact
`Program`, `Emit.of_safe` is the sole image constructor, `program_of`/`compiled_of`/`of_safe_at` deleted, the
certificate transparent, unforgeability intrinsic via typing controls AJ/AK (R5). Witness bytes and path set
byte-identical throughout. Next: **Intentional Stop 2** — the formal/public gate audit after R2–R5. `make check`
on the pinned toolchain is the supported run. Only Rob accepts.
