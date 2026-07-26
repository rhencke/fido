# Fido FCB Checkpoint Authoring Guide

> **Derived reference, not implementation authority.** The code and its gated theorems are the sole implementation authority.  
> **Living document.** Its identity is its Git blob at the exact ref resolved for the task; its
> history is the commit log. No version suffixes, no checksum manifest.  
> **Accepted amendments:** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE`; `FCB-A002-GIT-CANONICAL-FCB-STORAGE`; `FCB-A003-LIVING-DOCUMENTATION`;
> `FCB-A004-GIT-RESOLVABLE-LIVING-CORPUS`; `FCB-A005-SCOPED-NAME-OWNERSHIP`;
> `FCB-A006-INTRINSIC-EMIT-IMAGE-MINT`.  
> **Canonical live location:** `.review/fcb/current/` in the exact Git ref used for the task.  
> **Stable bootstrap:** `.review/fcb/current/INDEX.md`  
> Project libraries contain only a bootstrap shim. They do not contain or own the FCB corpus.  
> Regenerate, verify, and commit affected FCB files in Git after each accepted checkpoint or amendment.  
> This corpus does not accept C4 and does not authorize C5; `.review/NEXT_STEPS.md` remains the live checkpoint authority.


## 1. Selection

Select the lowest-numbered Roadmap checkpoint whose dependencies are accepted. A checkpoint may consume only the exact Closure, Latitude, and Acceptance-Gate rows listed by the Roadmap. A missing lower foundation blocks all higher work.

## 2. Required checkpoint document order

### A. Scope

Copy the Roadmap entry verbatim. List every consumed row by ID. State all exclusions. Nothing outside this set is authorized.

### B. Foundational-increment justification

Prove that every dependency is already accepted and that the checkpoint adds one complete vertical feature. Explain why no lower abstraction is missing. If this paragraph cannot be written honestly, stop.

### C. Frozen contracts

Before implementation, state exactly (identity is the contract's path at the baseline Git ref — documentation
is not checksummed):

- every public type or constructor added;
- every new `step` or `final` case;
- every public theorem statement;
- every exact compiler fact or query;
- every deletion that becomes legal;
- the `SC-00`–`SC-22` contract each item satisfies.

The public surface is frozen for the checkpoint. Internal forms are disposable under `SC-21`; implementation difficulty is evidence about internals, never permission to weaken the public claim.

**Whole-result retention:** If a checkpoint builds a proof-carrying object and publishes a later capability, decision, failure, safety, or output result, the contract must name:

- the exact causal object retained;
- the exact prior object it consumes;
- how foreign pairing is made unrepresentable;
- which public total projections later clients receive;
- which specification or determinism equalities are separate from production provenance.

A copied field set plus equality to rerunning the builder fails this duty.

### D. Fixture obligations

List new semantic fixtures and every Acceptance-Gate row discharged. Each acceptance fixture is a pair:

1. replay the pinned-gc side under the exact Toolchain Evidence profile;
2. run Fido’s production elaboration path and capture the exact diagnostic.

Store source, stdout, stderr, status, command, environment, and provenance. A test-only path does not discharge a production obligation.

### E. Acceptance gates

Name every command and check that must pass. Include:

- proof build and readable assumption gate;
- whole-theory assumption audit;
- source-to-generated-Go byte comparison;
- pinned-go build and run fixtures;
- replay of external evidence used by this checkpoint;
- direct inspection of the deployed semantic path;
- regression controls for every defect fixed during the checkpoint.

Green gates do not replace path inspection.

Inspect constructor topology at every publish boundary, not only inside the newest phase. Trace the exact object from construction through acceptance, failure, safety certification, and output. A theorem body knowing an object exists does not repair a result type that discarded it.

### F. Provenance duties

Models record `APPLIED` at most. Ship empty Rob countersign fields. Do not hand-remove an open act.

Every human act the checkpoint raises or resolves is added to or updated in `FIDO_FCB_HUMAN_ACTS.tsv` — one row, one owning source, one `<!-- FIDO-HUMAN-ACT:<ID> -->` anchor in that source — and the Human-Review Index is regenerated with `make human-acts-write` BEFORE the checkpoint is submitted for review. `make human-acts` must be green. An act recorded only in prose is not recorded.

### G. Whole-result implementation constraints

- Opaque does not mean discarded.
- Exact whole-result provenance survives every capability boundary.
- Specification equality never substitutes for retained identity.
- A successful or failed result retains the exact object that made the decision.
- No public query may rerun a builder to recover an object omitted by its constructor.

### H. Git publication duty

On Rob’s acceptance:

1. regenerate every affected FCB document from the accepted repository state;
2. update the Index and stable `INDEX.md` if the file set changed;
3. confirm every reference in the changed documents resolves at that ref (D-24);
4. commit the coherent replacement under `.review/fcb/current/` in Git;
5. retain superseded states through Git history, never as a second live set.

Project libraries contain bootstrap shims only. They are not regenerated with each checkpoint and change only if
the repository identity or stable bootstrap path changes.

## 3. Checkpoint template

```markdown
# FIDO CHECKPOINT C<N> — <NAME>

## 0. Authority and frozen identity
- Baseline Git ref:
- Contract path (at that ref):
- Human authorization token:
- FCB tree consulted (`git rev-parse <ref>:.review/fcb/current`):

## 1. Scope
- Roadmap entry:
- Closure rows:
- Latitude rows:
- Acceptance-gate rows:
- Explicit OUT / not authorized:

## 2. Foundational-increment justification

## 3. Frozen public contracts
### 3.1 Types and constructors
### 3.2 Compiler facts and total queries
### 3.3 Machine transitions and observations
### 3.4 Public theorem statements
### 3.5 Deletions authorized after replacement
### 3.6 Whole-result retention
- Exact causal object retained:
- Exact object consumed:
- Published capability/failure constructor topology:
- Total projections:
- Specification equalities that are explicitly not provenance:
- Forbidden rebuild calls:

## 4. Implementation constraints
- One authority per meaning
- No fuel
- No fallback or parallel path
- Standard collections only
- No raw reconstruction
- Internals disposable under SC-21
- Opaque does not mean discarded
- Exact causal provenance survives publication
- No equality-to-rerun provenance

## 5. Fixtures
### 5.1 Formal fixtures
### 5.2 Pinned-gc/Fido acceptance pairs
### 5.3 Negative and regression controls

## 6. Gates

## 7. Provenance and review
- Model record: APPLIED / BLOCKING finding
- Rob countersign: <empty>
- Human-Review Index regeneration (`make human-acts-write`, then `make human-acts` green):

## 8. FCB update plan
```

## 3a. Naming duty (D-25 / A005)

Every checkpoint contract carries a naming section, and it is frozen with the checkpoint:

- freeze the module and public identifier names alongside the frozen contracts;
- make every name relative to its real scope — the namespace states the domain once;
- forbid domain repetition and cryptic pseudo-namespace prefixes (`cp_`, `ewf_`, `tnft_`, `di_`, `Go` on a
  declaration inside a Go-domain module);
- require qualification at cross-module boundaries, so `Compilable.Program` and `Typing.Program` are
  distinguished by the namespace that owns them;
- resolve any collision with the smallest full semantic distinction, never a restored abbreviation;
- list the old-name and prefix residue searches the checkpoint must run, and state their expected result.

`make names` (`tools/naming-gate.py`) enforces this. The Rocq compiler already verifies code names for free —
a missed rename fails to build — so the gate exists for documentation and source comments, which have no
verifier at all.

## 3b. Reducible-carrier duty (D-26 / A006)

A reducible `Emit.Image` carrier is permitted ONLY because an opaque exact-value-indexed `Emit.Mint.Token`
owns its authority. A checkpoint may not generalise this into permission for public raw constructors
elsewhere: it is a narrow computation-boundary rule, forced by the certified transport having to kernel-reduce
`Emit.transport img`. Where no certified transport must reduce a representation, that capability stays
abstract.

## 4. Stop conditions

Stop and report an architecture conflict when a required result needs a new public authority, a different scope, a weakened theorem, a custom collection where a standard one should fit, a hidden trusted boundary, or a step bound. Do not implement an alternative autonomously.

Stop and report an architecture conflict when the requested public result cannot retain the exact causal object needed by later layers without adding or reopening a public contract.
