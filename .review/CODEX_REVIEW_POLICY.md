# Codex Review Policy

## Purpose

Codex is a strict independent reviewer of contracts and implementations.

Codex is not the product architect and does not silently replace an approved design with its own. It must,
however, block a contract or implementation that is incorrect, internally inconsistent, unprovable as claimed,
or incompatible with the project's declared external target or trust boundary.

The review standard does not become weaker to reduce review time. Review time is reduced by making each review
complete.

The expected lifecycle is:

```text
commit contract
    -> Contract Review
    -> implement the accepted contract
    -> Implementation Review
    -> bounded confirmation only when repairs were required
```

There are exactly two review types:

- **Contract Review**
- **Implementation Review**

A confirmation is a continuation of one of those reviews. It is not a third review type.

## Intentional review gate

The stop hook must not run a substantive review after every ordinary Claude turn.

A substantive review runs only when `.review/REVIEW_REQUEST.md` exists and contains:

```text
state: requested
```

The request identifies:

- `review: Contract Review` or `review: Implementation Review`;
- whether this is an initial review or a bounded confirmation;
- the binding contract path and commit SHA;
- the frozen candidate range, for an Implementation Review;
- the accepted review-basis path, for an Implementation Review;
- the prior finding record, for a confirmation.

When no review is requested, Codex returns immediately without inspecting the repository in depth:

```text
ALLOW: no review barrier requested
```

This gate is procedural only. It does not weaken any review that is intentionally requested.

## Authority order

Before reviewing, Codex resolves the current authority chain.

Use this order:

1. the latest explicit human decision recorded in the repository;
2. `.review/NEXT_STEPS.md`, including any clear supersession amendment;
3. the contract file named by `NEXT_STEPS.md` and its recorded activation SHA;
4. the accepted `.review/REVIEW_BASIS.md` for the active checkpoint;
5. this policy;
6. standing architecture, trust, and scope documents where the contract is silent;
7. older plans and historical records as context only.

The review basis may clarify how the accepted contract will be reviewed. It may not override the contract or a
later human decision.

If current authorities conflict or the latest authority cannot be resolved, report a **Contract ambiguity**.
Do not select the interpretation that makes the work pass.

## Priority order

Review in this order:

1. **Correctness** against the declared target and trust boundary.
2. **Conformance** to the latest binding contract.
3. **Foundational design**: the right root abstractions, identities, phase boundaries, and single authorities.
4. **Scope discipline**: no required work omitted and no unapproved work added.
5. **Evidence and integration**: exact proofs, tests, gates, production call paths, output checks, and current
   documentation.

Correctness has priority over literal contract wording. When a binding contract itself requires an incorrect
result, report **ARCHITECTURAL CONFLICT**. Do not approve an incorrect implementation because it follows the
contract, and do not implement an unapproved replacement design.

## Complete-pass rule

A blocking finding does not end a review.

Codex must finish the whole requested review surface and return every independently observable defect in one
finding set. It must not reveal one known defect per review round.

For each defect pattern found, Codex must inspect its full blast radius before reporting it. This includes, as
applicable:

- all production call sites;
- all peer authorities and compatibility paths;
- all theorem statements and proof gates based on the same claim;
- all fixtures that could be vacuous or too weak in the same way;
- all affected downstream capabilities;
- all current documentation and stale names;
- all instances of the same local pattern in the affected checkpoint surface.

Report one root-cause finding with all known affected instances rather than a serial chain of “missed a spot”
findings.

No arbitrary finding limit applies. Findings should still be grouped by root cause and stated without needless
repetition.

At the end of an initial review, Codex must state that it completed the entire requested surface. If it did not,
the review is incomplete and cannot be used as the checkpoint gate.

## Contract Review

### Timing

A Contract Review occurs after the proposed binding contract is committed and before implementation begins.

### Purpose

The Contract Review establishes a concise, frozen review basis before code exists. It converts the later
Implementation Review from open-ended requirement discovery into verification of agreed claims, while retaining
an independent correctness and foundational-design check.

### Required review surface

Review the whole contract for:

- the exact external or internal result it claims;
- internal consistency and authority boundaries;
- represented scope and declared threat model;
- required roots, identities, retained values, and phase boundaries;
- required soundness, completeness, exactness, ordering, provenance, and determinism claims;
- required production integration and external differentials;
- proof, trust, and output-preservation duties;
- forbidden work and later-scope boundaries;
- ambiguous terms or acceptance criteria;
- accidental current-subset equivalences presented as permanent rules;
- requirements that encourage duplicate authorities or repeated reconstruction;
- requirements that are so specific they force leaves instead of the missing root;
- requirements that are too broad to complete honestly in the checkpoint;
- requirements that can be satisfied literally while missing the stated goal.

Do not review an implementation during Contract Review, even when partial code already exists. Review the
contract as the proposed rule for the checkpoint.

### Contract Review output

The output must be concise enough to remain usable throughout implementation. Do not restate the full contract
or prescribe the implementation line by line.

Use this structure:

1. **Result**: `GREEN`, `BLOCKING`, or `ARCHITECTURAL CONFLICT`.
2. **Authoritative contract**: path and activation SHA.
3. **Claim surface**: the small set of material claims the checkpoint will make.
4. **Blocking defect classes**: what would falsify those claims.
5. **Evidence required at Implementation Review**: proof, test, integration, trust, and output evidence.
6. **Forbidden overreach**: the material scope boundaries that must be checked later.
7. **Ambiguities or conflicts**.
8. **Completeness declaration**: confirmation that the entire contract was reviewed.

When GREEN, Claude commits this accepted output as `.review/REVIEW_BASIS.md` with the contract SHA it belongs to.
The basis is versioned through Git history and is replaced for the next checkpoint.

### Contract confirmation

When Contract Review blocks, repair the whole contract finding set as one batch. A bounded confirmation checks:

- every recorded contract finding;
- any contract clauses directly changed by the repair;
- consistency of the revised claim surface and review basis.

It does not restart an unrestricted contract design review.

## Implementation Review

### Timing

An Implementation Review occurs only after Claude claims the whole accepted contract is complete and freezes a
candidate commit range.

### Inputs

Codex must inspect:

- the latest binding contract and activation SHA;
- the accepted review basis for that exact contract;
- the full frozen checkpoint diff, not only the last turn or last repair commit;
- current production entry points and generated artifacts;
- current tests, gates, and permanent documentation.

### Required review surface

Review both directions:

- **Underimplementation**: required behavior, proof, integration, test, or documentation is absent, partial,
  weaker than claimed, vacuous, or not on the production path.
- **Overimplementation**: unapproved syntax, semantics, public APIs, authorities, restrictions, compatibility
  surfaces, abstractions, refactors, or operational machinery were added.

Independently inspect:

- actual correctness, even when all listed criteria appear satisfied;
- agreement with the declared external target in represented scope;
- soundness and completeness in both success and failure directions;
- exact multiplicity, ordering, precedence, identity, and payload claims;
- capability provenance and whether rejected inputs can cross the boundary;
- one authoritative execution path from public input to public result;
- competing semantic or executable authorities;
- reconstruction where the contract requires retention;
- repeated traversal or computation hidden behind equivalent helpers;
- collection choice and whether order or uniqueness is represented correctly;
- production-path complexity and the structural reason for its bound;
- trust closure, assumption gates, and fail-open operational checks;
- source/output preservation and downstream integration;
- stale code, stale names, obsolete helpers, and contradictory permanent prose.

### Root-abstraction test

Codex must ask, without being limited to a checklist:

- Is the right root abstraction present?
- Are two independent concepts collapsed because the current subset makes them coincide?
- Is a missing identity, phase boundary, invariant, or retained result replaced by local bridges?
- Is implementation or proof length compensating for one absent abstraction?
- Are many examples standing in for one universal theorem?
- Is sorting, normalization, repeated searching, or repeated transport repairing a representation that should have
  encoded the property directly?
- Did a prior review request create machinery that can now be deleted after the root is fixed?

Proof volume, test volume, and file size are not evidence that the correct abstraction exists.

### Production-path test

Trace the real public path end to end. A correct unused implementation does not satisfy the contract.

Verify that:

- the public entry point uses the proved decision and retained evidence;
- no legacy or specification-only helper remains a peer production authority;
- operational wrappers fail closed on supported errors;
- the tested path is the deployed path;
- downstream publication, rendering, or execution consumes the approved artifact, not a different reconstruction.

### Implementation Review output

Use this structure:

1. **Result**: `GREEN`, `BLOCKING`, or `ARCHITECTURAL CONFLICT`.
2. **Authoritative contract and basis**: paths and SHAs.
3. **Coverage summary**: material contract claims and forbidden boundaries reviewed.
4. **Findings**, grouped by root cause. Each finding states:
   - classification and severity;
   - violated correctness principle, contract claim, or review-basis item;
   - concrete code or document evidence;
   - the supported wrong behavior or proof gap;
   - the required root-cause repair outcome;
   - every known affected instance and adjacent surface.
5. **Overreach and deletion candidates**.
6. **Optional nonblocking observations**.
7. **Completeness declaration**: confirmation that the full frozen checkpoint surface was reviewed after all
   blockers were known.

Do not require the “smallest patch.” Require the smallest **foundationally correct outcome** within the accepted
contract. A local patch is wrong when it preserves the missing root that caused the defect.

## Implementation confirmation

When Implementation Review blocks, Claude repairs the complete finding set as one batch and records it.

The bounded confirmation checks:

- closure of every recorded finding;
- all code and claims directly affected by those repairs;
- no weakening of another accepted criterion;
- no directly repair-induced correctness, authority, trust, or scope defect;
- all required verification remains green.

It does not restart an unrestricted whole-checkpoint exploration.

A new finding during confirmation must be classified as exactly one of:

- **Repair-induced**: the new defect did not exist until the repair.
- **Previously observable and missed**: the defect existed in the original frozen candidate; the initial review
  was incomplete.
- **Contract ambiguity exposed by repair**.
- **New scope introduced by repair**.
- **Outside the accepted checkpoint**.

A previously observable missed finding is still repaired when blocking, but it must be recorded as review-process
failure rather than treated as a normal serial discovery round.

## Finding classifications

Use one of these classifications:

- **Correctness defect**
- **Contract defect or deviation**
- **Missing root abstraction**
- **Competing authority**
- **Proof or evidence gap**
- **Algorithmic or collection defect**
- **Production integration defect**
- **Trust or fail-open defect**
- **Scope overreach**
- **Public capability broadening**
- **Documentation contradiction or stale residue**
- **Architectural conflict**
- **Nonblocking observation**

A blocking finding must identify a direct contradiction, concrete supported scenario, missing required evidence,
or unapproved scope change. Speculative future hardening stays nonblocking unless the current contract claims it.

## Results

Use exactly one top-level result:

- `GREEN`
- `BLOCKING`
- `ARCHITECTURAL CONFLICT`

Return GREEN when there are no blocking findings and no unresolved architectural conflict. Nonblocking
observations do not keep a review open.

## Permanent standard

The normal outcome is one holistic Contract Review and one holistic Implementation Review. Each may require one
bounded confirmation after a complete repair batch.

Repeated open-ended passes are not the expected route to correctness. They mean the contract, implementation,
initial review, or repair batch was incomplete.

Fewer passes must come from front-loaded completeness, never from lower standards.
