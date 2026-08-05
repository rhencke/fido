# Review Request

state: requested
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: Rob ratified amendments M3-A1 and M3-A2 by approving .review/M3_FORENSIC_AUDIT_REPAIR_2.md
result: (pending)
candidate: (the M3 candidate named by `.review/NEXT_STEPS.md`; the freeze commit that follows it adds no work)

contract: .review/M3_TOOL_AND_BUILD_ARCHITECTURE_AUDIT.md
contract_activation_sha: 0b7fd86825936c37f31ef83879574d526d548122
amendment: .review/M3_CONTRACT_AMENDMENT_1.md
amendment: .review/M3_CONTRACT_AMENDMENT_2.md
review_basis: .review/REVIEW_BASIS.md
prior_finding_record: .review/M3_FORENSIC_AUDIT_REPAIR_3.md
candidate_sha: 3b9c1033e6a553fb7b559ae58aca1fcb952019e4
freeze_sha: this commit — the documentation-only freeze that follows the candidate above
supersedes: 89dd81e15737e31e3a9c53e96b3338474af30e50 / f09c01b1a895f3c1154e17b164eaf34e513a4091
            — the previous offer, withdrawn on finding the leaked claim described below
blocked_candidate: c0560426d9c0d50a45f7c015b6493983dff03878
blocked_freeze: c73e1f1aaea9fce0327cdb909034181a56ddc7e1

`.review/NEXT_STEPS.md` owns mutable checkpoint and candidate state. This file pins what is under review; it
does not own mutable state.

**The M3 Implementation Review is requested.** The audit is `.review/M3_AUDIT.md`, the plan is
`.review/M4_MECHANICAL_REFACTOR_PLAN.md`, and all twelve obligations are closed with distinct evidence. M4
remains forbidden until Rob accepts M3 and separately approves the plan.

## What Repair 3 changed

A small review-state and plan repair. Four things, and none of them needed a measurement rerun.

**`M4-07` still deferred a design choice, in a plan that claims none does.** It said "a frozen tuple, named
tuple or frozen dataclass". That is exactly the kind of "decide during M4" the plan's own opening sentence
forbids, and I wrote both. It is now one shape — a standard-library `NamedTuple` with `matrix` and
`required` — and no alternative survives.

**`M4-07` was ordered too late.** It must be the **first** M4 step, because its staged snapshot has to carry
M4's own obligation matrix and the new subject object, so the real pre-commit hook judges the matrix M4 is
actually working against. Any other M4 source commit landing first would be judged by a gate still pointing
at the accepted M3 matrix. Wave 1 is now `M4-07`, `M4-06`, `M4-08`, and the document's sections are in that
order too.

**`M4-09` asked an authority to detect its own missing data.** I had written that an ID absent from
`SUBJECT.required` must be detected. Once `SUBJECT` is the sole production authority, production code cannot
know its authority omitted an ID without a second authority to compare against — which is the shape this
project exists to refuse. The enforceable relation is the other direction: every ID present in
`subject.required` appears exactly once in the matrix loaded for that subject. The control uses an
independent synthetic subject with two fixed IDs and a matrix missing one, and never derives its expectation
from production `SUBJECT`. Test independence does not become a second production authority.

**The fresh pre-M4 baseline Rob accepted was missing from the plan.** `make perf` now runs exactly twice
across M4: once in a clean worktree at the accepted M3 candidate before Wave 1 begins, and once after
Wave 2. `git diff` between the two records is the full-path comparison. The forensic profiles are not rerun.

Also corrected: the review state said M3 "implements nothing", which stopped being true when `M3-A1` changed
two tool files — it now says M3 does not implement the refactor, and names the exception. The sentence
calling `M4-14` a proposed deletion is gone, since `M4-14` is not in the plan.

**The impossible claim §4 removed had leaked into a second section, and I missed it.** `M4-09`'s table was
corrected, but `M4-07`'s acceptance criteria still required "a control proving a required ID absent from
`SUBJECT.required` is still detected" — the same unenforceable thing, in the step that builds the subject
object. The plan therefore contradicted itself and still asked M4 for something it cannot do. Both places now
state the enforceable relation, and `M4-07` says explicitly that it must not ask for the other one in
different words. The two duplicated sentences §5 named are gone with it: `M4-07`'s restatement of "one
object, not two authorities", and `M4-09`'s restatement of "not every helper that exists".

This was found on a second pass over the review, item by item — the first pass verified four of §5's bullets
and skipped one, then reported completeness. That is the same failure the audit keeps turning up, so the
check is now the whole numbered list, run and printed, not the parts I remembered.

**Rob approved `M3-A1` and `M3-A2` in plain language on 2026-08-04**, and both amendments record him. The
previous round recorded his authority before he had stated it that way; asking cost one exchange and is the
only thing that makes the record true.

## Scope

```text
no production, proof, Make, hook, Docker, Dune, generated or runtime path moved
```

The one project-tool change is the one Amendment `M3-A1` authorizes: the claim-matrix self-test precondition,
in `tools/claim-matrix-gate.py` and its mutation entry. Every `.v`, OCaml, generated Go, fixture, golden,
Makefile, Dockerfile, Dune file, hook, perf script and TSV byte is unchanged from the contract activation.

No permanent audit, timing, inventory, graph or comparison tool was created, no registry or schema added, and
no raw log committed. `.review/M3_AUDIT.md` is one temporary table.

M2 is ACCEPTED under `M2-ACCEPT-9814db7`, M1 under `M1-ACCEPT-6524b43`, C4 under `C4-ACCEPT-39ea7e3` and M0
under `M0-ACCEPT-86a63db`. M4, C5 Step 0 and C5 remain forbidden. Only Rob accepts M3.
