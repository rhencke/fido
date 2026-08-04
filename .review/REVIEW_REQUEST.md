# Review Request

state: closed
review: Contract Review
confirmation: yes
confirmation_used: yes
human_override: (none required; the GREEN Contract Review authorized the audit to begin)
result: GREEN (Contract Review). The M3 Implementation Review is NOT requested — see the conflict below.
candidate: (no review requested; `.review/NEXT_STEPS.md` owns the active state)

contract: .review/M3_TOOL_AND_BUILD_ARCHITECTURE_AUDIT.md
contract_activation_sha: 0b7fd86825936c37f31ef83879574d526d548122
review_basis: .review/REVIEW_BASIS.md
prior_finding_record: .review/M3_CONTRACT_REVIEW_REPAIR_1.md

`.review/NEXT_STEPS.md` owns mutable checkpoint and candidate state. This file pins what is under review; it
does not own mutable state.

**The audit and the plan are complete. The Implementation Review is NOT requested, because M3 cannot close
its obligations without changing a tool contract §9 forbids it to change.** The conflict is `Q-M3-02` in
`.review/OPEN_QUESTIONS.md`, and it is blocking: with all twelve rows closed, `tools/claim-matrix-gate.py`
fails its own self-test, because no M3 obligation can honestly name a declared code surface — M3 implements
nothing. Requesting a review with the rows left open is what the do-not-freeze-early rule forbids, so no
review is requested at all. Rob decides; I did not work around it.

The complete audit is `.review/M3_AUDIT.md` and the exact plan is `.review/M4_MECHANICAL_REFACTOR_PLAN.md`.
M4 remains forbidden until Rob accepts M3 and separately approves the plan.

## What the audit found

The headline is that **the ordinary edit loop is not waiting on the proof.** On the hot path `names` (22.3 s)
and `fcb` (28.6 s) are 50.9 s of a 63.7 s `make check`, while `prove` and `e2e` are 1.4 s and 1.3 s. Two
Python gates that read no `.v`, no `.vo` and no Docker layer are 80% of the wait.

Both were root-caused to an exact line rather than described:

- `tools/naming-gate.py:336` builds a regex **string** per line per retired name — 170 names × ~53 000 lines
  = **9 003 383 `re.escape` calls**, measured by cProfile in the pinned image. Every pattern is a constant.
- `tools/gate-mutation-test.py` is 22.4 s of `fcb`'s 28.6 s. It runs each gate's **whole** self-test per
  mutant, and those self-tests already copy the tree per control — ≈2 000 nested control executions, most of
  them copying 163 files, per `make fcb`.

On the cold path, two independent `make prover-log FIDO_PERF_COLD=1` runs agreeing within 0.8 s show
`rocq c gate/Assumptions.v` costs **77 s — 59% of the `prover` stage and 29% of the whole 270 s cold run** —
while the strictly stronger whole-theory `Fido Audit Assumptions` costs 1.72 s. And the sealed-capability
self-tests recompute their own precondition 21 unnecessary times: 25 calls, four distinct
`(prelude, sentinel)` pairs.

Four things turned out to be dead rather than slow. The exact paths are in the audit — this file is a live
authority, and D-24 rightly refuses to let one name a deleted path even to report it:

- 25 of 67 mutants route to `--m1-self-test`, and `--m1` is invoked nowhere;
- the `tools/source-diet.py` M1 replay path they guard names **six deleted ledgers**, so it cannot succeed;
- `tools/claim-matrix-gate.py` still names the previous checkpoint's matrix in its own docstring, and that
  file was deleted at M2 closeout — the hand-retarget updated the constant and missed the prose;
- `tools/naming-gate.py` carries an exclusion for a review document that is no longer in the tree, so it
  excludes nothing and would silently cover the next file to take that name.

## What I did not decide

`M4-11` — the 77 s readable Print-Assumptions gate — is written down and **deliberately left unauthorized.**
The whole-theory audit subsumes it for the machine, but it exists so a human can read which named surfaces
are closed, and `CLAUDE.md` makes those a standing public claim. Shrinking a readable proof surface to save
77 s is not a mechanical refactor and is not my call. It is `Q-M3-01` in `.review/OPEN_QUESTIONS.md`, owned
by Rob, non-blocking, with "change nothing" as the default if nobody answers.

Two M4 steps also carry a stated fallback rather than a promise, because each trades something: `M4-02`
(running each mutant against only the controls it names) and `M4-10` (narrowing the `PYTAG` cache key, which
inverts the risk to a stale image). Both say in the plan what to do instead if review judges the trade wrong.

## Scope

This candidate changed only `.review` documents:

```text
no production, proof, build, tool, generated or runtime path moved
```

Every Rocq module, the OCaml transport, the witness sources, the module file, the generated Go and the
reviewed goldens are byte-identical to the contract activation
`0b7fd86825936c37f31ef83879574d526d548122`, and no M4 step was executed.

The audit used only permitted evidence: the accepted `.review/PERFORMANCE.tsv` baseline, `make prover-log`,
`make profile`, per-target timings, ordinary Git commands, and two one-off cProfile runs inside the pinned
Python image. **No permanent audit, timing, inventory or comparison tool was created**, no registry or schema
was added, and no raw log is committed. `.review/M3_AUDIT.md` is one temporary table.

M2 is ACCEPTED under `M2-ACCEPT-9814db7`, M1 under `M1-ACCEPT-6524b43`, C4 under `C4-ACCEPT-39ea7e3` and M0
under `M0-ACCEPT-86a63db`. M4, C5 Step 0 and C5 remain forbidden. Only Rob accepts M3.
