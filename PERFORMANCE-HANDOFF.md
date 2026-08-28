# Commit / `make check` performance — handoff for the reviewer

Goal Rob set: a **cold** commit (pre-commit hook, `.githooks/pre-commit`) **under 60 s**.

This documents where the time goes now, the three safe cuts already landed, and the one
remaining dominant cost — which needs a certified-theory change (a bp-free `disposition`
tag) that is best decided by the reviewer, since it edits `Compilable/Analysis` during the
C4 closure freeze.

No proof is weakened anywhere below. Every measured number is wall-clock on this 4-core
builder, from the pinned Buildx image.

---

## 1. The mechanism (why it *felt* like 3 minutes)

The hook (and `make check`) time a **warmed** verification against the 120 s budget owned
solely by `tools/check-budget.sh` (`BUDGET_SECONDS=120`). If the **first** (cold) pass
exceeds 120 s, the hook runs the **entire** verification **a second time** ("warmed
confirmation") and judges *that*. So a slow cold pass costs `cold + warm` wall-clock.

- Before: cold **first pass 184 s** → over budget → warmed confirmation 25 s → **~210 s wall**.
- After the three cuts below: cold **first pass 86 s**, **under budget, single pass** — the
  double-run is gone. `git`-commit of a Dockerfile-only change is now ~26 s.

The budget mechanism itself is untouched (it has integrity self-tests and is Rob's to change).

---

## 2. Cuts already landed (committed on `c4-evidence-dag`)

| Commit | What | Effect |
|---|---|---|
| `0527968` | Sealed positive control `sealed_ok.v`: 7 `destruct (Index.all_files pXidx) eqn:E` first-element extractions forced WHNF through the **slow kernel reducer** (~2.3 s each, far worse cold). Replaced with `eval vm_compute in (…)` head extraction — same first file/package, VM path. | prover step **102 s → ~1.5 s** for that control |
| `5219546` (a) | The four heavy Rocq proof fixtures (evidence DAG, negative transport, rejection matrix, §25 provenance) are independent (distinct output trees, shared read-only library). They now compile **concurrently** in the emit RUN. | fixture section **~51 s → ~42 s** (Reject-bound) |
| `5219546` (b) | The e2e proof-assumption audit was **recompiling all 8 proof-bearing witnesses a second time** (stripped of `Materialize`) only to reach them in the Fido modpath. Now the witnesses compile once under `-R e2e Fido` and the audit **`Require`s their `.vo`** — a compiled vernacular command is not replayed on `Require`, so `Materialize` never re-fires. | audit **~45 s → ~2 s** |

All three are build-orchestration / tactic changes. `make e2e` green; byte-identity holds
(the pre-commit staged==pristine gate passed).

---

## 3. Where the 86 s cold pass goes now

Dominant step is `[emit 8/8]` at **~65 s**; `[prover]` ~15 s; go build + policy gates +
artifact byte-compare ~6 s. Inside the emit RUN:

```
 0–13 s   dune build (theory, shared mount) + Witness/Multi/Empty/Bytes/Alias materialization
13–18 s   (tail of materialization)
18–60 s   heavy proof fixtures, PARALLEL  → ~42 s, floored by WitnessReject   ◀── THE REMAINING COST
60–62 s   proof-assumption audit (now Require-based)
62–65 s   provenance-enforcement + shell-producer + cross-mount self-tests
```

So the single remaining dominant cost is **`e2e/WitnessReject.v` ≈ 42 s**.

---

## 4. Why WitnessReject.v is 42 s — the proof-bearing recompute floor

`WitnessReject.v` is a matrix of ~47 tiny one-statement programs, each proving
`Compilable.rejects/compiles/outsides (prog […])` with `Ltac reject := vm_compute;
reflexivity` (and `Qed`). Each proof reduces `Compilable.disposition (prog […])` — the full
compile pipeline — and pays it **twice**: once in the tactic, once when `Qed` re-verifies the
VM cast through the kernel. ~0.87 s/program × 47 ≈ 42 s. This re-runs on **every**
library-source commit (the fixtures import `Compilable.Analysis`, so any change re-verifies them).

The double-VM is inherent to a **kernel-verified** VM proof: `vm_compute; reflexivity. Qed.`
computes to check the goal, then Qed re-computes to certify the cast. `vm_cast_no_check`
would drop the Qed pass but **bypasses kernel verification** — unacceptable here (the whole
gate audits assumptions and forbids trusted fallbacks). Batching all 47 into one `vm_compute`
over a list does **not** help: the total reduction, not per-proof overhead, is the cost.

The cost scales with program complexity (measured 0.3 s–4 s across the matrix), i.e. it is in
the **analysis reduction**, not fixed index overhead.

### What `disposition` forces (the actual lever)

`Compilable.v`:
```
disposition p = disposition_from_data (data_of_result (analyze p))
disposition_from_data d =
  if data_diagnostics_empty d then (if data_boundaries_empty d then Compiled else OutsideScope)
  else Rejected
```
`Analysis.v`:
```
data_of_result _ = result_data p            (* the sealed Result holds no data; this RECOMPUTES *)
result_data p = mk_result_data i s (phase_data s) (bindings s)
                                (exist _ (raw_facts (bindings s)) _)
                                (exist _ (raw_preflight (bindings s)) _)
data_diagnostics_empty d = data_no_collision d && data_no_missing d && data_no_redecl d && data_no_cause d
data_boundaries_empty  d = data_no_req d
data_no_cause d = forallb (fun row => occ_cause row = None) (proj1_sig (rd_facts d))
data_no_req   d = forallb (fun row => occ_req  row = None) (proj1_sig (rd_facts d))
raw_facts b = flat_map (… occ_facts_va va ctab …) (nodes)          (* the O(n²) proof-bearing refs *)
```

So `vm_compute (disposition p)` forces `index_program`, `bindings`, and the **full
proof-bearing `raw_facts`** (each `OccFact` carries the exact site+kind refs / membership
proofs — the documented O(n²) floor), then reads emptiness off it. The **tag needs only the
emptiness of `occ_cause`/`occ_req` and the collision/missing/redecl booleans — not the exact
refs the facts carry.**

---

## 5. The lever: a bp-free `disposition` tag (theory change — reviewer's call)

Add a computation that decides `Compiled | Rejected | OutsideScope` **without materializing
the proof-bearing `OccFact` refs**, and prove it **equal** to the current `disposition`
(kernel-checked, byte-identical output, exactness of the real verdict untouched). Then route
`WitnessReject.v`'s `reject`/`compileok`/`outside` tactics through the light tag. Expected:
per-proof ~0.87 s → ~0.1 s, so WitnessReject ~42 s → ~5 s, emit ~65 s → ~28 s, and cold
commit **~50 s (under 60 s)**.

This is exactly the "bp-free projection view" pattern the codebase already uses for concrete
controls (see the memory notes on the exact-judgment vm cliff), but here it must cover the
whole **diagnostic-presence** decision (`data_no_cause` / `data_no_req` / collision / missing /
redecl) rather than a single row. The risk — and why I did not land it mid-freeze — is that a
provably-equal light emptiness path re-derives the analysis's cause/req decision logic and
proving the two agree is itself on the vm cliff. It must **not** introduce a second authority
for the verdict: the light path has to be a *projection/decision that the exact path is proven
to refine*, not a parallel evaluator.

Concretely, the cheapest shape to explore:
- a boolean `any_cause b : bool` / `any_req b : bool` over the bindings that decides presence
  **before** `occ_facts_va` builds the ref-bearing facts, with
  `any_cause (bindings p) = negb (data_no_cause (result_data p))` proved once (abstract `bp`);
- `disposition_fast p` built from those booleans + the existing (cheap) collision/missing/
  redecl deciders, with `disposition_fast p = disposition p` as the bridge theorem;
- controls reduce `disposition_fast` (bp-free ⇒ no O(n²) ref build) and rewrite by the bridge.

---

## 6. Complementary levers (no theory change) — if the tag is deferred

- **Split `WitnessReject.v` into N parallel-compiled chunks** (shared prelude in one small
  module). On 4 cores this brings the 42 s matrix to ~12–18 s. Costs a few fixture files
  (weigh against the tag, which needs none). Marginal to hit <60 s on 4 cores alone.
- **`prover` (~15 s)** is the `Analysis.v` compile (~8 s elaboration) + deps. Splitting the
  4000-line `Compilable/Analysis.v` at a real seam would let dune recompile only the edited
  part and parallelize — a structural change needing Rob's sign-off.
- **Policy gates** run one `docker run` per gate (~1–2 s startup each); batching them into a
  single container invocation trims a few seconds.
- **Mount serialization**: `prover` and `emit` share a `sharing=locked` dune `_build` mount,
  so they cannot overlap on a cold build (emit needs prover's `.vo`). This caps how much
  parallelism helps; only cutting each stage's own compute (the tag) gets under it.

---

## 7. Hard constraints for any further work

- No proof weakened; no `Admitted`/axiom; no `vm_cast_no_check` or other kernel-verification
  bypass; assumption audit must still catch an axiom in any fixture.
- Generated Go output must stay **byte-identical** (the staged==pristine gate enforces it).
- One authority per fact: a fast tag must be a **proven refinement/projection** of the exact
  `disposition`, never a second evaluator.
- `make check` must keep timing the complete path; do not move gates out of it.
