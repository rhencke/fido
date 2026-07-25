# FIDO SPEC-CLOSURE — REVIEW OF REPAIR 1 BUNDLE, AND REPAIR 2 DIRECTIVE

**Date:** 2026-07-23
**Reviewed bundle:** `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_R1_2026-07-23.zip`
**Review method:** Independent re-verification. Every hash re-checked from bundle root; the shipped audit script re-run (output matches the frozen JSON byte-for-byte); the shipped latitude extractor re-run against the pinned documents (output matches the frozen manifest byte-for-byte); dispositions audited for totality; the latitude ledger sampled adversarially; fixed points checked for regression.
**Repair authorization token (for the new work below):** `SPEC-CLOSURE-acceptance-repair-2`
**Authority limits:** identical to Repair 1. Documentary only. No code, `.v`, or gate changes. Nothing may claim FIXED, accepted, closed, or scored. All countersign cells are created empty and remain Rob's alone. This directive does not accept C4 or authorize C5.

---

## 1. VERIFIED — attacked and held

The following were independently attacked and survived. They are FIXED POINTS of Repair 2; weakening any of them is a regression, not a fix.

1. **Integrity.** All 28 frozen hashes verify. The Repair 1 directive is included byte-identical (`0bd21c…`). The pinned spec and memory model in `/pins` hash to the same values verified last round against the real go1.23.2 distribution files.
2. **Reproducibility.** `audit_spec_closure_bundle.py` re-runs clean and reproduces the frozen audit JSON exactly. `extract_latitude.py` re-runs against the pinned HTML and reproduces the frozen 227-candidate manifest exactly. The machinery is real, shipped, and honest.
3. **R-1 (evaluation order): Route A, correctly.** Plan §12.4 + §25.21 `SC-20-EVAL-ORDER-LATITUDE`; `step` admits every spec-permitted unspecified order with no synthetic choice label; the spec-*specified* lexical left-to-right order of calls, methods, and receives is a named deterministic obligation with its own fixture. SPEC-097 is bespoke. LAT-136/137 (including the spec's own `[1,2] or [2,2]` example) are owned.
4. **R-2 (latitude ledger): machinery and hard rows.** 227 mechanical candidates + 3 explicitly hand-added X-rows (append growth, select choice, scheduling), all 230 dispositioned, zero missing justifications, zero PROVED-REFINEMENT (no Route-B smuggling). The deep-cut rows are genuinely right: zero-size-variable address equality as STEP-NONDET (twice), float32 extended-intermediate-precision latitude, division-by-zero panic-or-IEEE, init hidden-dependency order, runtime panic *values* demoted to adequacy.
5. **The FMA row is exemplary.** LAT-121 models both fused and unfused branches as `step` nondeterminism, and the evidence file records a concrete pinned-toolchain observation — an actual one-ulp bit-pattern difference between `x*y+z` and `math.FMA` — labeled as adequacy evidence, not spec truth, exactly as directed. That observation is scar-quality work.
6. **R-3 (module/toolchain pin): design correct.** BOUND-001..003: emitted `go 1.23` equals the ledger's language version; module path from the one ModulePath authority; no `toolchain` directive; invocation contract `GOTOOLCHAIN=local`, `GOENV=off`, `GOWORK=off`, with `go version` verified before build; the shipped `alldocs.go`, `modfile/rule.go`, toolchain `select.go`, and gc `-lang=go1.23` source pinned as governing evidence. Changing a directive or governing source is declared a ledger-revision event.
7. **R-4 (terminal observation tuple): complete.** §22.3 defines `(stdout bytes, stderr projection, exit status)` once; println → stderr (observed: 14 bytes, exit 0); fatal panic → exit 2 with first-line projection `panic: <value>` (observed) and traceback-as-evidence-only; runtime noise excluded *explicitly* and owned by BOUND-X009, not by silence.
8. **R-5 (provenance): compliant.** Both disposition ledgers state the APPLIED-only rule; every countersign cell exists and is empty; the false uniform-elaboration claim is gone; the audit separates machine-checkable from judgment claims; a `template` column exists in the CSV.
9. **R-6: all four items.** Three synthesized anchors flagged with a header note and per-row notes; the grammar counting rule (174 definitions / 173 names, metagrammar included, `Expression` twice) is in the artifact header where the next auditor will find it; the NaN-map row (SPEC-124) states insertable / len-counted / unretrievable / undeletable / cleared-by-`clear`, with fixtures; SPEC-026 is rewritten bespoke and *correct* — identity includes tags, conversion ignores tags per the pinned rule — with both fixtures at plan §25.5.
10. **Fixed points intact.** `uintptr` remains OUT pending ADR-0001; SPEC-X005/X006 are strengthened, not weakened; range-over-func design untouched; no forbidden acceptance/score language found anywhere in the freeze or ledgers.

This was a strong repair. Most of it closes.

---

## 2. FINDINGS

### R2-1 — BLOCKING — Acceptance latitude was waved off with one false sentence; the taxonomy is missing its fourth kind

Eleven rows — every "Implementation restriction" sentence the extractor caught — carry the identical justification:

> "This permits or forbids compile-time acceptance behavior; it does not vary the meaning of a program after CompilableProgram exists."

That sentence is false **for claim (B)**. Fido's differential claim is two-sided: accepted programs must mean what the model says, **and accepted programs must be accepted by the pinned toolchain** — the fresh-build preflight makes `go build ./...` success part of the pipeline's definition of health. A spec-permitted compiler rejection that go1.23.2 gc *exercises* turns a Fido-accepted program into a red preflight. That is precisely a Fido-accepts / gc-rejects divergence, which this project's own law classifies as a Fido correctness failure, never a limitation. The preflight is the last line of defense; it must not be the mechanism.

Concretely misdispositioned:

- **LAT-077 (unused local variables).** Pinned gc **does** reject unused locals — it is the most famous strictness in the toolchain. If elaboration can admit an unused local into `CompilableProgram`, materialize fails. This row alone makes the class BLOCKING.
- **LAT-019 / LAT-134 (constant precision and rounding).** Fido's exact rationals intentionally exceed the spec minimum; pinned gc has finite constant precision and rejects constants it cannot represent ("constant overflows…", oversized literals). Fido can accept constants gc rejects. The acceptance bound must be pinned and enforced at elaboration.
- **LAT-148 (duplicate constant switch cases).** Pinned gc rejects duplicates. Same class.
- **LAT-085, LAT-171, LAT-177, LAT-181.** Each needs its own pinned-gc observation and an individual justification; none may share a sentence.

Two rows prove the template was pasted, not reasoned, which is why the class must be reopened rather than patched:

- **LAT-118** ("A compiler may not optimize under the assumption that overflow does not occur") is an implementation *prohibition* — a guarantee that wrap semantics are reliable. It is not acceptance behavior, and the justification attached to it is a category error. Correct disposition: NOT-LATITUDE, with a justification naming it a prohibition that *guarantees* deterministic wrap, owned by SC-05.
- **LAT-214** (memory-model prose comparing Go to Java/JavaScript) is exposition. NOT-LATITUDE is right; the acceptance-behavior justification attached to it is nonsense.

Also: **LAT-180 (OUT-COVERED) and LAT-181 (NOT-LATITUDE)** are the same anchor and the same import-path subject with inconsistent dispositions; unify them.

**Required change.**
1. Add a fourth live disposition to the Latitude Ledger: **`ACCEPTANCE-ALIGNMENT`**. Its row fields: the pinned-toolchain observation (does go1.23.2 exercise the restriction? — a compiled fixture with the accept/reject result and exact diagnostic, in the style of the existing FMA/println/panic observations), the Fido elaboration obligation, and the named contract.
2. Re-disposition every "Implementation restriction" row individually. No shared justification sentence anywhere in the ledger; the audit script gains a check that no justification string repeats across ACCEPTANCE-ALIGNMENT rows.
3. State the governing principle in the plan (§22): **Fido's acceptance is a subset of pinned-gc acceptance**, as a standing adequacy obligation with the theorem-shaped name `fido_accepts_subset_pinned_gc`, discharged per restriction by elaboration-time rejection (exact diagnostic; unrepresentable where the architecture allows) plus a fixture pair: the restricted program is rejected by Fido elaboration AND observed rejected by pinned gc.
4. First instances, in order: unused local variables; constant precision bounds (pin gc's observed limits and bound admitted constants, or reject oversize constants with an exact diagnostic at elaboration); duplicate constant switch cases.
5. Fix LAT-118, LAT-214, and the LAT-180/181 pair as above.

This is the same failure shape as last round, one level down: Repair 1 closed *execution* latitude and left *acceptance* latitude behind one template. Close the class, not the instances: the extraction already catches every "Implementation restriction" sentence, so the ledger has the candidates — they need real dispositions.

### R2-2 — REQUIRED — Remove the 13.8 MB executor binary from the bundle; ship the provenance chain instead

`.review/pins/go1.23.2-linux-amd64` is the actual `go` ELF executable, and it is why this bundle is fifteen megabytes. Two problems. First, a binary cannot self-attest: shipping a copy adds zero verification power (a tampered executor would ship its own tampered copy); the hash already recorded in the evidence file does all the work. Second, a documentary review bundle that contains an executable invites someone to run it, and bloats every future freeze that inherits it.

**Required change.** Delete the binary from the bundle. In `FIDO_GO1_23_PINNED_TOOLCHAIN_EVIDENCE`, keep the executor hash and add the provenance chain: the official `go1.23.2.linux-amd64.tar.gz` distribution SHA-256 as published in the Go release manifest, the member path (`go/bin/go`), and the statement that the local executor at `/usr/local/go/bin/go` hashes to the recorded value. The four pinned *source* files (alldocs, modfile rule, toolchain select, gc language) stay — text evidence is exactly right. Re-freeze; the bundle should drop to roughly one megabyte.

### R2-3 — RECOMMENDED — Decide the racy-run modeling scope deliberately

LAT-217/218/219 (word-tearing of multiword operations) and LAT-224 (racy read may observe any concurrently-executed write) are dispositioned STEP-NONDET, committing the machine to modeling access granularity and racy-read visibility. But every run exhibiting them already contains a `DataRace` BadPrefix and is condemned by `GoSafe`; the modeling cost is spent entirely on runs the safety theorem excludes. Either re-disposition to a single condemned-run rule — in a run containing a data race, reads at and after the race may yield havoc; the machine does not model sub-value access granularity — or keep STEP-NONDET and add an explicit §27 reserve acknowledging that this proof cost buys no reachable-safe-run semantics. Both are defensible; inheriting granularity modeling by accident is not.

### R2-4 — SMALL — Make template drift measurable, not just the dead sentence

The `template` column exists but is empty on all 491 rows, including the 48 operator and 25 keyword rows that (permissibly) share identical representation text — exactly the lexical-only class the flag was created for. Meanwhile the audit's "non-template" metric checks only for the *old* boilerplate sentence, so it cannot see a future incantation. Populate `template: lexical-only` on the OP- and KEY- shared rows (and any other justified shared-text rows), and extend the audit to emit a duplicate-representation histogram (top N with counts) so any new template announces itself in the frozen JSON.

---

## 3. Completion

Repair 2 is complete when: every R2 item's deliverables exist; the ACCEPTANCE-ALIGNMENT rows carry individual justifications and pinned-toolchain acceptance observations; the three named first instances have their fixture pairs; the binary is out and the provenance chain is in; the audit's new checks (justification-uniqueness, duplicate-representation histogram) run green and are frozen; all artifacts re-frozen with new SHAs; the repair ledger records `APPLIED` per row with **empty** Rob countersign cells; and nothing anywhere claims acceptance, closure, FIXED status, or a score. Deliver as `FIDO_GO1_23_SPEC_CLOSURE_REVIEW_BUNDLE_R2_<date>.zip`.

One sentence of standing, for the record: Repair 1 was the strongest submission this review has examined — the extraction reproduces, the evidence observations are exact, and ten of ten verified categories held under independent attack. What remains is one class, one binary, one deliberate scoping choice, and one metric. Rob's countersign, per row, is the only thing that ends this repair.
