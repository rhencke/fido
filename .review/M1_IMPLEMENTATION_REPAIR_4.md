# M1 IMPLEMENTATION REVIEW — BLOCKING — REPAIR 4

## Disposition

**M1 implementation candidate `c73925c6b7c432a8265bdb052388efaf57d96f6f` is BLOCKING.**

It becomes the **fourth blocked M1 implementation candidate**.

Documentation freeze `961af100028e8d12515b61bb48745b6f1d6d6c14` is not a separate implementation candidate.

**M1 repair 4 is the sole permitted implementation work.**

C4 and M0 remain accepted. This review does not reopen either checkpoint.

M2, M3, M4, C5 Step 0, C5, and all feature work remain forbidden.

No semantic, proof, build, or gate redesign is authorized. The repair is an evidence-map and current-comment correction.

Use:

```text
/loop 3m
```

Continue until every required correction is complete or a real M1 contract conflict blocks progress. When complete or genuinely blocked, notify Rob with the notification tool.

---

## 1. Exact review basis

```text
Uploaded snapshot: fido-main - 2026-07-28T173242.683.zip
Uploaded Git head: 961af100028e8d12515b61bb48745b6f1d6d6c14
Blocked M1 implementation candidate: c73925c6b7c432a8265bdb052388efaf57d96f6f
Documentation-only freeze: 961af100028e8d12515b61bb48745b6f1d6d6c14
M1 baseline authority ref: 068d3371ac3300303d6c7c99a97ed884182c81e4
Previous blocked M1 candidate: 8ad80e6614bff64b493bbdd1db937f4640eda252
M1 authority: .review/M1_SOURCE_DIET.md
Accepted review basis: .review/REVIEW_BASIS.md
```

Use all code, FCB, gates, ledgers, and documentation from this exact ref. Do not reset, rebase, rewrite history, or mix refs.

Preserve `life.md` exactly.

---

## 2. What repair 3 got right

Keep these results:

1. The permanent source-diet path runs only `--self-test`, `--check`, and `--wiring`.
2. The permanent path reads the current `.v` files and `M1_COMMENT_EXCEPTIONS.tsv`, not M1 baseline or candidate evidence.
3. A later clean report, `.v` file, declaration, or larger tree no longer fails merely because it postdates M1.
4. Removing the temporary M1 baseline, metrics, disposition, deletion, and obligation files leaves the permanent diet green.
5. A bad comment in later source still fails the permanent gate.
6. Permanent and M1-only source-diet controls are separated.
7. Permanent and M1-only mutation groups are separated.
8. The implementation candidate carries a header-only metric table.
9. Candidate-owned evidence is unchanged by the freeze.
10. The freeze changes only the four closed-overlay files it needed.
11. The exact candidate metrics reproduce:

```text
repository_total_bytes                 2,675,876
deterministic_compressed_archive_bytes   586,301
v_comment_bytes                           59,370
v_comment_block_count                         662
```

12. Every surviving top-level Rocq command matches the baseline after removing exactly the eight ledgered declarations.
13. Generated Go and reviewed runtime output remain unchanged.

The lifetime defect from repair 3 is closed. Do not alter its implementation.

---

# 3. Blocking finding A — the obligation matrix still names gates which no longer run the evidence

## 3.1 Contract violated

This violates:

- M1-02, M1-07, M1-08, M1-10, M1-12, M1-14, and M1-15;
- M1 §12, which requires every obligation row to close with exact evidence;
- the claim-matrix contract, whose `gate` cell names the gate which runs the row’s evidence;
- the freeze claim that all fifteen rows map to the evidence which establishes them.

Repair 3 correctly removed M1 exit checks from the permanent paths. The matrix still points several exit-only obligations at those permanent paths.

## 3.2 Exact false mappings

### M1-02 — baseline seal

The row names:

```text
implementation: tools/source-diet.py:check_baseline
gate: Makefile:diet
```

`make diet` no longer calls a baseline mode. `check_baseline` runs through the explicit M1 evidence path, not the permanent comment gate.

### M1-07 — exact deleted-file disposition

The row names:

```text
implementation: tools/source-diet.py:check_disposition
gate: Makefile:diet
```

The permanent diet deliberately reads no file-disposition ledger. Exact deleted-file evidence runs through `verify_m1_evidence`, including `check_disposition_exact`.

### M1-08 — deleted-declaration evidence

The row names:

```text
implementation: tools/source-diet.py:check_declaration_ledger
gate: Makefile:diet
```

The permanent diet deliberately reads no declaration-deletion ledger. This evidence runs through the explicit M1 verifier.

### M1-10 — surviving Rocq command identity

The row names:

```text
implementation: tools/source-diet.py:declaration_blocks
gate: Makefile:diet
```

`make diet` no longer runs code identity. The establishing surface is `check_code_exact`, reached through `verify_m1_evidence`.

### M1-12 — both mutation groups are load-bearing

The row names:

```text
gate: Makefile:fcb
```

`make fcb` runs `tools/gate-mutation-test.py` without `--m1`, so it proves only the permanent-policy group. The M1 exit-evidence group is run explicitly with:

```text
python3 tools/gate-mutation-test.py --m1
```

The row currently claims both groups while naming only the permanent one.

### M1-14 — proof/artifact preservation plus exact source preservation

The row names:

```text
gate: Makefile:check
```

`make check` establishes proof, extraction, transport, e2e, and generated-artifact preservation. By design, it does not establish M1’s baseline-to-candidate Rocq command identity. That second half is established by the explicit M1 verifier. The row must name both.

## 3.3 Why this blocks

The implementation is likely correct. The review evidence is not.

The claim-matrix checker verifies only that named strings exist. It does not infer which command invokes which check. Human review must reject a row which points to a real target that does not run the claimed evidence.

A false evidence map is exactly the kind of green-but-unearned claim M1’s matrix exists to prevent.

---

# 4. Required matrix repair

Correct the evidence topology without changing any gate behavior.

## 4.1 Explicit M1 verifier token

Use the exact command already present in `.review/REVIEW_REQUEST.md` as the gate token for exit-only evidence:

```text
.review/REVIEW_REQUEST.md:python3 tools/source-diet.py --verify-m1-evidence
```

Use the exact mutation command already present there for the M1-only mutation group:

```text
.review/REVIEW_REQUEST.md:python3 tools/gate-mutation-test.py --m1
```

## 4.2 Required row corrections

At minimum:

- **M1-02** — keep `check_baseline`; change the gate from `Makefile:diet` to the explicit M1 verifier.
- **M1-03** — name both `check_disposition` and `check_disposition_exact`; use the explicit M1 verifier as the gate.
- **M1-07** — name `check_disposition_exact` as the exact implementation surface; use the explicit M1 verifier.
- **M1-08** — keep `check_declaration_ledger`; use the explicit M1 verifier.
- **M1-10** — name `check_code_exact`, not only its parser helper; use the explicit M1 verifier.
- **M1-12** — name both the permanent mutation run and the explicit `--m1` run, or state the split in separate exact evidence tokens. The gate cell must include the explicit M1 mutation command; `Makefile:fcb` may remain only for the permanent group.
- **M1-13** — point the gate at the explicit M1 verifier command, not merely prose naming the mode.
- **M1-14** — name both `Makefile:check` and `tools/source-diet.py:verify_m1_evidence` as implementation surfaces; name both `Makefile:check` and the explicit M1 verifier in the gate cell.
- **M1-15** — point at the explicit M1 verifier command, which runs `check_freeze_overlay`.

M1-04, M1-05, M1-06, and M1-11 may continue to name `Makefile:diet`, because those are permanent comment-policy obligations which `make diet` actually runs.

Do not modify `tools/claim-matrix-gate.py` to infer call graphs. That is general tool work and belongs to M3. Correct the current rows.

---

# 5. Blocking finding B — the Makefile retains the pre-repair description of `diet`

## 5.1 Contract violated

This violates M1’s current-fact technical-comment law and M1-09.

Immediately above the corrected permanent-policy comment, the Makefile still says:

```text
The M1 source diet: the .v comment law, the exception relation both ways, and one disposition per file.
```

The repaired permanent `diet` target does **not** check one disposition per file. That is the intended result of repair 3.

The nearby text then states the opposite. The retained comments contradict each other.

## 5.2 Required correction

Delete the stale sentence.

Place the live-FCB comment directly above `fcb:` and keep one terse, current description directly above `diet:`:

```make
# The permanent source-comment policy only. M1 exit evidence runs explicitly for M1 review.
diet:
```

Preserve the useful explanation that a permanent baseline check would reject later files and declarations, but do not repeat it twice.

Change no recipe, prerequisite, target, hook, or behavior.

---

# 6. Strict-scope disposition

| Finding | Contract violated | Blocks M1 | Owner |
|---|---|---:|---|
| Exit-only matrix rows point at permanent targets which do not run them | M1 exact-evidence and exit contracts | **yes** | M1 repair 4 |
| Makefile says permanent diet checks one disposition per file | M1 current technical prose | **yes** | M1 repair 4 |
| Fragile counts, line numbers, and positional prose | none required for M1 acceptance | no | `M3-FRAGILE-PROSE` |
| Claim-matrix call-graph or mutation hardening | none required for M1 acceptance | no | M3 |
| Build timing and dependency cost | none in M1 | no | M2 |
| Proof-module or build-graph restructuring | none in M1 | no | M4 |
| `life.md` content | none; separately authorized character continuity | no | preserve exactly |

Do not pull nonblocking work into repair 4.

---

# 7. Allowed changes

Repair 4 may change only:

```text
Makefile                                  # comments only
.review/M1_OBLIGATION_MATRIX.tsv
.review/M1_IMPLEMENTATION_REPAIR_4.md
.review/NEXT_STEPS.md
.review/REVIEW_REQUEST.md
.review/M1_FILE_DISPOSITION.tsv           # exact candidate byte changes only
.review/M1_METRICS.tsv                    # header in candidate; exact rows in freeze
.review/fcb/current/FIDO_FCB_REFERENCES.tsv, only for repair-file replacement
```

A generated current-state view may change only when an existing gate proves it is required by those exact edits.

Do not change:

- any `.v` file;
- `tools/source-diet.py`;
- `tools/gate-mutation-test.py`;
- `tools/claim-matrix-gate.py`;
- the pre-commit hook;
- any Make target or recipe;
- Docker, Dune, OCaml, extraction, fixtures, goldens, generated Go, or runtime behavior;
- the M1 contract, FCB architecture, or M-series sequence;
- `life.md`.

No FCB amendment is required.

---

# 8. Candidate and freeze

Create one new implementation candidate containing:

- the corrected Makefile comments;
- the corrected open/closed matrix evidence map;
- the repair-4 authority and current-state transition;
- exact candidate-owned file disposition;
- header-only metrics;
- a closed review request until the candidate exists.

Then generate exact metrics from that candidate and make one later documentation-only freeze containing only the accepted freeze overlay.

The freeze must not modify candidate-owned evidence.

Nothing may follow the freeze.

---

# 9. Verification

Run:

```text
make diet
make fcb
make claims
make names
make check
make regenerate
make regen-guard
make fmt
make audit-fresh
python3 tools/source-diet.py --m1-self-test
python3 tools/gate-mutation-test.py --m1
python3 tools/source-diet.py --verify-m1-evidence \
  --baseline-ref 068d3371ac3300303d6c7c99a97ed884182c81e4 \
  --candidate-ref <new candidate>
```

Run the real pre-commit hook against the exact staged snapshot without bypassing it.

Also inspect the final matrix manually and prove:

1. every `gate` cell names a command which actually invokes the row’s implementation or evidence check;
2. `Makefile:diet` appears only on permanent comment-policy rows;
3. `Makefile:fcb` is not presented as running the M1-only mutation group;
4. M1-14 names both the full project gate and exact M1 source-identity evidence;
5. the permanent lifetime split remains unchanged;
6. the new freeze changes only the closed overlay;
7. generated bytes and runtime output remain exact;
8. C4 and M0 remain accepted;
9. M2 through M4 and C5 remain forbidden.

Do not create a prose-heavy closure report.

---

# 10. Definition of done

Repair 4 is complete only when:

- every M1 obligation row maps to the evidence path which actually runs it;
- no exit-only obligation points only to `make diet` or `make fcb`;
- the stale Makefile disposition sentence is gone;
- no tool or build behavior changed;
- candidate-owned evidence is exact and immutable;
- the metric table is generated from the exact candidate;
- the full verification passes;
- one new candidate is committed;
- one later documentation-only freeze names it;
- no commit follows the freeze;
- Claude notifies Rob.

Only Rob accepts M1.
