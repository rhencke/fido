# M2 GREAT MEASUREMENT CULLING — IMPLEMENTATION REVIEW — BLOCKING — REPAIR 4

## Disposition

**M2 replacement candidate `d44a69dd5f538cf9888303f579e766d889348018` is BLOCKING.**

It becomes the **fourth blocked Great Measurement Culling replacement candidate**.

Documentation-only freeze `d3194fa45f6cb92b77521bacfb01e1356f5b26c5` is not a separate implementation candidate.

C4, M0 and M1 remain accepted and are not reopened.

**M2 Culling Repair 4 is the sole permitted implementation work.**

M3, M4, C5 Step 0, C5 and feature work remain forbidden.

Use:

```text
/loop 3m
```

Continue until this exact repair is complete or a real conflict blocks progress. When complete or genuinely
blocked, notify Rob with the notification tool.

## Exact review basis

```text
Uploaded snapshot:
  fido-main - 2026-08-03T153020.848.zip

Uploaded Git head / documentation-only freeze:
  d3194fa45f6cb92b77521bacfb01e1356f5b26c5

M2 replacement implementation candidate:
  d44a69dd5f538cf9888303f579e766d889348018

Previous blocked replacement candidate:
  be0b569e598250449b9f131aeb8cbeaa3907860c

Accepted M1 candidate:
  6524b437bd7a7d6b2616563b8789e28a00c7af13
```

Use every file, FCB document, gate and current-state document from this exact ref. Do not mix refs, reset,
rebase or rewrite history. Preserve `life.md` exactly.

---

## What passes

The performance implementation now satisfies its accepted job:

- `tools/perf.sh` unconditionally removes and recreates `fido-perf-v1`;
- the builder configuration is established by the script rather than inherited;
- stable Python, Rocq, OCaml and Go stages are primed outside the measured interval;
- the cold and hot runs use the exact `make -j1 BUILDER=fido-perf-v1 check` path;
- the TSV has one start and nine completion rows per mode, with monotonic cumulative milliseconds;
- the recorded pair is cold `270.0 s`, hot `63.7 s`;
- publication remains a same-directory rename after both runs pass;
- no gate reads the performance record and nothing depends on `make perf`;
- Culling Repairs 1 and 2 and their D-24 rows are gone;
- the Index, Roadmap and Model Operations now point to the current-state owner instead of carrying the cursor;
- `.v`, OCaml, generated Go and goldens remain unchanged;
- the no-host-Python boundary and the exact D-30 complexity rule remain intact.

Do not change `tools/perf.sh`, the Makefile, Dockerfile, hook or `.review/PERFORMANCE.tsv` again.

---

## The sole blocker

Repair 3 required `.review/M_SERIES_PLAN.md` to keep the stable M-series sequence and permanent laws **without
carrying the active checkpoint cursor**.

The candidate did not complete that correction.

The document says near its top:

```text
Which are accepted and which is under way is owned by .review/NEXT_STEPS.md.
```

It then copies that state in the sequence:

```text
M0 Governance Closeout (accepted)
M1 Source Diet (accepted)
```

and the M2 section begins:

```text
**Active.** The full contract is ...
```

The review request consequently makes a false completion claim:

```text
the M-series plan ... no longer carry the current cursor
```

The values happen to agree today. That is not the accepted result. The point of the one-owner repair is that
the next transition must not require another synchronized edit across multiple authorities.

**Complexity fit: BLOCKED — one mutable checkpoint cursor still has two live owners.**

### Required correction

Edit `.review/M_SERIES_PLAN.md` only as follows:

1. Remove `(accepted)` from the M0 and M1 entries in the sequence.
2. Remove `**Active.**` from the M2 section.
3. State the M2 contract and obligation locations without claiming that M2 is currently active.
4. Replace the stale sentence under the M1-origin M3 findings:

   ```text
   None blocks M1, and none may be implemented before Rob accepts M1.
   ```

   with a current statement equivalent to:

   ```text
   These findings were assigned to M3 by the M1 review and remain mandatory M3 work.
   ```

Keep the exact M1 acceptance token where it is provenance for the permanent source-comment law. That is stable
rationale, not the current cursor.

Do not remove the stable M0–M4 order, dependencies, M4 approval act, permanent source-comment law, M2 product
description or M3 assignments.

No new gate, schema, banner generator or FCB amendment is authorized.

---

## Repository-state changes

1. Install `.review/M2_CULLING_REPAIR_4.md` as the sole repair authority.
2. Delete `.review/M2_CULLING_REPAIR_3.md`; Git owns it.
3. Replace its D-24 row and owner marker with Repair 4.
4. Reopen M2-01 and any matrix row whose exact evidence changes.
5. Correct the false claim in `.review/REVIEW_REQUEST.md`.
6. Update `.review/NEXT_STEPS.md` to name the new candidate and sole repair.
7. Commit one implementation candidate.
8. Add one later documentation-only freeze requesting Rob's review.
9. Notify Rob.

---

## Allowed changes

Repair 4 may change only:

- `.review/M_SERIES_PLAN.md`;
- `.review/M2_OBLIGATION_MATRIX.tsv`;
- `.review/NEXT_STEPS.md`;
- `.review/REVIEW_REQUEST.md`;
- deletion of `.review/M2_CULLING_REPAIR_3.md`;
- addition of `.review/M2_CULLING_REPAIR_4.md`;
- the exact D-24 row and owner-marker changes required by that replacement.

It may not change:

- `tools/perf.sh`;
- `.review/PERFORMANCE.tsv`;
- Makefile, Dockerfile or pre-commit hook;
- any other tool;
- any `.v`, OCaml or generated Go file;
- proof, extraction, transport, diagnostics, generated bytes or runtime behavior;
- `life.md`;
- M3, M4 or C5 work.

Do not run `make perf`.

---

## Verification

Run:

```text
make fcb-write
make fcb
make claims
make names
make diet
make hostpython
make fmt
make check
make regenerate
make regen-guard
make audit-fresh
```

Run the real pre-commit hook over the exact staged snapshot without bypassing it.

Also verify:

- `.review/M_SERIES_PLAN.md` contains no active-checkpoint assertion;
- its sequence contains no accepted-status annotations;
- `.review/NEXT_STEPS.md` is the sole owner of the active M2 candidate and successor prohibition;
- Governance remains the owner of accepted amendments and decisions;
- Repair 3 and its D-24 row are absent;
- only Repair 4 remains as the current repair authority;
- `tools/perf.sh` and `.review/PERFORMANCE.tsv` are byte-identical to candidate `d44a69d...`;
- every `.v`, OCaml, generated Go and golden byte is unchanged;
- generated hashes remain:

```text
go.mod
d8f8d4f62b5b574067a4e4bf64a298bbe2cb5bc9a28d8f9c321c776e838cf1fa

main.go
b6765619f969e7fd85b4998616d8a515c5a2c0e2d397c3ee915718f35fbc48de
```

- the whole-theory assumption audit remains green;
- M3, M4, C5 Step 0 and C5 did not begin.

---

## Definition of done

Repair 4 is complete only when:

- the M-series plan owns stable sequence and permanent laws only;
- `NEXT_STEPS` alone owns the active checkpoint and candidate;
- the review request no longer overclaims the one-owner result;
- no performance or correctness implementation changes;
- every required gate is green;
- one exact candidate and one later freeze are committed;
- no commit follows the freeze;
- Claude notifies Rob.

Only Rob accepts M2.
