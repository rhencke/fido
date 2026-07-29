# Review Request

state: requested
review: Implementation Review
confirmation: no
confirmation_used: no
human_override: (M2 Build Observatory, authorized by Rob's acceptance token `M1-ACCEPT-6524b43`)
result: awaiting Rob's human M2 review
candidate: 8325ddb9ee2dcb1087dbe22d754b9a7d4c5a3b43

contract: .review/M2_BUILD_OBSERVATORY.md
review_basis: .review/REVIEW_BASIS.md

`.review/NEXT_STEPS.md` owns mutable checkpoint and candidate state. This file pins the exact candidate under
human review; it does not own mutable state. Canonical data rows carry no candidate identity.

**A human M2 review is requested for candidate `8325ddb9ee2dcb1087dbe22d754b9a7d4c5a3b43`.** M1 is ACCEPTED under `M1-ACCEPT-6524b43`, C4 under
`C4-ACCEPT-39ea7e3` and M0 under `M0-ACCEPT-86a63db`. Every required obligation in
`.review/M2_OBLIGATION_MATRIX.tsv` is closed.

The Build Observatory is one registry, one runner and one tracked observation. The canonical suite recorded
399 sample(s) over 107 command-scenario pair(s) against this exact committed candidate.

**Permanent, run by every build and every commit:**

```text
make observatory   # the command-surface coverage validator and its controls
```

**M2 evidence, run explicitly for this review:**

```text
make observe HELP=1
make observe LIST=1
make observe COMPARE=.review/BUILD_OBSERVATION.json BASE=<a git ref carrying one>
python3 tools/build-observatory.py --self-test
python3 tools/gate-mutation-test.py
```

M2 measures and reports. It implements no optimization: every finding in
`.review/M2_RECOMMENDATIONS.tsv` carries an owner of M3, M4 or retain.

M3, M4, C5 Step 0 and C5 remain forbidden until Rob accepts M2. Only Rob accepts M2.
