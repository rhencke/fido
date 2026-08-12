# C6 — active task

Review: implementation

There is exactly one active thing: the **C4 exact-elaboration retreat repair (RC-S1)**, on one immutable
forward candidate, ready for a fresh whole-system review. Everything else — all of C6 Root 3 and every later
root — is **frozen behind the retreat** until Rob closes it. Rob alone closes the retreat and accepts.

This file is the current-action sheet. It says what is true now and nothing else. The repair and review
narrative, the superseded root-cause briefs, and the former migration inventory are Git history — recovered
from there, never restated here. The Root-3 contract lives in `DECISIONS.md`; the ownership law and the
retreat rule live in `ARCHITECTURE.md`; the milestone sequence lives in `ROADMAP.md`.

## The retreat and its repair

Per `ARCHITECTURE.md` §1 "Dependency retreat (targeted causal)", the accepted C4 guarantee `ARCH-03` — the
opaque static capability and its failure and outside-scope results all **retain the exact elaborated core by
construction**, and **equality to a rerun is never provenance** — was falsified: the reviewed candidate
discarded the core `compile` decided on and let the accessors rebuild a peer with `elaborate (source _)`. That
is recomputation wearing retention's clothes, which is exactly what the guarantee forbids.

The repair, on this candidate, in `Compilable.v`:

- each verdict record **physically stores** the `Core p` that `compile` branched on — `MkProg p c …`,
  `MkFail p c …`, `MkOut p c …`, one `c := elaborate p` per decision;
- `core` / `failure_core` / `outside_core` are record **projections** of that stored field — **none calls
  `elaborate`**, `all_diags`, `all_boundaries`, or any other source-to-analysis builder;
- `accepted` / `in_scope` / `rejected` / `outside_clean` / `outside_blocked` are statements over the stored
  core's own fields;
- the public `elaborate` **core factory is removed** from `CAPABILITY` — it survives only inside the sealed
  `Capability` module, so `compile` is the one route to a `Core`, and no client can mint a peer;
- an internal retention control, `compile_core_retained`, proves every verdict carries exactly the
  `elaborate p` its branch decided on; the sealed-capability probes test the live sealed constructors
  (`MkProg` / `MkFail` / `MkOut` / `MkCore` / `CoreRep` / `elaborate`, both qualified forms).

Verdict and emitted bytes are unchanged. This is the narrow historical object-retention repair over the
current two-list core — sufficient for the retreat, and expressly **not** the full Root-3 retained phase. No
Root-3 source, index, binding, report, renderer, emission route, or semantics is touched.

Negative causal closure — by construction, not by silence — for the accepted checkpoints the repair does not
touch: **C5 `Machine.T`** names no compiler object and no module imports it; **Root 1 `Names`** is pure name
identity the compiler consumes and never the reverse; **Root 2 `Float`/`Complex`** are lower numeric carriers
the compiler imports, independent of how the capability retains its core.

## Frozen behind the retreat

- **C6 Root 3** — the source / occurrence / binding / honest-outcome foundation — and every later C6 root,
  Final C6, and C7 stay frozen until Rob closes the retreat.
- Rob has chosen **C3-A** for the Root-3 contract (retain the broad source algebra, expand exact
  requirements — synthesis Choice C3-A). The full C3-A enumeration — exact represented forms, exact
  requirement families, the predecessor relation, the later-satisfaction rule, and the reopen trigger — lands
  in `DECISIONS.md` (`C6-ROOT3-RECUT`) when Root-3 work begins, which is after the retreat closes.
- The Root-3 root causes (the retained occurrence authority, intrinsic binding/package identity, the one
  per-site causal phase, the physical `Compilable.*` recut, the single argument renderer, direct
  `Emit.of_safe` witnesses, the certified decoded-path bridge, and paired Fido/Go differentials) all stay
  frozen. The `of_safe_at` direct-image migration is RC-01-downstream and frozen too.

## Missing evidence and operator actions

- **Candidate-bound supported run.** An official run producing checked proof artifacts, an OCI digest, and a
  pristine export (RC-11's remaining `EVIDENCE_BLOCKER` half) is required for acceptance, not for this stop.
- **GHCR package visibility.** Make the `fido-toolchain` GHCR package **public** so a cold or foreign
  `make check` pulls the pinned toolchain credential-free; until then a one-time `docker login ghcr.io` is
  operator setup. Rob's one-click toggle.
- **Governance current-truth subset.** The synthesis's remaining before-closure amendments to
  `ARCHITECTURE.md`, `DECISIONS.md`, `README.md`, and `.review/closure.csv` (state the actual current owner
  graph; record only that the verdicts retain the current `Core`, not that it is the full Root-3 phase; one
  current Go-executor tuple) are concurrent work before the retreat closes.

## The stop

This candidate is `IMPLEMENTED_NOT_ACCEPTED`. It stops at the **retreat review**: a fresh whole-system review
under the two-model rule, then Rob alone closes the retreat. No Root-3 (C-3) work begins until he does, and no
later C6 root or C7 is authorized. A choice of C3-A made before closure does not lift the freeze.
