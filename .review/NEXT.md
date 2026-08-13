# C6 — active task

Review: none

The active work is the **C4 exact-elaboration retreat repair**, now on its second review cycle. The first
repaired candidate (`808b01a`) was reviewed and returned `REVIEW_BLOCKED`: the private core retention was
correct, but the review found the fix incomplete at the public contract and surfaced four duplicate-authority
roots plus governance. That review's repair set is being worked here. Everything past the retreat — all of C6
Root 3 and every later root — stays **frozen** until Rob closes the retreat. Rob alone closes and accepts.

This file is the current-action sheet: what is true now, and nothing else. Repair/review narrative and
superseded briefs are Git history. The Root-3 contract lives in `DECISIONS.md`; the ownership law and retreat
rule in `ARCHITECTURE.md`; the milestone sequence in `ROADMAP.md`.

## Landed, each green through the full gate and pushed

- **O01 — the decided core is public** (`a0316f9`): `compile` returns one dependent `Decision` = decided core +
  a `Verdict` whose three branches carry payloads indexed by that same core; the standalone Failure/Outside
  mints are gone; `Program` is the Compiled projection reached only through `program_of`. `elaborate` and every
  payload/decision/program constructor are sealed; a branch-complete public client control reads each branch's
  fact over the one decided core. This is the honest completion of the first review's public-contract finding.
- **O04 — one argument renderer** (`7a1c92c`): a guard-accepted higher-order `render_arglist` parameterized by
  the element renderer is the single traversal; the inline duplicate is deleted; definitional reduction and
  bytes preserved.
- **O03 — one package-rule result** (`2a006e3`): `Compilable.Packages` computes one canonical
  `PackageRuleStatus`; `Facts` attaches the RootCause instead of re-deciding from counts; the dead theorem
  cluster and the peer list-scan count authority are deleted (`Packages.v` −255 lines), `package_no_empty`
  re-proved directly over the fold.
- **O05 — the FilePath grammar lives in Rocq alone** (`67c67b0`): `plugin/sink.ml`'s hand-written mirror of
  `FilePath.path_ok` is deleted; the materializer emits a certified path manifest beside the tree; `apply`
  compares discovered-vs-certified before effects and passes it; `Sink.sync` does filesystem-safety
  (`path_safe`) plus manifest membership, never re-deciding the grammar. Every filesystem defense preserved;
  bytes unchanged.

## Blocked — O02 (the occurrence authority), needs Rob

The review's SYN-O02 (one retained occurrence/view/meta authority; `occurrences_file` a direct table
enumeration; delete the `source_occurrence_at` source re-walk) is the **known `vm_compute` performance wall**:
reading the retained occurrence table en masse OOM-kills the demo witness 35–70× (five documented cycles,
mechanism-independent). The one untried unblock, `native_compute`, is **disabled at configure time in the
pinned toolchain image** (it silently falls back to `vm_compute`, still OOM). The unblocks all need Rob:

1. reconfigure `toolchain.Dockerfile` to enable `native_compute` — puts the native compiler in the TCB;
2. restructure the phase as a single fused source fold that never materialises all occurrence-views at once —
   in tension with the review's "one retained object" letter; or
3. profile the heap/term-size of table-sourced vs lazily-built occurrences and restructure from that.

The other four code roots are done; O02 is the sole remaining code blocker.

## Remaining (not gating on O02, but the candidate cannot close without them)

- **Governance normalization** (synthesis SYN-G01–G15): the current owner graph and public `Decision` in
  `ARCHITECTURE.md`; `DECISIONS.md`/`ROADMAP.md` to live-normal form; one current Go-executor tuple in
  `TOOLCHAIN.md`; `README.md`; `.review/closure.csv`/`latitude.tsv`; source/build comments.
- **Pre-closure deletions** (SYN-D11–D13): the non-gating performance subsystem, the Docker future-oracle
  cases, and dead gate-tool helpers.

## The stop

`IMPLEMENTED_NOT_ACCEPTED`. The replacement candidate cannot be completed until **Rob decides O02** (which
unblock to authorize); then the remaining governance/deletions close, then a fresh whole-system review under
the two-model rule, then Rob closes the retreat. No Root-3 (C-3) work begins until closure. Rob has chosen
**C3-A** for the Root-3 contract; its full enumeration lands in `DECISIONS.md` when Root-3 work begins, after
closure. `make check` on the pinned toolchain is the supported run — there is no separate evidence blocker.
