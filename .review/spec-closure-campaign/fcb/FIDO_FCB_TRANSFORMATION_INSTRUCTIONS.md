# FIDO — FCB TRANSFORMATION INSTRUCTIONS, v2
## (Addressed to ChatGPT, the checkpoint author. Supersedes FIDO_FCB_TRANSFORMATION_GUIDE_AND_ROADMAP_2026-07-23.)

**Date:** 2026-07-24 · **Issued by:** Rob (human authority) · **Drafted by:** Claude (external adversarial reviewer)
**Purpose:** transform the countersigned terminal bundle into the **Fido Conformance Basis (FCB)** — the standing document suite consulted for every future checkpoint — and retire the volley scaffolding to the archive. You (ChatGPT) do the dividing; these instructions specify where the cuts land. Quality bar for every document: *"of course this doc contains that."*

---

## 0. PRECONDITIONS (do not begin the transformation before all four)

1. Terminal directive **v12** () has been **executed**: all eighteen steps, `TERMINAL-REPAIR-CANDIDATE` status (Confirmed provenance) or Rob's explicit acceptance of `OPEN-REVIEW-CANDIDATE`.
2. Rob has worked the **Human-Review Index**: countersigns entered on the T/F/R rows he accepts.
3. Rob has made the **LAT-X004 policy choice** (menu i/ii/iii), and the consequent **regeneration, re-audit, and re-freeze** has run — the FCB is generated from the *post-choice* bundle, never the open candidate.
4. Rob has dispositioned or explicitly deferred **ADR-0001..0004** (a deferred ADR is carried into the FCB as OPEN with its Human-Review Index entry preserved).

## 1. SOURCES OF TRUTH (and nothing else)

The countersigned post-regeneration terminal bundle; the repository at its current accepted state; Rob's recorded dispositions. Chat history, superseded directives every earlier revision, and review prose are **provenance, not sources** — if something matters and lives only in prose, it must already be in the bundle; if it is not, flag it to Rob rather than importing it silently.

## 2. THE FCB FILE SET (the division)

Every document carries the standard banner: *derived reference, not authority — the code and its gated theorems are the sole authority; as-of repo SHA + bundle hash; regenerated at each checkpoint acceptance; stale copies must be deleted from every model library.* Naming: `FIDO_FCB_<TOPIC>_v<N>.md` (tables stay `.tsv`/`.csv` with generated `.md` views).

1. **FIDO_FCB_INDEX** — one page: every FCB file, its one-line purpose, its version, and the consultation map (§3). This is Rob's requested **manifest**.
2. **FIDO_FCB_GOVERNANCE** — authority rules (APPLIED-vs-countersign; one-authority-per-meaning; candidate-only acceptance; Rob as sole disposition owner); the **Settled Decisions register**: the volley ratchet's D-01..D-21 *contents* rewritten as standing law with their rationales, stripped of volley procedure; the ADR log (0001..0004 with statuses); amendment rules (a settled decision reopens only through Rob, with new information).
3. **FIDO_FCB_ARCHITECTURE_CHARTER** — the architecture plan, carried over intact with its §25 contract catalog (SC-00..SC-22) and the twelve architectural fixed points marked as such.
4. **FIDO_FCB_CLOSURE_LEDGER** (csv + generated md) — the 491-row spec-closure ledger, canonical, with the SC citation per row.
5. **FIDO_FCB_LATITUDE_LEDGER** (tsv + generated md) — the latitude ledger with the trichotomy dispositions, governance columns, and LAT-X004 closed per Rob's choice.
6. **FIDO_FCB_ACCEPTANCE_GATES** — every ACCEPTANCE-ALIGNMENT row's frozen future-Fido fixture spec, its `PENDING-IMPLEMENTATION` status, its owning contract, and **its implementing checkpoint** — the standing worklist that checkpoints discharge.
7. **FIDO_FCB_TOOLCHAIN_EVIDENCE** — pinned toolchain provenance, the probe environment profile, captured observations, the platform-pending note, and the margin notes.
8. **FIDO_FCB_FIXED_POINTS** — the 24 fixed points with their component registry (the projections), carried forward as the preservation contract for all future regenerations.
9. **FIDO_FCB_HUMAN_REVIEW_INDEX** — regenerated per checkpoint; every open human act, discovered never hardcoded.
10. **FIDO_FCB_ROADMAP** — C5–C17 as previously defined (C5 Machine base; C6 names/slots/places + first acceptance-gate discharges; C7 runtime expressions/eval order/fatal panic; C8 control flow/goto; C9 functions/closures/defer/panic/recover; C10 composite data; C11 packages/init/range; C12 methods/interfaces; C13 generics; C14 goroutines/channels/select; C15 HB/races/deadlock; C16 platform matrix per ADR-0004; C17 trim). Each entry lists which closure/latitude/acceptance rows it consumes.
11. **FIDO_FCB_CHECKPOINT_AUTHORING_GUIDE** — §4 below, as its own document.
12. **FIDO_FCB_MODEL_OPERATIONS** — the delegation table (ChatGPT chat-1 authors checkpoints; disposable research chats; Claude Code implements; Claude chat adversarially reviews; Rob decides); library-update duty (§6); the retirement register (§5).

## 3. THE CONSULTATION MAP (embed in the INDEX; this is the "reach for it again and again" rule)

| Deciding… | Consult | Use specifically |
|---|---|---|
| What to build next | ROADMAP | the next checkpoint's row list; never skip a foundational layer |
| Whether a construct is in scope | CLOSURE_LEDGER | the row's disposition + price; OUT means priced, not forgotten |
| What behavior the model must admit | LATITUDE_LEDGER + CHARTER §25 | disposition kind; STEP-NONDET rows are fixed points |
| What Fido must reject | ACCEPTANCE_GATES | the fixture spec + expected diagnostic; discharge = implement + run both halves |
| How to interpret spec vs gc conflicts | GOVERNANCE (ADR-0003) | the three tiers + interpretation clause |
| Constant-value semantics | LATITUDE_LEDGER LAT-X004 + CHARTER SC-05 | Rob's chosen policy; owner never moves |
| Any "can we change X?" | FIXED_POINTS, then GOVERNANCE Settled Decisions | if X is protected, the answer is Rob-or-no |
| What's still open for Rob | HUMAN_REVIEW_INDEX | never answer from memory |
| Toolchain/environment questions | TOOLCHAIN_EVIDENCE | the probe profile is the only sanctioned environment |

## 4. CHECKPOINT AUTHORING GUIDE (content requirements — Rob's second deliverable)

A checkpoint definition handed to Claude Code must contain, in order: **(a) Scope** — the ROADMAP entry verbatim plus the exact closure/latitude/acceptance rows consumed, each by ID; nothing outside the listed rows. **(b) Foundational-increment justification** — one paragraph proving every dependency of the scope is already accepted (the "no floor above a missing floor" rule). **(c) Frozen contracts** — the public-base additions (types, `step` cases, theorems) stated *before* implementation, hashed, with the SC contract each satisfies; internals explicitly disposable per SC-21. **(d) Fixture obligations** — new fixtures plus every ACCEPTANCE_GATES row discharged here, run as pairs: pinned-gc observation under the probe profile, and Fido's diagnostic, byte-captured. **(e) Acceptance gates** — the named checks that must pass, the replay duties, and the rule that the deployed path is the tested path. **(f) Provenance duties** — models record APPLIED at most; the checkpoint's countersign column ships empty; the Human-Review Index regenerates. **(g) Library duty** — on Rob's acceptance, regenerate affected FCB docs, bump versions, update both model libraries, delete stale copies (§6). Selection rule for "what next": the lowest-numbered ROADMAP entry whose dependencies are all countersigned — no cherry-picking glamour features over foundations, ever.

## 5. RETIREMENT REGISTER (the paintbrushes — archived in the frozen bundle, removed from live libraries)

Volley Protocol v1–v3 and the decision-ratchet *procedure* (contents absorbed into GOVERNANCE); directives every earlier revision (v12 remains as the executed authority, archived); `lint_directive.py`, `validate_return.py`, send/return packaging tools; the review lineage and adjudication briefs. **Explicitly NOT retired:** `run_fixture.py` + `PROBE_ENVIRONMENT.tsv` (the live differential-testing spine — migrates toward the repo as the BOUND-003 strengthening at its implementing checkpoint); the audit/verifier pattern (template for checkpoint gates); the extraction tools stay archived in-bundle for reproducibility on demand — the spec is pinned and does not change, so no live re-derivation cadence exists.

## 6. DELIVERY

Produce the FCB set; Rob uploads it to **both** model libraries — the ChatGPT project (primary, checkpoint authoring) and the Claude project (adversarial review) — and deletes every superseded document from both. A library containing a stale FCB version is a defect. Rob may consciously strike the second library; silence means both.

## 7. COMPLETION

Done when: every §2 document exists with its banner; the INDEX consultation map is total over the file set; the GOVERNANCE Settled Decisions register carries all 21 D-contents with rationale; ACCEPTANCE_GATES enumerates every PENDING-IMPLEMENTATION row with an implementing checkpoint; the retirement register is enacted; both libraries updated; and Claude (adversarial reviewer) has performed one showroom pass over the set, findings dispositioned by Rob. Then: **C4 review → Step 0 → C5.** The dog writes theorems again.
