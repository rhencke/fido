# Fido FCB Fixed Points

> **Derived reference, not implementation authority.** The code and its gated theorems are the sole implementation authority.  
> **Living document.** Its identity is its Git blob at the exact ref resolved for the task; its
> history is the commit log. No version suffixes, no checksum manifest.  
> **Accepted amendments:** `FCB-A001-INTRINSIC-STATIC-CAPABILITY-PROVENANCE`; `FCB-A002-GIT-CANONICAL-FCB-STORAGE`; `FCB-A003-LIVING-DOCUMENTATION`;
> `FCB-A004-GIT-RESOLVABLE-LIVING-CORPUS`.  
> **Canonical live location:** `.review/fcb/current/` in the exact Git ref used for the task.  
> **Stable bootstrap:** `.review/fcb/current/INDEX.md`  
> Project libraries contain only a bootstrap shim. They do not contain or own the FCB corpus.  
> Regenerate, verify, and commit affected FCB files in Git after each accepted checkpoint or amendment.  
> This corpus does not accept C4 and does not authorize C5; `.review/NEXT_STEPS.md` remains the live checkpoint authority.


A fixed point may change only through Rob’s explicit reopening with new information. Future FCB regeneration must preserve every component projection below. The public base is frozen; internal representations remain disposable under `SC-21`.

## 1. Architectural fixed points

### ARCH-01 — Deletion and generalization standard

The five retention tests and the prohibition list in Charter §1.

### ARCH-02 — Minimal Machine base

No Go feature defines a second run relation.

### ARCH-03 — One owner per meaning and retained static-capability provenance

The authority chain in Charter §3 has one owner per meaning. The opaque static capability and opaque failure result retain the exact whole compiler object by construction. Their public fact, diagnostic, layout, and plan interfaces are projections. Equality to a rerun is never provenance.

### ARCH-04 — Expression fact/use split

The use builder never inspects the raw child again.

### ARCH-05 — Single type algebra

Closed runtime types use the same algebra; aliases do not create identity; recursive named types refer to declarations.

### ARCH-06 — Static slot versus dynamic place

Source binding identity and runtime storage identity never collapse.

### ARCH-07 — Stack-only panic/defer/recover

The two named invariants justify direct recovery without tokens.

### ARCH-08 — Resource-local origins

Live state retains exact origins and proofs connect them to run actions.

### ARCH-09 — Finite bad-prefix safety

Safety and liveness stay separate.

### ARCH-10 — No vacuous library safety

An empty set of starts does not prove open-world library safety.

### ARCH-11 — Do-Not-Do-Early list

No state, feature, or compatibility scaffold lands before its complete vertical feature.

### ARCH-12 — Candidate-only acceptance

Rob alone records acceptance against frozen, green artifacts.

## 2. Evidence and model fixed points

### EVID-01

Pinned spec and memory-model bytes.

### EVID-02

Reproducible extraction and audit outputs.

### EVID-03

Route A evaluation-order nondeterminism and deterministic specified-order fixtures.

### EVID-04

FMA both-branches model; target observation is adequacy evidence only.

### EVID-05

Select, map iteration, and scheduling nondeterminism; print/println adequacy demotion.

### EVID-06

Module/language/toolchain boundary and no-switch invocation.

### EVID-07

Terminal observation tuple.

### EVID-08

APPLIED-only provenance, empty countersigns, judgment split.

### EVID-09

Synthesized anchors and grammar counting rule.

### EVID-10

NaN map and struct-tag semantics with fixtures.

### EVID-11

SC-21 proof-cost contract remains fixed.

### EVID-12

`uintptr` remains OUT unless a reviewed scope change lands.

## 3. Component registry

| Fixed point | Component | Baseline path | Terminal path | Selector | Protected projection |
|---|---|---|---|---|---|
**Path typing (D-24).** A path naming a file under `.review/fcb/current/` resolves in the same Git ref that
carries this registry; baseline and terminal are distinguished by **ref**, not by filename. A cell marked
`EXTERNAL · <name> · R1 bundle · PROVENANCE-PENDING` is an external evidence reference: the bytes belong to the
R1 spec-closure bundle, are not held by Git, and their availability is an open human act recorded in the Human
Review Index. No component silently points at a repository path that does not exist.

| ARCH-01 | charter | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `markdown-section: `## 1. Standard`` | `normalized-section-text` |
| ARCH-02 | charter | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `markdown-section: `## 2. Permanent Public Semantic Base`` | `normalized-section-text` |
| ARCH-03 | charter | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `markdown-section: `## 3. Complete Authority Chain`` | `normalized-section-text` |
| ARCH-03 | static-capability-provenance | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `markdown-section: `## 4. \`Compilable.Program\` Is the Static Capability`` | `normalized-section-text` |
| ARCH-04 | charter | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `markdown-section: `## 5. Facts Depend on Exact Source Roles`` | `normalized-section-text` |
| ARCH-05 | charter | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `markdown-section: `## 6. One Type Algebra`` | `normalized-section-text` |
| ARCH-06 | charter | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `markdown-section: `## 11. Static Bindings and Dynamic Cells Are Different`` | `normalized-section-text` |
| ARCH-07 | charter | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `markdown-section: `## 13. Panic, Defer, and Recover`` | `normalized-section-text` |
| ARCH-08 | charter | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `markdown-section: `## 15. One Structured Label per Transition`` | `normalized-section-text` |
| ARCH-09 | charter | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `markdown-section: `## 17. Safety Is a Finite Bad-Prefix Property`` | `normalized-section-text` |
| ARCH-10 | charter | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `markdown-section: `## 19. Starts`` | `normalized-section-text` |
| ARCH-11 | charter | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `markdown-section: `## 24. Current Repository Reconciliation`` | `normalized-section-text` |
| ARCH-12 | charter | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `markdown-section: `## 26. Acceptance and Freeze Rule`` | `normalized-section-text` |
| EVID-01 | spec-pin-bytes | `EXTERNAL · go_spec_go1.23.html · R1 bundle · PROVENANCE-PENDING` | `EXTERNAL · go_spec_go1.23.html · R1 bundle · PROVENANCE-PENDING` | `whole-file: —` | `raw-bytes` |
| EVID-01 | memmodel-pin-bytes | `EXTERNAL · go_mem_2022-06-06.html · R1 bundle · PROVENANCE-PENDING` | `EXTERNAL · go_mem_2022-06-06.html · R1 bundle · PROVENANCE-PENDING` | `whole-file: —` | `raw-bytes` |
| EVID-02 | extractor-script | `EXTERNAL · extract_latitude.py · R1 bundle · PROVENANCE-PENDING` | `EXTERNAL · extract_latitude.py · R1 bundle · PROVENANCE-PENDING` | `whole-file: —` | `raw-bytes` |
| EVID-02 | frozen-candidate-manifest | `EXTERNAL · FIDO_GO1_23_LATITUDE_MANIFEST_2026-07-23.tsv · R1 bundle · PROVENANCE-PENDING` | `EXTERNAL · FIDO_GO1_23_LATITUDE_MANIFEST_2026-07-23.tsv · R1 bundle · PROVENANCE-PENDING` | `whole-file: —` | `raw-bytes` |
| EVID-02 | byte-reproduction-claim | `EXTERNAL · FIDO_GO1_23_SPEC_CLOSURE_FREEZE_R1_2026-07-23.md · R1 bundle · PROVENANCE-PENDING` | `EXTERNAL · FIDO_GO1_23_SPEC_CLOSURE_FREEZE_TERMINAL_2026-07-23.md · R1 bundle · PROVENANCE-PENDING` | `anchored-region: `The audit byte-reproduces` … `SHA-256 manifest.`` | `anchored-normalized-text` |
| EVID-03 | order-model | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `markdown-section: `### 12.4 Order-of-evaluation latitude`` | `normalized-section-text` |
| EVID-03 | order-contract | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `markdown-section: `### 25.21 \\`SC-20-EVAL-ORDER-LATITUDE\\``` | `normalized-section-text` |
| EVID-04 | fma-row-core | `FIDO_FCB_LATITUDE_LEDGER.tsv` | `FIDO_FCB_LATITUDE_LEDGER.tsv` | `table-row: `LAT-121`` | `named-fields {disposition, owner_row, contract, justification}` |
| EVID-04 | fma-observation | `EXTERNAL · FIDO_GO1_23_PINNED_TOOLCHAIN_EVIDENCE_R1_2026-07-23.md · R1 bundle · PROVENANCE-PENDING` | `EXTERNAL · FIDO_GO1_23_PINNED_TOOLCHAIN_EVIDENCE_R1_2026-07-23.md · R1 bundle · PROVENANCE-PENDING` | `markdown-section: `## 1. Ordinary multiply-add is not fused by default`` | `normalized-section-text` |
| EVID-05 | select-choice | `FIDO_FCB_LATITUDE_LEDGER.tsv` | `FIDO_FCB_LATITUDE_LEDGER.tsv` | `table-row: `LAT-X002`` | `named-fields {disposition, owner_row, contract}` |
| EVID-05 | map-iteration | `FIDO_FCB_CLOSURE_LEDGER.csv` | `FIDO_FCB_CLOSURE_LEDGER.csv` | `table-row: `SPEC-X006`` | `named-fields {disposition, owner, test}` |
| EVID-05 | scheduler-choice | `FIDO_FCB_LATITUDE_LEDGER.tsv` | `FIDO_FCB_LATITUDE_LEDGER.tsv` | `table-row: `LAT-X003`` | `named-fields {disposition, owner_row, contract}` |
| EVID-05 | print-println-demotion | `FIDO_FCB_CLOSURE_LEDGER.csv` | `FIDO_FCB_CLOSURE_LEDGER.csv` | `table-row: `SPEC-X005`` | `named-fields {disposition, owner, test}` |
| EVID-06 | bound-001 | `FIDO_FCB_CLOSURE_LEDGER.csv` | `FIDO_FCB_CLOSURE_LEDGER.csv` | `table-row: `BOUND-001`` | `named-fields {disposition, representation}` |
| EVID-06 | bound-002 | `FIDO_FCB_CLOSURE_LEDGER.csv` | `FIDO_FCB_CLOSURE_LEDGER.csv` | `table-row: `BOUND-002`` | `named-fields {disposition, representation}` |
| EVID-06 | bound-003 | `FIDO_FCB_CLOSURE_LEDGER.csv` | `FIDO_FCB_CLOSURE_LEDGER.csv` | `table-row: `BOUND-003`` | `named-fields {disposition, representation}` |
| EVID-06 | invocation-contract | `EXTERNAL · FIDO_GO1_23_PINNED_TOOLCHAIN_EVIDENCE_R1_2026-07-23.md · R1 bundle · PROVENANCE-PENDING` | `EXTERNAL · FIDO_GO1_23_PINNED_TOOLCHAIN_EVIDENCE_R1_2026-07-23.md · R1 bundle · PROVENANCE-PENDING` | `anchored-region: `The adequacy invocation uses` … `workspace selection.`` | `anchored-normalized-text` |
| EVID-07 | tuple-section | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `markdown-section: `### 22.3 Terminal observation tuple`` | `normalized-section-text` |
| EVID-08 | f-disposition-rule | `EXTERNAL · FIDO_ARCHITECTURE_F_DISPOSITIONS_2026-07-23.md · R1 bundle · PROVENANCE-PENDING` | `EXTERNAL · FIDO_ARCHITECTURE_F_DISPOSITIONS_2026-07-23.md · R1 bundle · PROVENANCE-PENDING` | `anchored-region: `**Disposition rule:**` … `plan §26.`` | `anchored-normalized-text` |
| EVID-08 | checkable-claims-key | `EXTERNAL · FIDO_GO1_23_SPEC_CLOSURE_AUDIT_R1_2026-07-23.json · R1 bundle · PROVENANCE-PENDING` | `EXTERNAL · FIDO_GO1_23_SPEC_CLOSURE_AUDIT_TERMINAL_2026-07-23.json · R1 bundle · PROVENANCE-PENDING` | `json-pointer: `/checkable_only`` | `key-presence` |
| EVID-08 | judgment-key | `EXTERNAL · FIDO_GO1_23_SPEC_CLOSURE_AUDIT_R1_2026-07-23.json · R1 bundle · PROVENANCE-PENDING` | `EXTERNAL · FIDO_GO1_23_SPEC_CLOSURE_AUDIT_TERMINAL_2026-07-23.json · R1 bundle · PROVENANCE-PENDING` | `json-pointer: `/judgment_not_certified`` | `key-presence` |
| EVID-09 | heading-manifest | `EXTERNAL · FIDO_GO1_23_SPEC_HEADING_MANIFEST_2026-07-23.tsv · R1 bundle · PROVENANCE-PENDING` | `EXTERNAL · FIDO_GO1_23_SPEC_HEADING_MANIFEST_2026-07-23.tsv · R1 bundle · PROVENANCE-PENDING` | `whole-file: —` | `raw-bytes` |
| EVID-09 | grammar-manifest | `EXTERNAL · FIDO_GO1_23_SPEC_GRAMMAR_MANIFEST_2026-07-23.tsv · R1 bundle · PROVENANCE-PENDING` | `EXTERNAL · FIDO_GO1_23_SPEC_GRAMMAR_MANIFEST_2026-07-23.tsv · R1 bundle · PROVENANCE-PENDING` | `whole-file: —` | `raw-bytes` |
| EVID-10 | nan-map-row | `FIDO_FCB_CLOSURE_LEDGER.csv` | `FIDO_FCB_CLOSURE_LEDGER.csv` | `table-row: `SPEC-124`` | `named-fields {disposition, representation}` |
| EVID-10 | struct-tag-row | `FIDO_FCB_CLOSURE_LEDGER.csv` | `FIDO_FCB_CLOSURE_LEDGER.csv` | `table-row: `SPEC-026`` | `named-fields {disposition, representation}` |
| EVID-10 | struct-tag-fixtures | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `anchored-region: `Required struct-tag fixtures:` … `pinned rule permits it.`` | `anchored-normalized-text` |
| EVID-10 | nan-map-fixture | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `anchored-region: `- a NaN-keyed map entry is insertable` … `removed by \\`clear\\`;`` | `anchored-normalized-text` |
| EVID-11 | sc21-contract | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `FIDO_FCB_ARCHITECTURE_CHARTER.md` | `markdown-section: `### 25.22 \\`SC-21-PROOF-COST-INTERNALS\\``` | `normalized-section-text` |
| EVID-12 | uintptr-pre-row | `FIDO_FCB_CLOSURE_LEDGER.csv` | `FIDO_FCB_CLOSURE_LEDGER.csv` | `table-row: `PRE-22`` | `named-fields {disposition, price}` |

**Components:** 42. **Parent fixed points:** 24.
