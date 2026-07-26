# Source Forest Campaign — Status Ledger

Campaign: **Specification-Shaped Source Forest, Snapshot-Local Occurrence Identity, and Occurrence-Anchored
Compilation.** The full design is `.review/SOURCE_FOREST_MASTER_PLAN.md`. **Git history is the detailed archive:
superseded per-repair theorem tables and prior candidate detail live in the git log and the superseded repair
directives, NOT in this file.** This ledger is the COMPACT CURRENT state only.

## Completed checkpoints

- **C0–C3 GREEN and accepted by Rob** (C3 accepted at the original C4 baseline `8c9212a`): preflight + proof
  spike; spec-shaped file roots + path-keyed `GoFileSet`; production `Index` + `NodeRef` navigation;
  occurrence-anchored diagnostics + one `AnalysisResult`.

## C4 authority

- Active checkpoint: **C4** — source type names, compiler resolution, and unified numeric conversions (including
  the `byte`→`uint8` / `rune`→`int32` SOURCE ALIASES, which are C4 work and are present in the current candidate).
- Functional contract: `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md` (identity is its path at the authorizing Git ref; documentation is not checksummed).
- Accepted review basis: `.review/REVIEW_BASIS.md`.
- Original C4 baseline: `8c9212a8c814c7a99a5e3ef1970a0ae32425a918`.
- **Blocked C4 implementation candidates (all sixteen):** `89b8e54` (1) · `1c4a7de` (2) · `806ce87` (3) ·
  `af2fc87` (4) · `9d4aff5` (5) · `3b4f40e` (6) · `3a92d22` (7) · `91e8dbb` (8) · `a2a5b46` (9) · `a8a4472` (10) ·
  `3ecf32e` (11) · `48c0b31` (12) · `af7d5d3` (13) · `9d5246e` (14) · `3386c02` (15) ·
  `20c5ad5c499d5046563471624117b80c737c7157` (16).
- **Seventeenth blocked candidate:** `12b1bc998a8a2a6b5ecd2360d734f7e2d56eac7c` —
  repair 15 made substantial, real progress and did NOT close C4.
  `25bcd7aa6b53f1e506a32c5077990a884bea8574` is its documentation-only freeze, not a separate candidate.
- **Repair authority (ACTIVE): `.review/C4_IMPLEMENTATION_REPAIR_16.md`**, under accepted FCB amendments
  A001 / Governance D-22 and A005 / Governance D-25. Repair 16 is the sole active C4 work and subsumes every
  still-live repair-14 and repair-15 obligation; the repair-15 authority document is archived in Git history.
- **C4 disposition: NOT accepted.** The candidate above awaits Rob's human C4 Implementation Review; only Rob
  accepts C4. The three reasons `20c5ad5` was BLOCKED are all closed by repair 15: A005 is complete and its
  naming gate now fails closed in both working-tree and staged-snapshot mode; `Compilable.Core` retains
  package refs, layout, plan and both diagnostic lists with their exactness evidence; and the public `Failure`
  retains the exact rejected core. Repair 14 is **not separately accepted** and is subsumed by repair 15.
  `c5b67495` is a **documentation-only freeze**, not a candidate; `37c9597` remains a superseded
  documentation-only acceptance closeout. Repair 15 is implemented on top of the current head — no reset,
  rebase, history rewrite, force-push, or revert of the A005 migration. Ranges: full human C4 review
  `8c9212a..12b1bc9`; **repair-12 `37c9597..af7d5d3`**; **repair-13 `af7d5d3..9d5246e`**;
  **repair-14 `9d5246e..3386c02`**; **A005 `c5b674..20c5ad5`**; **repair-15 `20c5ad5..deda8bd`**.
  Automatic Codex review is DISABLED.
- The post-C4 foundation consolidation / ruthless trim and C5 (= `uintptr` + rune constants/literals, reopens
  ADR-0001) remain FORBIDDEN until C4 is accepted.

## Repair 16 — retained package provenance, an abstract Core, a gate that sees constructors — ACTIVE

**`12b1bc998a8a2a6b5ecd2360d734f7e2d56eac7c` is BLOCKING — the eighteenth blocked candidate.**
Authority: `.review/C4_IMPLEMENTATION_REPAIR_16.md`, under accepted FCB amendments **A001** / Governance
**D-22** and **A005** / Governance **D-25**. Five findings: package facts and diagnostics must start from the
exact retained visit rather than a rerun; `Compilable.Core` and its constructor must be abstract to clients;
the A005 naming gate must actually parse constructors (it reported a false green over live residue); the
direct capability fixtures must query only the returned objects; and the live corpus must state one current
truth. It subsumes repairs 14 and 15, whose authority documents are archived in Git history.

**The retained-elaboration boundary (A001 / D-22).** Repair 14 replaced the reconstruction root with a
retained `Compilable.Core`; repair 15 completes it. The core now retains the WHOLE elaboration — input,
phase, package refs tied to its own retained visit, layout, plan, and both diagnostic lists — each built
once and stored with its exactness evidence rather than recomputed by a query. The accept/reject decision
is indexed by that exact core, and BOTH outcomes retain it: the capability on success, and
`Compilable.Failure` on rejection, whose diagnostics are a projection of the core it holds rather than a
copied list. The stripped result peer and the reconstruction bridges are deleted.

**Required:** one `Compilable.Core` built once; the accept/reject decision indexed by that exact core; success
and failure both retaining it; `Compilable.Program` retaining the accepted core behind an opaque constructor with
every public query a projection; `Compilable.compile` passing the exact object through; and deletion of the
reconstruction root, including the now-retired `cp_prov` as provenance and the now-retired
`elaborate_ok_seals_*` rebuilt-phase forms. A
canonical-rerun equality may survive only as a clearly labelled specification/determinism theorem.

**Rob authorized implementation on 2026-07-25:** begin on the current `main` head, do not reset to `9d5246e`,
preserve the recorded out-of-band changes; C5 and the post-C4 trim remain forbidden. The reviewer added one
scope decision (standing): **`Index.Program` is NOT deleted during a repair** — if the retained core makes it redundant,
record the redundancy and the affected queries and theorems, keep the wrapper, and propose deletion under a
separate contract (preferably the post-C4 trim).

**Repair 12 and 13 results are retained unchanged** (see below). No implementation has been performed yet:
only the authority file, the answered dispositions, and the current-state documents are written.

## Repair 13 — exact standard work-member index — landed at `9d5246e` (baseline `af7d5d3`)

**The defect (real production code, now removed).** `Compilable.WorkForest.forest_items` is a legitimate ordered
per-file-order list, but it was ALSO used as a production `Index.Key` identity lookup table: `forest_member_at`
searched it with `List.find` on `Index.key_equalb`, using the carried `Compilable.forest_keys_nodup` field as its uniqueness
mechanism, in the live semantic path `build_outcome_trace → build_conversion_step → build_conversion_work →
forest_member_at` — once per conversion. That is the `list + NoDup` keyed-table shape the binding collection law
forbids; it survived proof erasure and made a nested chain's operand recovery avoidably quadratic. The previous
collection audit's "no `List.find` for identity/membership storage", "`NoDup` is never a carried uniqueness field
standing in for a map", and "every identity-keyed collection has a mature standard backing" rows were FALSE.

**The repair as landed.** `forest_member_at` and its `List.find` are DELETED. Identity now lives in a separate
carried field `Compilable.forest_index : Compilable.WorkIndex Compilable.forest_items`, backed ENTIRELY by the pinned-stdlib `Index.KeyMap`
(`FMapAVL`) — Fido authors no tree, bucket, or find/add. It is built ONCE by `build_work_index` from the
ALREADY-BUILT item list (`work_index_map` takes the list, so no second work discovery and no `Compilable.input_visit`
re-traversal); OVERWRITE-FREE (`work_index_fresh` / `work_index_add_fresh` prove every `add` writes an absent key);
TOTAL with no option/fallback/empty-default precisely because the key-`NoDup` is a PROOF ARGUMENT (a
duplicate-keyed list cannot be handed to the builder, and `Compilable.WorkIndex` is uninhabitable for one anyway); and
EXACT in both directions (`work_index_exact` / `Compilable.index_exact` — sound and complete, so every item has exactly one
entry and every entry is exactly one item). The record is INDEXED BY the item list and the forest field is
dependent, so a foreign map is not pairable with a forest. `Compilable.index_domain` and `Compilable.index_key_inj` are DERIVED, never
stored — no second domain or uniqueness authority, and `Compilable.forest_key_inj` is now that map-derived theorem instead of a
hand-rolled NoDup induction. `index_member_at` / `forest_index_member_at` are the TOTAL member queries (ONE
`KeyMap.find`, the impossible `None` discharged by a Prop existence hypothesis, no stand-in member);
`index_member_at_retained`, `index_no_foreign` and `index_nonexpr_absent` pin exactness, foreign-key absence and
wrong-kind absence. `build_conversion_work` queries at the key of the operand `ExprRef` the item ALREADY CARRIES
(`Compilable.work_conv`) rather than the separately computed `operand_key`, preserving `Compilable.conversion_operand_ref_eq` / `Compilable.conversion_operand_expr` /
`Compilable.conversion_operand_role` / `Compilable.conversion_operand_key`; `build_conversion_step` places that SAME member in the processed suffix and
the outcome trace is untouched. The ordered list keeps its SOURCE-ORDER role only. Repair 12's exact source-step
identity results are RETAINED unchanged.

**New direct fixtures.** `deep_nested_index_at` / `deep_nested_chain_index_evidence`: on the real four-deep chain,
each of the four conversions recovers its EXACT operand member through the index at the CARRIED operand ref's key,
that member is the one the `ConversionStep` placed in the processed suffix, and the operand/current outcomes are
the accepted `Compilable.ExpressionSuccess` values. `twin_expr_index_distinct`: two occurrences carrying the LITERALLY SAME expression
value (`uint8(7)` twice) are distinct work items with distinct `Index.Key`s and distinct index entries, each key
answering with its own retained member — expression-value equality cannot conflate them.

**Collection audit rewritten** (`.review/COLLECTION_AUDIT.md`) with the two inventories the summary form hid: an
EXPLICIT `find`/list-scan site inventory (every site named — `Names.classify` survives and is classified in full
as a spelling classification over the fixed closed sixteen-name descriptor enumeration with a proved inverse, not
keyed storage; `forest_member_at` is recorded as deleted) and an EXPLICIT `NoDup` inventory naming the only two
carried `NoDup` record fields in the theory (`Compilable.forest_keys_nodup`, now a fact about the ordered enumeration that
licenses the index build and never the lookup mechanism; `Compilable.annotated_context_nodup`, a fact about each item's context ref
list). No `list + NoDup` identity table remains anywhere.

## Current implementation architecture (RETAINED)

One immutable `Syntax.Program` source authority → one retained `Compilable.Input` → one proof-carrying
`Compilable.WorkForest` (exact `WorkMember`/`SuffixMember` handles; `Compilable.Conversion`/`ConversionStep`). The expression
outcome authority is the intrinsic causal object `Compilable.Outcomes = Compilable.outcomes_acc + Compilable.outcomes_trace`: an `Compilable.Trace`
INDEXED by the `Compilable.Accumulator` it builds (`Compilable.TraceStep` retains the exact tail trace/accumulator/current
member/freshness/`StepCause`), so accumulator and causal predecessor chain are NOT freely pairable.
`total_forest_outcome_cause` PROJECTS the trace to each member's `RetainedMemberCause` carrying the authenticated
tail accumulator + `StepCause` producing the FINAL outcome + tail-to-final QUERY PRESERVATION;
`final_operand_outcome` connects the exact tail operand result to the final-table operand result. The conversion
semantic branch consumes one `ConversionStep` + one exact operand `SuffixMember`, one total tail query, one
`Typing.convert_constant`. One dependent `Compilable.Phase` object chain; facts and diagnostics projected from the same
retained outcome table; exact table sealing on successful elaboration; source-name/alias/renderer/diagnostic/
differential results and the canonical generated Go bytes unchanged; no C5.

## Current acceptance evidence (theorem / gate surfaces)

Universal (over any retained table/member): `retained_convsuccess_closure` / `retained_childfail_closure`
(+no-local-reason) / `retained_convfail_diag` (returns the exact retained annotated member/context pair) /
`outcome_trace_unique_step` (+`trace_currents_eq`). Concrete (over the deep programs): the exact valid-chain success
bundle `deep_nested_convsuccess_at` (proving `nested_success_bundle`) instantiated on all four conversions
(`deep_nested_chain_success_evidence`) — **the returned `ConversionStep` carries the source `ts`/`x` identity (no
existential `ts0`/`x0`, repair 12), so the "exact ConversionStep" claim is justified by the public type**;
the exact `Compilable.ConversionFailure`→`Compilable.InvalidConversion` diagnostic theorem
`deep_fail_innermost_diag` (stating `t = Compilable.fact_type (type_name_fact_at_table (Compilable.phase_type_name_facts phase) (Compilable.conversion_target_node_ref
(Compilable.step_conversion step)))`, the annotated member, and the stored singleton); the outer child-failure closure
`deep_fail_childfail_closure_at`, `deep_fail_exactly_one_diag`, the exact work count, wrong-kind/foreign exclusion,
fact-table sealing, and the two-`uint8` retained-fact fixture — all NAMED in the readable assumption gate; the weaker
projections (`deep_nested_ok_closure_at`, `deep_fail_outer_operands_final_fail`, `deep_nested_chain_operands_final_ok`,
`deep_nested_all_ok`) are labeled corollaries. Repair 13 adds the work-index surfaces to the same gate: construction
(`work_index_map`, `work_index_fresh`, `work_index_add_fresh`, `work_index_exact`, `build_work_index`, `Compilable.forest_index`),
exactness/uniqueness (`Compilable.index_exact`, `Compilable.index_domain`, `Compilable.index_key_inj`, `Compilable.forest_key_inj`), the total queries
(`index_member_at`, `index_member_at_retained`, `forest_index_member_at`, `forest_index_member_at_retained`),
exclusion (`index_no_foreign`, `forest_index_no_foreign`, `index_nonexpr_absent`), the conversion path
(`build_conversion_work`), and the two direct fixtures (`deep_nested_index_at` /
`deep_nested_chain_index_evidence`, `twin_expr_index_distinct`).

## Current verification state

Every commit passes the full staged pre-commit verification: `make prove` — readable Print-Assumptions gate
axiom-free (**523/523** surfaces closed) + whole-theory `Fido Audit Assumptions` + adversarial self-tests A–E +
sealed-capability client self-tests F–X with a positive control; `make e2e` (materialize + pinned-Go
`go build ./...` + goldens + sink + full alias matrix); `make check` working-tree generated bytes byte-match the
pristine build; `make regenerate` no drift; `make regen-guard` DAG edge load-bearing; `make fmt` conforming.
Generated `go.mod` and `main.go` have been byte-identical across the whole repair arc.

⚠ **Green commands have not caught a single one of the blockers.** A `List.find` keyed by `Index.Key`
typechecks, proves, builds and emits identical bytes — repair 13. A capability that keeps copied projections
plus a Prop equality to rerunning the elaborator does likewise — repair 14. A package map folded from a rerun
of `program_visit`, a publicly constructible `Core`, and direct fixtures that recover their result through an
equality to a rebuilt peer all do likewise — repair 17's findings 1, 2 and 4, every one of them green.

⚠ **Sealing is not one boundary but several, and the reasons differ.** `Compilable.Core`, `Program`,
`Failure`, `Facts` and `Safe.Program` are abstract outright. `Emit.Image` cannot be: the certified transport
kernel-reduces it, and a module seal removes the projection bodies that reduction needs. A006 seals the
AUTHORITY there instead — an opaque value-indexed `Emit.Mint.Token` — and keeps the carrier reducible. The
rule that decides which applies is whether a certified transport must reduce the representation.

⚠ **And the sharpest instance is a gate that could not see.** The A005 naming gate parsed constructors only
when the first character was already uppercase, so 51 live lower-case constructors were never examined and it
reported success — twice, in two modes, over a defect it existed to find. Fixing that exposed a second blind
spot: the first constructor after `:=` was never extracted either, which meant two must-ACCEPT controls had
been passing vacuously. A control that passes because the parser is blind is indistinguishable from one that
passes because the rule is right.

Verification does not inspect topology, and a checker cannot report what it never parsed. Only reading the
actual retention shape does the first; only adversarial controls plus a coverage check do the second.

## Scope

ADR-0001-PINNED-64-BIT-TARGET and SR-001 are **ACCEPTED FOR CURRENT BASIS** (Rob, 2026-07-25): Go 1.23 on
`linux/amd64` with `GOAMD64=v1`; `int`/`uint` 64-bit and distinct from fixed-width types. Reopen at C16 or any
earlier explicit request to add another target or `uintptr`. This authorizes neither `uintptr` — which stays OUT
until a separate reviewed scope change pays its inclusion price — nor C5 nor the post-C4 trim.
ADR-0002-BOUNDED-DECIMALFLOAT-DOMAIN **REJECTED AS WRITTEN / OPEN**; SR-009 **UNRESOLVED EXISTING RESTRICTION**;
every other `.review/UNSUPPORTED_AND_RESTRICTED_SCOPE.md` entry stays PROPOSED with a neutral classification
unless Rob explicitly accepts it. No numeric-model change in repair 12, 13 or this disposition commit; the
Float.Decimal decision work is not begun.
