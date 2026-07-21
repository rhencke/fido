# Source Forest Campaign — Status Ledger

Campaign: **Specification-Shaped Source Forest, Snapshot-Local Occurrence Identity, and Occurrence-Anchored
Compilation.** The full design is `.review/SOURCE_FOREST_MASTER_PLAN.md`; Git history is the detailed archive.

## Authority

- Active checkpoint: **C4** — source type names, compiler resolution, and unified numeric conversions.
- Functional contract: `.review/C4_SOURCE_TYPE_NAME_CONVERSION_PLAN.md`.
- Contract SHA-256: `9ec55b38444e3a32eaf6cb024f72285527992ba1612dabfdc99ce6f89c8517b4`.
- Accepted review basis: `.review/REVIEW_BASIS.md`.
- Original C4 baseline: `8c9212a8c814c7a99a5e3ef1970a0ae32425a918`.
- First blocked candidate: `89b8e54634e7012612a51990756ad29a579c1b0f` (C4 Implementation Review BLOCKING).
- Second blocked candidate / repair-2 baseline: `1c4a7de8e9e265b929a3ba9ce1c8fb1317ca98ca` (second BLOCKING).
- Human authorization: `C4-source-type-resolution-1`; repair 1 `C4-retained-facts-and-diagnostics-repair-1`;
  repair 2 `C4-typed-reference-single-path-repair-2` (ACTIVE).
- Repair authority (active): `.review/C4_IMPLEMENTATION_REPAIR_2.md` (repair 1 `.review/C4_IMPLEMENTATION_REPAIR_1.md`
  superseded — deleted in the first repair-2 implementation commit; git history is its archive).
- Automatic Codex review: DISABLED. The directive is the accepted human Contract Review; on repair completion
  the candidate is frozen (`review(final): C4 — freeze single-path typed-reference candidate`) and reported for
  Rob's human Implementation Review — no Codex review is requested or run.
- C5 and every later checkpoint remain forbidden.

## Completed checkpoints

| Checkpoint | Scope | Result |
|---|---|---|
| C0 / C0A / C0B | occurrence-index proof spike, snapshot-local identity, exact source correspondence | GREEN, human-approved |
| C1 / C1A / C1B | specification-shaped files, path-keyed source forest, standard collections | GREEN, human-approved |
| C2 | production occurrence index, references, navigation, indexed traversal | GREEN, human-approved |
| C3 | fresh-image literal-build closeout: exact `go build ./...` acceptance model, fresh-build runner, publication workflow, source type/package semantics | **ACCEPTED** by Rob at baseline `8c9212a` |

## C4 implementation state

Active under this contract.  Goal: replace the three family-specific conversion constructors
(`EIntConvert`/`EFloatConvert`/`EComplexConvert`) with one source-shaped `EConvert TypeSyntax GoExpr`; resolve
the source type name in `GoCompile` through the current predeclared context; retain occurrence-keyed type-name
facts; render from the source spelling; and delete the old path in the same checkpoint.  Sixteen live target
names (the fourteen existing numeric names plus the `byte`→`uint8` and `rune`→`int32` source aliases); no new
semantic types.  No C5 work (no `uintptr`, no rune literals/constants).

- **`1c4a7de` (repair-1 candidate) was a SECOND C4 Implementation Review BLOCKING; production-root repair 2
  `C4-typed-reference-single-path-repair-2` (authority `.review/C4_IMPLEMENTATION_REPAIR_2.md`) is ACTIVE.** The
  green tree is not the true contract: the live production expression pass still runs on raw NodeKey arithmetic +
  a hidden second semantic route (typed refs/retained facts proved BESIDE the path). Blocking classes:
  - **2.1** production `outcome_step` fills `ef_use_resolved` via `occ_use_resolved` → `resolve_expr_const` →
    recursive `const_info` → a SECOND `convert_const` per nested conversion — "one convert_const per conversion"
    is false. Use-context resolution must come from the just-computed ConstInfo.
  - **2.2** typed refs (`conversion_target_ref`) are NOT on the live path — the conversion branch reads raw
    `find (type_name_key …)` / `find (operand_key …)`, no index arg, no ExprRef/TypeNameRef/operand-ExprRef value.
  - **2.3** `tnfacts := prog_type_name_facts p` re-folds `prog_visit p` = `concat (prog_blocks p)` — a SECOND
    visit after the retained one; build from the let-bound `visit`.
  - **2.4** impossible structural failures become semantic values (missing fact → EOChildFail; ref-None → [];
    `leaf_ci` fake `CBool false` for EConvert) — eliminate via a total proof-backed function / `False_rect`.
  - **2.5** `EOConvFail` stores only GoType+ConstInfo; the diagnostic re-mints the target ref — the outcome must
    CARRY the exact conversion/target/operand refs + facts; diagnostics PROJECT them.
  - **2.6** the gated theorems (`prog_conv_outcome_consumes`/`elaborate_ok_seals_tnfacts`/`occ_expr_diags_conv_sound`)
    prove the raw-key path, not the typed-ref path — replace them.
  - **2.7** `repeated_name_distinct_refs` is CONDITIONAL (assumes the two occurrences) — need a CONCRETE compiled
    two-`uint8` snapshot minting+querying both real refs.
  - **2.8** false current prose/comments (one-visit/one-convert claims, "NO source syntax", NEXT_STEPS placeholders).

  Kept from repair 1 (do not reopen without need): `DiagnosticReason` retains a `TypeNameRef`; erased reports
  retain source-target syntax; byte/uint8 & rune/int32 erased differ; the pinned-Go accept+reject alias matrix;
  the deleted family-specific renderer helpers; the improved architecture prose. Superseded landed inventory:
  - **(repair-1) 2.5** — ARCHITECTURE.md GoAST/GoCompile/GoRender rows + master-plan C4.4 updated to the live
    `EConvert`/consumed-facts/source-spelling reality; the dead `integer_keyword`/`float_keyword`/`complex_keyword`
    helpers + their GoRender ASCII lemmas/examples + gate entries DELETED.
  - **2.6 CLOSED** — this candidate is the `review(final): C4 — freeze retained-fact repair candidate` freeze.

  New/strengthened surfaces (gated): §3.3 `conversion_target_ref_conv` (target ref minted through the retained
  index: KTypeName, the exact RConversionTarget child, recovering the raw source `TypeSyntax`); §5.1
  `prog_conv_outcome_consumes` + `elaborate_ok_seals_tnfacts`; §5.2 `predeclared_all_sixteen` (one closed
  conjunction, all 16 mappings); §5.3 `repeated_name_distinct_refs` (two same-name occurrences → distinct refs,
  equal syntax, equal facts — replaces the tautological `scar_repeated_uint8`); §4 `occ_expr_diags_conv_sound` +
  the byte/uint8 & rune/int32 erase-differ fixtures + matching uint8/int32 accept/reject scars.

  The parts NOT reopened (good): the proof-carrying `IdentifierSyntax`, the closed sixteen-name `TypeName`,
  `SupportedTypeName`, one raw `EConvert`, `KTypeName`/`TypeNameRef`/the target-operand layout, the predeclared
  mapping, source-spelling rendering, byte/rune identity + alias mapping, byte-identical generated bytes, no C5.

  Landed inventory (from the first candidate, retained + repaired):
  - `GoNames.v` — the source-name foundation (proof-carrying `IdentifierSyntax`; the closed sixteen-name
    `TypeName` + `SupportedTypeName` — retained identifier + symbol + classify-match proof; `tn_spelling` /
    `classify` inverse; `byte`/`uint8` + `rune`/`int32` source-distinctness).
  - `GoAST` — ONE `EConvert TypeSyntax GoExpr` (`TypeSyntax = TSName (TNUnqualified SupportedTypeName)`); the
    three family-specific constructors DELETED.
  - `GoIndex` — `KTypeName` occurrence kind + `ViewTypeName` + the two-child conversion (type-name at
    `Pos.succ me`, operand at `Pos.succ (Pos.succ me)`); `TypeNameRef` (= `NodeRefOf KTypeName`) +
    `type_name_ref_syntax`; all occ / navigation / walk / sound / complete proofs migrated.
  - `GoTypes` — `const_info … ProgramTyped` wrapped in a `Section` parameterized by a total resolver
    `rt : TypeSyntax -> GoType`; `ProgramTyped` stays THE type authority; no source-name→`GoType` table here.
  - `GoCompile` — the `predeclared_type` resolver (the §7 sixteen-name table); the sealed occurrence-keyed
    `TypeNameFactTable` (fact = the resolved `GoType` only, keyed by `NodeKey`, retained in
    `ElaborationFacts`/`CompilableProgram`); the total `type_name_fact_at` query proved to PROJECT the sealed
    table = `predeclared_type` of the source name recovered through the ref; `byte`/`uint8` (`rune`/`int32`)
    distinct source syntax, equal facts; the §12 alias scars + representative fixtures + intrinsic-domain
    exclusion.
  - `GoSafe` / `GoRender` — evaluation + source-spelling rendering (`render_type_syntax = render_stn`); the
    determinism theorem `render_const_info_denotes_functional` re-proved over the sixteen source spellings;
    `byte`/`rune` render distinct text.
  - e2e — every conversion fixture migrated to `EConvert` (canonical `main.go` BYTE-IDENTICAL); a DISPOSABLE
    `WitnessAlias.v` byte/rune pinned-Go differential (`byte(255)`/`rune(65)` accepted by Go, prints `255 65`).
- Candidate SHA: the `review(final): C4` freeze commit. Original C4 baseline `8c9212a`; blocked candidate
  baseline `89b8e54`; full human-review range `8c9212a..<freeze>`; repair range `89b8e54..<freeze>`.
- Gate: 397/397 axiom-free (baseline 386 + the C4 surfaces; the repair removed the 8 dead-keyword gate entries
  and added the §3.3/§4/§5.1/§5.2/§5.3 consumption/all-sixteen/repeated-name/erase-differ surfaces).
- Verification GREEN: `make prove` (397/397 axiom-free + whole-theory audit + self-tests A-E), `make e2e`
  (pinned-Go `go build ./...` + the full byte/rune/uint8/int32 accept+reject alias matrix + goldens),
  `make check` (working-tree generated bytes byte-identical), `make regenerate`, `make regen-guard`.
- The §9 design point is RESOLVED, not deferred: the production path now READS the retained type-name fact +
  operand fact (the once-built map, sealed unchanged), never an inline `predeclared_type` on the production path
  (the resolver stays only in the map construction / declarative spec / GoSafe·GoRender proof statements).
- Human C4 Implementation Review: PENDING (no Codex — automatic review disabled; the directive is the accepted
  human Contract Review). `REVIEW_REQUEST` stays closed; freeze reported to Rob for his human review.

## Standing decisions

- Platform resource limits such as NAME_MAX, PATH_MAX, disk, and memory are outside the semantic model.
- Contract Review precedes implementation for checkpoints activated after the policy was adopted. C3 was the
  explicit transition exception; C4's Contract Review is Rob's directive itself, with the automatic Codex
  review path disabled.
- Each review permits at most one bounded confirmation. A blocking confirmation returns control to Rob.
