# C4 repair 18 — whole-system closure audit

The record of the agreed one-round closure-process experiment. Repair 18 was not frozen after the three named
findings closed; this is what the whole-system audit found and what it changed.

Green commands are necessary evidence, not sufficient. Everything below was read by hand as well as run.

---

## 1. Claim-to-theorem matrix

`.review/C4_REPAIR_18_CLAIM_THEOREM_MATRIX.tsv` — 19 load-bearing completion claims, each naming the exact
public surface, fixture and gate that establish it. Checked by `tools/claim-matrix-gate.py` (`make claims`,
in `make check` and in the pre-commit hook over the exported staged tree): 16 controls, 15 must-fail with the
reason pinned.

**What the matrix caught on its author.** Six rows failed on the first run because I had named surfaces from
memory that did not exist under those names:

| I wrote | It actually is |
|---|---|
| `Print Assumptions …` cited as a declaration | a gate line, not a surface — the claim belongs to `Makefile:prove` |
| `Dockerfile:audit self-test A` | the label reads `reject /tmp/tA A` |
| `Dockerfile:whole-theory audit OK` | the text says `whole-certified-theory audit OK` |
| `tools/staged-generated-compare.sh:compare_trees` | that script has no functions at all |
| `gate/Assumptions.v` as an owner of declarations | it owns `Print Assumptions` lines |
| `Safe.certify_retains` | the theorem is `certify_retains_capability` |

Every one of those would have gone into the freeze report as confident evidence. That is the exact failure
this gate exists for.

**What it does not do:** it does not read Rocq types and does not judge whether a theorem is strong enough.
Human review does that. Saying so narrowly is deliberate — a gate that promised to verify claim strength
would be the same overclaim one layer up.

### The exact aggregate statements

```coq
Theorem deep_nested_compile_fixture :
  exists cp Hcp,
    compile deep_nested_program = Compiled cp Hcp
    /\ AcceptedFixture cp Hcp.

Theorem deep_fail_compile_fixture :
  exists fail,
    compile deep_fail_program = Rejected fail
    /\ RejectedFixture fail.
```

`AcceptedFixture cp Hcp` carries twenty fields: `input`, `phase`, `expression_facts`, `type_name_facts`,
`package_refs`, `package_refs_own_visit`, `layout`, `plan`, `forest`, `index_exact`, `outcomes`, `trace`,
`distinct_occurrences`, the four `int8`/`int16`/`int32`/`int64` causes, and `phase_diagnostics`,
`raw_diagnostics`, `final_diagnostics`. `Hcp` is not a fresh source equation — it is the proof object the
`Compiled` branch itself carries, so the deep fields interrogate that capability's own core through the
decision's own evidence.

`RejectedFixture fail` carries fifteen: `core`, `raw_diagnostics`, `input`, `phase`, `package_refs`,
`package_refs_own_visit`, `layout`, `plan`, `forest`, `index_exact`, `outcomes`, `trace`, `innermost_cause`,
`outer_causes`, `rejected`. `Failure` is indexed by its program, so no transport is involved at all.

`Emit.deep_nested_emit_fixture` destructs the accepted root exactly once and carries that witness and its
source proof through `Safe.certify` and `Emit.of_safe`, so `AcceptedFixture cp Hcp` arrives unchanged. It
does not re-invoke `compile_complete` and then assert the two capabilities coincide.

---

## 2. Public constructor and mint audit

Every public path that can create one of the seven authorities, and what stops it:

| Authority | Intended mint | Sealed against | Control |
|---|---|---|---|
| `Compilable.Core` | `compile` only | `MakeCore`, `CoreRepresentation`, `build_elaboration_core`, `elaborate_at`, `decision_of_core`, `MakeElaboration` | sealed `O`–`X` |
| `Compilable.Program` | `compile` | `MakeProgram`, `Capability.MakeProgram`, `minted` | sealed `F`, `I`, `L`, `N` |
| `Compilable.Failure` | `compile` | `MakeFailure`, `Capability.MakeFailure` | sealed `G`, `J` |
| `Compilable.Facts` | projection of the accepted core | `MakeFacts`, `AcceptedFacts.MakeFacts` | sealed `H`, `K` |
| `Safe.Program` | `Safe.certify` | `Safe.Make`, `ProgramRepresentation`, `Certificate.Make` | sealed `AE`–`AG` |
| `Emit.Mint.Token` | `Emit.Mint.issue` | `Mint.Issue`, `Mint.TokenRepresentation` | sealed `Y`, `Z` |
| `Emit.Image` | `Emit.of_safe` / `of_safe_at` | the retired `MakeImage` name | sealed `AA` |

The visible `Emit.Pack` carrier constructor is **deliberately not sealed** and is not described as private
anywhere. It is a reducible carrier, and what stops it authorizing foreign bytes is that the token's indices
force the payload — a typing fact, tested as one by `mintfail AB`/`AC`/`AD`, which require the failure to be
a TYPING error rather than an absent name. No helper accepts arbitrary bytes plus an independently supplied
equality: `AD` is exactly that attempt, and it fails to typecheck.

Every negative fixture checks the REASON it failed, not merely that it failed. The positive control compiles
the whole public path — mint, `Outcome` destruct, accepted and rejected core queries, certify, emit,
transport — so the negatives are not passing because a client failed to load the theory.

`make names` confirms no retired module, type, compound or deleted surface survives as a live name, and no
compatibility alias or old constructor name is present.

---

## 3. Reconstruction audit

Searched all six certified modules — 1,857 declaration blocks — for the seven prohibited builders, and
classified every hit against whether the declaration's STATEMENT speaks of a value returned by `compile`.

- `Safe.v`, `Render.v`, `Emit.v`, `e2e/`, `plugin/`: **zero occurrences of any prohibited builder.** After a
  capability or failure is returned, nothing downstream re-runs a builder.
- `Compilable.v`: 102 declarations mention one. Every one is either a builder-side definition (`program_visit`
  IS the visit; `Admissible` is defined through `elaborate`), a specification bridge stated explicitly over
  freshly built objects (`phase_domain_exact`), or the sealed implementation where the builders live.
- **Returned-object statements naming a prohibited builder: none.** The single flagged hit was
  `bucket_present_of_domain`, and reading it showed the match is in the section-header comment that follows
  it, not in code.

The two root fixtures and the emit fixture additionally carry an executable check
(`tools/claim-matrix-gate.py:BUILDER_PROHIBITION`) with a control that injects a builder to prove it fires.

---

## 4. Semantic-peer and compatibility audit

Deleted in repair 18, each because it stated strictly less than a surviving surface over an object its
statement was free to pick:

| Deleted | Superseded by |
|---|---|
| `deep_nested_capability_retains_elaboration` | `AcceptedFixture` |
| `deep_nested_capability_retains_causes` | `AcceptedFixture` |
| `deep_nested_seals_expression_fact_table` | `accepted_fixture_expression_facts` |
| `deep_nested_chain_operands_final_ok` | `accepted_conversion_cause` |
| `nested_index_bundle`, `deep_nested_index_at`, `deep_nested_chain_index_evidence` | absorbed into `accepted_conversion_cause` — the navigation they tested is real and is now a conjunct over the cause's own suffix |
| `deep_fail_capability_retains_rejected_elaboration` | `RejectedFixture` |
| `deep_fail_capability_retains_rejected_causes` | `RejectedFixture` |
| `deep_fail_outer_operands_final_fail` + its claim | `childfail_conversion_cause` |
| `deep_fail_childfail_closure_at` | `childfail_conversion_cause` |
| `retained_convsuccess_closure` | `retained_convsuccess_cause` |
| `retained_childfail_closure` | `retained_childfail_cause` |
| `program_member_at` | orphaned when the index peers were absorbed; `member_at_in_forest` is the surface |

No collapsed outcome peer, old result classifier, second diagnostic authority, second source or typed tree,
second evaluator, or compatibility alias survives. The two remaining "legacy compile class" comments named
code that no longer exists and are gone.

**Retained deliberately, with its consumer stated:** `phase_domain_exact` is a builder-side theorem, honestly
stated over `build_expression_phase`, and carries the wrong-kind-key exclusion the fixtures do not. It is
gated. It is not a returned-object claim and does not present itself as one.

A scan for declarations with no in-theory consumer returns a large list; nearly all are gated public theorem
surfaces, whose gate IS their consumer. Deleting a required theorem to reduce a count is explicitly not the
goal.

---

## 5. Documentation and reference audit

- Stable bootstrap `INDEX.md` read; every file the Index names read.
- D-07 human-act generator check: green, 19 controls.
- D-24 typed-reference check: green, 27 declared references, 25 resolving in-tree, 2 explicitly typed
  off-tree with a stated availability.
- Closure-ledger view: green, 491 rows regenerated from the canonical CSV.
- `NEXT_STEPS.md` and `OPEN_QUESTIONS.md` read; no open implementation question.
- **Old candidate hashes in current documents:** every 40-hex string found is a SHA-256 of pinned toolchain
  evidence, not a Git candidate. Classified: historical evidence, correctly typed.
- **Repair-number mentions in current documents:** all past-tense retained-results records, except the A006
  amendment register entry, which names "C4 repair 17 acceptance boundary" as part of the accepted amendment
  substance. Classified: historical record of what the amendment affected at acceptance time; not changed,
  because changing accepted substance is not the implementer's to do.
- Current state appears only in its owning root: `NEXT_STEPS.md` for the candidate and active repair,
  `FIDO_FCB_HUMAN_ACTS.tsv` for open human acts, and the generated views of each.

---

## 6. Full execution-path audit

Run on the working tree and, via the pre-commit hook, on the exact exported staged snapshot with no bypass:

- naming gate (47 controls) — green
- D-07 human-acts gate (19 controls) — green
- D-24 reference gate (16 controls) — green
- closure-ledger view check — green
- claim-matrix gate (16 controls) — green
- transport-only OCaml origin gate, generated-output gate, index-authoritative generated-mode gate — green
- `make prove`: dune build, readable Print-Assumptions gate **539/539 axiom-free**, certified-module coverage,
  whole-certified-theory assumption audit, adversarial self-tests A–E, sealed-capability self-tests F–AA and
  AE–AG, mint typing controls AB–AD, positive control — green
- `make e2e`: `Fido Materialize` witness / multi / EMPTY / boundary-byte pristine trees; forged and raw
  transports rejected before any effect; sink adversarial suite; pinned `go build ./...` over the whole tree;
  multi-package differential; rejection fixtures; witness vs reviewed goldens — green
- working-tree and staged generated byte-compare — green, **generated `go.mod` and `main.go` byte-identical
  to the reviewed baseline**
- `make fmt` — green

## Scope

No C5, no checkpoint-definition Step 0, no post-C4 feature, no broad source cleanup, no proof-module
partitioning. C4 is NOT accepted; only Rob accepts it.
