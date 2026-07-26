# C4 repair 19 — whole-system closure audit

The record of the audit run after the six blocking findings turned green, not instead of it. Every count
below was observed in this repair; none is copied from an earlier one.

Two of the audit's own targets were Buildx cache hits on unchanged inputs. A cached verdict is valid, but an
audit should watch its assertions rather than infer them from a cache key, so `make audit-fresh` forces the
prover and the pinned-Go e2e to actually run. The numbers here come from that forced run.

---

## 1. Public constructor and mint audit

Every path that can construct one of the seven authorities, and what stops it. **Each control now proves the
module under test LOADED and a public sentinel resolved before probing the hidden name** — the defect finding
C named, where six controls could pass because `Compilable` cannot import its own downstream modules.

| Authority | Intended mint | Sentinel proving the module loaded | Sealed against | Controls |
|---|---|---|---|---|
| `Compilable.Core` | `compile` | `Compilable.compile` | `MakeCore`, `CoreRepresentation`, `build_elaboration_core`, `elaborate_at`, `decision_of_core`, `MakeElaboration` | O–X |
| `Compilable.Program` | `compile` | `Compilable.compile` | `MakeProgram`, `Capability.MakeProgram`, `minted` | F, I, L, N |
| `Compilable.Failure` | `compile` | `Compilable.compile` | `MakeFailure`, `Capability.MakeFailure` | G, J |
| `Compilable.Facts` | projection of the accepted core | `Compilable.compile` | `MakeFacts`, `AcceptedFacts.MakeFacts` | H, K |
| `Safe.Program` | `Safe.certify` | `Safe.certify` | `Safe.Make`, `ProgramRepresentation`, `Certificate.Make` | AE–AG |
| `Emit.Mint.Token` | `Emit.Mint.issue` | `Emit.Mint.issue` | `Mint.Issue`, `Mint.TokenRepresentation` | Y, Z |
| `Emit.Image` | `Emit.of_safe` / `of_safe_at` | `Emit.of_safe` | the retired `MakeImage` name | AA |

**25 sealed controls, all two-stage.** Stage two additionally requires the failure text to contain the hidden
term, so an unrelated error cannot stand in for a seal.

**3 meta-controls on the helper itself**, each observed firing: feeding it the old `Syntax Compilable`-only
prelude while probing `Safe.Make` and `Emit.Mint.Issue` (it must call that invalid evidence), and probing a
reachable public term (it must fail its own expectation).

**3 mint typing controls** (AB–AD): foreign go.mod bytes, a foreign file map, and an equality proof offered
in place of a token — each must fail by TYPING, not by absence.

The visible `Emit.Pack` carrier constructor remains deliberately unsealed and is not described as private
anywhere. What stops it authorizing foreign bytes is that the token's indices force the payload, which is a
typing fact and is tested as one.

No Rocq changed for this finding. All six constructors were already sealed; the two-stage helper is what now
shows it.

## 2. Public theorem topology audit

Read as final types, not as proofs.

```coq
Definition accepted_conversion_at (input : Input deep_nested_program) (ph : Phase input)
    (local : positive) (ts : Syntax.TypeExpr) (x : Syntax.Expr) : Prop :=
  exists occ (wm : WorkMember (phase_work ph)),
       Index.source_occurrence_at deep_nested_src local = Some occ
    /\ Index.view_expr occ = Some (Syntax.Convert ts x)
    /\ work_occurrence (proj1_sig wm) = occ
    /\ Index.Snapshot.node_ref_key (work_node_ref (proj1_sig wm))
       = Index.MakeKey (FilePath.Make "main.go" eq_refl) local
    /\ accepted_conversion_cause (phase_ot ph) wm ts x.
```

- **One exact accepted returned object.** `deep_nested_compile_fixture : exists cp Hcp, compile
  deep_nested_program = Compiled cp Hcp /\ AcceptedFixture cp Hcp`, with `Hcp` the `Compiled` branch's own
  source proof.
- **One exact rejected returned object.** `deep_fail_compile_fixture : exists fail, compile deep_fail_program
  = Rejected fail /\ RejectedFixture fail`. `Failure` is indexed by its program, so no transport is involved.
- **Exact source occurrence in every concrete cause field.** Accepted at locals 11 / 9 / 7 / 5 via
  `accepted_conversion_at`; rejected at 11 (`deep_fail_innermost_diag_claim`) and 9 / 7 / 5
  (`childfail_conversion_at`). The local is a parameter of the proposition, not a number in a proof script.
- **Exact retained cause object.** All three cause predicates take their suffix and tail accumulator as
  PROJECTIONS of `total_forest_outcome_cause`, so no foreign pair satisfies them.
- **Exact predecessor accumulator and suffix, exact diagnostic reason and refs.** Carried by those
  projections and, on the rejected side, by the exact singleton `InvalidConversion` pinned across the phase,
  raw and command-ordered lists.
- **No equality to a rebuilt peer, and no shape-only theorem described as occurrence evidence.**
  `nested_conversion_cause` is deleted. `deep_nested_ok_at_shape` survives and is named for what it drops,
  because `deep_nested_all_ok` is about every member resolving rather than about which occurrence each is.

Builder prohibition re-checked over `AcceptedFixture`, `RejectedFixture`, both roots, both occurrence
predicates and `Emit.deep_nested_emit_fixture`: **clean**, and the check is executable
(`tools/claim-matrix-gate.py:BUILDER_PROHIBITION`) with a control that injects a builder to prove it fires.

## 3. A005 audit

- **UpperCamelCase local notations in certified source: 0**, counted across all sixteen `.v` modules.
- All eight aliases deleted — `TypedProgram`, `Resolve` (three declarations), `Stmt`, `Decl`, `File` and
  `SourceFile` are gone. Five of them had no bare use at all.
- Every live use is qualified — `Typing.Program predeclared_type`,
  `Typing.Resolve Compilable.predeclared_type`.
- Comments that presented the deleted `[TypedProgram]` alias as the public judgment now name the real
  surface.
- The gate rule is the CLASS, not those names, with 8 controls: four for the exact aliases the migration left
  behind, one for an alias never seen before, one indented, and two must-accept lower-case resolver-
  specialized notations.
- No compatibility alias, wrapper, re-export or deleted-surface return: `make names` scans 92 files and the
  deleted-surface table now carries all sixteen surfaces removed across repairs 17–19.

## 4. D-24 audit

The injection was run, not reasoned about. Appending

```markdown
**Operational review:** read `.review/NO_SUCH_OPERATIONAL_FILE.md`.
```

to the FCB Index makes the gate fail:

```text
fido: FCB-REFERENCE GATE FAILED — 1 UNDECLARED operational reference(s) in the live authority corpus …
  .review/fcb/current/FIDO_FCB_INDEX.md names '.review/NO_SUCH_OPERATIONAL_FILE.md'
```

Current state: **52 declared references — 50 resolve in this tree, 2 explicitly typed off-tree** with a stated
availability; every row has exactly one owner marker bound to a line carrying its exact path; **17 live
authority documents name no undeclared operational path.**

The manifest grew from 27 rows to 52 because that is how many operational references the corpus actually
makes. The twenty-five additions were undeclared, and none of them was dangling — which is why the gap was
invisible.

25 controls, 24 must-fail with the reason pinned, including the reviewer's exact mutation, an existing but
undeclared `tools/` path, a missing marker, a duplicate marker, a marker whose line does not carry its path,
one path claimed by two rows, an anchor disagreeing with its row id, a repository path falsely typed as
external, an undecodable owner document, and an empty corpus.

## 5. Semantic-peer audit

Deleted in repair 19, each because it had no distinct current purpose:

| Deleted | Why |
|---|---|
| `deep_nested_ok_closure_at`, now deleted | explicitly weaker than the cause-owned predicates; its only named consumer was its own assumptions-gate line |
| `nested_conversion_cause` | shape-only peer beside the exact occurrence predicate |
| the eight UpperCamelCase local notation aliases | A005 |
| the `legacy-class` comment | its only subject was deleted code |

Every surface repair 19 touched or introduced was checked for a consumer. All have one, or are gated with a
stated role. **`deep_nested_all_ok` is retained deliberately**: it covers all five retained work items
including the leaf, which the four conversion causes do not, so it is the no-fail-open-anywhere claim rather
than a weaker restatement. Its gate prose now says that instead of comparing it to a theorem that no longer
exists.

No collapsed outcome peer, old result classifier, second diagnostic or cause authority, second source or
typed tree, second evaluator, or compatibility view survives.

## 6. Full execution-path audit

Observed in this repair, on this tree:

| Command | Result |
|---|---|
| `make names` | 56 controls (32 must-flag, 18 must-accept, 6 enumeration/read fail-closed, **all executed**); 92 files, no violation |
| `make fcb` | human acts 19 controls; references 25 controls, 52 rows, 17 documents; closure ledger 491 rows |
| `make claims` | 18 controls; **19 obligations, 19 closed, 0 open** |
| `make prove` (forced) | readable gate **540/540 axiom-free**; module coverage; whole-theory audit over constants, inductives and named assumptions; self-tests A–E; **25 two-stage sealed controls + 3 helper meta-controls + 3 mint typing controls**; positive control |
| `make e2e` (forced) | pinned Go built the whole tree in a fresh root with the rendered `go.mod`, accepted the empty module, ran the witness vs goldens, the multi-package and go-list differential, and the full rejection matrix |
| `make check` | green, including the working-tree generated byte compare |
| `make regenerate` | green; **the working tree was unchanged afterwards** |
| `make regen-guard` | green — `--target sync` is unbuildable when go-e2e fails and buildable when it passes, so publication cannot precede validation |
| `make fmt` | 127 tracked files conform |
| pre-commit hook | run on the exact staged export for every commit in this repair, no `--no-verify` |

Generated bytes, unchanged from the reviewed baseline:

```text
go.mod   d8f8d4f62b5b574067a4e4bf64a298bbe2cb5bc9a28d8f9c321c776e838cf1fa
main.go  b6765619f969e7fd85b4998616d8a515c5a2c0e2d397c3ee915718f35fbc48de
```

## Scope

No C5, no checkpoint-definition Step 0, no runtime `Machine` types, no post-C4 feature, no broad source
cleanup, no proof-module partitioning, no new compatibility path, no new FCB amendment.

C4 is NOT accepted. Only Rob accepts it.

## What this audit does not claim

The obligation matrix and this document verify that named surfaces, fixtures and gates EXIST and that the
controls fire. Neither judges whether a theorem is strong enough for its claim. That reading is human review's,
and this repair exists because the last two attempts at it found statements weaker than the prose around them.
