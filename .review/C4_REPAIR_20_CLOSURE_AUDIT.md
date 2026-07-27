# C4 repair 20 — whole-system closure audit

The record of the audit run after the two blocking findings turned green, not instead of it. Every count below
was observed on this candidate; none is copied from an earlier repair.

Both defects were reproduced against the exact reviewed candidate `0ffdc5f` before anything was edited, and
both repairs were then mutation-tested by reverting them — a control nobody has watched fail is not evidence,
and both of these findings existed because a control had never been watched fail in the layout that mattered.

---

## 1. Public constructor and mint audit

Every path that can construct one of the seven authorities, and what stops it. Unchanged by repair 20; re-run
and re-observed rather than assumed.

| Authority | Intended mint | Sentinel proving the module loaded | Sealed against | Controls |
|---|---|---|---|---|
| `Compilable.Core` | `compile` | `Compilable.compile` | `MakeCore`, `CoreRepresentation`, `build_elaboration_core`, `elaborate_at`, `decision_of_core`, `MakeElaboration` | O–X |
| `Compilable.Program` | `compile` | `Compilable.compile` | `MakeProgram`, `Capability.MakeProgram`, `minted` | F, I, L, N |
| `Compilable.Failure` | `compile` | `Compilable.compile` | `MakeFailure`, `Capability.MakeFailure` | G, J |
| `Compilable.Facts` | projection of the accepted core | `Compilable.compile` | `MakeFacts`, `AcceptedFacts.MakeFacts` | H, K |
| `Safe.Program` | `Safe.certify` | `Safe.certify` | `Safe.Make`, `ProgramRepresentation`, `Certificate.Make` | AE–AG |
| `Emit.Mint.Token` | `Emit.Mint.issue` | `Emit.Mint.issue` | `Mint.Issue`, `Mint.TokenRepresentation` | Y, Z |
| `Emit.Image` | `Emit.of_safe` / `of_safe_at` | `Emit.of_safe` | the retired `MakeImage` name | AA |

**25 sealed controls, all two-stage** — stage one compiles a sentinel that must succeed, so a control cannot
pass because the module was never loaded; stage two must fail AND its text must contain the hidden term.
**3 meta-controls on the helper itself** (`omitted-safe`, `omitted-emit`, `reachable`), each observed firing.
**3 mint typing controls** (AB–AD): foreign go.mod bytes, a foreign file map, and an equality proof offered in
place of a token — each must fail by TYPING, not by absence.

The visible `Emit.Pack` carrier constructor remains deliberately unsealed and is not described as private
anywhere. What stops it authorizing foreign bytes is that the token's indices force the payload, which is a
typing fact and is tested as one.

No Rocq changed in repair 20.

## 2. Accepted and rejected retained-object flow

Read as final types, not as proofs.

- **One exact accepted returned object.** `Compilable.deep_nested_compile_fixture : exists cp Hcp, compile
  deep_nested_program = Compiled cp Hcp /\ AcceptedFixture cp Hcp`, with `Hcp` the `Compiled` branch's own
  source proof.
- **One exact rejected returned object.** `Compilable.deep_fail_compile_fixture : exists fail, compile
  deep_fail_program = Rejected fail /\ RejectedFixture fail`. `Failure` is indexed by its program, so no
  transport is involved.
- **Safety and emission consume the same accepted capability.** `Emit.deep_nested_emit_fixture` destructs the
  accepted root ONCE and carries that same `cp`/`Hcp` through `Safe.certify` and `Emit.of_safe`.

## 3. Cause-theorem public identity fields

- **Exact source occurrence in every concrete cause field.** Accepted at locals 11 / 9 / 7 / 5 via
  `accepted_conversion_at`; rejected at 11 (`deep_fail_innermost_diag_claim`) and 9 / 7 / 5 via
  `childfail_conversion_at`. The local is a parameter of the proposition, not a number in a proof script.
- **Exact retained cause object.** All three cause predicates take their suffix and tail accumulator as
  PROJECTIONS of `total_forest_outcome_cause`, so no foreign pair satisfies them.
- **Exact predecessor accumulator and suffix, exact diagnostic reason and refs.** Carried by those
  projections and, on the rejected side, by the exact singleton `InvalidConversion` pinned across the phase,
  raw and command-ordered lists.

## 4. Builder and reconstruction calls after a capability is returned

`tools/claim-matrix-gate.py:BUILDER_PROHIBITION` re-checked over both returned-object roots: **clean**. The
check is executable, not asserted, and its control injects `build_expression_phase` into a root's proof to
prove it fires. The banned set is `build_elaboration_core`, `build_compilation_input`,
`build_expression_phase`, `Index.index_program`, `elaborate`, `program_visit`, `program_package_refs`.

## 5. Compatibility and collapsed-result peers

None survives. The naming gate's deleted-surface table carries every surface removed across repairs 17–20, so
a compatibility projection cannot return unnoticed; `make names` scans 93 files and reports no live hit for
any of them. No collapsed outcome peer, old result classifier, second diagnostic or cause authority, second
source or typed tree, second evaluator, or compatibility view exists.

Repair 20 deleted no Rocq surface, so this section adds nothing to the table.

## 6. Live aliases and notations, INCLUDING multiline statements

This is blocker B, and it is the one section whose method changed.

The gate no longer reads physical lines. `tools/naming-gate.py:local_notations` parses the same stripped-code
statement stream every other declaration rule uses, extracts the alias as a GENERAL identifier, and judges it
afterwards. Re-scanning the tracked theory through that extractor:

```text
23 tracked .v files; 16 Local Notation statement(s); 0 UpperCamelCase
```

All sixteen are lower-case resolver-specialized notations in `Compilable.v`, `Render.v` and `Safe.v` — they
name an executable function at a fixed resolver, not another module's public type or judgment, which is what
the accepted class rule permits.

**The defect, reproduced against `0ffdc5f` before the repair:**

| Layout | Old gate | New gate |
|---|---|---|
| `Local Notation HiddenAlias := nat.` | FLAGGED | FLAGGED |
| newline before the name | **MISSED** | FLAGGED |
| newline after `Local` | **MISSED** | FLAGGED |
| newline before `:=` | **MISSED** | FLAGGED |
| indented, split three ways | **MISSED** | FLAGGED |

**72 controls, all executed**: 38 must-flag, 24 must-accept, 6 enumeration/read fail-closed, and 4
repository-level ones that write the alias into a genuinely tracked `Compilable.v` and run BOTH input modes.
Each repository-level control is paired with a clean twin on the same tree, so a failure for an unrelated
reason cannot masquerade as the rule working.

**Mutation-tested.** Reverting `local_notations` to the old line scanner fails eight controls, including both
repository-level mutations. Making extraction conditional on the first character — the exact failure mode that
previously hid lower-case constructors, the first constructor after `:=`, and upper-case record fields — fails
five. Neither mutation passes silently.

## 7. Every current authority document and its operational paths

This is blocker A.

**The defect, reproduced against `0ffdc5f` before the repair.** Appending one dangling `.review/` path to the
active repair directive left the gate green, because corpus membership was a Python tuple that did not include
it. The same mutation against the repaired gate:

```text
fido: FCB-REFERENCE GATE FAILED — 1 UNDECLARED operational reference(s) in the live authority corpus —
every repository-rooted path a current authority names must have a typed row in
.review/fcb/current/FIDO_FCB_REFERENCES.tsv:
  .review/C4_IMPLEMENTATION_REPAIR_20.md names '.review/NO_SUCH_OPERATIONAL_FILE.md'
```

Current state:

```text
69 declared reference(s): 67 resolve in this tree, 2 explicitly typed off-tree;
every row has one bound owner marker; 17 live-set role(s) agree with the FCB Index table;
4 structural declaration(s) point at an authority;
23 current authority document(s) name no undeclared operational path
```

The manifest grew from 53 rows to 69 and the scanned corpus from 17 documents to 23. The additions are the
live FCB set named by full path with a stated role, the active repair, the M-series plan, the obligation
matrix and this audit, the two campaign documents the functional contract names, and `ARCHITECTURE.md` —
which `CLAUDE.md` calls the binding charter and which was never scanned.

**Roles are assigned honestly, not to raise the count.** `PROGRESS.md` is a status ledger, the obligation
matrix and this audit are evidence, the generated human and ledger views are projections of canonical data —
all `reference`. The canonical `.csv` and `.tsv` ledgers behind those views are `authority`.

**48 controls, 45 must-fail with the reason pinned**, including the reviewer's exact mutation, a dangling path
injected into each of the three documents the old gate never read, each of those three rows downgraded to
`reference`, an authority that is a directory, one that cannot be decoded, one that cannot be read (injected,
because `chmod 000` is not a control on a tree that builds as root), a live-set role disagreeing with the FCB
Index table, a table line deleted outright, a table path with no manifest row, each structural declaration
removed, and a declaration retargeted at a path with no row.

**Dynamic discovery is proved by three controls, not asserted:** a brand-new authority file naming an
undeclared path FAILS; the same file with clean text PASSES; and the same file with the same undeclared path,
left as a `reference`, passes because it is correctly not scanned. None of the three requires a Python edit.

**Mutation-tested.** Restoring the hard-coded corpus — the exact old defect — fails seven controls including
all three reviewer reproducers. Removing the authority-role requirement on the structural declarations fails
four. Removing the Index-table cross-check fails one.

## 8. Tools, Docker, Make, Dune, extraction, OCaml and staged paths

| Surface | Observed |
|---|---|
| Tracked files | 130; no untracked non-ignored file exists, so nothing escapes a gate by being invisible to it |
| Certified modules | 16, exactly the `dune` `(modules …)` list; 23 tracked `.v` including gate and e2e |
| Handwritten OCaml | 4 files — `plugin/materialize.mlg`, `plugin/sink.ml`, `e2e/sink_test.ml`, `e2e/apply.ml` — the transport boundary and nothing else |
| Tools | 12 tracked, each with one owner and one gate; `tools/rocq-profile.py` and `tools/regen-guard-test.sh` are diagnostics, deliberately not gates |
| Make targets | `check prove prover-log profile emit regenerate audit-fresh regen-guard fmt names claims fcb fcb-write prove-errors builder install-hooks` |
| Staged path | the pre-commit hook exports the index once and runs the STAGED copy of every gate against it; run for every commit in this repair, never `--no-verify` |

## 9. Generated artifacts and runtime goldens

Unchanged from the reviewed baseline:

```text
go.mod   d8f8d4f62b5b574067a4e4bf64a298bbe2cb5bc9a28d8f9c321c776e838cf1fa
main.go  b6765619f969e7fd85b4998616d8a515c5a2c0e2d397c3ee915718f35fbc48de
```

## 10. A007 documentation

Installed, and not implemented. Governance carries `D-27` and the A007 register row; the amendment record is
under the FCB amendments directory; every accepted-amendment banner names A007, including the one inside the
human-acts generator so the generated view is not hand-edited; the Roadmap carries the M1–M4 sequence with
zero closure, latitude or acceptance-gate rows moved; the Checkpoint Authoring Guide carries the
mechanical-change duty; Model Operations carries the sequencing rule; Fixed Points states that A007 reopens
none; `M4-PLAN-APPROVAL` is a canonical `DEFERRED` human act whose anchor lives in the M-series plan.

**No M-series implementation landed.** No source diet, no build measurement, no tool consolidation, no proof
partitioning. No C5 type, relation or feature landed.

## 11. Completion claims against their theorem or executable control

`.review/C4_REPAIR_20_OBLIGATION_MATRIX.tsv`: **12 obligations, 12 closed, 0 open.** Every row names a surface
that is DECLARED under that exact name, a fixture whose token occurs literally, and a gate that runs. 18
controls, 17 must-fail with the reason pinned.

One row states an unsupported boundary rather than inventing a surface: A007 is accepted documentation
authority and has no Rocq or Python declaration. Naming one to fill the column would be the same overclaim the
matrix exists to catch.

## 12. Full execution path

Observed on this candidate:

| Command | Result |
|---|---|
| `make names` | 72 controls (38 must-flag, 24 must-accept, 6 enumeration/read fail-closed, 4 repository-level over both input modes, **all executed**); 94 files, no violation |
| `make fcb` | human acts 19 controls; references **48 controls, 69 rows, 23 authorities**; closure ledger 491 rows |
| `make claims` | 18 controls; **12 obligations, 12 closed, 0 open** |
| `make prove` (forced uncached) | readable gate **540/540 axiom-free**; module coverage; whole-certified-theory audit over constants, inductives and named assumptions; self-tests A–E; 25 two-stage sealed controls + 3 helper meta-controls + 3 mint typing controls |
| `make e2e` (forced uncached) | pinned Go built the whole tree in a fresh root with the rendered `go.mod`, accepted the empty module, ran the witness vs goldens, the multi-package and go-list differential, and the full rejection matrix |
| `make check` | green, including the working-tree generated byte compare |
| `make regenerate` | green; **the working tree was unchanged afterwards** |
| `make regen-guard` | green — `--target sync` is unbuildable when go-e2e fails and buildable when it passes, so publication cannot precede validation |
| `make fmt` | 130 tracked files conform |
| pre-commit hook | run on the exact staged export for every commit in this repair, **no `--no-verify`** |

## Scope

No C5, no checkpoint-definition Step 0, no M1–M4 implementation, no runtime `Machine` types, no post-C4
feature, no broad source cleanup, no proof-module partitioning, no new compatibility path, no FCB amendment
beyond installing the already-accepted A007.

C4 is NOT accepted. Only Rob accepts it.

## What this audit does not claim

The obligation matrix and this document verify that named surfaces, fixtures and gates EXIST, that the
controls fire, and that reverting each repair makes them fail. None of that judges whether a theorem is strong
enough for its claim. That reading is human review's, and this repair exists because the previous attempt's
enforcement was weaker than the prose around it in two places that no gate could see.
