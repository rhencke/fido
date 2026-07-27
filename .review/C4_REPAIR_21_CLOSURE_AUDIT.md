# C4 repair 21 — whole-system closure audit

The record of the audit run after the two blocking findings turned green, not instead of it. Every count below
was observed on this candidate; none is copied from an earlier repair.

Both defects were reproduced against candidate `9645752` before anything was edited. Every root helper is then
mutation-tested by deleting its effect and requiring that gate's own NAMED controls to fail — because a
control that survives the deletion of the rule it protects is decoration, and both D-24 blockers reached a
freeze exactly that way.

---

## 1. Repository and corpus counts

| Quantity | Observed |
|---|---|
| Repository inventory (working-tree mode: tracked plus untracked-nonignored) | **131 files** |
| Top-level entries / top-level namespaces (directories) | **37 / 6** |
| Manifest rows | **94** — 92 in-repository, 2 external |
| Current authorities (`corpus_role = authority`) | **23** |
| Live FCB set (immediate entries of the canonical directory) | **17 regular files, 0 other entries** |
| Live-file table rows agreeing with the manifest | **17** |
| Structural declarations checked | **4** |
| Tracked files | **131** |
| Untracked non-ignored files | **0** |

The inventory is derived from the exact snapshot in both modes. The gate holds no list of repository
namespaces, no list of root files, and no list of authority documents; `.review/fcb/current/FIDO_FCB_REFERENCES.tsv`
is the one hard-coded path, because something has to load the manifest that owns everything else.

## 2. Newly declared manifest rows

Twenty-nine rows were added because a current authority genuinely names those repository files and nothing
declared them. The old path grammar could not see any of them: a root file is not a namespace, so a bare
`Compilable.v` was invisible, and a dot-prefixed root path was invisible too.

| Class | Rows |
|---|---|
| Certified modules named by the source inventory | `COLLECTIONS-V` `COMPILABLE-V` `COMPLEX-V` `DECIMAL-V` `EMIT-V` `FILEPATH-V` `FLOAT-V` `INDEX-V` `INTEGER-V` `MODULEPATH-V` `NAMES-V` `RENDER-V` `SAFE-V` `SYNTAX-V` `TYPING-V` `VERSION-V` |
| Build and gate inputs | `DOCKERIGNORE` `DUNE-PROJECT` `EDITORCONFIG` `GITHOOKS-PRE-COMMIT` |
| Tracked generated module | `GO-MOD` `MAIN-GO` |
| Other current repository files | `LIFE-MD` `PAINFUL-LESSONS-MD` |
| Repair-21 documents | `REVIEW-C4-IMPLEMENTATION-REPAIR-21-MD` `REVIEW-C4-REPAIR-21-OBLIGATION-MATRIX-TSV` `REVIEW-C4-REPAIR-21-CLOSURE-AUDIT-MD` |
| New tool | `TOOLS-GATE-MUTATION-TEST-PY` |

Retired with their documents: `REVIEW-C4-IMPLEMENTATION-REPAIR-20-MD`,
`REVIEW-C4-REPAIR-20-OBLIGATION-MATRIX-TSV`, `REVIEW-C4-REPAIR-20-CLOSURE-AUDIT-MD`.
Moved to the external namespace: `PROBE-ENVIRONMENT` → `external:PROBE_ENVIRONMENT.tsv`,
`EVIDENCE-SANDBOX` → `external:sandbox`.

## 3. False operational references removed

Turning the model on found these in the LIVE corpus, not in a fixture. Each is a case where a reader was
being sent somewhere that does not exist, or a marker was proving something it did not prove.

| Where | What was wrong | Now |
|---|---|---|
| the stable bootstrap | named the checkpoint authority by a path that only resolves from inside the FCB directory | names it from the repository root |
| `CLAUDE.md` | the `Dockerfile` owner marker sat on a line where the path appeared only inside a longer token | moved to prose naming the file as a token |
| `CLAUDE.md` | named a central `.fido` staging design — a shape that must never exist — as though it were a live path | stated in words |
| `CLAUDE.md` | the `.review` and `.review/spec-closure-campaign` marker lines carried a trailing slash, so neither bound its canonical path | spelled canonically |
| the FCB Index | the live-location line carried a trailing slash on the marker line | spelled canonically |
| the repair-21 directive | eight synthetic reproducer paths would have been live dangling references, and section 5 requires controls that inject those exact literals and watch the gate fail | respelled, with an installer's note; the literals live once, in the gate's control table |
| my own new D-24 prose | used the dot-slash form as a placeholder for "some path", which by the rule I had just written IS a reference | stated in words |

The last row is the one worth keeping. The rule caught its own author within minutes of being written, which
is the only evidence that matters about whether a rule is real.

## 4. Blocker A — the path universe

**The defect, reproduced against `9645752`.** Each of these left the repair-20 gate green:

| Injected into the active repair authority | Old gate | New gate |
|---|---|---|
| a dangling path under a dot namespace | PASSED | `UNDECLARED operational reference` |
| a dangling dot-prefixed root path | PASSED | `UNDECLARED operational reference` |
| a dangling root path in explicit root-relative form | PASSED | `UNDECLARED operational reference` |
| an existing but unmanifested root module | PASSED | `UNDECLARED operational reference` |
| an owner outside the tree with a matching marker file | PASSED | `has a ".." segment` |
| a missing repository path retyped as external evidence | PASSED | `must use the 'external:' identity form` |
| an undeclared file, directory or symlink in the live FCB set | PASSED | `contains a DIRECTORY` / `contains a SYMLINK` |
| a second row for a non-canonical spelling of a declared target | PASSED | `is stored with a leading "./"` |
| an owner marker naming the longer path that contains the declared one | PASSED | `as an exact token` |
| a repeated live-file table row with the same role | PASSED | `more than once` |

**Current state:**

```text
working tree inventory 131 file(s), 37 top-level entries, 6 namespace(s);
94 declared reference(s): 92 in-repository, 2 external;
every row canonical with one bound owner marker;
live set 17 declared regular file(s) and 17 role(s) agreeing with the FCB Index table;
4 structural declaration(s) point at an authority;
23 current authority document(s) name no undeclared operational path
```

## 5. Blocker B — mutable candidate state

The canonical `C4-REVIEW` row said no candidate was offered and named the previous one, while `NEXT_STEPS`
offered `9645752`. That was drift introduced in repair 20 — the row was written while the review request was
closed and never updated when it reopened, which is exactly the failure mode the one-owner law exists to stop.

The act now reads:

```text
Review the exact C4 candidate named by .review/NEXT_STEPS.md, and accept or block it. Only Rob accepts C4.
```

**Canonical human-act data now carries 0 Git object IDs.** The generator rejects any 7-to-40 character hex run
delimited on both sides — and accepts a 64-character content digest, because a pinned-bytes identity is a
durable fact and an over-broad pattern would have pushed a real provenance record out of the data authority.
Both directions have a control, and both fail when the rule or its boundary is removed.

## 6. Every negative control and its pinned reason

### D-24 reference gate — 62 controls (57 must-fail, 5 must-accept)

| Control | Pinned reason |
|---|---|
| active repair names a dangling path under a dot namespace | `UNDECLARED operational reference` |
| active repair names a dangling dot-prefixed root path | `UNDECLARED operational reference` |
| active repair names a dangling root path in explicit root-relative form | `UNDECLARED operational reference` |
| authority names an existing but unmanifested root module | `UNDECLARED operational reference` |
| authority names an existing but unmanifested dotfile | `UNDECLARED operational reference` |
| active repair names a malformed parent-traversal path | `MALFORMED operational reference` |
| manifest owner escapes the repository by traversal | `has a ".." segment` |
| manifest owner is absolute | `is absolute` |
| manifest owner is a directory, not a file | `is not a readable regular file` |
| manifest owner reached through a symlink | `is reached through a symlink` |
| a missing repository path typed as external evidence | `must use the 'external:' identity form` |
| an external identity that resolves inside the repository | `resolves inside the repository` |
| an external identity inside a repository namespace | `begins with the repository namespace` |
| a repository row wearing the external identity form | `may not use the external identity form` |
| the live FCB set contains an undeclared regular file | `carry no corpus role and are never scanned` |
| the live FCB set contains a directory | `contains a DIRECTORY` |
| the live FCB set contains a symlinked directory | `contains a SYMLINK` |
| the live FCB set contains a symlinked file | `contains a SYMLINK` |
| a manifest target written in explicit root-relative form | `is stored with a leading "./"` |
| a manifest target with a doubled separator | `has an empty path segment` |
| a manifest target with a "." segment | `has a "." segment` |
| a manifest target with a backslash | `uses a backslash` |
| two rows resolving to the same target | `is claimed by 2 rows` |
| an owner marker bound to the longer containing path | `as an exact token` |
| the FCB Index repeats one live-set path with the same role | `more than once` |
| the FCB Index repeats one live-set path with a different role | `more than once` |
| the Index table role disagrees with the manifest | `the corpus must state one truth` |
| a live-set file dropped from the Index table | `does not state a corpus role` |
| the Index table names a path with no manifest row | `no manifest row` |
| a newly added authority row scans its target with no Python change | `UNDECLARED operational reference` |
| the ACTIVE REPAIR row marked reference | `a document that assigns current work is an authority` |
| the FUNCTIONAL CONTRACT row marked reference | `a document that assigns current work is an authority` |
| the ACCEPTED REVIEW BASIS row marked reference | `a document that assigns current work is an authority` |
| the M-SERIES PLAN row marked reference | `a document that assigns current work is an authority` |
| NEXT_STEPS names no active repair | `does not declare the active repair directive` |
| REVIEW_REQUEST names no functional contract | `does not declare the functional contract` |
| the FCB Index names no M-series plan | `does not declare the accepted M-series plan` |
| NEXT_STEPS names an active repair with no row | `which has no row in` |
| no row declares an authority role | `corpus is empty` |
| a declared path is missing | `does not exist in this tree` |
| the manifest itself is deleted | `does not exist` |
| a symlinked declared target | `is reached through a symlink` |
| a file declared as a directory | `may not be a current authority` |
| a directory declared as a file | `declared a file but is not one` |
| unknown kind | `is not one of` |
| unknown corpus_role | `is not one of authority, reference` |
| repository kind claiming an off-tree availability | `may not have availability` |
| duplicate id | `duplicate id` |
| malformed field count | `expected 7 fields` |
| rows out of canonical order | `not in canonical id order` |
| invalid UTF-8 in the manifest | `is not valid UTF-8` |
| a manifest row whose owner has no marker | `missing owner marker` |
| a duplicate owner marker | `occurs 2 times, expected once` |
| a marker whose line does not carry its declared path | `as an exact token` |
| an owner_anchor that does not match its row id | `owner_anchor must be` |
| an authority that cannot be decoded | `is not valid UTF-8` |
| an authority that cannot be read | `could not be read` |

Five must-ACCEPT: the canonical fixture in **both** input modes; a newly added clean authority discovered and
scanned; the same new file left as a `reference` and correctly NOT scanned; and a deleted `NEXT_STEPS` row,
which fails for its own structural reason rather than this one.

### D-07 human-acts gate — 23 controls (20 must-fail, 3 must-accept)

The three added by this repair: a full candidate SHA in the act text, a short SHA, and a SHA hidden in the
effect column — each pinned to `which is a Git object ID`. The two must-accepts that keep the rule from being
over-broad: a SHA-256 content digest, and an ordinary dated act. The remaining seventeen must-fails are the
repair-18 set, unchanged.

### Claim-matrix gate — 21 controls (20 must-fail, 1 must-accept)

Four are new for the nine-column schema: a dangling positive-evidence token, a dangling negative control, a
dangling mutation control, and a required obligation with no row at all — `accepted obligation(s) have NO row`.
That last one is the reviewer's "absent" case: a matrix that quietly drops an accepted requirement is not a
matrix with a gap, and nothing else would have noticed.

### Naming gate — 72 controls, all executed

Unchanged by this repair, re-run and re-observed: 38 must-flag, 24 must-accept, 6 enumeration/read
fail-closed, 4 repository-level over both input modes.

## 7. Mutation test — every root helper

`tools/gate-mutation-test.py` deletes one helper's effect at a time, reruns that gate's own self-test in a
copy of the tree, and requires the SPECIFIC named controls that depend on that rule to fail. Every anchor is
asserted to occur exactly once first, so a refactor that moves a helper fails loudly instead of silently
testing nothing.

| Root helper | Controls that fired |
|---|---|
| repository inventory derivation | 2 |
| canonical path parsing | 3 |
| owner and target root containment | 2 |
| external / repository separation | 1 |
| live-set entry-kind checking | 2 |
| live-set declaration closure | 1 |
| exact marker token binding | 1 |
| duplicate target identity | 1 |
| duplicate Index table rows | 2 |
| structural declarations must name an authority | 2 |
| the candidate-state rule | 2 |
| the boundary protecting content digests | 1 |
| statement-level local-notation parsing | 3 |
| general identifier extraction before judgement | 2 |

**14 of 14 detected.** Two of these were VACUOUS on the first run and are recorded because the fix mattered:
the inventory mutant only neutered the working-tree branch while the self-test runs in snapshot mode, and the
canonicality mutant targeted a comparison that could never fire. That comparison was deleted rather than kept
— split-then-join is the identity, so once the segment and prefix rules pass there is nothing left to catch,
and a check that cannot fire is worse than no check because it reads as protection.

## 8. C4 surfaces that did not move

No Rocq, OCaml, Go, extraction, renderer or golden changed in this repair. Re-observed rather than assumed:

- one exact retained `Compilable.Core`; accepted and rejected decisions indexed by that exact core;
- `Compilable.compile` the sole `Program` and `Failure` mint; accepted `Facts` an exact view of the core;
- `Safe.certify` the sole `Safe.Program` mint; `Emit.Mint.issue` the sole image-authority mint;
- `Emit.Image` a reducible carrier, not an arbitrary-byte authority; every raw authority constructor sealed;
- one accepted and one rejected returned-object root over one exact returned object, with source locals
  11 / 9 / 7 / 5 in the public propositions;
- no prohibited builder in either root — re-checked executably by `tools/claim-matrix-gate.py:BUILDER_PROHIBITION`,
  whose control injects one to prove it fires.

## 9. A007 — installed, not implemented

Governance `D-27`, the A007 amendment record, the M-series plan and the deferred `M4-PLAN-APPROVAL` act are
all in Git and unchanged. **No M-series implementation landed:** no source diet, no build measurement, no tool
consolidation of the M3 kind, no proof partitioning. No C5 type, relation or feature landed.

The one new tool, `tools/gate-mutation-test.py`, is not M-series work: it is the mutation evidence this
directive requires in the obligation matrix, and it replaced three throwaway scripts rather than adding a
build path.

## 10. Generated artifacts

Unchanged from the reviewed baseline:

```text
go.mod   d8f8d4f62b5b574067a4e4bf64a298bbe2cb5bc9a28d8f9c321c776e838cf1fa
main.go  b6765619f969e7fd85b4998616d8a515c5a2c0e2d397c3ee915718f35fbc48de
```

## 11. Full execution path

| Command | Result |
|---|---|
| `make names` | 72 controls, all executed; 95 files, no violation |
| naming gate, working-tree mode | green |
| naming gate, exported-snapshot mode | green (run by the hook over the staged export) |
| `make fcb` | human acts 23 controls; references **62 controls**; closure ledger 491 rows; **14 mutants** |
| `make claims` | 21 controls; **13 obligations, all 12 required present, 13 closed, 0 open** |
| `make prove` (forced uncached) | readable gate **540/540 axiom-free**; module coverage; whole-certified-theory audit over constants, inductives and named assumptions; self-tests A–E; sealed-constructor and mint controls |
| `make e2e` (forced uncached) | pinned Go built the whole tree in a fresh root, ran the witness vs goldens, the multi-package and go-list differentials, and the full rejection matrix |
| `make check` | green, including the working-tree generated byte compare |
| `make regenerate` | green; **the working tree was unchanged afterwards** |
| `make regen-guard` | green — `--target sync` is unbuildable when go-e2e fails and buildable when it passes |
| `make fmt` | 131 tracked files conform |
| pre-commit hook | run on the exact staged export for every commit in this repair, **no `--no-verify`** |

## 12. Exact candidate

```text
39ea7e3b012ec798c6a756c971c10bb363557ef8
```

## Scope

No C5, no checkpoint-definition Step 0, no M1–M4 implementation, no post-C4 feature, no broad source cleanup,
no proof-module partitioning, no new FCB amendment. C4 is NOT accepted. Only Rob accepts it.

## What this audit does not claim

The obligation matrix and this document verify that named surfaces, tokens, controls and gates EXIST, that the
controls fire, and that deleting each rule makes its own named controls fail. None of that judges whether a
theorem or a rule is strong enough for its claim — that reading is human review's. What changed here is only
that the enforcement now covers the whole repository rather than the part a tool had been told about.
