# Manual C3 Milestone Audit

Snapshot audited:

```text
fido-main (72).zip
archive root: fido-main/
recorded snapshot SHA: de6bd759d8fe1977bc196b5aaed04aa60b9560b1
```

Audit goals:

1. repair the Codex review process;
2. identify material C3 holes without relying on another serial Codex cycle;
3. identify review-driven overarchitecture or overreach that should be removed.

## Overall disposition

**C3 is not ready for human approval in this snapshot.**

The core architecture is substantially right and should be retained: one raw AST, a semantic-free occurrence
index, snapshot-local references, occurrence-keyed facts, structured diagnostics, source/package rule
factorization, literal fresh-image `go build ./...` planning, elaboration provenance, and a downstream
DirectoryImage bridge.

The remaining blocking issues are concentrated and repairable. They are not a reason to restart C3.

The largest process defect is also clear: the current review policy has trained Codex to propose the smallest
local correction after each stop, while the active contract contains a very large late-stage attack list. That
combination encourages serial discovery and proof growth instead of one complete root-cause review.

This audit is static. Rocq, Docker, and the pinned Go toolchain were not available in this environment, so I did
not run `make check`. I did reproduce the fresh-runner fail-open behavior with a local shell simulation.

## Correct work to retain

Do not reopen these roots unless a concrete repair requires a local change:

- `GoAST` remains the one source authority.
- `GoIndex` remains structural and semantic-free.
- `IndexedProgram p` retains one snapshot-local index.
- `NodeRef`, typed references, navigation, and indexed traversal remain the occurrence identity foundation.
- `GoTypes` owns constant/type relations and no longer imports `GoIndex`.
- `GoCompile` is the sole layer where occurrence identity and type semantics meet.
- `ExprFactTable` uses the standard `NodeKey` map and stores semantic facts, not copied syntax.
- package buckets use the standard package map and preserve duplicate declarations until validation.
- diagnostics carry exact snapshot-local anchors and explicit erased reports.
- nested conversion failure uses the innermost failing conversion as primary.
- diagnostic node ordering is now based on unique keys, singleton buckets, and strict standard-map order.
- package source validity is factored into declaration-name uniqueness and main-entry validity.
- final command acceptance separately models fresh-image literal `go build ./...` behavior.
- the default executable-name and fresh-root layout concepts are real requirements, not optional embellishment.
- `ElaborationFacts` and `CompilableProgram` retain provenance from the one elaboration result.
- `DirectoryImage` remains the immutable authoritative source image.
- build work belongs in a disposable fresh copy, never in the authoritative or sink tree.

## Blocking implementation defects

### 1. The production elaborator traverses every file twice

**Classification:** Algorithmic defect / competing execution path

The code says the visit blocks are retained once:

```text
GoCompile.v:685-693
  prog_blocks p := map binding_visit ...
  prog_visit p  := concat (prog_blocks p)
```

The package-bucket helper separately reconstructs that traversal:

```text
GoCompile.v:2612-2613
  prog_package_refs idx := fold_right ... (prog_visit p)
```

But `elaborate_indexed` already computes and retains:

```text
GoCompile.v:6159-6160
  blocks := prog_blocks p
  visit  := concat blocks
```

and then ignores that retained `visit` when it computes buckets:

```text
GoCompile.v:6162
  buckets := prog_package_refs idx
```

`prog_package_refs idx` expands to a second `prog_visit p`, which expands to a second `prog_blocks p` and a
second `Snap.visit_file` for each file. The adjacent comment claims the opposite.

**Required repair outcome:**

Factor one executable helper over the retained visit value, for example:

```coq
prog_package_refs_from_visit idx visit :=
  fold_right (ppkg_step idx) ... visit

prog_package_refs idx :=
  prog_package_refs_from_visit idx (prog_visit p)
```

Use `prog_package_refs_from_visit idx visit` inside `elaborate_indexed`. Prove the canonical helper equality once
and reuse the current exactness theorems. Audit the final public path for every remaining `prog_visit`,
`prog_blocks`, and `visit_file` evaluation so the “one retained traversal” claim is true in executable code, not
only extensionally.

This is one root finding. All affected comments, performance claims, and gate surfaces must be corrected in the
same repair.

### 2. The fresh-build runner can silently omit source files and return success

**Classification:** Trust / fail-open defect

The central runner is in `Dockerfile:658-679`.

It suppresses `find` errors in command substitutions:

```sh
_foreign=$(find ... 2>/dev/null)
_empty=$(find ... 2>/dev/null)
```

It also copies and verifies files through `find | while` pipelines:

```sh
find . -name '*.go' -type f | while ...
find . (...) -type f | while ...
```

The stage uses `set -u`, not fail-closed pipeline handling. A failed `find` can produce an empty result, the
pipeline can still return success, only `go.mod` can be materialized, and the fake or real command can be invoked
on the incomplete tree.

I reproduced the control-flow defect by putting failing `find` and successful `go` shims first on `PATH`. The
runner returned `rc=0`; its fresh root contained `go.mod` but omitted the authoritative `main.go`.

**Required repair outcome:**

Use checked manifest files and explicit command-status handling:

1. enumerate the authoritative file set to a temporary manifest and fail if enumeration fails;
2. validate the manifest before creating or populating the fresh root;
3. materialize every manifest entry, checking every operation;
4. independently enumerate the fresh root to a second manifest and fail if enumeration fails;
5. compare exact path sets and bytes;
6. invoke Go only after exact materialization succeeds.

Do not rely on shell pipelines whose producer status is discarded. Do not hide observation errors with
`2>/dev/null` unless the error is captured and treated as failure.

Keep this small. It is a fail-closed manifest copy, not a new filesystem security subsystem.

The runner currently claims that it rejects `.fido`, VCS state, nested modules, and all extras. Its checks do not
fully establish that claim: a `.fido` or `.git` directory containing `.go` files is not excluded merely by the
shown predicates. Choose one honest boundary:

- accept only an exact manifest supplied by the authoritative DirectoryImage export and compare it exactly; or
- narrow the runner claim to the already-certified pristine export it actually consumes.

Do not duplicate the full FilePath grammar in shell.

### 3. The advertised general publication command still sinks before fresh-build validation

**Classification:** Production integration defect / capability-boundary mismatch

The active contract says every certified `DirectoryImage` is fresh-built before publication and says to refactor
if `Fido Emit` performs sink effects first.

The public plugin path still does this directly:

```text
plugin/g_fido.mlg:199-205
  decode DirectoryImage transport
  Fido_sink.sync dir go_mod entries
```

The witness files call `Fido Emit ... To ...`, and Docker's `emit` stage synchronizes those trees before the
`go-e2e` fresh build. The canonical `sync` image is later gated by a `/validated` marker from `go-e2e`, so the
tracked regenerate path has a fresh-build gate. The advertised general `Fido Emit` command does not.

Current permanent docs repeatedly call `Fido Emit` the one general output transport and publication command.
That makes the real public capability broader than the proved fresh-build contract.

**Required repair outcome:**

Establish one honest public workflow:

```text
proved DirectoryImage
  -> exact pristine export
  -> fresh disposable literal build validation
  -> sync the original pristine image
```

No public or documented publication path may sink an unvalidated image.

The low-level Rocq transport decoder may remain, but then it must be clearly internal/export-only and not be
advertised as the final publication capability. A high-level wrapper may orchestrate validation and sink work.
Do not move Go semantics into handwritten OCaml, do not build in the sink destination, and do not publish the
post-build workspace.

Update all public docs and Make targets to name the actual supported workflow.

### 4. The old “exactly one main” source judgment remains a live public authority

**Classification:** Competing semantic authority / stale root

At the top of `GoCompile.v` the old root remains:

```text
GoCompile.v:75-87
  AllPackagesOneMain
  ProgValid := ProgramTyped /\ AllPackagesOneMain
  prog_ok
  prog_ok_iff
```

The corrected factorization appears much later:

```text
GoCompile.v:5784-5789
  PackageDeclsUnique
  MainPackagesHaveEntry
  PackageRulesValid
  SourceProgramValid
```

The code then proves the new root equivalent to the old one and keeps both names active:

```text
GoCompile.v:5791-5803
  current_package_rules_exactly_one
  source_program_valid_iff : SourceProgramValid <-> ProgValid
```

The final `GoCompile` uses `SourceProgramValid`, but the old root remains widely named, documented, and gated.
This leaves two public conceptual authorities and makes permanent headers describe the superseded rule as the
primary semantics.

**Required repair outcome:**

Make `SourceProgramValid` the only live source-validity root.

Keep one theorem that states the current grammar consequence:

```text
PackageRulesValid <-> every current package has exactly one DMain
```

Do not keep `AllPackagesOneMain` or old `ProgValid` as peer public roots. Either delete them after proving the
bridge in a local section, or rename/confine a minimal historical specification helper so it cannot be mistaken
for the source judgment or used by production.

Define any retained executable source decision directly against the factored rules and prove its reflection
there. Remove superseded gate entries and permanent prose.

`elaborate_valid_of_no_diags` at `GoCompile.v:6144-6146` returns the old `ProgValid` and appears unused. Delete it.
The generic `result` and `bool_sumbool` definitions at `GoCompile.v:6396-6400` also appear unused after the new
`CompileOutcome` path. Delete them after a final call-site check.

### 5. Permanent documentation still states superseded architecture

**Classification:** Documentation contradiction / stale residue

Examples:

- `GoIndex.v:20-28` says “C2 in progress” and lists completed navigation and reference work as pending.
- `dune:3` omits the permanent indexing and elaboration phases and describes the old package-grouping compiler.
- `Dockerfile:7-10` still says `ProgValid = ProgramTyped + one-main-per-package`.
- `GoCompile.v` begins with the old exactly-one-main/prog_ok story rather than the current source/command split.
- the gate still names old `ProgValid`, analysis, and exact-one helper surfaces.
- `.review/SOURCE_FOREST_STATUS.md` has the current C3 section plus historical C3, C2, C1B, C1A, C1, C0B, and C0A
  headings still marked `ACTIVE`.

**Required repair outcome:**

Reconcile all current authority documents and permanent module headers in one pass. Historical details may
remain, but only one checkpoint is active. Source headers state permanent responsibility, not campaign status.

The status ledger is now over 1,000 lines and has become close to a second plan. C6 may compact its history, but
this repair must at least correct active labels and current summaries so no live authority contradicts the code.

## Required simplifications and overreach corrections

### 6. Replace the 571-line string-proof expansion with one component-level root

**Classification:** Missing root abstraction papered over by proof length

Between `fido-main (71).zip` and this snapshot, `GoCompile.v` grew by exactly 571 lines, with 571 insertions and
no deletions. The additions form four proof blocks around import-path string shape and executable-name
nonemptiness.

The new region begins near `GoCompile.v:4697` and introduces:

- `str_starts_slash`;
- `str_ends_slash`;
- `str_no_double_slash`;
- append and tail lemmas;
- basename and dirname shape proofs;
- split/join reconstruction proofs;
- module-path and file-parent canonical-string proofs;
- `package_import_path_canonical`;
- the final executable-name nonempty proof.

The target cmd/go rule is component-based: choose the last import-path component, or the prior component when the
last is a valid major-version element. The implementation proves this through a large parallel character-level
canonicality system.

**Required repair outcome:**

Introduce or reuse one canonical component view derived from the existing intrinsic `ModulePath` and package
directory components. Compute and characterize the last/previous component there, then bridge once to the
rendered import-path string.

Do not create a second parallel import-path authority. Prefer existing `split_slash`/component data and a small
proof-only view over a new public datatype when possible. The refactor should delete substantially more code than
it adds.

Retain the exact cmd/go behavior, all required computed fixtures, and a universal nonempty result theorem.
Delete the redundant character-level proof ecosystem after the bridge is complete.

This is a semantic/proof-root correction, not the broad physical module split reserved for C6.

### 7. Reduce the readable assumption gate to load-bearing surfaces

**Classification:** Review-driven proof-surface overgrowth

`gate/axiom_gate.v` contains 578 `Print Assumptions` commands in this snapshot.

The project also runs a whole-certified-theory assumption-closure audit over every declaration. The readable gate
is therefore most valuable as a focused public-claim audit, not as a second listing of every concrete fixture,
intermediate helper, historical authority, and local proof.

**Required repair outcome:**

Keep readable assumption checks for:

- public semantic roots;
- load-bearing exactness and reflection theorems;
- capability provenance;
- trust and output-boundary claims;
- universal ordering, soundness, completeness, and determinism claims.

Remove:

- concrete fixture-only surfaces whose declarations still compile and remain covered by the whole-theory audit;
- superseded weaker theorems;
- old exactly-one/analysis authorities;
- internal helper lemmas added only to prove a gated public theorem.

Do not weaken the whole-theory audit or remove concrete tests. The goal is a smaller, clearer claim surface, not a
smaller proof closure.

### 8. Remove the giant checkpoint-specific Codex attack list from permanent reviewer guidance

**Classification:** Review-process overenumeration

The active contract contains a large late-stage Codex-specific attack list. It was useful as emergency steering,
but it mixes implementation requirements with reviewer instructions and biases the reviewer toward listed leaves.

**Required repair outcome:**

Install the generalized two-review policy. Add a short amendment to the active contract saying that review
cadence and review output are governed by `.review/CODEX_REVIEW_POLICY.md` and the accepted review basis.

Do not rewrite the whole active contract or delete its functional requirements. Mark its old review-cadence and
attack-list sections as historical/superseded for review procedure.

For future checkpoints, Contract Review produces a compact `.review/REVIEW_BASIS.md`; do not create a permanent
catalogue of current bugs.

### 9. Share canonical and retained builders rather than maintaining peer logic

**Classification:** Simplification / authority hardening

The code contains readable canonical specifications and executable retained-input variants for package buckets,
fresh plans, and diagnostics. This is legitimate when one is clearly a specification and one is the production
implementation, but several definitions duplicate the same decision shape.

**Required repair outcome:**

Factor one shared builder over explicit inputs where practical:

- package buckets over a supplied visit stream;
- fresh build plan over module, package keys, and root layout;
- command-facing diagnostics over a supplied retained plan.

Define the source-only convenience functions by applying that shared builder to canonical inputs. Prove the
bridge once. Keep readable specification theorems, but do not leave peer executable authorities that can drift.

## Review-process repair

The permanent review process should use only:

- **Contract Review**
- **Implementation Review**

Both are complete-pass reviews. A blocker never ends the pass. Codex must search the full blast radius of each
root defect before returning it.

A tiny `.review/REVIEW_REQUEST.md` gate prevents the stop hook from performing a full review after every ordinary
Claude turn. `.review/REVIEW_BASIS.md` stores the compact accepted Contract Review result for the active
checkpoint.

A blocked review gets one complete repair batch and one bounded confirmation. A finding first discovered during
confirmation is classified as repair-induced, previously observable and missed, contract ambiguity, new scope,
or outside scope.

The policy must remain general. It must not encode C3, Go diagnostics, current filenames, or this audit's defect
list.

## Recommended C3 closeout order

1. Install the permanent review policy, stop-hook prompt, review-request gate, and review-basis format.
2. Record this human audit as C3's accepted review basis; do not run a retroactive Contract Review over code that
   already exists.
3. Fix the repeated package traversal.
4. Make the fresh runner fail closed and exact.
5. close the publication-before-validation gap.
6. remove the old source semantic authority and dead helpers.
7. replace the string-proof expansion with the component-level root.
8. prune the readable assumption surface while preserving the whole-theory audit.
9. reconcile permanent docs, headers, status labels, and active-contract review amendments.
10. run the full proof, e2e, byte, and staged checks.
11. freeze one candidate and request one holistic **Implementation Review** against the complete C3 range and
    accepted review basis.
12. repair the complete finding batch, if any, then run one bounded confirmation.

## Approval standard

C3 is ready for human approval only when:

- the real elaboration performs one source traversal;
- the fresh runner cannot treat observation/copy failure as success;
- every supported public publication path fresh-validates before sink effects;
- the factored source judgment is the only live semantic root;
- the executable-name proof has a clear component-level foundation rather than hundreds of compensating string
  lemmas;
- the readable gate exposes the real public claim surface;
- permanent docs and status name one current architecture;
- full verification is green;
- the one holistic Implementation Review is GREEN, with at most one bounded confirmation.
