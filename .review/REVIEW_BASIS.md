# C3 Accepted Review Basis — Human Manual Audit

checkpoint: C3 Fresh-Image Literal-Build Final Repair
contract: .review/C3_FRESH_IMAGE_LITERAL_BUILD_PLAN.md
contract_alias: .review/NEXT_STEPS.md
contract_sha256: a13779c2e55c679e461e857d019eeae6adef27b0666876ed0cac92833814f212
checkpoint_baseline: fea649389ee52d442373c43ea2bdb3be2eca47db
snapshot_audited: de6bd759d8fe1977bc196b5aaed04aa60b9560b1
basis_authority: Rob's requested manual audit, recorded before C3 closeout

## Material claim surface

1. **One source and occurrence foundation**
   - one raw specification-shaped AST;
   - one retained snapshot-local structural index;
   - no typed, resolved, copied, or parent-linked AST.

2. **One semantic elaboration root**
   - one production `elaborate` execution;
   - one retained indexed traversal;
   - occurrence-keyed facts and exact structured diagnostics;
   - `go_compile` only projects the retained elaboration result.

3. **Exact source/package semantics**
   - package-block declaration uniqueness and main-entry validity are independent roots;
   - their current exactly-one consequence is proved, not used as the permanent root;
   - source diagnostic soundness, completeness, multiplicity, anchors, precedence, and canonical order are exact.

4. **Exact fresh-image literal-build semantics**
   - selected packages, import paths, executable naming, fresh root layout, overwrite classes, and directory
     collision follow the pinned one-shot `go build ./...` contract;
   - command preflight precedence is modeled;
   - full planning includes every real semantic input, including ModuleSpec.

5. **One immutable publication artifact**
   - DirectoryImage is the authoritative source image;
   - fresh build runs in a disposable exact materialization;
   - no post-build byte is published;
   - every supported public publication workflow validates before sink effects.

6. **Trust and output**
   - zero project assumptions;
   - fail-closed gates and operational wrappers;
   - standard collections only;
   - existing generated Go source bytes remain unchanged;
   - C4 work remains absent.

## Blocking defect classes

- a second executable index, traversal, package decision, semantic decision, or capability path;
- a source/package rule that is only accidentally correct for the current grammar;
- a literal-build plan that omits a real input or diverges from the pinned command;
- a fail-open fresh runner (an infrastructure failure taken as a Go outcome), or fail-open copying, proof, or
  publication;
- a public publication path that bypasses fresh validation;
- facts or diagnostics that copy syntax, lose identity, deduplicate evidence, misorder results, or prove only a
  weaker/vacuous claim;
- a missing root abstraction hidden by local bridges, repeated computation, large proof scaffolding, sorting, or
  fixture volume;
- unapproved language, semantic, operational, collection, or public capability scope;
- a production path different from the proved and tested path;
- stale current documentation or gate surfaces that preserve a superseded authority;
- assumption, staged-tree, e2e, or generated-byte drift.

## Evidence required at Implementation Review

- executable call-path evidence for one index and one source visit;
- exact source and command soundness/completeness theorems;
- retained-fact and capability-provenance theorems;
- universal diagnostic soundness, completeness, multiplicity, ordering, precedence, and determinism surfaces;
- exact DirectoryImage/fresh-layout bridge;
- a fail-closed fresh disposable-copy runner that classifies infrastructure failure apart from a Go build
  outcome, plus the exact DirectoryImage/generated-layer byte bridge (no checksum or manifest substitute);
- proof that every supported publication path validates first and sinks the original image;
- standard-collection audit;
- readable load-bearing assumption gate plus whole-theory closure audit;
- full pinned-Go differential matrix;
- full `make check`, staged verification, and source-byte identity;
- current permanent documentation and status authority.

## Forbidden overreach

- new C4 or later syntax or semantics;
- a second AST or semantic authority;
- custom collection or sort machinery;
- Go semantics in handwritten OCaml;
- build in the sink or authoritative tree;
- publication of a post-build tree;
- broad physical module reorganization reserved for C6;
- platform resource-limit modeling outside the accepted contract;
- giant reviewer-specific defect catalogues in permanent Codex policy;
- compatibility surfaces with no approved consumer;
- proof or test growth that preserves a missing root instead of fixing it.

## Accepted manual closeout findings

The implementation must close the findings in `MANUAL_C3_AUDIT.md` before requesting Implementation Review:

1. repeated package traversal;
2. fail-open fresh runner;
3. publication-before-validation gap;
4. old exactly-one source authority and dead helpers;
5. stale permanent documentation and active labels;
6. character-level executable-name proof overarchitecture;
7. readable gate overgrowth;
8. review-process overenumeration;
9. duplicated canonical/retained builders where one shared root is practical.

## Use

This is C3's accepted review basis because implementation already existed when the permanent Contract Review
process was introduced. Do not run a retroactive open-ended Contract Review for C3. Future checkpoints must run
Contract Review before implementation.

Implementation Review must still independently assess correctness, missing roots, competing authorities,
underimplementation, and overimplementation. This basis is not a waiver for defects omitted from the manual
finding list.
