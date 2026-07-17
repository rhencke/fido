Claude Code correction checkpoint: C0B — exact source-occurrence correspondence

THIS IS A BINDING CORRECTION CHECKPOINT INSIDE THE EXISTING SOURCE FOREST CAMPAIGN.

It does not activate C1.

The persistent campaign architecture remains in:

  .review/SOURCE_FOREST_MASTER_PLAN.md

The current repository baseline for this correction is:

  46a9d65092a58dacb805f34acd2ad1269886a54e

That baseline contains the completed, Codex-green C0 and C0A proof spikes.

Keep all existing C0 and C0A commits.

Do not rewrite, squash, reset, rebase, or force-push their history.

===============================================================================
0. BEFORE IMPLEMENTATION
===============================================================================

1. Stop any currently running `/loop`.

2. Read, in full:

   - `.review/SOURCE_FOREST_MASTER_PLAN.md`
   - `.review/SOURCE_FOREST_STATUS.md`
   - `.review/CODEX_REVIEW_POLICY.md`
   - `.review/NEXT_STEPS.md`
   - `OccurrenceSpike.v`

3. Read the C0A commit sequence:

   30d0d51c71b01dded1c60f8fff6cace955a34621
   0e6b7397d2e4bdc9835cc8e828b1c7a597500ffa
   5176e7b8e078a17025d93f5e703b0899d968ed38
   357430b38db94358c6a43db9647c01039cc0eda4
   c74cb0aac8746e86a1fa798ab27fa9ba8e5cd7a7
   46a9d65092a58dacb805f34acd2ad1269886a54e

4. Replace:

   .review/NEXT_STEPS.md

   with this directive VERBATIM.

   - Do not summarize it.
   - Do not rewrite it.
   - Do not omit sections.
   - Do not weaken its theorem statements.
   - Do not broaden its feature scope.

5. Update:

   .review/SOURCE_FOREST_STATUS.md

   to record:

   - active checkpoint: C0B;
   - correction baseline SHA: `46a9d65092a58dacb805f34acd2ad1269886a54e`;
   - C0A remains Codex-green history;
   - human review found one remaining under-specification:
     the index is proved structurally consistent with `build_file`, but `build_file`
     is not yet proved universally to label each exact source occurrence with the
     correct kind, role, parent, and subtree boundary;
   - C1 remains forbidden until C0B is human-approved.

6. Commit the C0B contract/status activation before implementation.

   Commit message prefix:

     milestone(contract): C0B —

7. Then run exactly:

   /loop 5m completing NEXT_STEPS until codex review is green and then notify me and stop the loop.

The loop is authorized only for C0B.

C0B uses two intentional Codex barriers:

1. semantic-root review;
2. final exhaustive review.

Do not intentionally stop for progress narration, routine proof work, ordinary
compilation, fixtures, gate updates, or documentation.

The final notification and loop stop happen only after the FINAL barrier is GREEN.

===============================================================================
1. WHY C0B EXISTS
===============================================================================

C0 and C0A established a strong occurrence-navigation design:

- immutable downward-owned syntax trees;
- path-unique source snapshots;
- file-local positive preorder IDs;
- root local ID = 1;
- abstract pure-Gallina positive-key radix tries;
- `SyntaxIndex fs`, `FileRef fs`, and `NodeRef fs` indexed by the exact source
  snapshot;
- exact outer index construction;
- total metadata, kind, role, containing-file, and children queries;
- only `parent_of` optional;
- no file-list scan during ordinary navigation;
- list-free direct-child interval jumps;
- parent/child inversion;
- source-ordered children;
- source-snapshot-local identity;
- no typed AST;
- zero axioms.

Keep those decisions.

The remaining defect is not a bad data structure.

It is an under-specified theorem boundary.

Today, the implementation proves that:

  SyntaxIndex fs

contains exactly:

  outer_of fs

and that each file slot contains:

  build_file f

It also proves that the tables produced by `build_file` are structurally
well-formed:

- entries occupy canonical intervals;
- non-roots have parents;
- parent links are nested;
- subtree intervals are valid;
- ancestry and child enumeration are correct.

But the universal theorem family does not yet prove:

> The metadata stored at local ID N is the metadata of the exact source
> occurrence at local ID N.

In particular, the existing theorem family would not necessarily fail if the
builder were changed to make a structurally consistent but semantically wrong
labeling such as:

- a leaf expression marked `KDecl`;
- a binary expression marked `KStatement`;
- the left child marked `RChild 1`;
- the right child marked `RChild 0`;
- declaration indexes shifted by one;
- statement indexes shifted by one.

The table could remain navigable and interval-correct while diagnostics,
typed-reference refinement, declaration identity, and compiler facts attach to
the wrong source occurrence.

C0B closes that exact gap.

The new permanent root is:

  exact source occurrence
      -> independently specified source metadata
      -> canonical builder metadata
      -> sealed NodeRef query

The source specification must be independent of the metadata builder.

The proof must be universal.

Concrete fixtures supplement that theorem but do not replace it.

===============================================================================
2. NON-NEGOTIABLE ARCHITECTURE
===============================================================================

Keep unchanged:

- `TForest` path uniqueness;
- exact source-snapshot indexing;
- `SyntaxIndex fs`;
- `FileRef fs`;
- `NodeRef fs`;
- public `NodeKey = (FilePath, local ID)`;
- hidden file slots;
- file-local positive preorder IDs;
- `root_id = 1`;
- `NodeMeta` fields:
  - kind;
  - parent local ID;
  - role;
  - subtree end;
- abstract `NodeTable`;
- positive-key radix-trie implementation;
- exact outer table equality:
  - `si_outer = outer_of fs`;
- total validated-reference queries;
- list-free `child_enum`;
- no syntax subtree in `NodeMeta`;
- no production AST migration yet.

Correct:

- the missing per-occurrence source/metadata specification;
- the public source-recovery API;
- the raw slot abstraction leak;
- three stale documentation statements.

Do not add:

- C1 `GoSourceFile`;
- production `GoFileSet`;
- production `GoIndex`;
- diagnostics;
- source type syntax;
- numeric types;
- structural types;
- imports;
- functions beyond the toy grammar;
- parent pointers;
- author-supplied IDs;
- typed AST;
- flattened syntax caches;
- a second recursive source tree;
- primitive arrays;
- list-backed node lookup;
- new Go behavior.

The spike remains isolated and temporary.

Generated Go bytes must remain unchanged.

===============================================================================
3. DEFINE AN INDEPENDENT SOURCE-OCCURRENCE SPECIFICATION
===============================================================================

3.1 Purpose

Add one table-free source-occurrence specification for the toy grammar.

It must answer:

  For source file f and local preorder ID n,
  what exact source occurrence does n designate,
  and what metadata should that occurrence have?

This is the semantic specification against which `build_file` is proved correct.

It is not:

- a second mutable AST;
- a replacement source tree;
- a navigation cache;
- a NodeTable;
- a production compiler structure;
- a hot-path random-access promise.

3.2 Preferred typed source view

Prefer a kind-indexed view that reuses the original syntax fragments:

  Inductive SyntaxView : SyntaxKind -> Type :=
  | ViewFile :
      TFile ->
      SyntaxView KFile

  | ViewDecl :
      TDecl ->
      SyntaxView KDecl

  | ViewStatement :
      TStmt ->
      SyntaxView KStatement

  | ViewExpression :
      TExpr ->
      SyntaxView KExpression.

Names may differ.

Equivalent sigma/record encoding is acceptable.

The view must refer to the original syntax value.

Do not invent a parallel recursive grammar with independently copied children.

3.3 Source occurrence

Define a source occurrence carrying the exact independently derived structural
facts, conceptually:

  Record SourceOccurrence := {
    occurrence_kind        : SyntaxKind;
    occurrence_view        : SyntaxView occurrence_kind;
    occurrence_parent      : option positive;
    occurrence_role        : NodeRole;
    occurrence_subtree_end : positive
  }.

The local ID may be:

- an input to the lookup function; or
- an additional field.

Either is acceptable.

Define:

  occurrence_meta :
    SourceOccurrence ->
    NodeMeta

as exactly:

  mkMeta
    occurrence_kind
    occurrence_parent
    occurrence_role
    occurrence_subtree_end

Do not let `occurrence_meta` consult the builder or NodeTable.

3.4 Table-free lookup

Define:

  source_occurrence_at :
    TFile ->
    positive ->
    option SourceOccurrence

or an equivalent declarative relation plus reflected executable lookup.

The implementation must derive its answer directly from the source tree.

It must not call or inspect:

- `NodeTable.get`;
- `NodeTable.set`;
- `build_expr`;
- `build_stmt`;
- `build_decl`;
- `build_seq`;
- `build_file`;
- `FileIndex`;
- `SyntaxIndex`;
- `ref_meta`;
- `node_kind`;
- `node_role`;
- `parent_of`;
- `children_of`;
- `child_enum`.

The source specification may use table-free structural helpers such as:

- `end_expr`;
- `end_stmt`;
- `end_decl`;
- `next_stmts`;
- `next_decls`;
- independently defined source sizes or boundaries.

Those helpers must themselves be functions only of the source syntax and the
starting local ID.

3.5 Coverage of the complete toy grammar

The specification must cover every currently indexed toy occurrence:

- file root;
- each declaration;
- each statement;
- each expression;
- every nested expression occurrence.

It must derive the exact current roles:

- file root:
  - `RFileRoot`;

- declaration N:
  - `RFileDecl N`;

- statement N in a declaration:
  - `RDeclStmt N`;

- expression directly held by a print statement:
  - `RStmtExpr`;

- expression child N:
  - `RChild N`.

It must derive exact parent IDs.

It must derive exact subtree ends.

It must preserve source order.

3.6 Independence audit

At the semantic-root barrier, include an explicit audit in the commit message:

- functions used by `source_occurrence_at`;
- confirmation none call the metadata builder or NodeTable;
- confirmation the builder does not call `source_occurrence_at`;
- confirmation the two sides share only ordinary source datatypes and
  independently acceptable table-free arithmetic helpers;
- confirmation no theorem is proved merely by unfolding two aliases of the same
  implementation.

If the source specification is merely `build_file` translated into another
name or projected back out of its table, classify that as an architectural
failure and stop.

===============================================================================
4. PROVE EXACT PER-FILE SOURCE/METADATA CORRESPONDENCE
===============================================================================

4.1 Load-bearing theorem

Prove one universal theorem equivalent to:

  Theorem build_file_source_exact :
    forall (f : TFile) (local : positive),

      NodeTable.get local (fi_table (build_file f))

      =

      option_map occurrence_meta
        (source_occurrence_at f local).

Names may differ.

The equality direction may be reversed.

A logically equivalent iff theorem is acceptable:

  NodeTable.get local ... = Some meta
  <->
  exists occurrence,
    source_occurrence_at f local = Some occurrence
    /\ meta = occurrence_meta occurrence.

The theorem must prove both presence and absence.

It must not require an already-existing `NodeRef`.

It must not assume the queried local ID is valid.

It must range over every positive local ID.

4.2 Consequences that must be explicit

Derive and gate:

A. Source occurrence -> metadata

  source_occurrence_at f local = Some occurrence
  ->
  NodeTable.get local (fi_table (build_file f))
    = Some (occurrence_meta occurrence).

B. Metadata -> source occurrence

  NodeTable.get local (fi_table (build_file f)) = Some meta
  ->
  exists occurrence,
    source_occurrence_at f local = Some occurrence
    /\ meta = occurrence_meta occurrence.

C. Absence equivalence

  source_occurrence_at f local = None
  <->
  NodeTable.get local (fi_table (build_file f)) = None.

D. Unique occurrence

  source_occurrence_at f local = Some o1
  ->
  source_occurrence_at f local = Some o2
  ->
  o1 = o2.

E. Kind exactness

  a source occurrence's kind is exactly the stored `nm_kind`.

F. Role exactness

  a source occurrence's role is exactly the stored `nm_role`.

G. Parent exactness

  a source occurrence's parent is exactly the stored `nm_parent`.

H. Subtree-boundary exactness

  a source occurrence's subtree end is exactly the stored `nm_subtree_end`.

4.3 Exactness is stronger than structural well-formedness

Keep `SubtreeWF`, `ForestWF`, parent/child, ancestry, and interval theorems.

Do not delete them.

But document the distinction:

  structural theorem:
    the table forms a coherent occurrence tree;

  source-correspondence theorem:
    that coherent occurrence tree describes the exact source tree.

Neither subsumes the other.

4.4 No proof by concrete evaluation alone

`vm_compute` fixtures are useful.

They do not satisfy this section.

The universal theorem must be closed axiom-free.

===============================================================================
5. SEMANTIC-ROOT REVIEW BARRIER
===============================================================================

Stop for the ROOT review only after all of the following are true:

- `SourceOccurrence` or an equivalent independent source specification exists;
- `source_occurrence_at` covers the complete toy grammar;
- it is table-free and builder-independent;
- the universal exact per-file theorem is proved;
- presence and absence are both pinned;
- kind, role, parent, and subtree end are all included in the equality;
- no second AST or persistent flattened source cache exists;
- all root theorem assumptions are closed;
- generated bytes remain unchanged;
- C1 has not begun.

Commit:

  milestone(root): C0B — independent source occurrence specification and exact builder correspondence

Any Codex-driven root repair must use:

  review(root): C0B —

After root review becomes GREEN, continue directly to final integration.

Do not stop again until the final barrier.

If Codex finds that the source specification is circular, builder-derived, or
too weak to detect wrong kind/role labels, repair the root before continuing.

===============================================================================
6. LIFT EXACTNESS THROUGH THE SEALED SNAPSHOT API
===============================================================================

6.1 Total occurrence recovery from a NodeRef

For every valid:

  r : NodeRef fs

provide a total source-occurrence view, conceptually:

  source_occurrence_of_ref :
    NodeRef fs ->
    SourceOccurrence.

It may internally use:

  source_occurrence_at
    (file_ref_file (node_ref_file r))
    (node_ref_local r)

plus a proof that this option is `Some`.

No semantic fallback is permitted.

No `option` should remain at the public valid-reference layer if `NodeRef`
validity proves the occurrence exists.

Names may differ.

6.2 Load-bearing sealed theorem

Expose through `SNAP_SIG` a theorem equivalent to:

  ref_meta_matches_source :
    forall fs
           (idx : SyntaxIndex fs)
           (r : NodeRef fs),

      ref_meta idx r

      =

      occurrence_meta (source_occurrence_of_ref r).

This is the permanent public theorem.

It says:

> The metadata returned for this valid source reference is the metadata of this
> exact source occurrence.

6.3 Public projections

Derive and expose:

  node_kind_matches_source

  node_role_matches_source

  node_parent_matches_source

  node_subtree_end_matches_source.

The parent theorem may be phrased through metadata or `parent_of`.

At minimum, pin:

  nm_parent (ref_meta idx r)
  =
  occurrence_parent (source_occurrence_of_ref r).

For non-root occurrences, connect the parent local ID to the returned
`parent_of` reference.

6.4 Exact source fragment view

The source-occurrence view must recover the original syntax fragment.

For example:

  ViewExpression (TLeaf 5)

not merely:

  KExpression.

The existing expression-only `node_at` helper must be handled in one of these
ways:

Preferred:

- delete it and replace it with the general total source-occurrence/source-view
  API;

Acceptable:

- retain it only as a convenience projection from the new general occurrence
  specification;
- prove it agrees with `source_occurrence_of_ref`;
- do not leave it as an independent recursive source locator.

Do not keep two separate source-recovery authorities.

6.5 No hot-path claim

The table-free source-occurrence lookup is a proof and occasional inspection
facility.

It may cost proportional to a source prefix or, in the worst case, the file
size.

State that honestly.

Ordinary compiler traversal in production C2 will receive:

  original syntax fragment + canonical NodeRef

together.

Ordinary metadata navigation continues to use the index.

Do not optimize proof-only source recovery by storing a copied syntax tree in
metadata.

===============================================================================
7. REMOVE THE PUBLIC RAW-SLOT ABSTRACTION LEAK
===============================================================================

`SNAP_SIG` currently exposes:

  index_at :
    SyntaxIndex fs ->
    positive ->
    option FileIndex.

That exposes arbitrary physical file-slot inspection and the raw `FileIndex`
representation.

The hidden file slot is an optimization handle, not a public semantic identity.

Remove `index_at` from `SNAP_SIG`.

It may remain:

- private inside `Snap`; or
- as a local/internal definition used to prove outer-table exactness.

Do not expose arbitrary slot lookup as a public navigation API.

Retain internal exact outer-index construction:

  si_outer = outer_of fs.

Retain internal absence/presence proofs.

Replace the public raw-slot theorem with the stronger validated-reference
theorem:

  ref_meta_matches_source.

After sealing, add a negative abstraction fixture such as:

  Fail Check OccurrenceSpike.Snap.index_at.

Equivalent module-abstraction evidence is acceptable.

Also keep negative fixtures confirming raw constructors remain hidden:

  mkSyntaxIndex
  mkFileRef
  mkNodeRef.

===============================================================================
8. MUTATION-SENSITIVE REGRESSIONS
===============================================================================

8.1 Purpose

Concrete regressions should make the universal theorem's consequences obvious.

They are not substitutes for the universal theorem.

8.2 Existing same-shape snapshots

Keep:

- `fs_a` with leaf payload 5;
- `fs_b` with leaf payload 6;
- erased index data equal;
- reference types non-interchangeable;
- exact source view differs by payload;
- repeated equal leaves in `fs_a` have distinct references.

Restate the payload recovery through the new general source-occurrence API.

8.3 Kind fixtures

Pin at least:

- file root -> `KFile`;
- function declaration -> `KDecl`;
- print statement -> `KStatement`;
- leaf expression -> `KExpression`;
- binary expression -> `KExpression`.

Each fixture must derive from:

  ref_meta_matches_source

or the universal per-file exact theorem.

Do not prove them by independently unfolding the builder.

8.4 Role fixtures

Use a witness that covers:

- at least two declarations;
- at least two statements in one declaration;
- a nested binary expression.

Pin:

- declaration 0 -> `RFileDecl 0`;
- declaration 1 -> `RFileDecl 1`;
- statement 0 -> `RDeclStmt 0`;
- statement 1 -> `RDeclStmt 1`;
- print-held expression -> `RStmtExpr`;
- left binary child -> `RChild 0`;
- right binary child -> `RChild 1`.

8.5 Parent fixtures

Pin exact parent local IDs for the same witness:

- declarations parented by file root;
- statements parented by their declaration;
- print expression parented by its statement;
- binary children parented by the binary expression.

8.6 Subtree fixtures

Pin representative subtree ends:

- leaf end = own ID;
- binary end = rightmost descendant;
- statement end = expression end;
- declaration end = final statement descendant;
- file root end = final occurrence.

8.7 Mutation criterion

The new universal theorem or its gated corollaries must fail if any of these
hypothetical mutations is made:

- `TLeaf` metadata kind changed to `KDecl`;
- `TBin` metadata kind changed to `KStatement`;
- left and right `RChild` indexes swapped;
- declaration index incremented incorrectly;
- statement index incremented incorrectly;
- parent ID changed while intervals remain nested;
- subtree end changed while the table remains populated.

Record in the completion report which theorem statements are mutation-sensitive
to each category.

Do not add deliberately broken tracked code or axiom fixtures.

===============================================================================
9. RECONCILE THE MASTER PLAN AND STATUS
===============================================================================

9.1 Root ID

The master plan still contains conceptual/public text saying:

  file root local ID = 0

or:

  every file root has local ID zero.

C0 selected positive IDs with:

  root_id = 1.

Update every active architectural statement to say:

  file root local ID = 1

or, where representation independence is intended:

  one fixed canonical root local ID
  (currently positive 1).

Do not leave contradictory root-ID laws in the active plan.

9.2 Final SyntaxIndex invariant

The C0A decision record has an earlier paragraph describing the superseded
one-directional invariant:

  real slots hold their file build.

Rewrite the headline decision record to the final invariant:

  si_outer = outer_of fs

with exact presence and absence.

Keep the historical review ledger explaining how Codex found and repaired the
earlier fail-open version.

Do not rewrite history.

9.3 Source-recovery complexity

The master plan currently suggests occasional source recovery may cost O(depth).

The toy `source_occurrence_at`/`occ_file` style lookup can traverse preceding
siblings and recompute structural boundaries.

State the honest bound:

- proof/inspection source recovery may be O(file size) in the worst case;
- it is not used by ordinary parent/kind/role navigation;
- production traversal supplies syntax and NodeRef together;
- no copied source cache is justified now.

9.4 Exact source correspondence

Add the new permanent law to the master plan:

> The production GoIndex must prove not only structural tree validity and exact
> outer-table construction, but exact per-occurrence correspondence between the
> source occurrence and its metadata: kind, role, parent, and subtree boundary.

Add it to the production C2 acceptance criteria.

9.5 Public storage abstraction

Update the master plan to say:

- raw file slots are hidden;
- no public arbitrary `index_at slot` operation;
- exactness is exposed through validated source references and theorem surfaces;
- internal physical-table inspection remains an implementation/proof detail.

9.6 Status ledger

Preserve:

- C0 history;
- C0A history;
- all prior Codex findings;
- all prior repair SHAs.

Add a C0B section recording:

- baseline;
- contract SHA;
- root candidate/reviews;
- final candidate/reviews;
- exact theorem names;
- mutation fixtures;
- gate count;
- verification;
- push;
- human disposition pending.

===============================================================================
10. PROOF AND ASSUMPTION GATE
===============================================================================

10.1 Required public surfaces

Gate at least:

Independent source specification

- source-occurrence lookup is deterministic;
- source view recovers the original fragment;
- file root source occurrence;
- declaration source occurrence;
- statement source occurrence;
- leaf source occurrence;
- binary source occurrence.

Exact per-file correspondence

- universal `build_file_source_exact`;
- source -> metadata;
- metadata -> source;
- absence equivalence;
- occurrence uniqueness;
- kind exactness;
- role exactness;
- parent exactness;
- subtree-end exactness.

Sealed reference layer

- total `source_occurrence_of_ref`;
- `ref_meta_matches_source`;
- `node_kind_matches_source`;
- `node_role_matches_source`;
- parent metadata matches source;
- subtree end matches source;
- exact source fragment recovery for `fs_a` and `fs_b`;
- equal leaves remain distinct references.

Existing foundations remain gated

- NodeTable laws;
- builder structural well-formedness;
- parent/child inverse;
- same-file navigation;
- ordered/NoDup children;
- interval ancestry;
- snapshot-local references;
- exact outer index;
- non-circular minting;
- no copied subtree metadata;
- no structural-equality deduplication.

10.2 Assumption closure

Every new public surface must print:

  Closed under the global context

with no axiom lines.

No:

- `Admitted`;
- `Axiom`;
- `Parameter` escape outside ordinary sealed module signatures implemented by
  closed definitions;
- primitive array assumptions;
- source-text axiom scanner.

The whole-theory audit must include the complete spike.

10.3 Abstraction checks

Add compile-time negative checks confirming these are not publicly accessible:

- raw `SyntaxIndex` constructor;
- raw `FileRef` constructor;
- raw `NodeRef` constructor;
- public raw-slot `index_at`.

Do not expose an equivalent raw storage escape under another name.

===============================================================================
11. PERFORMANCE AND RESPONSIBILITY AUDIT
===============================================================================

C0B must not regress the C0A performance shape.

Ordinary navigation from an existing `NodeRef` remains:

- containing file:
  - O(1) projection;

- metadata/kind/role/subtree end:
  - one outer slot lookup;
  - one per-file local lookup;

- parent:
  - same metadata lookup plus direct construction;

- children:
  - one file-index acquisition;
  - list-free interval jump proportional to direct children;

- ancestry:
  - same-file check;
  - metadata lookup;
  - constant arithmetic after lookup.

Raw-key minting remains a separate boundary:

- one path scan;
- one outer lookup;
- one local lookup;
- no per-file index rebuild.

The new source specification:

- is table-free;
- is not used by ordinary navigation;
- may be linear in source size;
- exists to specify and occasionally inspect exact source occurrences.

Responsibility audit:

- source syntax owns source fragments;
- source occurrence specification states what local IDs mean;
- builder constructs metadata;
- exact theorem connects them;
- index owns efficient navigation;
- NodeRef owns snapshot-local occurrence identity;
- no layer invents source semantics from a plausible fallback.

===============================================================================
12. FINAL REVIEW BARRIER
===============================================================================

After ROOT GREEN, complete:

- lift through `Snap`;
- total source occurrence recovery;
- public exactness theorem;
- delete/replace independent `node_at`;
- remove public `index_at`;
- mutation-sensitive fixtures;
- master-plan reconciliation;
- status update;
- assumption gate;
- complete verification.

Commit:

  milestone(final): C0B — seal exact source-occurrence correspondence through NodeRef

Any Codex-driven final repair must use:

  review(final): C0B —

The final Codex review must inspect the complete C0B range.

The final review should specifically answer:

1. Is the source occurrence specification independent of `build_file` and
   NodeTable?

2. Does the universal theorem pin kind, role, parent, and subtree end?

3. Does it prove absence as well as presence?

4. Can a valid NodeRef recover one exact source occurrence without fallback?

5. Is `ref_meta` universally proved equal to that occurrence's metadata?

6. Would wrong kind/role/index assignments break the theorem?

7. Is raw slot inspection absent from the public API?

8. Did any second AST, copied syntax cache, parent pointer, or typed AST appear?

9. Did ordinary navigation retain its established complexity?

10. Did C1 remain untouched?

After final GREEN:

- run complete verification again;
- run the staged-tree pre-commit gate;
- commit any ledger-only final GREEN record without changing code/proofs;
- fast-forward push;
- notify Rob;
- stop the loop;
- do not begin C1.

===============================================================================
13. ACCEPTANCE CRITERIA
===============================================================================

Workflow

- C0B directive copied verbatim into `.review/NEXT_STEPS.md`.
- Contract/status activation committed before implementation.
- Exact `/loop 5m ...` command started.
- At most two intentional Codex barriers used.
- Root and review repairs have distinct commit prefixes.
- Final and review repairs have distinct commit prefixes.
- No progress stops.
- C1 not started.
- Final GREEN reached.
- Verification green.
- Fast-forward push complete.
- Notification sent.
- Loop stopped.

Source occurrence specification

- Independent of NodeTable and builder.
- Covers every toy occurrence.
- Recovers exact original syntax fragments.
- Derives correct kind.
- Derives correct role.
- Derives correct parent.
- Derives correct subtree end.
- No persistent second AST.
- No copied syntax in metadata.

Exactness

- Universal per-file source/table equality.
- Presence both directions.
- Absence both directions.
- Unique source occurrence per local ID.
- Wrong metadata kind cannot satisfy theorem.
- Wrong role cannot satisfy theorem.
- Wrong parent cannot satisfy theorem.
- Wrong subtree end cannot satisfy theorem.
- Exact theorem is not merely concrete computation.

Sealed reference layer

- Every valid NodeRef has a total exact source occurrence.
- `ref_meta` equals source occurrence metadata.
- `node_kind` equals source occurrence kind.
- `node_role` equals source occurrence role.
- parent metadata equals source occurrence parent.
- subtree end equals source occurrence boundary.
- Existing snapshot-local identity remains.
- Existing total navigation remains.
- Existing child/parent/ancestry proofs remain.
- No fallback or silent filtering.

Abstraction

- `index_at` removed from public `SNAP_SIG`.
- Hidden slots remain private.
- Raw constructors remain private.
- No equivalent raw table escape.
- Public facts are phrased through validated source references.

Documentation

- Root ID corrected to 1/current canonical ID.
- Final exact `si_ok` design stated in headline record.
- Historical fail-open repair remains in ledger.
- Source recovery complexity stated honestly.
- Exact source/metadata law added to C2 architecture.
- C0B history recorded without rewriting C0/C0A history.

Proof and behavior

- Every new public theorem axiom-free.
- Whole-theory audit green.
- Full `make check` green.
- Existing generated bytes unchanged.
- Existing Go e2e unchanged and green.
- Staged-tree verification green.

===============================================================================
14. COMPLETION REPORT
===============================================================================

When complete, report:

- C0B contract commit SHA;
- root candidate SHA;
- every `review(root): C0B` SHA;
- root Codex final result;
- final candidate SHA;
- every `review(final): C0B` SHA;
- final Codex result;
- complete C0B commit range;
- exact independent source specification shape;
- every function used by the source specification;
- independence audit;
- exact universal source/table theorem statement;
- presence theorem;
- absence theorem;
- uniqueness theorem;
- kind theorem;
- role theorem;
- parent theorem;
- subtree-end theorem;
- total NodeRef source-occurrence function;
- sealed `ref_meta` source theorem;
- handling/deletion of old `node_at`;
- removal of public `index_at`;
- negative abstraction checks;
- mutation-sensitive witness layout;
- exact kind fixtures;
- exact role fixtures;
- exact parent fixtures;
- exact subtree fixtures;
- theorem that would fail for each mutation category;
- all new/changed assumption surfaces;
- full `Print Assumptions` result;
- whole-theory audit result;
- gate count;
- generated-byte comparison;
- e2e result;
- staged pre-commit result;
- master-plan corrections;
- status-ledger corrections;
- push result;
- notification result;
- confirmation loop stopped;
- confirmation C1 not started.

Do not list a retained correctness flaw as a known limitation.

If a real obstacle requires changing the ownership, identity, or exactness design:

- classify it as an ARCHITECTURAL CONFLICT;
- notify Rob;
- stop the loop;
- wait.

===============================================================================
15. HARD STOP
===============================================================================

When final Codex review is GREEN and final verification passes:

1. Commit the completed C0B checkpoint.
2. Record the final GREEN result in the status ledger.
3. Fast-forward push.
4. Notify Rob.
5. Stop the `/loop`.
6. Do not activate C1.
7. Wait for human review.

===============================================================================
BOTTOM LINE
===============================================================================

C0 proved that efficient occurrence indexing is feasible.

C0A proved that references belong to the exact source snapshot and navigation is
total and efficient.

C0B proves that the metadata behind each reference describes the exact source
occurrence it claims to describe.

The complete root becomes:

  exact immutable source snapshot
      -> canonical source occurrence meaning
      -> exact metadata builder correspondence
      -> snapshot-local NodeRef
      -> total efficient navigation
      -> future compiler facts and diagnostics

No source ambiguity.

No structurally coherent mislabeling.

No public raw storage escape.

No second AST.

No C1 work until this theorem boundary is human-approved.
