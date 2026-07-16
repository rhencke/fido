Claude Code correction checkpoint: C0A — exact snapshot-local occurrence identity and total navigation

THIS IS A BINDING CORRECTION CHECKPOINT INSIDE THE EXISTING SOURCE FOREST CAMPAIGN.

It does not activate C1.

The persistent campaign architecture remains in:

  .review/SOURCE_FOREST_MASTER_PLAN.md

The current repository baseline for this correction is:

  11fd1a131d4b659065c0b3eafd277eb5aafd0645

Keep all existing C0 commits. Do not rewrite, squash, reset, or force-push history.

===============================================================================
0. BEFORE IMPLEMENTATION
===============================================================================

1. Stop any current `/loop`.

2. Read, in full:

   - `.review/SOURCE_FOREST_MASTER_PLAN.md`
   - `.review/SOURCE_FOREST_STATUS.md`
   - `.review/CODEX_REVIEW_POLICY.md`
   - `OccurrenceSpike.v`
   - the C0 commits:
       a3a4d5320c470c17bc7319c0d6f6e31bdfbf5af2
       9a2e85ee96bc8cfbc0fbd614482158cd41934d15
       cf91bc971bf1fa8363fd517c56802b55740925cc
       11fd1a131d4b659065c0b3eafd277eb5aafd0645

3. Replace `.review/NEXT_STEPS.md` with this correction directive VERBATIM.

4. Update `.review/SOURCE_FOREST_STATUS.md` to say:

   - active checkpoint: C0A;
   - C0 was Codex-green but human review found a foundational source/index coupling defect;
   - C1 remains forbidden until C0A is human-approved;
   - preserve the earlier Codex findings and repair ledger rather than rewriting history.

5. Commit the contract/status activation before implementation.

   Commit message prefix:

     milestone(contract): C0A —

6. Then run exactly:

   /loop 5m completing NEXT_STEPS until codex review is green and then notify me and stop the loop.

The loop is authorized only for C0A.

===============================================================================
1. WHY C0A EXISTS
===============================================================================

The C0 spike successfully established:

- file-local positive preorder IDs;
- an abstract pure-Gallina positive-key radix trie;
- parent/role/subtree-end metadata;
- one-pass insertion;
- interval ancestry;
- list-free O(number-of-direct-children) child enumeration;
- structural equality does not determine occurrence identity;
- the theorem family is axiom-free.

Keep those decisions.

The remaining defect is conceptual:

  the current `NodeRef` belongs to a free-standing `SyntaxIndex` value,
  not to the exact source snapshot that index describes.

Current shape:

  SyntaxIndex := list FileIndex

  NodeRef (idx : SyntaxIndex)

That permits two different source forests with identical paths and tree shape but
different literal payloads to compute the same structural index value and therefore
share the same `NodeRef` type.

That is not the intended architecture.

A diagnostic, declaration identity, resolution fact, or nominal type identity must
refer to an occurrence in one exact immutable source snapshot.

The corrected root is:

  source snapshot
      -> one certified derived SyntaxIndex for that snapshot
      -> FileRef snapshot
      -> NodeRef snapshot

The reference belongs to the source snapshot, never merely to the index data.

The second defect is API honesty:

- `ref_meta` currently returns `option`;
- `node_kind` invents `KFile` if metadata is missing;
- `containing_file` returns `option`;
- `children_of` silently drops a child if rebuilding its reference fails.

A validated source occurrence must make structurally guaranteed queries total.
No impossible-case fallback may manufacture a plausible semantic answer.

The third defect is complexity accounting:

- current metadata navigation first performs a linear `file_of` scan over
  `SyntaxIndex := list FileIndex`;
- the ledger therefore overstates parent/kind/meta lookup as merely O(log n).

C0A must remove the hidden file-list scan from ordinary navigation.

===============================================================================
2. NON-NEGOTIABLE ARCHITECTURE
===============================================================================

Keep:

- recursive immutable source trees;
- downward ownership only;
- derived parent navigation;
- one canonical preorder per file;
- file-local positive IDs;
- root local ID = 1;
- `NodeMeta` containing:
    kind;
    parent local ID;
    role;
    subtree end;
- abstract `NodeTable`;
- positive-key radix-trie implementation;
- interval-jump direct-child enumeration;
- no syntax subtree copied into metadata;
- no production AST migration yet.

Correct:

- source/index dependence;
- file-root identity;
- validated-reference totality;
- outer file lookup on the navigation path;
- complexity claims;
- constructor abstraction.

Do not add:

- C1 `GoSourceFile`;
- production `GoFileSet`;
- production `GoIndex`;
- diagnostics;
- source type syntax;
- numeric types;
- structural types;
- parent pointers;
- author-supplied IDs;
- typed AST;
- flattened syntax cache;
- primitive arrays;
- list-backed node lookup;
- new Go behavior.

===============================================================================
3. MAKE THE TOY SOURCE SNAPSHOT PATH-UNIQUE
===============================================================================

Replace the unconstrained alias:

  TForest := list TFile

with an intrinsic toy source set/snapshot, conceptually:

  Record TForest := {
    forest_files : list TFile;
    forest_paths_unique :
      NoDup (map tf_path forest_files)
  }.

Equivalent shape is acceptable.

The exact source snapshot still includes its concrete file sequence for C0A.
C1 will establish the permanent `GoFileSet` abstraction and its extensional/order-
independent semantics.

For C0A, the required fact is simpler:

- one path names at most one toy file root;
- `FileRef` by path is unambiguous;
- duplicate file paths are unrepresentable;
- raw `NodeKey = (FilePath, LocalNodeId)` cannot ambiguously name two roots.

Add:

- reflected/decidable file lookup;
- lookup functionality from path uniqueness;
- duplicate-path negative construction fixture;
- two-file witness using the intrinsic forest constructor.

Do not turn the toy forest into the production file-set implementation.

===============================================================================
4. SOURCE-INDEXED `SyntaxIndex`
===============================================================================

Change the index from free-standing data into a source-indexed certified value.

Required public shape:

  SyntaxIndex (fs : TForest) : Type

  index_forest :
    forall fs : TForest,
      SyntaxIndex fs

The constructor of `SyntaxIndex` must be private.

A `SyntaxIndex fs` must carry or imply a theorem equivalent to:

  IndexDescribesForest fs index_data

The proof must establish that every metadata entry corresponds to the canonical
preorder occurrence of `fs`, and every indexed occurrence in `fs` has exactly one
metadata entry.

Do not satisfy the type parameter merely by storing arbitrary tables beside an
unused proof field.

The index exactness theorem must drive the total query API in Part 7.

The physical metadata of two same-shaped source snapshots may compute identically.
That is acceptable.

Their `SyntaxIndex fs1` and `SyntaxIndex fs2` types remain distinct because they are
indexed by different source values.

===============================================================================
5. `FileRef` IS A SOURCE-SNAPSHOT FILE-ROOT HANDLE
===============================================================================

Introduce:

  FileRef (fs : TForest) : Type

A `FileRef fs` identifies exactly one file-root occurrence in `fs`.

It must provide, directly or by total projection:

- the exact `TFile`;
- its `FilePath`;
- a hidden structural handle suitable for efficient access to that file's index;
- proof that the file is an actual member/root of `fs`.

Recommended spike representation:

  Record FileRef (fs : TForest) := {
    file_ref_slot : positive;
    file_ref_file : TFile;
    file_ref_at_slot :
      forest_file_at fs file_ref_slot = Some file_ref_file
  }.

Names may differ.

The slot is:

- derived by the canonical forest traversal;
- private implementation metadata;
- not author supplied;
- not source identity;
- not rendered;
- not serialized as the public key.

The public identity of a file occurrence remains its unique `FilePath`.

Prove:

- every source file has one `FileRef`;
- two `FileRef fs` values with the same path identify the same source file;
- file-reference equality is decidable by path;
- the hidden slot does not create a second identity authority.

Hide the raw `FileRef` constructor behind a module signature or equivalent private
construction boundary.

===============================================================================
6. `NodeRef` BELONGS TO THE EXACT SOURCE SNAPSHOT
===============================================================================

Replace:

  NodeRef (idx : SyntaxIndex)

with:

  NodeRef (fs : TForest)

Conceptually:

  Record NodeRef (fs : TForest) := {
    node_ref_file  : FileRef fs;
    node_ref_local : positive;
    node_ref_valid :
      ValidLocalOccurrence fs node_ref_file node_ref_local
  }.

The validity proposition may be reflected through the canonical index, but its
meaning must be:

  this local ID names an actual occurrence in this exact file of this exact source
  snapshot.

It must not merely mean:

  a key happens to be present in some free-standing table.

A public raw key remains:

  Record NodeKey := {
    node_file  : FilePath;
    node_local : positive
  }.

Provide:

  node_ref_key :
    NodeRef fs -> NodeKey

The hidden file slot is not part of `NodeKey`.

Node-reference equality is exactly `NodeKey` equality within one source snapshot.

Prove:

- decidable `NodeKey` equality;
- key equality implies `NodeRef fs` equality;
- `NodeRef` proof fields do not create multiple identities;
- different local IDs in one file give different references;
- equal syntax fragments in different positions have different references.

Hide the raw `NodeRef` constructor.

The comment claiming one function is the only way to mint a reference must become
true, not merely aspirational.

===============================================================================
7. ORDINARY NAVIGATION MUST NOT SCAN THE FILE LIST
===============================================================================

Ordinary navigation begins with an existing validated `NodeRef fs`.

It must not:

- call `file_of` over a list of file indexes;
- search by `FilePath`;
- reconstruct the whole source index;
- recover a file by structural equality.

Use the `FileRef`'s hidden structural handle to access the correct per-file index.

Recommended index data:

- one abstract outer `NodeTable` keyed by the hidden file slot;
- each outer entry contains the corresponding per-file index/table;
- each per-file table remains keyed by local positive ID.

Equivalent efficient representation is acceptable only if:

- ordinary metadata navigation has no O(number-of-files) scan;
- containing file is a projection;
- the exact complexity is documented;
- no second file identity is introduced.

The preferred complexity is:

  index build:
    O(files log files + nodes log nodes-per-file)

  containing file:
    O(1) projection from NodeRef

  metadata / kind / role / immediate parent:
    O(log files + log nodes-per-file)

  ancestor:
    metadata lookup above + O(1) interval arithmetic

  direct children:
    one file-index acquisition;
    then O(k log nodes-per-file) for k direct children;
    never O(descendants)

A raw lookup:

  ref_of_key :
    SyntaxIndex fs -> NodeKey -> option (NodeRef fs)

may perform a path lookup once when converting an external/raw key into a handle.
Document that cost honestly.

The hot compiler traversal and all navigation from an existing `NodeRef` must not
use that raw path lookup.

===============================================================================
8. TOTAL VALIDATED-REFERENCE API
===============================================================================

For a valid source-indexed reference and certified index, provide total functions:

  ref_meta :
    SyntaxIndex fs ->
    NodeRef fs ->
    NodeMeta

  node_kind :
    SyntaxIndex fs ->
    NodeRef fs ->
    SyntaxKind

  node_role :
    SyntaxIndex fs ->
    NodeRef fs ->
    NodeRole

  subtree_end :
    SyntaxIndex fs ->
    NodeRef fs ->
    positive

  containing_file :
    NodeRef fs ->
    FileRef fs

Only structurally optional answers remain optional:

  parent_of :
    SyntaxIndex fs ->
    NodeRef fs ->
    option (NodeRef fs)

because a file root has no parent.

Provide total:

  children_of :
    SyntaxIndex fs ->
    NodeRef fs ->
    list (NodeRef fs)

`children_of` must not:

- call `ref_of` and discard `None`;
- filter supposedly invalid children;
- silently truncate on a missing table entry.

The child-enumeration correctness theorem already proves each local child ID is a
real occurrence.

Use that proof to construct each child reference directly.

Likewise, `parent_of` must construct the parent reference directly from the parent-
validity theorem. It must not use a fail-soft raw lookup.

Delete:

- `node_kind` fallback to `KFile`;
- total-query `option` results whose `None` case contradicts `NodeRef` validity;
- silent child filtering.

If an impossible index inconsistency cannot be eliminated by the type/proof design,
that is an architectural failure, not a branch to paper over.

===============================================================================
9. SOURCE RECOVERY AND EXACT SNAPSHOT BINDING
===============================================================================

Retain the source-recovery relation/helper used by the equal-leaf theorem, but make
its role explicit:

- proof/diagnostic inspection helper;
- not parent navigation;
- not the hot compiler path;
- not a second AST;
- no copied subtree cache.

Strengthen the exactness story:

  node_at / occurrence_at
    connects one `NodeRef fs` to the exact source occurrence in `fs`.

It may remain a relation or kind-indexed view in the toy spike.

Required witness pair:

  fs_a:
    file a contains two leaves with value 5

  fs_b:
    identical paths and identical tree shape,
    but the corresponding leaves have value 6

Prove or pin:

1. The structural metadata/index data may be equal after erasing its source index.

2. A reference of type:

     NodeRef fs_a

   is not directly usable as:

     NodeRef fs_b

   Add an axiom-free `Fail Definition`/`Fail Check` or a stronger typed theorem.

3. `node_at` for the left leaf in `fs_a` recovers `TLeaf 5`.

4. `node_at` for the corresponding leaf in `fs_b` recovers `TLeaf 6`.

5. The two equal `TLeaf 5` occurrences inside `fs_a` still have distinct `NodeRef fs_a`
   values.

This is the decisive regression for the source-snapshot-local identity design.

===============================================================================
10. REQUIRED THEOREM SURFACES
===============================================================================

Preserve and restate the existing structural theorem family over the corrected
source-indexed API.

Gate at least:

Source snapshot / file roots

- path uniqueness;
- file lookup functionality;
- duplicate-path unrepresentability;
- every file has one FileRef;
- FileRef path equality decides file occurrence equality.

Index/source exactness

- `index_forest` describes exactly its `fs`;
- every source occurrence has one metadata entry;
- every metadata entry corresponds to one source occurrence;
- no index entry belongs to another source snapshot.

Node references

- raw constructor hidden;
- `ref_of_key` sound and complete;
- `node_ref_key` injective;
- NodeRef equality reflected by NodeKey equality;
- same-shaped/different-source references are non-interchangeable;
- repeated equal fragments in one source have distinct refs.

Total queries

- `ref_meta` total;
- `node_kind` is the indexed kind, with no fallback;
- `node_role` total;
- `containing_file` is the carried FileRef;
- parent root = None;
- every non-root parent is Some valid reference;
- children contain no dropped/invalid reference.

Navigation

- parent/child inverse at the NodeRef level;
- parent and child carry the same FileRef;
- containing-file recovery;
- canonical enumeration exact and NoDup;
- children source-ordered;
- interval ancestry sound and complete;
- direct-child interval-jump sound and complete;
- builder deterministic;
- builder does not perform structural-equality search;
- metadata stores no recursive syntax subtree.

Performance-shape surfaces

Rocq need not prove a machine-cost model, but the code structure and abstraction
must expose:

- no `List.find`/linear file scan in navigation from NodeRef;
- no `pos_seq` or descendant-list materialization in direct-child enumeration;
- no repeated `index_forest` call inside query functions;
- no list-backed NodeTable;
- one outer slot lookup plus one local metadata lookup;
- one index construction per snapshot.

===============================================================================
11. MODULE ABSTRACTION
===============================================================================

Keep `NodeTable` sealed.

Also seal:

- `SyntaxIndex` constructors;
- `FileRef` constructors;
- `NodeRef` constructors.

Expose only:

- source/index builder;
- canonical traversal;
- validated raw lookup;
- total navigation;
- key/equality observations;
- theorem surfaces.

Do not expose a record constructor and simultaneously claim invalid or cross-snapshot
references cannot be minted.

Use proof-irrelevant validity evidence where it simplifies reference equality.

Do not use kernel primitives.

===============================================================================
12. MASTER PLAN AND STATUS RECONCILIATION
===============================================================================

Make targeted edits to `.review/SOURCE_FOREST_MASTER_PLAN.md` so the persistent
architecture explicitly states:

- `NodeRef` is indexed by the exact source snapshot, not by index data;
- a NodeRef carries or directly projects a validated FileRef;
- `containing_file`, `ref_meta`, `node_kind`, and `children_of` are total;
- only `parent_of` is optional;
- navigation from an existing NodeRef performs no file-list scan;
- raw NodeKey lookup is a separate minting boundary with separately stated cost;
- impossible index inconsistency has no semantic fallback.

Do not rewrite the entire master plan.

Update `.review/SOURCE_FOREST_STATUS.md` with:

- C0A commit range;
- selected outer file-index access design;
- exact corrected complexities;
- source-snapshot regression;
- total-query API;
- Codex findings and repair SHAs;
- final push;
- human disposition pending.

Do not erase the historical C0 Codex-green result.
Record that human holistic review found a deeper architectural defect afterward.

===============================================================================
13. CODEX REVIEW CADENCE
===============================================================================

This is a foundational correction, so use at most two intentional stops.

ROOT BARRIER

Stop only after:

- path-unique toy source snapshot exists;
- `SyntaxIndex fs` exists;
- `FileRef fs` exists;
- `NodeRef fs` exists;
- constructors are hidden;
- ordinary navigation has no file-list scan;
- total metadata/kind/file API exists;
- same-shaped/different-source reference separation is pinned;
- local proof gate is green.

Commit:

  milestone(root): C0A — source-indexed references and total navigation root

Codex-driven repairs:

  review(root): C0A —

After root GREEN, continue without another progress stop.

FINAL BARRIER

Complete:

- full theorem restatement;
- NodeRef-level parent/child proofs;
- source recovery fixtures;
- master-plan/status reconciliation;
- assumptions gate;
- whole-theory audit;
- complete repository checks;
- generated-byte identity.

Commit:

  milestone(final): C0A — close exact snapshot-local occurrence foundation

Final Codex repairs:

  review(final): C0A —

After final GREEN:

- run final verification;
- commit any review/status completion;
- fast-forward push;
- notify Rob;
- stop the loop;
- do not activate C1.

===============================================================================
14. FORBIDDEN SHORTCUTS
===============================================================================

Do not “fix” source binding by:

- adding source payload hashes to NodeKey;
- making syntax value equality part of occurrence identity;
- copying syntax into NodeMeta;
- indexing NodeRef by both source and an arbitrary index value;
- packaging a free-standing index and merely storing the source beside it without a
  correspondence theorem;
- keeping partial queries and proving callers never see None;
- mapping missing metadata to KFile or another default;
- silently dropping invalid children;
- carrying raw parent pointers in AST nodes;
- adding a typed AST;
- using a list outer table and relabeling its scan as constant/logarithmic;
- selecting PArray/Uint63;
- beginning C1 migration while C0A is incomplete.

===============================================================================
15. ACCEPTANCE CRITERIA
===============================================================================

C0A is GREEN only when all are true:

Source coupling

- `SyntaxIndex` is indexed by exact source snapshot.
- `NodeRef` is indexed by exact source snapshot.
- `FileRef` is indexed by exact source snapshot.
- references from same-shaped but different-payload snapshots are non-interchangeable.
- index/source correspondence is proved.

File identity

- toy source paths are unique by construction.
- FileRef identity is path identity.
- hidden file slots are optimization handles only.
- containing file is O(1) projection from NodeRef.

Totality

- `ref_meta` total.
- `node_kind` total, no KFile fallback.
- `node_role` total.
- `containing_file` total.
- `children_of` total, no option filtering.
- only root-parent absence remains a real `None`.

Efficiency

- no file-list scan in navigation from NodeRef.
- parent/kind/meta use efficient table lookup.
- direct children remain list-free interval jumps.
- one index build per snapshot.
- exact complexity claims match implementation.
- raw key lookup cost is stated separately.

Identity

- NodeRef equality is NodeKey equality.
- proof/index handles do not create second identity.
- equal fragments in different positions have distinct refs.
- same key within one snapshot identifies one occurrence.
- source recovery returns the exact source payload.

Architecture

- no parent pointer in AST.
- no copied syntax authority.
- no typed AST.
- no kernel primitive.
- no C1 work.
- OccurrenceSpike remains temporary and isolated.

Proof / integration

- every new public theorem axiom-free.
- whole-theory audit green.
- no Admitted/Parameter/Axiom.
- full `make check` green.
- generated Go bytes unchanged.
- pushed fast-forward.
- loop stopped.
- human disposition pending.

===============================================================================
16. COMPLETION REPORT
===============================================================================

Report:

- contract activation SHA;
- root candidate SHA;
- root Codex findings and repair SHAs;
- final candidate SHA;
- final Codex findings and repair SHAs;
- final pushed SHA/range;
- exact `TForest` path-uniqueness shape;
- exact `SyntaxIndex fs` representation;
- exact `FileRef fs` representation;
- exact `NodeRef fs` representation;
- hidden file-slot role;
- outer/per-file table design;
- query complexities;
- raw-key minting complexity;
- total API signatures;
- deleted fallback/option/filter branches;
- same-shaped/different-source regression;
- repeated-equal-leaf regression;
- source recovery theorem;
- parent/child NodeRef theorem;
- complete Print Assumptions result;
- whole-theory audit result;
- full check result;
- generated-byte identity result;
- master-plan/status edits;
- push result;
- notification sent;
- loop stopped;
- explicit confirmation that C1 did not begin.

===============================================================================
17. HARD STOP
===============================================================================

When C0A is Codex-green and final verification passes:

1. Commit.
2. Fast-forward push.
3. Notify Rob.
4. Stop the loop.
5. Do not activate C1.
6. Wait for human review.

Bottom line:

  The structural index may be reusable data.

  The occurrence reference is not reusable across source snapshots.

  A NodeRef means:

    this exact occurrence
    in this exact file
    in this exact immutable source snapshot.

  Once that proposition is carried intrinsically, structural navigation is total,
  efficient, and honest.
