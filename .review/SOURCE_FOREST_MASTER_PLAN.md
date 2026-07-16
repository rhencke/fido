Claude Code master campaign: Specification-Shaped Source Forest, Snapshot-Local Occurrence Identity, and Occurrence-Anchored Compilation

THIS FILE IS A PERSISTENT MASTER ARCHITECTURE PLAN.

It is intentionally larger than one implementation milestone.

It preserves the complete design across several human-reviewed checkpoints so that later rounds do not depend on chat context, memory, or reconstruction from partial commit messages.

It is NOT true that every future checkpoint in this file is active at once.

Only the checkpoint copied into `.review/NEXT_STEPS.md` is active and binding for a Codex review.

===============================================================================
PART 0 — INSTALLATION, PERSISTENCE, AND CHECKPOINT CONTROL
===============================================================================

0.1 Stop any currently running loop

Before changing the repository:

- stop any current `/loop`;
- confirm the working tree is understood;
- do not start implementation from an uncommitted mystery state.

0.2 Store this complete plan permanently

Copy this entire file VERBATIM to:

  .review/SOURCE_FOREST_MASTER_PLAN.md

Do not summarize it.

Do not keep only the first checkpoint.

Do not omit later checkpoints.

Do not rewrite the architecture into a shorter interpretation.

Commit that master plan before implementation with a message beginning:

  milestone(contract):

The baseline for this campaign is:

  5e7efd8adf38473a931a0144ede62b2caa90272a

If the repository tip has moved before installation:

- compare the new tip against that baseline;
- preserve any intervening approved work;
- record the actual campaign base SHA in the status file;
- stop on an architectural conflict rather than silently rebasing the plan onto incompatible work.

0.3 Keep the master plan separate from the active Codex contract

The Codex stop hook reviews `.review/NEXT_STEPS.md`.

Do NOT put every future checkpoint into `.review/NEXT_STEPS.md` as simultaneously required work.

That would make Codex correctly report every intermediate checkpoint incomplete.

Instead:

- `.review/SOURCE_FOREST_MASTER_PLAN.md` contains this entire long-term design;
- `.review/NEXT_STEPS.md` contains only the currently activated checkpoint, its standing laws, its exact acceptance criteria, and an explicit reference to the master plan;
- future checkpoints are preserved design context but are not active obligations until Rob explicitly activates them.

At campaign installation, activate only Checkpoint C0.

0.4 Add a small durable campaign ledger

Create:

  .review/SOURCE_FOREST_STATUS.md

Its initial contents should record:

- campaign name;
- master-plan commit SHA;
- actual base SHA;
- active checkpoint: C0;
- checkpoint contract commit SHA;
- root candidate SHA, when one exists;
- root Codex result and repair SHAs;
- final candidate SHA;
- final Codex result and repair SHAs;
- verification result;
- push result;
- human disposition:
  - pending;
  - approved;
  - revise;
  - abandoned.

Update this file only at checkpoint boundaries.

It is a ledger, not a second plan.

0.5 Activate a checkpoint explicitly

For every checkpoint:

1. Rob explicitly authorizes that checkpoint.
2. Copy that checkpoint's activation contract from this master plan into `.review/NEXT_STEPS.md`.
3. Include this exact statement near the top:

   > Only this activated checkpoint is currently binding. Later checkpoints in
   > `.review/SOURCE_FOREST_MASTER_PLAN.md` are preserved architectural context,
   > not current completion criteria.

4. Commit `.review/NEXT_STEPS.md` before checkpoint implementation.
5. Record its commit SHA in `.review/SOURCE_FOREST_STATUS.md`.
6. Run the normal loop:

   /loop 5m completing NEXT_STEPS until codex review is green and then notify me and stop the loop.

7. Do not activate the next checkpoint automatically.

0.6 Human and Codex stopping discipline

This is a multi-round campaign.

Each checkpoint ends with:

- a coherent commit;
- an intentional Codex stop review;
- review-driven repairs in separate commits;
- final verification;
- a normal fast-forward push;
- notification;
- loop termination;
- human review before the next checkpoint.

Never force-push.

Keep a linear ledger.

If push fails:

- report the operational failure;
- do not claim success;
- stop.

Do not intentionally stop for:

- progress narration;
- routine compilation;
- ordinary proof completion;
- mechanical wiring;
- fixture addition;
- documentation updates;
- questions already answered by the active contract.

For a foundational checkpoint, use at most:

1. one semantic-root review;
2. one final exhaustive review.

For a small proof-spike or cleanup checkpoint, use only the final review.

Review-driven commits must begin:

  review(root):

or:

  review(final):

Implementation candidates must begin:

  milestone(root):

or:

  milestone(final):

The checkpoint identifier must appear immediately after the prefix or in the first line, for example:

  milestone(root): C2 — canonical occurrence index and parent navigation
  review(root): C2 — make parent lookup use the certified node table
  milestone(final): C2 — integrate NodeRef through the full proof gate

Do not squash implementation commits and review-driven repairs together.

0.7 Architectural conflict rule

If an objective defect cannot be repaired without changing:

- the source-forest ownership model;
- the occurrence-identity model;
- the syntax/compile/type responsibility split;
- the declared complexity guarantees;
- the one-AST architecture;
- the checkpoint scope;

classify it as:

  ARCHITECTURAL CONFLICT

Then:

- commit nothing speculative;
- notify Rob;
- stop the loop;
- wait.

Do not quietly redesign the plan.

===============================================================================
PART 1 — CAMPAIGN PURPOSE AND FINAL OUTCOME
===============================================================================

1.1 Why this campaign exists

Fido is about to grow from a small literal-and-conversion generator into a language model with:

- source type names;
- aliases and defined types;
- recursive type declarations;
- function signatures;
- parameter and result declarations;
- methods and method sets;
- interfaces;
- imports and scopes;
- useful diagnostics;
- later structural and operational features.

The current representation is too small to be the permanent root:

  GoFileAST := list GoDecl
  prog_files : fmap FilePath GoFileAST

It was coherent for the tiny current fragment because:

- every file was implicitly package `main`;
- imports were impossible;
- the only varying source-file content was a declaration list;
- the renderer synthesized the package clause from compiler facts.

That is no longer the right direction.

This campaign replaces that shortcut before more language features make it expensive to unwind.

1.2 Final architectural outcome

At campaign completion:

- `GoProgram` owns a path-keyed set of immutable file-root source trees;
- each `GoFileNode` contains:
  - its intrinsic filesystem path;
  - one specification-shaped `GoSourceFile`;
- `GoSourceFile` follows the Go specification's abstract source-file structure:
  - package clause;
  - imports;
  - top-level declarations;
- only fully supported grammar productions are live;
- presentation-equivalent forms have one canonical renderer spelling;
- the AST stores children only;
- no syntax node stores a parent pointer;
- every semantically addressable source occurrence has a canonical snapshot-local `NodeRef`;
- one derived certified `SyntaxIndex` provides:
  - parent;
  - children;
  - containing file;
  - occurrence kind;
  - deterministic occurrence order;
- parent navigation never searches the whole source tree;
- `GoCompile` decorates occurrences with contextual meaning and diagnostics;
- `GoTypes` owns origin-free semantic types and relations;
- diagnostics point to source occurrences;
- source spans remain optional future metadata;
- no typed AST, copied program, target AST, or text IR exists.

1.3 The concise design

The durable design is:

> A `GoProgram` owns a path-unique set of immutable,
> specification-shaped source-file trees.
>
> A source occurrence is identified inside its file by a canonical,
> snapshot-local reference derived from the tree, not by parent fields or
> author-supplied IDs.
>
> A certified structural index derives upward navigation from the one
> downward-owned tree.
>
> `GoCompile` connects source occurrences to binding, resolved semantic
> types, and diagnostics.
>
> `GoTypes` defines semantic relations without source spelling or location.
>
> `GoRender` renders the original source AST canonically.

===============================================================================
PART 2 — BINDING DESIGN LAWS
===============================================================================

2.1 The Go specification owns source structure

The Go 1.23 specification is the grammar authority.

Fido's AST is:

- a deliberately bounded abstract subset of the Go grammar;
- not an independently invented language that merely prints Go-shaped text;
- not a concrete syntax tree;
- not a text editor model.

The ordinary translation rule is:

- required grammar component -> record field;
- optional grammar component -> `option`;
- repetition -> ordered list or finite sequence;
- grammar alternative -> inductive constructor;
- lexical value -> intrinsic lexical datatype;
- contextual semantic restriction -> `GoCompile` / `GoTypes`.

2.2 Abstract syntax, not presentation syntax

Preserve source distinctions that affect:

- binding;
- type resolution;
- nominal identity;
- semantic rules;
- diagnostics;
- intentional source spelling.

Canonicalize distinctions that are purely presentational:

- whitespace;
- comments;
- semicolon insertion;
- import block grouping;
- redundant parentheses;
- equivalent formatting choices.

Do not generalize this into “discard any syntax that looks cosmetic.”

For each normalized distinction, confirm it carries no language semantics.

For example, grouped constant declarations can interact with `iota` and implicit
expression repetition. They may not be flattened merely because grouped imports
can be.

2.3 Syntax-smart and semantics-dumb

The source AST should guarantee:

- context-free grammar structure;
- intrinsic lexical validity;
- required components;
- correct parent-to-child category shape;
- source-selected names and spellings;
- file-path uniqueness at the program-container level.

The source AST should not carry:

- resolved declarations;
- semantic package identities;
- imported package objects;
- effective import bindings;
- scope tables;
- expression types;
- underlying types;
- assignability evidence;
- method sets;
- interface-satisfaction evidence;
- constant representability results;
- compiler-validity flags;
- diagnostics;
- copied resolved syntax.

Grammatically valid but semantically invalid programs must remain representable.

2.4 One ownership edge

The source tree stores only downward ownership:

- file -> package/imports/declarations;
- declaration -> signature/body;
- signature -> parameter/result declarations;
- statement -> expressions;
- expression -> child expressions;
- type syntax -> child type syntax.

Do not store both parent and child edges in the source value.

The inverse relation is derived once in `GoIndex`.

2.5 Syntax fragments are not source occurrences

A context-free `GoExpr`, `TypeSyntax`, or declaration value may exist as a builder fragment.

A source occurrence is that value at one exact position inside one immutable `GoProgram`.

Diagnostics, binding, declaration identity, and compilation facts refer to occurrences.

Two structurally equal expressions in different positions are distinct occurrences.

2.6 Compilation decorates the original program

There is one source program.

Compilation may produce:

- facts;
- proofs;
- finite tables indexed by `NodeRef`;
- diagnostics indexed by `NodeRef`.

Compilation may not produce:

- a typed copy of the AST;
- a normalized copy of the AST;
- a target AST;
- a separate resolved syntax tree;
- a source-text IR.

2.7 Semantic values carry no diagnostic provenance

Semantic types and signatures must not carry:

- AST parents;
- file paths;
- source ranges;
- parameter source names when names do not affect semantic identity;
- diagnostic prose.

Source provenance lives in the source occurrence reference.

2.8 Relation-specific semantics

Do not create one universal “representative type.”

Keep separate:

- type identity;
- alias expansion;
- underlying type;
- assignability;
- conversion;
- comparability;
- strict comparability;
- nilability;
- map-key admissibility;
- function-signature identity;
- method-signature identity;
- method sets;
- interface satisfaction.

Go erases different source details for different relations.

2.9 No feature breadth during foundational migration

Until Checkpoint C3 is accepted:

- no new numeric type;
- no structural type;
- no named type;
- no import;
- no operation;
- no general function;
- no interface;
- no arithmetic.

The migration must preserve current behavior before it validates itself with new type syntax and numeric completion.

===============================================================================
PART 3 — SOURCE FOREST
===============================================================================

3.1 Source file versus file placement

A source file is a grammar object.

A file path is compilation-unit placement metadata.

Keep them separate:

  Record GoSourceFile := {
    source_package : PackageClauseSyntax;
    source_imports : list ImportSpecSyntax;
    source_decls   : list TopLevelDeclSyntax
  }.

  Record GoFileNode := {
    file_path   : FilePath;
    file_source : GoSourceFile
  }.

The path belongs to the file-root program node.

The path does not become a child production inside Go's source grammar.

3.2 Current supported subgrammar

During the migration, do not make future source productions representable before their semantics.

The first source-file model may use intentionally narrow live domains:

- package clause:
  - only the currently supported canonical `package main` form;
- imports:
  - absent / intrinsically empty;
- top-level declarations:
  - only the current `func main()` declaration form;
- statements and expressions:
  - the current admitted forms.

The record fields should nevertheless follow the permanent source-file categories.

Do not represent arbitrary package names and then reject every non-main package.

Do not represent imports and then reject them wholesale.

That would repeat the subset-filter mistake.

3.3 Path-keyed file set

Replace the public `dict[path, AST]` shape with a path-keyed file set:

  Record GoFileSet := {
    file_members : list GoFileNode;
    file_paths_unique :
      NoDup (map file_path file_members)
  }.

This is semantically:

  set[GoFileNode]

with uniqueness determined by `file_path`.

Required meaning:

- same path twice: impossible;
- different paths with identical source: allowed;
- same path with different source: impossible;
- physical list order: not program semantics.

Expose:

  find_file
  file_member
  file_paths
  FilesEqual

`FilesEqual` is extensional by path lookup.

The physical representation may later change without altering this public meaning.

3.4 Program root

  Record GoProgram := {
    prog_module : ModuleSpec;
    prog_files  : GoFileSet
  }.

`ModuleSpec` remains outside source files because it renders the module's `go.mod`.

No synthetic source-level program AST node is required.

Whole-program diagnostics may use an `AtProgram` anchor.

3.5 Construction API

Keep program writing intentionally straightforward:

  build_program :
    ModuleSpec ->
    list GoFileNode ->
    option GoProgram

Failure at this boundary should mean the file collection cannot describe one source tree set, chiefly duplicate paths.

Semantic invalidity remains a compiler result.

3.6 Rendering responsibility

After the source-file migration:

- `GoRender` renders the package clause from `GoSourceFile`;
- `GoCompile` proves package-clause and package-grouping validity;
- `CompilationFacts` no longer invents package spelling for the renderer.

A convenience builder may construct a canonical main-package file.

The builder creates ordinary source syntax.

The renderer does not synthesize missing source syntax behind the AST's back.

===============================================================================
PART 4 — OCCURRENCE IDENTITY AND NAVIGATION
===============================================================================

4.1 PSI inspiration, reshaped for Fido

Steal these concepts:

- file-rooted hierarchy;
- source elements have occurrence identity;
- upward and downward navigation;
- source reference and resolved declaration are separate;
- semantic conclusions remain separate from syntax.

Do not transplant:

- mutable PSI objects;
- editor documents;
- reparsing;
- invalid-element lifecycle;
- virtual files;
- user-data bags;
- smart pointers across edits;
- token/trivia trees.

Fido's program is an immutable compilation snapshot.

4.2 Canonical file-local occurrence identity

Each semantically addressable occurrence in one file receives a deterministic local ID from one canonical preorder traversal.

Conceptually:

  0 = file root
  1 = first indexed child
  2 = next preorder occurrence
  ...

The public raw key is:

  Record NodeKey := {
    node_file  : FilePath;
    node_local : LocalNodeId
  }.

`LocalNodeId` should be abstract to callers.

Its implementation is selected in Checkpoint C0.

4.3 Snapshot-indexed validated references

  Record NodeRef (p : GoProgram) := {
    node_file  : FileRef p;          (* a validated file root of THIS p, carried — not recomputed *)
    node_local : LocalNodeId;
    node_valid : ValidLocal p node_file node_local
  }.

`NodeRef` is indexed by the EXACT source snapshot `p`, never by free-standing index data.  Two different
programs with identical paths and identical tree shape but different literal payloads must NOT share a
`NodeRef` type: a reference belongs to one immutable source program, so `SyntaxIndex`, `FileRef`, and
`NodeRef` are all parameterised by `p` and are not interchangeable across snapshots (enforced at the type
level — a `NodeRef p1` cannot be used where a `NodeRef p2` is expected).

A `NodeRef` CARRIES (directly projects) a validated `FileRef p`; the public identity is the file PATH plus
the local id (`node_key := (file path, local)`).  The hidden per-file slot inside `FileRef` is a private
optimization handle — never the public key, never rendered.  There is no free-standing key re-validated on
every navigation step.

The constructor is private.

References are produced by:

- indexed traversal;
- validated lookup;
- compiler facts;
- diagnostic construction.

Node equality is key equality, not proof-field equality and not syntax-fragment equality.

Use proof-irrelevant / `SProp` validity fields where appropriate.

4.4 Typed references

Define one occurrence kind authority:

  SyntaxKind :=
    KFile
    KPackageClause
    KImportSpec
    KTopLevelDecl
    KDeclaration
    KFunctionDecl
    KMethodDecl
    KSignature
    KParameterDecl
    KResultDecl
    KField
    KType
    KStatement
    KExpression
    KIdentifier
    ...

Only currently live kinds need constructors immediately.

Then:

  NodeRefOf p k

and aliases such as:

  FileRef p
  DeclRef p
  TypeRef p
  ExprRef p
  SignatureRef p
  NameRef p

Role-specific refinements may later distinguish:

- declaration name;
- reference name;
- package name;
- parameter name;
- field name.

Do not invent a second identity system for each role.

4.5 Derived syntax index

Create one dedicated structural module:

  GoIndex.v

It imports source syntax.

It does not import `GoTypes` or `GoCompile`.

It derives:

  SyntaxIndex p

from one `GoProgram p`.

The index is not author-supplied.

It is not mutable.

It is not a second AST.

It is a certified navigation index over the original source forest.

It carries (or implies) an EXACT source/index correspondence — `IndexDescribesForest` — proved BOTH ways: every
metadata entry corresponds to exactly one canonical preorder occurrence of the snapshot, AND every occurrence
has exactly one entry, with NO entry at a location the source does not occupy.  A one-directional "real entries
are correct" invariant is fail-open (it admits spurious entries beside an unused proof field) and is forbidden;
the correspondence must pin absence as well as presence, and it drives the total query API.

4.6 Core metadata

The selected implementation should use small structural metadata, conceptually:

  Record NodeMeta := {
    node_kind        : SyntaxKind;
    node_parent      : option LocalNodeId;
    node_role        : NodeRole;
    node_subtree_end : LocalNodeId
  }.

`NodeRole` records how an occurrence participates in its parent, for example:

- file package clause;
- file declaration N;
- declaration body;
- statement N;
- println argument N;
- conversion operand;
- later:
  - parameter name N;
  - parameter type;
  - struct field type;
  - method signature.

Do not store the full recursive syntax subtree in every metadata entry.

4.7 Public navigation API

At minimum:

  parent_of :
    SyntaxIndex p ->
    NodeRef p ->
    option (NodeRef p)

  children_of :
    SyntaxIndex p ->
    NodeRef p ->
    list (NodeRef p)

  containing_file :
    NodeRef p ->
    FileRef p

  node_kind :
    SyntaxIndex p ->
    NodeRef p ->
    SyntaxKind

  is_ancestor :
    SyntaxIndex p ->
    NodeRef p ->
    NodeRef p ->
    bool

  traverse_file :
    syntax + canonical NodeRef together

The ordinary compiler traversal must receive the original syntax fragment and its `NodeRef` together.

It should not repeatedly perform random syntax lookup.

API honesty (binding).  Structurally guaranteed queries are TOTAL — no `option`, no invented fallback:
`containing_file`, `ref_meta`, `node_kind`, `node_role`, `node_subtree_end`, and `children_of` all return a
real result for every valid `NodeRef`.  ONLY `parent_of` is optional, and its single `None` is the honest
root case (a root has no parent).  `node_kind` returns the INDEXED kind — it never manufactures a `KFile`
(or any other) placeholder; `children_of` enumerates every direct child and drops none.  An impossible index
inconsistency (a validity proof contradicting the table) is discharged by the carried validity evidence via
a total extraction from a proven-present option, NOT by a semantic default that would fabricate a plausible
answer.

Navigation from an existing `NodeRef` performs NO file-list scan: the carried `FileRef`'s hidden slot indexes
directly into the slot-keyed outer table (one outer lookup), then one per-file metadata lookup — O(log files)
+ O(log nodes/file), never a linear `List.find` over the files.

Raw `NodeKey` lookup (`ref_of_key` / `file_of_path`) is a SEPARATE minting boundary with its own separately
stated cost.  It is the one place a path is resolved by scanning the file list once (path → slot), then
validated THROUGH the precomputed index (outer-slot + per-file lookup) — it never rebuilds the per-file
index.  Cost O(files + log files + log nodes/file).  The hot path from an existing `NodeRef` never uses it.
`ref_of_key` is proved sound (a returned reference carries exactly the queried key) and complete (minting from
any reference's own key recovers exactly that reference).

4.8 Efficiency contract

“Derived” means one indexing pass per immutable program snapshot.

It does NOT mean search from the file root on every query.

Forbidden implementation:

  parent_of(node):
    search the AST until an equal child is found

Required asymptotic shape:

- build index:
  - O(n) with a suitable builder, or
  - O(n log n) with a certified persistent table;
- containing file:
  - O(1) projection from the reference;
- immediate parent:
  - O(1) with an audited dense table, or
  - O(log n) with a certified trie/map;
- walk upward d levels:
  - O(d) or O(d log n);
- direct children:
  - proportional to the number of direct children, modulo table lookup;
- ancestor test:
  - constant-time arithmetic after metadata lookup using preorder intervals;
- no whole-file search in parent navigation;
- no list-backed linear node-table lookup in the final certified path;
- no O(n²) repeated append during index construction.

The indexer must visit each source occurrence once and insert each metadata entry once.

Use:

- reverse accumulation;
- difference lists;
- a certified table builder;
- or another asymptotically honest construction.

4.9 Candidate node-table implementations

Checkpoint C0 must compare at least:

A. a certified positive-key trie / Patricia-style table;

B. a dense primitive array or equivalent, only if:
   - its assumption closure is empty;
   - its kernel/trust story is acceptable under Fido's zero-axiom policy;
   - its executable behavior is reliable under the pinned Rocq toolchain;
   - its proofs remain maintainable.

Do not select a list table merely because it is easy to prove.

The proof spike chooses the physical representation.

The public `NodeTable` API must hide that choice.

4.10 Children from preorder intervals

With preorder local IDs and `subtree_end`:

- first child, if any, begins immediately after the parent;
- next sibling begins at `subtree_end(child) + 1`;
- direct children can be enumerated by jumping over whole child subtrees;
- ancestor relation is interval containment within the same file.

Cache `first_child` / `next_sibling` only if real use justifies it.

Do not add fields by reflex.

4.11 Occasional syntax recovery

The hot compiler path gets syntax and reference together during traversal.

For occasional diagnostic inspection, a helper may recover a syntax occurrence by:

- following the parent chain;
- using stored roles;
- descending from the file root.

That may cost O(depth), not O(file size).

Do not flatten and duplicate the entire AST merely to make rare random syntax inspection constant-time.

If a later measured workload needs a compact nonrecursive syntax-view cache, add it behind the same `GoIndex` API as a derived optimization.

That must not become a second syntax authority.

4.12 Foundational index theorems

Prove at least:

1. every file root has local ID zero;
2. every file root has no parent;
3. every non-root occurrence has exactly one parent;
4. parent/child are inverse:
   - `parent_of child = Some parent`
   - iff child is an immediate child of parent;
5. parent and child belong to the same file;
6. every occurrence is reachable from its file root;
7. every occurrence appears exactly once in canonical enumeration;
8. `NodeKey` equality decides occurrence identity;
9. repeated structurally equal fragments in different places have distinct refs;
10. `containing_file` agrees with `node_file`;
11. children are in source order;
12. index construction is deterministic;
13. preorder interval ancestry is sound and complete;
14. metadata describes the original AST, not a copied invented tree.

===============================================================================
PART 5 — RESOLUTION, TYPES, AND COMPILATION FACTS
===============================================================================

5.1 Source names remain source names

The compiler must never rewrite source spelling in the AST.

Examples:

  byte
  uint8
  rune
  int32
  MyType
  pkg.OtherType

remain their source-selected syntax.

Compilation attaches semantic meaning to their occurrences.

5.2 References are separate facts

A source name use is a source occurrence.

Its resolved target is a separate fact.

Conceptually:

  SymbolRef p :=
    SourceSymbol DeclRef
    PredeclaredSymbol PredeclaredId
    later ImportedSummarySymbol ...

  ResolveResult p :=
    Resolved SymbolRef
    Unresolved
    Ambiguous (list SymbolRef)

Do not replace source identifiers with declaration objects in the AST.

5.3 Nominal identity

A source-defined type's nominal identity should be its defining declaration occurrence, or a thin opaque wrapper around that occurrence.

No random symbol ID is needed if the defining `NodeRef` is already canonical in the immutable snapshot.

Predeclared identities remain a small closed domain.

5.4 Semantic types remain origin-free

`GoTypes` should eventually parameterize named semantic types by a nominal identity type supplied by compilation.

Conceptually:

  SemanticType NominalId :=
    TBool
    TInteger IntegerType
    TFloat FloatType
    TComplex ComplexType
    TString
    TNamed NominalId
    TArray ...
    TSlice ...
    TStruct ...
    TPointer ...
    TFunc ...
    TMap ...
    TChan ...
    TInterface ...

Do not add future constructors before their source syntax and semantics land.

5.5 Signatures

Source signatures preserve names and spellings.

Semantic signatures contain only:

- ordered parameter semantic types;
- ordered result semantic types;
- variadicness.

Parameter and result names remain in the AST and are available by occurrence reference.

They do not enter function-type or interface-method identity.

5.6 Compilation facts decorate occurrences

Successful facts are occurrence-indexed.

Only add live facts needed by current syntax.

The long-term shape may include:

  resolved_reference_at
  declaration_symbol_at
  resolved_type_at
  expression_type_at
  resolved_signature_at
  type_definition_body_at
  package_facts
  method_set_facts
  interface_facts

Do not add empty speculative fields simply because the roadmap names them.

5.7 No second compiler authority

`GoCompile` owns:

- package grouping;
- package-clause consistency;
- scopes;
- declarations;
- name resolution;
- alias resolution;
- nominal identities;
- type-syntax resolution;
- recursive validity;
- use of `GoTypes` relations;
- diagnostics;
- whole-program validity.

`GoTypes` owns the semantic relations themselves.

`GoCompile` may be split into internal modules for manageability.

That is module factoring, not a second compiler authority.

===============================================================================
PART 6 — DIAGNOSTICS
===============================================================================

6.1 Diagnostic anchors

  DiagnosticAnchor p :=
    AtNode NodeRef
    AtFile FileRef
    AtPackage PackageKey
    AtProgram

Use node anchors when syntax exists.

Use file/package/program anchors for absence errors.

Do not invent fake AST nodes for missing declarations.

6.2 Structured diagnostics

Diagnostics should carry:

- diagnostic code;
- primary anchor;
- related anchors;
- structured payload.

They should not carry authoritative English prose in the proof core.

Examples:

- invalid constant conversion:
  - primary conversion expression;
- default constant overflow:
  - primary literal expression;
- duplicate main:
  - primary later declaration;
  - related earlier declaration;
- no main:
  - package anchor;
- unresolved type:
  - primary type-name occurrence;
- duplicate parameter:
  - primary later name;
  - related earlier name;
- interface mismatch:
  - primary required signature;
  - related provided signature.

6.3 Deterministic order

Canonical diagnostic order:

1. file path;
2. local node ID;
3. diagnostic code;
4. related keys as a tie-breaker where needed.

Package/program-only errors receive a documented deterministic position.

Storage order of `GoFileSet` must not affect diagnostics.

6.4 Analysis result

The permanent direction is:

  AnalysisResult p :=
    AnalysisOK (CompilationFacts p)
    AnalysisFailed (NonEmpty (Diagnostic p))

The proof-producing compiler remains exact against one declarative whole-program judgment.

If `go_compile` remains as a convenience API, it must be a projection of the one analysis root.

It may not independently recompute validity.

6.5 Diagnostic proof surfaces

Prove:

- every node anchor belongs to the diagnosed program;
- every file anchor belongs to the program;
- successful analysis yields no diagnostics;
- failed analysis yields at least one diagnostic;
- analysis success iff declarative compilation holds;
- analysis failure iff no valid compilation facts exist, under the selected exact theorem;
- diagnostic order is deterministic;
- no diagnostic stores a copied AST node as its identity;
- no semantic type carries source location.

===============================================================================
PART 7 — RENDERING
===============================================================================

7.1 Render the original source AST

`GoRender` traverses the original source forest.

It preserves source-selected semantic spellings:

- package clause;
- import binding choice;
- declaration names;
- parameter/result names;
- selected type names;
- alias versus definition syntax;
- expression structure.

7.2 Canonical presentation

The renderer chooses one canonical concrete spelling for presentation-equivalent forms:

- one import block style;
- one whitespace policy;
- one semicolon policy;
- one parenthesization policy;
- existing canonical literal spellings.

7.3 Semantic type does not choose source spelling

Example:

  AST says `byte`
  GoCompile resolves it to semantic `uint8`
  GoTypes treats it as identical to `uint8`
  GoRender still emits `byte`

This is the core source/meaning split.

7.4 `go.mod`

`go.mod` remains rendered separately from `ModuleSpec`.

It is not a `GoSourceFile`.

===============================================================================
PART 8 — RESPONSIBILITY TABLE
===============================================================================

GoSyntax / GoAST

Owns:

- specification-shaped abstract syntax;
- source-selected identifiers and names;
- required/optional/repeated grammar structure;
- downward ownership;
- intrinsic lexical validity.

Does not own:

- binding;
- semantic types;
- package identity;
- diagnostics;
- parent pointers;
- source spans.

GoFileSet / GoProgram

Owns:

- module snapshot;
- path-bearing file roots;
- unique file paths;
- order-independent file-set meaning.

Does not own:

- package validity;
- import validity;
- expression typing.

GoIndex

Owns:

- canonical occurrence identity;
- node kind;
- parent/child navigation;
- containing file;
- deterministic occurrence order;
- structural roles;
- preorder intervals.

Does not own:

- name resolution;
- semantic types;
- compiler acceptance;
- copied syntax.

GoTypes

Owns:

- exact constants;
- intrinsic typed constants;
- semantic type identity;
- underlying types;
- assignability;
- conversion legality;
- representability;
- comparability;
- nilability;
- signature identity;
- methods/interfaces when landed.

Does not own:

- source spelling;
- scopes;
- import resolution;
- diagnostic locations.

GoCompile

Owns:

- whole-program package structure;
- scopes and declarations;
- binding and resolution;
- alias/defined-type handling;
- nominal IDs;
- type-syntax resolution;
- recursive validity;
- invocation of GoTypes relations;
- occurrence-indexed facts;
- diagnostics;
- exact compiler judgment.

Does not own:

- AST rewriting;
- pretty printing;
- another type relation universe.

GoRender

Owns:

- canonical concrete Go spelling of original source syntax.

Does not own:

- name resolution;
- package inference;
- type normalization.

GoSafe

Owns:

- guarantees beyond compiler acceptance over the same compiled program.

SourceMap, later

Owns:

- optional `NodeRef -> SourceSpan`.

Does not own:

- occurrence identity;
- semantic meaning.

===============================================================================
PART 9 — FORBIDDEN DESIGNS
===============================================================================

Do not introduce:

- parent pointers inside recursive syntax values;
- an arena graph as the authoritative source AST;
- author-assigned node IDs;
- a global freshness obligation for syntax construction;
- a public structural path datatype mirrored across every grammar constructor;
- a zipper as the public compiler/diagnostic identity;
- a typed AST;
- a copied resolved program;
- semantic types carrying source names or locations;
- one universal normalized representative type;
- list-backed O(n) node-table lookup in the final index;
- whole-tree search in `parent_of`;
- repeated `index_program` recomputation per query;
- O(n²) append-based index construction;
- a flattened syntax cache that becomes independently authoritative;
- arbitrary package/import syntax before its semantics;
- feature growth hidden inside the migration.

===============================================================================
PART 10 — GLOBAL PROOF, PERFORMANCE, AND BEHAVIOR GATES
===============================================================================

Every checkpoint must preserve:

- zero Fido axioms;
- whole-certified-theory audit coverage;
- no `Admitted`;
- no `Parameter`/`Axiom` escape;
- one raw AST authority;
- `go build ./...` acceptance for every emitted certified program;
- go vet diagnostic-only;
- existing generated ownership/sink behavior;
- no force push;
- staged-tree verification;
- byte-exact generated artifact checks when a checkpoint declares bytes unchanged.

Performance claims must be honest:

- complexity is part of the architecture;
- where Rocq does not prove asymptotics directly, the implementation shape and selected table's documented complexity must support the claim;
- benchmark evidence may supplement but never replace semantic proofs;
- no user-facing claim may call a list scan constant-time.

===============================================================================
PART 11 — CHECKPOINT MAP
===============================================================================

C0 — Preflight cleanup and occurrence-index proof spike

Purpose:

- close small residue from the complex review;
- select the physical NodeTable / LocalNodeId representation;
- prove the occurrence/index idea in isolation.

No production AST migration.

C1 — Specification-shaped file roots and path-keyed source forest

Purpose:

- replace map[path, declaration-list] with path-bearing file roots;
- move the package clause into source syntax;
- preserve current semantics and generated bytes.

No occurrence index yet.

C2 — Production occurrence index and navigation

Purpose:

- land GoIndex;
- canonical NodeRef;
- efficient parent/children/file navigation;
- integrate traversal references through the current source forest.

No diagnostic redesign yet.

C3 — Occurrence-anchored diagnostics and compilation facts

Purpose:

- make compiler failures say where and why;
- make successful facts occurrence-indexed;
- retain one analysis root and no typed AST.

No new Go language feature.

C4 — Source type-name syntax and contextual resolution foundation

Purpose:

- make source type spelling a syntax occurrence;
- establish source name -> semantic type resolution;
- remove resolved semantic type tags from permanent raw conversion syntax only when exact current semantics permit it.

This checkpoint may be split into C4a/C4b after C3 human review.

C5 — Complete predeclared numeric identity and rune constants

Purpose:

- `uintptr`;
- `byte`/`rune` alias resolution;
- exact rune constant kind and defaulting;
- canonical rune rendering;
- complete current predeclared numeric universe.

No arithmetic.

C6 — Campaign closeout and holistic audit, only if needed

Purpose:

- remove transitional adapters;
- reconcile permanent docs;
- perform one holistic review from the source root through emission;
- freeze the foundation before structural types.

Do not activate C6 automatically if C5 already leaves no residue.

===============================================================================
PART 12 — CHECKPOINT C0
===============================================================================

C0 ACTIVE SCOPE

C0 is the first checkpoint to copy into `.review/NEXT_STEPS.md`.

C0.1 Preflight residue

Fix the small accepted cleanup items from the complex review:

1. GoSafe prose that says invalid raw syntax contains only integer/float conversions:
   include complex conversion.

2. The assumptions-gate renderer summary:
   include complex literal / complex conversion recognizers.

3. `CompileError` prose:
   include complex component overflow and nonzero-imaginary scalar conversion.

4. Add the explicit underflow-boundary scar in kernel and pinned-Go differential form:

     int(complex(3, tinyNonzeroImag))             rejects
     int(complex64(complex(3, tinyNonzeroImag)))  accepts when the explicit
                                                   complex64 boundary rounds
                                                   the imaginary component to zero

Use a reviewed tiny value that pinned Go 1.23 treats as intended.

The formal model must observe:

- the exact untyped imaginary value before conversion;
- the rounded typed-complex exact value after conversion;
- the scalar conversion rule checking the current exact typed value.

C0.2 Isolated proof spike

Create an isolated, temporary, axiom-free spike module.

Use a tiny toy source grammar with:

- two file roots;
- declarations;
- statements;
- nested expressions;
- two structurally equal leaf expressions in different positions.

Prototype:

- file-local preorder IDs;
- NodeKey;
- validated NodeRef;
- NodeKind;
- NodeRole;
- NodeMeta;
- selected NodeTable;
- parent_of;
- children_of;
- containing_file;
- subtree interval ancestry;
- one-pass builder.

Do not integrate this spike into production GoAST yet.

C0.3 Representation comparison

Compare at least:

A. positive-key trie / Patricia-style persistent table;

B. primitive/dense array support available in the pinned Rocq version.

For each candidate record:

- assumption closure;
- trust implications;
- lookup complexity;
- construction complexity;
- proof ergonomics;
- computation behavior under `vm_compute` / native evaluation as appropriate;
- extraction/runtime implications if any;
- equality/proof irrelevance ergonomics.

Choose one.

Do not leave two production candidates live.

C0.4 Required spike proofs

Prove:

- root ID is canonical;
- root has no parent;
- every non-root has one parent;
- parent/child inverse;
- same-file parentage;
- containing file recovery;
- deterministic enumeration;
- equal leaves in two positions have unequal refs;
- decidable NodeKey equality;
- sound preorder interval ancestor test;
- index builder does not depend on structural equality search.

C0.5 Performance inspection

The implementation must visibly avoid:

- source-tree search in parent lookup;
- list scan in final node-table lookup;
- repeated append to the end of a growing list;
- repeated index reconstruction.

Add a focused benchmark or computation probe if useful, but do not present benchmarking as a proof of semantics.

C0.6 Decision record

Update `.review/SOURCE_FOREST_STATUS.md` with:

- selected LocalNodeId representation;
- selected NodeTable representation;
- selected metadata fields;
- build/query complexity;
- rejected alternatives and reasons;
- proof-spike commit SHA.

If a minor internal choice remains undecided, name it.

Do not leave the ownership or identity architecture undecided.

C0.7 Review cadence

C0 is small and isolated.

Use only one intentional Codex stop:

- final exhaustive review.

After green:

- run full existing repository verification;
- commit C0 complete;
- fast-forward push;
- notify Rob;
- stop.

Do not begin C1.

C0.8 C0 acceptance

- residue fixed;
- underflow scar pinned;
- proof spike axiom-free;
- efficient table selected;
- required structural proofs closed;
- current generated bytes unchanged;
- current e2e green;
- master architecture either confirmed or architectural conflict reported;
- pushed;
- loop stopped.

===============================================================================
PART 13 — CHECKPOINT C1
===============================================================================

C1 is activated only after human approval of C0.

C1.1 Replace the file root

Introduce:

  GoSourceFile
  GoFileNode
  GoFileSet
  GoProgram

Use the specification-shaped source-file categories.

For current live scope:

- package clause is source-owned canonical `package main`;
- imports are unrepresentable / intrinsically empty;
- top-level declarations contain only the current main-function form.

Do not broaden package/import semantics.

C1.2 Remove the declaration-list alias as the file authority

Delete the permanent equation:

  GoFileAST := list GoDecl

A list of declarations may remain as the `source_decls` field.

It is no longer the entire file.

C1.3 Move file path into the file-root node

Every source file root carries its `FilePath`.

`GoFileSet` enforces path uniqueness.

Do not retain a parallel outer map key and inner file-path field.

One path authority only.

C1.4 File-set API and laws

Provide:

- constructor/build function;
- lookup by path;
- membership;
- path enumeration;
- duplicate-path unrepresentability;
- extensional equality by lookup;
- order-independent semantic facts.

Existing users should consume the abstraction, not the backing list.

C1.5 Package clause responsibility

Move package spelling from `CompilationFacts` to `GoSourceFile`.

Delete `cf_pkg_name` or any replacement whose only purpose is to tell the renderer what the source file says.

`GoCompile` still proves:

- files are grouped correctly by path;
- the current package clause is valid for the current generated-package policy;
- package-level main rules.

`GoRender` renders the AST package clause.

C1.6 Pipeline migration

Migrate:

- GoCompile;
- GoSafe;
- GoRender;
- GoEmit;
- witnesses;
- empty program;
- multi-package differential;
- directory image;
- pre-commit verification;
- documentation;
- assumption gate.

No temporary adapter may remain at final green if it is a second file authority.

C1.7 Behavior preservation

Generated bytes must remain byte-identical.

The current source forest renders the same `package main` files.

The sink behavior and recursive path set remain unchanged.

C1.8 Root review

Use one semantic-root stop after:

- GoSourceFile / GoFileNode / GoFileSet exist;
- path uniqueness and lookup laws are proved;
- package clause is source-owned;
- old map[path, AST] authority is deleted;
- local core compiles;
- generated pipeline integration may still be incomplete.

Commit:

  milestone(root): C1 — specification-shaped file roots and keyed file set

Repair under:

  review(root):

Do not proceed to final integration until root green.

C1.9 Final review

After root green:

- complete full pipeline migration;
- remove adapters;
- update docs/gates;
- prove behavior preservation;
- verify byte identity;
- commit:

  milestone(final): C1 — integrate the source forest through emission

Repair under:

  review(final):

After final green:

- verify;
- push;
- notify;
- stop.

C1.10 C1 acceptance

- one source file root;
- one path authority;
- one path-keyed set;
- package clause in AST;
- no imports represented;
- current semantics unchanged;
- no copied program;
- generated bytes unchanged;
- full proof/e2e/staged checks green;
- pushed;
- loop stopped.

===============================================================================
PART 14 — CHECKPOINT C2
===============================================================================

C2 is activated only after human approval of C1.

C2.1 Land production GoIndex

Create:

  GoIndex.v

Use the C0-selected table and ID representation.

The spike module should be deleted or reduced to tests once production proofs subsume it.

Do not keep a parallel spike authority.

C2.2 Enumerate current semantic source occurrences

Index at least:

- file root;
- package clause;
- top-level declaration;
- statement;
- expression;
- each nested expression occurrence.

Do not index:

- list-container nodes;
- fixed punctuation;
- whitespace;
- generated keywords.

Later syntax kinds grow locally.

C2.3 One canonical index construction

Provide one deterministic:

  index_file
  index_program

The compiler must let-bind/build the index once per analysis snapshot.

Do not call `index_program` independently from every query.

C2.4 NodeRef and typed refs

Land:

- NodeKey;
- NodeRef p;
- NodeRefOf p k;
- FileRef;
- DeclRef;
- StmtRef;
- ExprRef;
- package-clause ref as appropriate.

Hide raw constructors.

Prove decidable key/ref equality.

C2.5 Navigation

Land:

- parent_of;
- children_of;
- containing_file;
- node_kind;
- node_role;
- is_ancestor;
- canonical traversal returning syntax and ref together.

Parent queries use metadata lookup only.

C2.6 Structural proofs

Close every theorem in Part 4.12 relevant to current syntax.

Add explicit repeated-expression fixture:

  println(1, 1)

and prove the two `EInt 1` occurrences have distinct refs while yielding equal syntax fragments.

C2.7 Compiler integration without semantic redesign

Thread `SyntaxIndex` / NodeRef through traversal infrastructure.

Do not redesign diagnostics yet.

Existing compiler/type logic may continue computing the same semantic judgments over syntax fragments.

This checkpoint establishes occurrence identity, not new language meaning.

C2.8 Root review

Stop after:

- production index exists;
- efficient parent lookup exists;
- NodeRef/typed refs exist;
- full structural theorem family is green;
- repeated-equal-occurrence identity is proven;
- no production compiler integration beyond traversal is required yet.

Commit:

  milestone(root): C2 — canonical occurrence index and parent navigation

Repair under:

  review(root):

C2.9 Final review

After root green:

- integrate indexed traversal through current compiler/render proof infrastructure where appropriate;
- ensure the index is built once;
- delete spike/adapter residue;
- update docs and gate;
- keep generated bytes unchanged.

Commit:

  milestone(final): C2 — integrate snapshot-local NodeRef through the source forest

After green:

- verify;
- push;
- notify;
- stop.

C2.10 C2 acceptance

- no parent search;
- no list-backed node table;
- one derived index;
- canonical NodeRef;
- typed refs;
- complete structural proofs;
- current language behavior unchanged;
- generated bytes unchanged;
- pushed;
- loop stopped.

===============================================================================
PART 15 — CHECKPOINT C3
===============================================================================

C3 is activated only after human approval of C2.

C3.1 Introduce structured diagnostic anchors

Land:

- AtNode;
- AtFile;
- AtPackage;
- AtProgram.

Every node diagnostic carries a valid NodeRef into the exact rejected program snapshot.

C3.2 Replace coarse current failures

Current failures should gain precise anchors:

- invalid literal/default representability:
  - literal ExprRef;
- invalid explicit conversion:
  - conversion ExprRef;
- invalid nested conversion:
  - innermost failing occurrence as primary;
  - outer occurrence as related where useful;
- duplicate main:
  - later declaration primary;
  - earlier declaration related;
- package with no main:
  - package anchor;
- whole-program structural failures:
  - appropriate file/package/program anchor.

Keep diagnostic codes small and exact.

C3.3 One analysis root

Introduce the permanent analysis direction:

  AnalysisResult p

If old `go_compile` remains, make it a projection of `analyze`.

Delete independent duplicated checks.

C3.4 Occurrence-indexed successful facts

Add only currently useful facts, for example:

- resolved type / resolved constant at expression occurrences;
- package grouping and entry facts at file/package occurrences.

Do not add speculative empty reference/method/interface tables yet.

Prove every fact key is a valid occurrence of the right kind.

C3.5 Deterministic diagnostics

Canonicalize diagnostic order independently of `GoFileSet` storage order.

Add tests with:

- multiple invalid expressions;
- duplicate mains;
- files inserted in different physical orders.

Prove/verify equal semantic file sets produce equal ordered diagnostics under the selected extensional notion.

C3.6 Exactness theorems

Prove:

- `AnalysisOK facts` iff declarative compile judgment;
- `AnalysisFailed ds` yields nonempty valid diagnostics;
- no valid facts exist on failure, under the selected theorem;
- success has no diagnostics;
- current `CompilableProgram` is produced only from `AnalysisOK`;
- renderer/emitter still require compiled/safe evidence.

C3.7 No typed AST

Audit the repository for:

- copied expression nodes in fact tables;
- resolved syntax trees;
- diagnostic identity by copied syntax value;
- parent/path duplication.

Delete any such residue.

C3.8 Root review

Stop after:

- diagnostic types exist;
- current compiler errors have valid anchors;
- one analysis root exists;
- exact success/failure theorem core is green;
- downstream report formatting and broad fixtures may remain.

Commit:

  milestone(root): C3 — occurrence-anchored analysis and diagnostics

C3.9 Final review

After root green:

- complete all diagnostics;
- deterministic order;
- reports/tests/docs;
- compiler/e2e integration;
- no behavior drift except improved structured error evidence.

Commit:

  milestone(final): C3 — complete occurrence-indexed compilation facts and diagnostics

After green:

- verify;
- push;
- notify;
- stop.

C3.10 C3 acceptance

- every current compiler failure says where and why structurally;
- every node anchor is valid;
- one analysis root;
- occurrence-indexed facts;
- deterministic diagnostics;
- no typed AST;
- no generated-byte drift unless explicitly reviewed;
- pushed;
- loop stopped.

===============================================================================
PART 16 — CHECKPOINT C4
===============================================================================

C4 is activated only after a dedicated human design review of C0-C3.

The architecture below is preserved now so it is not lost.

The exact live source-name subset may be refined before activation.

C4.1 Source identifier domain

Introduce an intrinsic source identifier domain.

A deliberately bounded ASCII subset is acceptable initially:

  [A-Za-z_][A-Za-z0-9_]*

with keywords excluded where the grammar requires an identifier.

Valid non-ASCII Go identifiers may remain unrepresentable if that scope is stated honestly.

Do not use raw unchecked strings.

C4.2 Specification-shaped type-name syntax

The permanent direction:

  TypeNameSyntax :=
    Unqualified IdentifierSyntax
    Qualified IdentifierSyntax IdentifierSyntax

  TypeSyntax :=
    TSName TypeNameSyntax
    later:
      arrays
      structs
      pointers
      functions
      interfaces
      slices
      maps
      channels

Only live constructors are added.

Type-name occurrences are indexed by GoIndex.

C4.3 Predeclared universe is compiler context

Predeclared names are not semantic constructors in the AST.

`GoCompile` resolves source names through the current scope chain and universe declarations.

Eventually, source declarations may shadow predeclared names according to Go rules.

Do not hard-code “the source spelling byte always means builtin byte” into semantic AST constructors.

C4.4 Conversion source syntax

The permanent direction is a source conversion whose target is source type syntax.

Do not delete the family-specific current conversion nodes until exact replacement semantics exist for every newly representable target.

Before `EConvert TypeSyntax Expr` becomes live:

- audit every type name made representable as a conversion target;
- model every accepted conversion from the currently representable operand domain;
- make unsupported target forms unrepresentable rather than blanket-rejected.

This is a vertical feature, not a cosmetic node rename.

C4.5 Possible checkpoint split

C4 may be split after human review into:

C4a:
- identifier/type-name syntax;
- universe-scope resolution;
- occurrence-indexed resolved type facts;
- unresolved-name diagnostics;
- no conversion migration yet.

C4b:
- unified source conversion syntax;
- migration from semantic target tags;
- exact conversion coverage;
- deletion of old conversion nodes.

Do not combine them merely to reduce checkpoint count if the semantic root becomes muddy.

C4.6 Source/semantic spelling proof

Required representative fact:

  source `byte` occurrence
    -> resolves through compiler context
    -> semantic type `uint8`
    -> renderer still emits `byte`

Likewise:

  rune -> int32

Parameter and result names remain source occurrences and do not enter semantic signature identity.

C4.7 Review cadence

C4a/C4b are foundational.

Each activated subcheckpoint may use:

- one root review;
- one final review.

Stop and push between them if split.

===============================================================================
PART 17 — CHECKPOINT C5
===============================================================================

C5 is activated only after C4 is accepted.

C5.1 Complete numeric semantic identity

Add the one remaining genuine numeric type:

  uintptr

It must be:

- a distinct semantic integer type;
- unsigned;
- pinned to 64 bits for current linux/amd64 scope;
- range-equivalent to uint64 on that target;
- type-distinct from uint and uint64.

Do not add pointer or unsafe semantics.

C5.2 Aliases

Source names:

  byte
  rune

resolve through the compiler's predeclared universe as aliases:

  byte -> uint8
  rune -> int32

Do not add:

  TByte
  TRune
  IByte
  IRune

The renderer preserves the selected source name.

C5.3 Rune constant kind

Add exact untyped rune constants distinct from ordinary untyped integer constants.

Conceptually:

  CRune RuneValue

A rune literal:

- carries an exact Unicode scalar value;
- defaults to rune, therefore semantic int32;
- does not default to platform int.

The `RuneValue` domain should intrinsically enforce the chosen exact Go-valid scalar range.

Run targeted pinned-Go experiments for:

- U+0000;
- ASCII;
- quote/backslash;
- U+007F;
- U+00FF;
- BMP non-ASCII;
- supplementary-plane value;
- surrogate rejection;
- above-U+10FFFF rejection.

C5.4 Rune rendering

Choose one canonical ASCII source spelling per RuneValue.

A simple candidate:

- `'\uXXXX'` for BMP scalar values;
- `'\UXXXXXXXX'` for supplementary scalar values;
- lowercase or uppercase hex chosen once and pinned.

Use an independent certified decoder.

Prove semantic round trip.

Do not preserve arbitrary human rune-literal spelling.

C5.5 Constant/default/conversion integration

Extend:

- GoConst;
- TypedConst/defaulting;
- numeric conversion;
- GoSafe runtime values;
- renderer denotation;
- compiler facts;
- diagnostics;
- proof gate;
- e2e differential.

A typed rune is ordinary typed int32.

A rune constant remains distinguishable only while untyped.

C5.6 Source-name fixtures

Cover:

- `byte(65)` versus `uint8(65)`:
  - different source spellings;
  - identical semantic type;
- `rune(65)` versus `int32(65)`:
  - different source spellings;
  - identical semantic type;
- bare `65`:
  - defaults to int;
- bare `'A'`:
  - defaults to rune/int32;
- uintptr min/max/overflow;
- uintptr distinctness from uint/uint64.

C5.7 No operations

Do not add:

- arithmetic;
- rune/string operations beyond any conversion semantics strictly required by the represented conversion grammar;
- pointers;
- unsafe;
- arrays/slices;
- imports.

C5.8 Campaign validation

C5 is the first feature checkpoint that deliberately stresses:

- source spelling in AST;
- contextual name resolution;
- alias identity;
- semantic type relations;
- occurrence-indexed diagnostics;
- original-AST rendering.

If C5 requires foundational changes to C0-C3 rather than local extensions, report an architectural conflict.

C5.9 Review cadence

Use root and final reviews.

After final green:

- run a holistic source -> index -> compile -> type -> render -> Go differential audit;
- push;
- notify;
- stop.

Do not begin structural types.

===============================================================================
PART 18 — POST-CAMPAIGN ROADMAP
===============================================================================

After this campaign, resume the Static Type Universe Arc:

1. arrays;
2. slices;
3. pointers;
4. structs;
5. maps;
6. channels;
7. function types/signatures;
8. type aliases and defined types;
9. recursive validity;
10. method signatures and method sets;
11. non-generic value interfaces;
12. imports/package scopes when their closed-world model is ready;
13. only then operations consuming those roots.

Every future syntax production follows the same vertical rule:

  specification-shaped AST
    -> occurrence indexing
    -> binding/resolution
    -> semantic relations
    -> diagnostics
    -> rendering
    -> proofs
    -> pinned-Go differential

===============================================================================
PART 19 — CAMPAIGN CLOSEOUT
===============================================================================

At campaign closeout, verify:

Source authority

- one GoProgram;
- one path-keyed source-file set;
- one GoSourceFile shape;
- package clause source-owned;
- no outer path map plus inner path duplication;
- no declaration-list masquerading as a complete source file.

Occurrence authority

- one SyntaxIndex;
- one NodeRef identity;
- no parent fields in AST;
- no author IDs;
- no public paths/zippers;
- efficient parent lookup;
- canonical containing-file recovery.

Semantic authority

- GoCompile owns contextual resolution;
- GoTypes owns semantic relations;
- no semantic source spelling;
- no universal representative type;
- no typed AST.

Diagnostics

- every current failure has a valid anchor;
- absent syntax uses file/package/program anchors;
- deterministic ordering;
- source spans optional and absent today.

Rendering

- original AST rendered;
- source alias spellings preserved;
- presentation alternatives canonicalized;
- `go.mod` separate.

Proof/trust

- full zero-axiom gate;
- whole-theory coverage;
- all staged/e2e checks green;
- no stale spike/adapter;
- no hidden list scan sold as efficient indexing.

Workflow

- all checkpoint commit ranges recorded;
- root/final Codex findings and repair cost visible;
- every checkpoint pushed;
- no force push;
- final human approval recorded.

===============================================================================
PART 20 — CHECKPOINT COMPLETION REPORT
===============================================================================

For every checkpoint, report:

- master-plan commit SHA;
- active NEXT_STEPS contract SHA;
- checkpoint base SHA;
- root candidate SHA, if used;
- root Codex findings;
- root repair SHAs;
- final candidate SHA;
- final Codex findings;
- final repair SHAs;
- final checkpoint SHA;
- pushed ref and push result;
- complete commit range;
- files added/deleted/rewritten;
- representations introduced;
- representations deleted;
- every theorem added or materially changed;
- assumption-gate count and result;
- whole-theory audit result;
- `make prove`;
- `make e2e`;
- `make check`;
- staged pre-commit result;
- generated-byte result;
- pinned-Go differential result;
- known architecture conflicts, which must be zero to claim completion;
- notification result;
- confirmation loop stopped.

===============================================================================
PART 21 — C0 NEXT_STEPS ACTIVATION BLOCK
===============================================================================

When installing this master plan, copy the following block into
`.review/NEXT_STEPS.md` as the first active contract:

---

Claude Code checkpoint C0: preflight cleanup and occurrence-index proof spike

THIS IS THE ONLY ACTIVE CHECKPOINT.

The complete persistent architecture is stored at:

  .review/SOURCE_FOREST_MASTER_PLAN.md

Only this activated checkpoint is currently binding. Later checkpoints in the
master plan are preserved architectural context, not current completion criteria.

Before implementation:

1. Stop any current loop.
2. Read:
   - `.review/SOURCE_FOREST_MASTER_PLAN.md`;
   - `.review/CODEX_REVIEW_POLICY.md`;
   - `.review/SOURCE_FOREST_STATUS.md`.
3. Commit this active checkpoint contract before implementation.
4. Record the contract SHA in the status file.
5. Run:

   /loop 5m completing NEXT_STEPS until codex review is green and then notify me and stop the loop.

Implement only Master Plan Checkpoint C0.

Required work:

- fix the three stale complex-era comments described in C0.1;
- add the exact complex-underflow scalar-conversion scar described in C0.1;
- build the isolated occurrence-index proof spike;
- compare certified positive-trie and dense/primitive-array candidates;
- select one NodeTable/LocalNodeId representation;
- prove the C0 structural theorem set;
- record the decision in `.review/SOURCE_FOREST_STATUS.md`;
- preserve current generated bytes and all existing behavior.

Forbidden:

- production AST migration;
- GoFileSet;
- production GoIndex integration;
- diagnostic redesign;
- source type syntax;
- new numeric types;
- structural types;
- arithmetic;
- parent pointers;
- author-supplied IDs;
- list-backed final node lookup;
- typed AST.

Review cadence:

- one intentional final Codex stop only;
- no progress stops.

Completion:

- Codex green;
- full verification green;
- commit;
- fast-forward push;
- notify;
- stop loop;
- do not begin C1.

---

END OF MASTER PLAN
