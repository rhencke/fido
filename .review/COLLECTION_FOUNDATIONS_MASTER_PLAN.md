Claude Code directive: C1A — Standard Collection Foundations and Repository-Wide Collection Audit

Baseline repository:
  rhencke/fido
  75d24b22dfa5131738d2ede8a0e1d7bf567891b2

THIS IS A BINDING FOUNDATIONAL CORRECTION CHECKPOINT INSIDE THE SOURCE FOREST CAMPAIGN.

C1 reached Codex GREEN, but Rob's holistic review found that the collection abstraction is still wrong:
the public file “set” is an exposed list plus NoDup, the generic FMap implementation is a linear association
list, package compilation repeatedly scans file lists, and the occurrence spike contains a hand-written trie.
Those choices are not acceptable as permanent compiler foundations.

C2 remains FORBIDDEN until C1A is Codex-green, pushed, and human-approved.

This directive is intentionally complete. Before implementation, write it VERBATIM to both:

  .review/COLLECTION_FOUNDATIONS_MASTER_PLAN.md
  .review/NEXT_STEPS.md

Update:

  .review/SOURCE_FOREST_STATUS.md

to record:

- active checkpoint: C1A;
- C1 was Codex-green but human review found a repository-wide collection-model defect;
- C1 history is preserved;
- C2 is forbidden until C1A is human-approved;
- this directive is the binding completion contract.

Commit the contract/status activation before implementation:

  milestone(contract): C1A — install standard-collection migration and audit contract

Then run exactly:

  /loop 5m completing NEXT_STEPS until codex review is green and then notify me and stop the loop.

The loop is authorized only for C1A.

===============================================================================
0. EXECUTIVE OUTCOME
===============================================================================

By the end of C1A:

1. Fido contains NO project-authored general-purpose map or set implementation.

2. Every identity-keyed Rocq collection is backed by a mature implementation from the pinned Rocq standard
   library, behind a small domain wrapper where useful.

3. Every membership-only Rocq collection uses a mature standard finite-set implementation when such a
   collection is actually needed.

4. Every OCaml identity-keyed or membership-only collection uses the OCaml/Rocq runtime's mature Map/Set
   implementation rather than repeated list membership scans.

5. Lists remain only where sequence, source order, execution order, multiplicity, or stack/queue behavior is
   actually part of the meaning, or where a list is an explicitly DERIVED enumeration of a map/set.

6. The program file collection is a REAL map:

     FilePath -> GoSourceFile

   The path is the map key. It is not redundantly stored in the mapped source value.

7. The current custom FMap.v implementation is deleted.

8. The custom positive-key trie in OccurrenceSpike.v is deleted and replaced by the standard positive-key map.

9. Package grouping/counting is performed through a package map, not repeated O(files²) scans.

10. DirectoryImage uses the standard file map directly, and its list transport is a canonical derived
    enumeration.

11. The sink uses Map/Set membership for desired outputs, stale-file checks, and abandoned-temp collection.

12. All current behavior and every generated file byte remain unchanged.

13. PAINFUL_LESSONS.md permanently records the collection mistake.

This is a foundational correction, not a performance-only refactor. The collection algebra is part of the model.

===============================================================================
1. STANDING LAW
===============================================================================

Preserve all existing standing laws:

- zero project axioms;
- no Admitted;
- no kernel primitives;
- no fuel;
- one raw AST;
- no typed/copy/target/text IR;
- GoCompile exactness for represented syntax;
- generated-byte identity;
- staged-tree verification;
- go vet diagnostic-only;
- no force push;
- no new Go language feature in this checkpoint.

Add this binding collection law:

  Ordered source/execution sequence
      -> list

  Identity-keyed finite collection
      -> mature finite map

  Membership-only unordered finite collection
      -> mature finite set

  Duplicate-invalid name collection before validation
      -> map from key to a nonempty occurrence bucket

  Validated unique binding collection
      -> map from key to one value

  Graph
      -> map from vertex identity to finite adjacency set

  Stack / rollback log / queue
      -> list only when its order is operationally meaningful

  Map/set enumeration
      -> derived list only; never a second semantic authority

A proof of NoDup beside a publicly exposed list does NOT make that list the right semantic abstraction for a
map. A custom wrapper is allowed; a custom collection implementation is not.

===============================================================================
2. PINNED STANDARD-LIBRARY RESEARCH
===============================================================================

The Dockerfile pins:

  rocq-core 9.2.0
  rocq-stdlib 9.1.0

Use only collection implementations available in that pinned environment.

Required candidates to inspect in the pinned container:

General ordered-key finite maps:
- Stdlib.FSets.FMapAVL
- Stdlib.FSets.FMapFullAVL
- Stdlib.FSets.FMapFacts
- Stdlib.FSets.FMapInterface

Positive-key finite maps:
- Stdlib.FSets.FMapPositive
- PositiveMap / PositiveMapAdditionalFacts

Finite sets:
- Stdlib.MSets.MSetAVL
- Stdlib.MSets.MSetPositive
- Stdlib.MSets.MSetFacts
- Stdlib.MSets.MSetInterface

Ordered key support:
- Stdlib.Structures.OrdersEx
- Stdlib.Structures.OrderedTypeEx
- String_as_OT or the pinned equivalent

Research conclusions already established:

- FMapAVL is the standard-library AVL-tree finite-map implementation.
- FMapFullAVL additionally carries/proves the AVL balance invariant.
- FMapPositive is the standard positive-key binary-trie map and originates in certified-compiler work.
- MSetAVL is the modern standard finite-set AVL implementation.
- FMap add overwrites an existing key, so a source-builder that must REJECT duplicates must test membership
  before add and prove that behavior; overwriting is not acceptable.
- Ordered-map elements are a derived key-ordered enumeration.
- Primitive PArray/Uint63-based collections remain forbidden by Fido's no-kernel-primitive law.

At the beginning of implementation, run a small pinned-container proof/computation spike comparing FMapAVL
and FMapFullAVL for the exact operations Fido needs:

- empty;
- mem;
- find;
- add;
- map/mapi;
- fold;
- elements;
- cardinal;
- Equal;
- MapsTo;
- zero-assumption closure;
- vm_compute or equivalent evaluation behavior on representative maps;
- reduction of FileMap.elements through di_transport.

Choose ONE general ordered-key map implementation before the ROOT barrier.

Selection rule:

- Prefer FMapFullAVL if its carried balance proof and computation behavior are practical under the pinned
  proof/emission pipeline.
- Otherwise use FMapAVL, document that it is the standard mature AVL implementation, and make no stronger
  formal asymptotic theorem than the standard library actually exposes.
- Do not write a replacement tree.
- Do not leave both live as production alternatives.

For positive keys, use the standard FMapPositive implementation. Do not compare it against a project-authored
trie: the project-authored trie is being removed.

Record the selected modules and the reason in SOURCE_FOREST_STATUS.md.

===============================================================================
3. REPOSITORY-WIDE COLLECTION AUDIT
===============================================================================

The following classification is binding unless implementation uncovers a concrete contradiction.

-------------------------------------------------------------------------------
3.1 KEEP AS LIST — ORDER OR MULTIPLICITY IS SEMANTIC
-------------------------------------------------------------------------------

digits.v
- dds_double digit list
- pos_digits
- dlist_val
Reason: positional base representation; order and repetition are the value.

FilePath.v / ModulePath.v
- split path components
Reason: path component order is semantic.

GoAST.v source grammar
- source_imports
- source_decls
- statement bodies
- println arguments
Reason: source order and repetition are semantic. Imports are empty today but remain a source sequence.

GoRender.v
- argument/declaration/statement rendering traversals
Reason: source order determines bytes.

GoSafe.v
- println argument value lists
- statement/declaration/file trace lists
Reason: argument and execution order are semantic.

Occurrence index
- children_of result
- canonical preorder enumeration
Reason: source order is part of navigation/diagnostics.

e2e witness construction
- source declarations/statements/arguments
Reason: source order.

OCaml sink
- created_dirs rollback stack
- created_temps rollback stack
- ordered error accumulation where report order is useful
Reason: reverse creation/cleanup or presentation order is operationally meaningful.

OCaml transport decoder
- decoded map bindings as an incoming list
Reason: it is a transport enumeration only. It must be validated into a map immediately.

-------------------------------------------------------------------------------
3.2 REPLACE — WRONG CURRENT COLLECTION
-------------------------------------------------------------------------------

FMap.v
Current:
  Record fmap K A := list (K * A) + NoDup keys
Problem:
- project-authored general map;
- linear lookup;
- quadratic duplicate builder;
- exposed backing list;
- easy accidental order dependence.
Disposition:
- DELETE the module and every import/use.

GoAST.GoFileSet
Current:
  list GoFileNode + NoDup file paths
Problem:
- semantically a map wearing a list-shaped coat;
- exposed physical order;
- duplicated path in node when later converted to map.
Disposition:
- replace stored collection with standard FilePath map.

GoAST.prog_entries
Current:
  derived list (FilePath * list GoDecl), used as semantic input.
Problem:
- exposes enumeration as semantic root;
- downstream definitions traverse physical list order.
Disposition:
- delete from semantic definitions;
- retain a bindings/nodes list only as a clearly derived standard-map enumeration if a consumer genuinely
  needs one.

GoCompile.main_count_in_dir / AllPackagesOneMain
Current:
- for each file, scan all file entries to count package mains.
Problem:
- O(files²);
- package identity is key-based, not sequence-based.
Disposition:
- build one standard PackageMap keyed by package directory and aggregate each file once.

GoEmit.DirectoryImage.di_go_files
Current:
- custom fmap.
Disposition:
- standard FilePath map from FilePath to rendered bytes.

OccurrenceSpike.NodeTable
Current:
- project-authored positive-key radix trie.
Problem:
- reimplements a standard certified collection.
Disposition:
- replace with Stdlib FMapPositive.

OccurrenceSpike.TForest
Current:
- list of files + NoDup paths.
Problem:
- same wrong file-collection abstraction.
Disposition:
- standard FilePath map.

OccurrenceSpike outer index
Current:
- custom positive map keyed by hidden file slots.
Problem:
- hidden slot existed only to avoid a file-list scan;
- once the source forest is a real FilePath map, the path is already the efficient unique key;
- hidden slot is redundant implementation identity.
Disposition:
- outer standard FilePath map keyed directly by FilePath;
- delete hidden file slots.

plugin/fido_sink.ml desired outputs
Current:
- list of desired files;
- List.mem for every discovered stale file.
Problem:
- repeated linear membership;
- desired identity is final path.
Disposition:
- OCaml StringMap keyed by relative/final path;
- derive an ordered bindings list for stage/install iteration.

plugin/fido_sink.ml abandoned temps
Current:
- mutable list, unordered membership collection.
Disposition:
- OCaml StringSet unless a proven operational order is required.

plugin/g_fido.mlg audit roots
Current:
- audit roots accumulated as lists, while do_emit already uses Names.GlobRef.Set.
Disposition:
- use Names.GlobRef.Set consistently;
- convert to elements only at the API boundary if the Rocq API requires a list.

-------------------------------------------------------------------------------
3.3 FUTURE COLLECTION SHAPES — UPDATE THE MASTER PLAN NOW
-------------------------------------------------------------------------------

Do not implement future language features in C1A, but correct the persistent architecture so later work does
not repeat the mistake.

Scopes before duplicate validation:
  NameMap (NonEmptyList DeclRef)

Validated scopes:
  NameMap SymbolRef

Compiler facts:
  NodeKeyMap Fact
or another mature-map wrapper keyed by the canonical occurrence key.

Diagnostics:
  ordered output list derived from a NodeKeyMap (list DiagnosticBucket) or a canonical map/set representation.

Method collection before validation:
  MethodNameMap (NonEmptyList MethodDeclRef)

Validated method set:
  MethodNameMap Method

Recursive-type / package dependency graph:
  DeclMap DeclSet
  PackageMap PackageSet

Struct source fields:
  KEEP list in AST because field order affects layout/source.
Derived selector lookup:
  FieldNameMap (NonEmptyList FieldRef)

Interface source elements:
  KEEP list in AST.
Derived interface/method facts:
  maps/sets by semantic identity.

Imports:
  KEEP source import list.
Derived file scope:
  NameMap BindingBucket.

Never let a standard map's overwrite behavior erase duplicate source occurrences. Collect buckets first; validate
to a unique map second.

===============================================================================
4. STANDARD COLLECTION WRAPPER MODULE
===============================================================================

Create a small certified module, preferably:

  Collections.v

It may define domain key modules, instantiate standard collection functors, and re-export selected facts.
It must NOT define a tree/list-backed map/set implementation.

Required contents:

1. FilePath ordered key

Define a total lexicographic order via fp_string, using the pinned standard String ordered type.

The equality exposed to the map must coincide with Leibniz FilePath equality.

Prove and gate:
- compare equality iff FilePath equality;
- decidable equality;
- strict total order requirements expected by the chosen map implementation.

2. FilePath map

Instantiate the selected standard AVL map:

  Module FileMapBase := ...
  Module FileMapFacts := ...
  Module FileMapProps := ...

Expose an abstract domain wrapper/API, not tree constructors.

3. String/package map

Instantiate a standard ordered string map for package directories:

  Module PackageMapBase := ...

4. Positive node map

Wrap or alias the standard positive-key map:

  Module NodeMapBase := FMapPositive.PositiveMap

Expose the find/add/empty facts needed by OccurrenceSpike.

5. Sets

Instantiate mature standard sets only where this checkpoint actually needs a Rocq set.
Do not add speculative unused wrappers merely to list them.

6. Assumption and computation gate

Add public wrapper theorems to the readable gate and whole-theory audit:
- lookup after add same key;
- lookup after add different key;
- map key/functionality facts;
- ordered elements;
- standard map Equal;
- positive map laws;
- any set membership facts actually used.

No wrapper theorem may depend on a project axiom or kernel primitive.

===============================================================================
5. REPLACE THE PROGRAM FILE COLLECTION WITH A REAL MAP
===============================================================================

The permanent stored source forest becomes:

  GoFileMap := FileMap.t GoSourceFile

or an equivalent thin domain wrapper.

Rename GoFileSet to GoFileMap unless there is a compelling source-level reason not to. The public name should
not conceal that the object is a map.

GoProgram becomes:

  Record GoProgram := {
    prog_module : ModuleSpec;
    prog_files  : GoFileMap
  }.

GoSourceFile remains the specification-shaped grammar object:

  package clause
  ordered imports
  ordered declarations

GoFileNode remains only a convenient construction/view form:

  Record GoFileNode := {
    file_path   : FilePath;
    file_source : GoSourceFile
  }.

The stored map value is GoSourceFile, NOT GoFileNode. The map key is the one path authority.

The map binding itself is the file-root occurrence:

  FilePath ↦ GoSourceFile

Required API:

  empty_files
  find_file
  maps_to_file
  file_mem
  file_count
  file_paths
  file_bindings
  file_nodes              (derived construction/view enumeration only)
  map_file_values
  FilesEqual              (the standard map Equal relation)

Every enumeration must be documented as DERIVED and canonically ordered by FilePath.

Delete:
- file_members as a public semantic field;
- file_paths_unique proof field;
- custom List.find lookup;
- first-match semantics;
- any parallel stored path.

===============================================================================
6. DUPLICATE-REJECTING CONSTRUCTION MUST BE EXACT
===============================================================================

The standard map add operation overwrites. Fido's builder must reject duplicates before add.

Implement:

  filemap_of_nodes :
    list GoFileNode -> option GoFileMap

using the standard map's mem/find/add operations.

Failure must mean duplicate FilePath and nothing else.

Prove universally:

  filemap_of_nodes_success_iff_unique :
    (exists fm, filemap_of_nodes nodes = Some fm)
    <->
    NoDup (map file_path nodes)

  filemap_of_nodes_none_iff_duplicate :
    filemap_of_nodes nodes = None
    <->
    ~ NoDup (map file_path nodes)

  filemap_of_nodes_maps_to :
    success preserves every exact path -> source binding

  filemap_of_nodes_complete :
    every resulting binding came from exactly one input node

  filemap_of_nodes_permutation :
    Permutation nodes1 nodes2 ->
    successful results are FileMap.Equal

  filemap_of_nodes_duplicate_rejects :
    same path twice rejects even when source values are equal

  filemap_of_nodes_duplicate_different_source_rejects :
    same path twice rejects when sources differ

Then:

  build_program :
    ModuleSpec -> list GoFileNode -> option GoProgram

must be exact over that builder.

Gate the build_program success/failure iff uniqueness theorem.

This closes the C1 human-review finding that the existing builder was proved only in the success direction.

===============================================================================
7. MAP-BASED TYPING
===============================================================================

Delete semantic dependence on prog_entries.

Define source-file typing:

  SourceFileTyped sf :=
    FileTyped (source_decls sf)

Declarative whole-program typing should be map-based:

  ProgramTyped p :=
    forall path sf,
      FileMap.MapsTo path sf (prog_files p) ->
      SourceFileTyped sf

The executable checker may traverse FileMap.elements, because that is the standard map's canonical derived
enumeration.

Prove:
- program_typedb iff ProgramTyped;
- ProgramTyped respects FileMap.Equal;
- program_typedb equal on FileMap.Equal maps;
- empty map typed;
- reordered construction produces the same typing result.

Do not expose the backing tree or use an input-order list as the judgment root.

===============================================================================
8. MAP-BASED PACKAGE GROUPING
===============================================================================

Replace repeated scanning with one package aggregation.

Current package identity:
  fp_parent path : string

Use the standard PackageMap:

  PackageMap.t PackageSummary

For current scope, PackageSummary should contain only live facts actually needed, for example:

  main declaration count

Do not add speculative method/import/type fields.

Build package summaries in one pass over the file map:

  package_summaries :
    GoFileMap -> PackageMap

Each source file contributes exactly once to the parent-directory package.

Required exactness:
- every represented file contributes to exactly its fp_parent package;
- no package is created without at least one file;
- each package summary's main count equals the sum of file_main_count over its files;
- empty file map yields empty package map;
- map-equal file collections yield map-equal package summaries;
- input construction order cannot change package summaries.

Define:

  AllPackagesOneMain

over PackageMap bindings, not over repeated file scans.

Define/refactor:

  ProgValid
  prog_ok
  go_compile

through the map-based typing and package-summary roots.

Prove:
- prog_ok iff ProgValid;
- GoCompile respects FileMap.Equal;
- go_compile acceptance/error class is invariant under file insertion order;
- multi-package and empty-module fixtures remain correct;
- package aggregation performs one file-map traversal plus logarithmic package-map operations, not a nested
  file scan.

Delete:
- main_count_in_dir over list entries;
- AllPackagesOneMain over prog_entries;
- any other O(files²) package scan.

===============================================================================
9. MAP-BASED RENDERING AND DIRECTORY IMAGE
===============================================================================

GoRender continues to render one GoSourceFile directly.

Pin the current empty import domain:

  source_imports_nil :
    forall sf, source_imports sf = []

Add a total render_imports eliminator/helper even though the domain is empty. The renderer should structurally
consume the source field, so adding an import constructor later forces a renderer update rather than silently
ignoring a now-live field.

GoEmit:

  render_map :
    SafeProgram -> FileMap.t string

should use the standard FileMap map/mapi operation.

DirectoryImage:

  di_go_files : FileMap.t string

No custom fmap remains.

Transport:

  di_go_file_entries

is a DERIVED canonical list from FileMap.elements, mapping FilePath to fp_string.

Required theorems:
- rendered map has the same key domain as the source file map;
- every map binding has exact rendered bytes for its source;
- FileMap.Equal source maps produce FileMap.Equal rendered maps;
- canonical elements of extensionally equal rendered maps are equal;
- di_transport is independent of original input-node order;
- emitted on-disk paths remain unique;
- all headers/ASCII proofs survive;
- generated files and go.mod remain byte-identical.

Delete all FMap.v types, constructors, functions, facts, imports, and gate surfaces.

Delete FMap.v from dune and the repository.

===============================================================================
10. OCCURRENCE SPIKE MIGRATION
===============================================================================

OccurrenceSpike is temporary but remains part of the certified theory until production GoIndex lands. It must
obey the same collection law now.

10.1 Positive local-node map

Replace the hand-written NodeTable trie with the standard positive map.

A thin NodeTable API wrapper may remain if it materially simplifies proofs, but:
- its storage is FMapPositive.PositiveMap;
- it contains no custom tree constructors;
- it proves laws from standard map facts;
- its representation is standard-library-backed.

10.2 Toy source forest

Replace:

  list TFile + NoDup paths

with a standard FilePath map.

Separate toy source from placement exactly as production does:

  TSourceFile
  TFileNode construction/view
  TForest := FileMap.t TSourceFile

10.3 Outer index

Replace hidden positive file slots and the positive outer table with:

  FileMap.t FileIndex

keyed directly by FilePath.

The hidden slot was introduced only to avoid a list scan. A real FilePath map removes that need.

FileRef becomes conceptually:

  path
  source
  proof FileMap.MapsTo path source fs

NodeRef remains:
  FileRef fs
  local positive
  local-validity proof

NodeKey remains:
  FilePath * positive

No second file identity.

10.4 SyntaxIndex

  SyntaxIndex fs

contains or is equal to the standard FileMap mapping each source file to its per-file PositiveMap index.

Exactness must prove presence AND absence through standard map semantics.

10.5 Preserve the C0/C0A/C0B theorem family

Restate and gate all accepted foundations:
- exact snapshot-local reference types;
- source/index exactness;
- universal source-occurrence correspondence;
- correct kind/role/parent/subtree metadata;
- repeated-equal syntax has distinct refs;
- same-shape/different-payload snapshots have non-interchangeable refs;
- total ref_meta/kind/role/subtree/containing-file;
- parent optional only at root;
- child enumeration exact/source-ordered/NoDup;
- interval ancestry sound+complete;
- raw key minting sound+complete;
- parent/child inverse;
- no copied syntax tree.

10.6 Performance

After migration:
- file lookup/index lookup: standard FileMap logarithmic shape;
- local metadata lookup: positive-key map bit-depth shape;
- containing file: projection from FileRef;
- direct children: O(number of children * positive-map lookup), no descendant materialization;
- no hidden slot;
- no list scan;
- no custom trie.

The occurrence spike must remain isolated from production semantics and still be deleted when C2 production GoIndex
subsumes it.

===============================================================================
11. OCAML COLLECTION AUDIT
===============================================================================

Use mature OCaml collections; do not write a custom hash/tree.

11.1 Sink desired outputs

In plugin/fido_sink.ml:

  module StringMap = Map.Make(String)
  module StringSet = Set.Make(String)

or the equivalent modules already available in the pinned OCaml runtime.

Convert the incoming transport entries immediately into a desired-output StringMap.

Requirements:
- reject duplicate relative paths before any filesystem effect;
- include go.mod under its distinguished final key or keep it separately with a map for .go files, but do not
  use a list for identity/membership;
- use StringMap.mem/StringSet.mem for stale-file membership;
- derive StringMap.bindings for canonical stage/install iteration;
- output order must not depend on transport input order;
- same map with permuted input bindings produces the same final directory.

11.2 Abandoned temps

Use StringSet for the unordered unique set of validated abandoned temp paths unless a real operational ordering
requirement is demonstrated.

11.3 Keep rollback stacks as lists

created_dirs and created_temps remain lists because cleanup order is meaningful.

11.4 Assumption audit roots

In plugin/g_fido.mlg, use Names.GlobRef.Set consistently while collecting:
- constants;
- inductives;
- variables;
- direct term references.

Convert to a list only at the Assumptions API boundary if required.

11.5 Transport list

decode_entries remains a list decoder because the certified Rocq transport is an enumeration.
It is not the semantic collection. Validate it into the sink's map immediately.

11.6 Tests

Extend the real sink driver/e2e:
- duplicate desired path rejects before effects;
- permuted transport entries produce the same tree;
- many desired files do not trigger repeated List.mem stale checks;
- abandoned temp collection is unique;
- all existing fault-injection, ownership, dirty-tree, and recovery tests remain green.

===============================================================================
12. REPOSITORY DOCUMENTATION AND PAINFUL LESSON
===============================================================================

Update:

- ARCHITECTURE.md
- CLAUDE.md
- PROGRESS.md
- Dockerfile comments
- Makefile comments
- dune synopsis
- .review/SOURCE_FOREST_MASTER_PLAN.md
- .review/SOURCE_FOREST_STATUS.md
- gate comments
- any stale “file set = list + NoDup” or custom-fmap description

The permanent architecture must say:

- GoProgram stores a standard-library-backed FilePath map;
- a file-map binding is the file-root program occurrence;
- GoFileNode is a construction/view value, not the stored map value;
- semantic equality is standard map Equal;
- enumerations are canonical derived lists;
- package grouping uses a PackageMap;
- occurrence indexes use FileMap + PositiveMap;
- future scopes/facts/graphs follow the collection algebra law;
- no Fido-authored general-purpose map or set implementation exists.

Update PAINFUL_LESSONS.md.

Revise lesson 3's obsolete custom-FMap example so it no longer praises a carried NoDup field as the permanent
map foundation.

Add this new permanent lesson, with wording equivalent to:

14. **The collection algebra is part of the model; a list with a uniqueness proof is not a map.**
    Fido used exposed association lists plus `NoDup` as finite maps. That looked small and proof-friendly, but
    lookup and construction were linear/quadratic, physical order leaked into compiler definitions, and every
    consumer needed permutation/congruence proofs to recover the semantics the datatype should have expressed.
    Identity-keyed state uses mature Rocq finite maps; membership-only state uses mature finite sets; duplicate-
    invalid source bindings use maps to occurrence buckets until validation; ordered syntax/execution stays a
    list; map/set lists are derived enumerations only. A domain wrapper is welcome. A project-authored general
    collection implementation is not. Standard map `add` overwrites, so source builders must detect duplicates
    before insertion rather than erase the evidence needed for diagnostics.

Keep the lesson concise enough to remain useful.

===============================================================================
13. ROOT REVIEW BARRIER
===============================================================================

Use one intentional semantic-root Codex stop after ALL of the following are true:

- pinned stdlib collection choice is recorded;
- Collections.v exists and is axiom-free;
- FilePath ordered-key facts are proved;
- standard FileMap, PackageMap, and PositiveMap wrappers exist;
- FMap.v is deleted;
- custom OccurrenceSpike trie is deleted;
- GoProgram's stored files are a standard FilePath map;
- GoFileNode is construction/view only;
- duplicate-rejecting map builder is sound and complete;
- OccurrenceSpike uses standard maps and has no hidden slot;
- core occurrence source-correspondence proofs compile over the new maps;
- no production semantic consumer is allowed to keep a second list-backed file authority;
- generated bytes may still await full integration, but the local root is proof-green.

Commit:

  milestone(root): C1A — standard collection authority and map-backed source roots

Codex repairs:

  review(root): C1A —

Do not proceed to final integration until root review is GREEN.

The root review should specifically attack:

- accidental custom collection code hidden in wrappers;
- map add silently overwriting duplicates;
- FilePath ordered-type correctness;
- map equality versus record equality;
- a remaining path copy in a mapped value;
- hidden file slots;
- source map and occurrence index disagreement;
- a list enumeration becoming semantic authority;
- use of primitive arrays/integers;
- unproved builder completeness.

===============================================================================
14. FINAL INTEGRATION BARRIER
===============================================================================

After ROOT GREEN, continue directly without another progress stop.

Complete:

- map-based GoTypes;
- PackageMap aggregation and GoCompile;
- map-based GoRender/GoEmit/DirectoryImage;
- canonical transport;
- OCaml Map/Set migration;
- order-independence/extensionality theorems;
- sink/e2e fixtures;
- docs and painful lesson;
- gate updates;
- whole-theory audit;
- byte-exact regeneration check;
- staged-tree pre-commit verification.

Commit:

  milestone(final): C1A — complete repository-wide standard collection migration

Codex repairs:

  review(final): C1A —

After FINAL GREEN:
- run full verification again;
- run staged-tree verification;
- update SOURCE_FOREST_STATUS.md with root/final SHAs, Codex findings, repair SHAs, proof count, and push;
- fast-forward push;
- notify Rob;
- stop the loop;
- do not begin C2.

===============================================================================
15. REQUIRED UNIVERSAL THEOREMS / GATES
===============================================================================

At minimum, gate:

Collections
- FilePath ordered equality correctness;
- standard FileMap lookup/add facts;
- standard PositiveMap lookup/add facts;
- standard map elements key order / uniqueness facts used by Fido;
- zero assumptions for wrapper surfaces.

File map construction
- success iff input paths unique;
- None iff duplicate;
- exact MapsTo preservation;
- exact no-invented-binding completeness;
- permutation -> FileMap.Equal;
- build_program corresponding exactness.

File-map semantics
- ProgramTyped definition/reflection over MapsTo;
- ProgramTyped respects FileMap.Equal;
- program_typedb respects FileMap.Equal.

Package map
- package summary exactness;
- every file contributes once;
- no empty invented package;
- map-equal files -> map-equal summaries;
- package main decision reflection;
- ProgValid/prog_ok respects FileMap.Equal.

Rendering/emission
- rendered map domain equals source map domain;
- rendered binding exactness;
- map equality preserved;
- canonical transport equality under FileMap.Equal;
- path uniqueness;
- source_imports_nil;
- unchanged headers/ASCII/provenance.

Occurrence
- standard-map source/index exactness;
- all C0B source-occurrence correspondence surfaces;
- NodeRef equality/lookup/navigation;
- no hidden slot;
- standard positive map;
- parent/child/ancestry/children proofs.

OCaml/e2e
- duplicate desired path rejection;
- input-order permutation differential;
- unchanged sink safety/fault tests.

Do not merely add concrete fixtures where a universal theorem is required.

===============================================================================
16. PERFORMANCE AND REPRESENTATION INSPECTION
===============================================================================

The implementation shape must visibly establish:

- no FilePath lookup through List.find;
- no custom association-list map;
- no custom trie;
- no O(n²) duplicate-path checker;
- no nested all-files package count;
- no List.mem desired membership in the sink;
- no repeated rebuilding of standard maps per query;
- no map/set semantics based on enumeration order;
- no primitive array/int dependency;
- one map construction per immutable snapshot/analysis;
- canonical standard-map enumeration for transport/output.

Benchmark/computation probes may supplement this inspection but do not replace semantic proofs.

Record representative before/after computation probes for:
- 1, 10, 100, and a practical larger file count;
- package aggregation;
- FileMap lookup;
- PositiveMap lookup;
- transport enumeration;
- sink stale membership.

Do not claim machine asymptotics as a kernel theorem unless actually proved.

===============================================================================
17. FORBIDDEN
===============================================================================

During C1A, do NOT add:

- C2 production GoIndex;
- structured diagnostics;
- identifiers or type-name syntax;
- uintptr;
- rune constants;
- pointers;
- named types;
- arrays/slices/maps/channels/function types;
- structs/interfaces;
- imports;
- arithmetic;
- general calls;
- any new Go behavior.

Do NOT retain:

- FMap.v;
- custom map/set/tree/hash implementations;
- list + NoDup as a public identity-keyed collection;
- map keys duplicated inside mapped values;
- hidden FileRef slots;
- overwrite-on-duplicate source construction;
- semantic dependence on prog_entries;
- repeated package list scans;
- raw map tree constructors in public APIs;
- two production map candidates;
- a transitional second file authority at final green.

If the pinned standard library cannot support the required semantics without violating the standing trust/performance
rules, report an architectural conflict and stop. Do not silently rebuild the collection.

===============================================================================
18. ACCEPTANCE
===============================================================================

C1A is complete only when:

- all repository collection uses have been classified;
- every current identity-keyed collection is standard-map-backed;
- every current membership-only collection uses a mature set where appropriate;
- all retained lists have a documented ordering/multiplicity/stack/transport reason;
- FilePath -> GoSourceFile is the stored program file map;
- FMap.v is deleted;
- custom OccurrenceSpike trie is deleted;
- hidden file slots are deleted;
- package grouping is map-based;
- DirectoryImage is map-based;
- transport is canonical and derived;
- sink desired/stale/temp collections use OCaml Map/Set appropriately;
- g_fido audit roots use the existing mature set;
- builder exactness is proved both ways;
- semantic order independence is proved;
- all C0/C0A/C0B occurrence guarantees survive;
- PAINFUL_LESSONS.md contains the permanent lesson;
- master plan is reconciled;
- zero assumptions;
- no generated-byte drift;
- full `make check` green;
- staged gate green;
- Codex final GREEN;
- fast-forward pushed;
- loop stopped;
- C2 not begun.

===============================================================================
19. HUMAN-READABLE DESIGN SUMMARY
===============================================================================

The intended final shape is:

  ModuleSpec
  +
  FileMap.t GoSourceFile
      key   = intrinsic FilePath
      value = specification-shaped source file

Typing:
  quantified over FileMap.MapsTo
  executable over canonical FileMap.elements

Compilation:
  one FileMap traversal
  -> PackageMap summaries
  -> package validity

Rendering:
  FileMap.map render_file

Directory image:
  FileMap.t rendered bytes

Transport:
  canonical FileMap.elements list

Occurrence index:
  outer FileMap by FilePath
  inner PositiveMap by local occurrence ID

OCaml sink:
  StringMap desired outputs
  StringSet membership-only state
  lists only for ordered work/rollback

The AST owns source order.
Maps own identity.
Sets own membership.
Buckets preserve duplicate evidence.
Derived lists enumerate; they do not define meaning.
