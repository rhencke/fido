# Collection audit

A CURRENT-STATE classification of every persistent or repeatedly-queried collection in the repository, plus
the notable false positives. The binding collection law (CLAUDE.md rule 10 / ARCHITECTURE.md): a mature
standard collection is used for every identity-keyed or membership-only role; a `list` is retained only for
order / repetition / positional structure / stack / transport enumeration / derived map-set enumeration; Fido
authors NO collection storage or generic **collection** algorithm. (Fido owns many legitimate compiler
algorithms — traversal, typing, rendering, occurrence indexing; the prohibition is only against reimplementing
generic COLLECTION machinery — map/set/dictionary/trie/balanced-tree storage and its find/insert/balance/union.)

**This is a living current-state inventory, maintained at every checkpoint rather than a frozen record.**
`OccurrenceSpike.v` is deleted and `GoIndex.v` is the production occurrence/index authority; the
`OccurrenceSpike.*` rows have been REPLACED by the `GoIndex.*` rows below (outer `FMapAVL FilePath FileIndex`,
inner sealed `FMapPositive positive NodeMeta`, derived enumeration `list`s classified as ordered/derived),
with the strict standard-collection law retained.

Columns: **file / symbol** · **contents** · **identity key** · **order matters?** · **duplicates matter?** ·
**lookup pattern** · **selected backing** · **retained / change** · **reason**.

## Rocq — certified theory

| file / symbol | contents | key | order? | dups? | lookup | backing | verdict | reason |
|---|---|---|---|---|---|---|---|---|
| `GoAST.GoFileMap` (`prog_files`) | path → GoSourceFile | `FilePath` | no | rejected | by path | **`FMapAVL`** (`Collections.FileMapBase`) | retained | identity-keyed program file storage; the map key is the file-root identity |
| `GoAST.filemap_of_nodes` input `list GoFileNode` | construction nodes | — | no (permutation-invariant result) | preserved until validation | sequential fold | `list` | retained | a construction SEQUENCE feeding the duplicate-rejecting builder; duplicate evidence is preserved (build fails, never overwrites) |
| `GoAST.file_bindings` / `prog_bindings` | (path, source) pairs | — | canonical (key sort) | n/a | enumerate | `FileMap.elements` (derived) | retained | DERIVED canonical enumeration of the map; not an identity authority |
| `GoAST.file_paths` / `prog_keys` | paths | — | canonical | n/a | enumerate | `map fst file_bindings` (derived) | retained | derived key enumeration |
| `GoCompile.package_summaries` | directory → PackageSummary | `string` (`fp_parent`) | no | summed once each | by directory | **`FMapAVL`** (`Collections.PackageMapBase`) | retained | identity-keyed package aggregation; one `FM.fold`, no O(files²) scan |
| `GoCompile.list_dir_count` / `PM.elements` in `source_spec_valid_b` | package proof enumerations | — | canonical | n/a | proof fold / forallb | derived `elements` / spec `list` | retained | proof/spec views over the canonical package-map enumeration, not storage |
| `GoEmit.DirectoryImage.di_go_files` | path → rendered bytes | `FilePath` | no | n/a | by path | **`FMapAVL`** (`FM.map render_file`) | retained | identity-keyed rendered `.go` map (the standard `map` of the source map) |
| `GoEmit.di_go_file_entries` | (path-string, bytes) transport | — | canonical | n/a | enumerate | `FileMap.elements` (derived) | retained | DERIVED canonical transport list; identity authority is `di_go_files` |
| `GoIndex.NodeTable` (`Collections.NodeMapBase`) | local id → NodeMeta | `positive` | no | n/a | by id | **`FMapPositive`** | retained | per-file local-node index; a thin SEALED API (`Module NodeTable : NODE_TABLE`) delegating storage + the three laws to the standard positive map — no Fido-authored storage; the selected backing remains `FMapPositive` |
| `GoIndex.outer_of` / `Snap.SyntaxIndex.si_outer` | path → FileIndex | `FilePath` | no | n/a | by path | **`FMapAVL`** (`FileMapBase.map build_file`) | retained | outer program index keyed by path (the sealed `SyntaxIndex`'s internal map IS `outer_of (prog_files p)`); one map lookup reaches a file's index — no hidden slot |
| `GoIndex.child_ids` / `all_ids` / `Snap.children_of` / `Snap.file_refs` | occurrence ids / refs | — | source order | no (`NoDup` proved) | interval-jump / enumerate | `list` | retained | ordered canonical children / preorder reference enumeration; `NoDup` is a theorem ABOUT a derived list, not a stored-map invariant |
| `GoIndex.occs_file` / `walk_file` / `Snap.visit_file` | (id or ref, source occurrence) pairs | — | source preorder | no (`NoDup` proved) | one structural pass (`walk_*` threads a next-free-id cursor; no boundary rescan) | `list` | retained | the DERIVED canonical indexed-traversal enumeration (each occurrence's syntax + validated ref together); `occs_file` is the readable spec, `walk_file` its single-pass impl (`walk_file = occs_file`); proved source-ordered + NoDup + exact vs `source_occurrence_at`; a transient traversal RESULT, never stored in `GoProgram`/`SyntaxIndex`/semantic facts |
| `GoCompile.elaborate` folds / `GoCompile.occ_arg_typedb` over `occs_file`/`visit_file` | per-occurrence typing bits + fact/diagnostic/bucket accumulation | — | source preorder | n/a | `forallb` / `fold_right` / `flat_map` over the retained visit stream | `list` | retained | GoCompile's ONE indexed whole-program elaboration folds the derived traversal enumeration (delegating to the SAME `GoTypes.expr_typedb`/`const_info` resolver); `GoCompile.occ_arg_typedb` (moved off GoTypes, which now imports no GoIndex) is the leaf predicate, `GoCompile.occs_file_typedb_eq` its `= source_file_typedb` bridge — GoCompile is the sole GoIndex+GoTypes meeting point; a proof/computation view over canonical enumerations, not storage (there is no separate `indexed_program_typedb` peer checker) |
| `GoCompile.ExprFactTable` / `prog_status_map` | occurrence -> `ExprFact` / `option ConstInfo` | `NodeKey` (`mkKey FilePath positive`) | canonical (path then local id) | no (one entry per occurrence; a bucket value prevents overwrite) | by NodeKey | **`FMapAVL`** (`NodeKeyMapBase`, a thin `FMapAVL` wrapper over the `NodeKey` ordered key) | retained | the SEALED occurrence-keyed fact table + the single-pass status map; keys are validated occurrence NodeKeys (no foreign/forged key — `prog_expr_facts_domain`); `elements` is a DERIVED canonical enumeration, never a second identity authority |
| `GoCompile.prog_package_refs` package main-ref buckets | package dir -> its `main` `DeclRef` list | `string` (package dir = `fp_parent`) | canonical (source stream order within a bucket; PackageMap key order across) | no (every main retained; no overwrite — `ppkg_step` prepends) | by package key | **`FMapAVL`** (`PackageMapBase` over the `String` key) | retained | one `fold_right` over the RETAINED visit stream (never a second `visit_file`); a bucket's length is the package's `main` count; drives the missing/duplicate-main diagnostics directly (`package_summaries` is spec-only) |
| `GoCompile.root_layout` / `root_layout_of_keys` fresh root layout | root entry name -> `FreshRootEntryKind` (go.mod / root source file / directory) | `string` (root component / "go.mod") | canonical (PackageMap key order) | no (disjoint keys — dotted source vs dotless dir) | by output-name lookup (`PM.find`) | **`FMapAVL`** (`PackageMapBase` over the `String` key) | retained (via `ef_root_layout` in ElaborationFacts) | one `fold_right` over the canonical `file_bindings`; the cmd/go default-output preflight looks up the sole-main default exec name here; the downstream DirectoryImage bridge recomputes it from the rendered image's own keys |
| `GoCompile.semantic_diagnostics` node-diagnostic buckets (`bucket_flatten`) / `erased_report` | node-primary diagnostics keyed by occurrence NodeKey (a `list` bucket value) ++ the package-primary list | `NodeKey` (`mkKey FilePath positive`) for the node buckets | canonical: node-primary diagnostics in STRICT NodeKey path/local order (`semantic_diagnostics_node_strict`, on unique keys / singleton buckets), THEN package-primary/missing-main in PackageMap key order | no (a `list` bucket value prevents a future map overwrite; each occurrence emits at most one node diagnostic, so buckets are singletons — NO project-authored sort) | by NodeKey then positional | **`FMapAVL`** (`NodeKeyMapBase.t (list DiagnosticReason)` node-diagnostic buckets) + `list` | retained | the canonical diagnostic order — invalid-conversion / defaulting / main-redeclared (all NodeKey-anchored) prepended into a standard `NodeKeyMap` and flattened by its canonical key-sorted `elements` (no roll-your-own sort), THEN the package-anchored missing-main-entry list; a REORDERING of the raw one-pass diagnostics (`collect_diagnostics_In` — exactly the diagnostics of `expr_diags ++ pkg_diags`, no loss/dup); `erased_report = map erase_diagnostic` projects it to a snapshot-independent `list ErasedDiagnostic` (`erased_report_src`, a source function via the same bucketing) for cross-snapshot comparison |
| `source_decls` / `SPrintln` args / `TFun` body / `list ImportSpecSyntax` | source syntax | — | yes (as written) | yes (positional) | positional | `list` | retained | ordered source grammar — repetition and position are semantic |
| `GoSafe.eval_stmt` / `eval_decl` / `eval_file` | ordered runtime `println`-argument evaluation results (`option GoValue`) | — | **yes (output order)** | yes (a repeated argument evaluates again) | `map` / `flat_map` | `list` | retained | the abstract runtime TRACE — argument/statement order is the observable output order; not identity/membership storage |

## OCaml — plugin + e2e

| file / symbol | contents | key | order? | dups? | lookup | backing | verdict | reason |
|---|---|---|---|---|---|---|---|---|
| `fido_sink.ml` transport `entries` param | (path, bytes) | — | canonical (from Rocq) | rejected on validate | validated into map | `list` | retained | a certified transport ENUMERATION whose identity authority is the map it is validated into |
| `fido_sink.ml` `desired_map` | rel-path → (target,parent,base,bytes) | `string` | no (path-sorted install) | **rejected before effect** | by path | **`Map.Make(String)`** | retained | desired-output identity map; duplicate rel path fails before any filesystem effect |
| `fido_sink.ml` `desired_targets` | absolute target paths | `string` | no | n/a | membership | **`Set.Make(String)`** | retained | O(log n) stale-file membership (not `List.mem`) |
| `fido_sink.ml` `temps` (abandoned) | temp paths | `string` | no | unique | membership / iterate | **`Set.Make(String)`** | retained | unordered-unique abandoned-temp set |
| `fido_sink.ml` `created_dirs` / `created_temps` | rollback stack | — | **yes (reverse creation)** | n/a | iterate | `list` | retained | rollback order is meaningful — a stack, not identity/membership |
| `fido_sink.ml` `cleanup_errors` | error strings | — | yes (accumulation) | n/a | append/print | `list` | retained | ordered error accumulation |
| `g_fido.mlg` audit roots (`grefs`) | GlobRef roots | GlobRef | no | deduped | union → API list | **`Names.GlobRef.Set`** | retained | identity set of audit roots; converted to a list only at the `Assumptions.assumptions` boundary |
| `g_fido.mlg` `decode_entries` result | (path, bytes) | — | canonical | n/a | fold-decode | `list` | retained | list decoder of the certified transport enumeration; validated into the sink map |
| `e2e/sink_test.ml` `faults` | fault tokens | `string` | no | no | membership | **`Fido_sink.SSet`** (`Set.Make(String)`) | retained | membership-only fault flags over the sink's shared standard set |
| `Sys.readdir` results (`inspect` / `remove_stale_go`) | directory names | — | OS order | n/a | iterate | `array` (OS) | retained | filesystem enumeration returned by the OS; iterated once, no identity/membership storage |
| `fido_apply.ml` `Sys.readdir` (`go_files`) | directory names | — | OS order | n/a | iterate | `array` (OS) | retained | filesystem enumeration; iterated once during the source-tree walk |
| `fido_apply.ml` `go_files` accumulator / `entries` | (rel `.go` path, bytes) | — | walk order → `List.rev` | n/a (source tree has distinct paths; sink re-validates) | accumulate → validated into sink map | `list` | retained | a transport-ENUMERATION accumulator built by the recursive tree walk, `List.rev`-ed and handed to `Fido_sink.sync` (which validates it into its `Map.Make(String)`); the identity authority is the sink map, not this list |

## Notable false positives (searched, NOT collection defects)

- `List.mem` / `List.find` in Rocq/OCaml elsewhere: none used as identity/membership storage
  (the last one, `sink_test` faults, is now a set; the sink's stale check is `SSet.mem`).
- `NoDup` occurrences: all are theorems ABOUT a derived `elements`/children/path list (e.g.
  `render_image_keys_nodup`, `thm_children_of_nodup`), never a carried uniqueness field standing in for a map.
- `existsb` / `forallb` / `fold_left` / `fold_right`: proof/spec structure over canonical enumerations
  (`program_typedb`, `source_spec_valid_b`, `list_dir_count`, `pkg_foldl`) — not collection storage or repeated-scan lookup.
- `digits` list, `FilePath` path components, runtime `SPrintln` argument order: ordered source/leaf sequences.
- `Record`/`Inductive` names containing Map/Set/Table/Index (`GoFileMap`, `PackageSummary`, `SyntaxIndex_T`,
  `FileIndex`, `NodeTable`): all are aliases / thin wrappers / domain records over standard maps — none defines
  a recursive storage tree (the old `FMap.v` association list and the old `NodeTable` radix trie are deleted).

## Result

No project-authored general-purpose collection implementation remains. Every identity-keyed or membership-only
collection names a mature standard backing (`FMapAVL` / `FMapPositive` / `Map.Make` / `Set.Make` /
`Names.GlobRef.Set`); every retained `list` has an order / repetition / stack / transport / derived-enumeration
reason.
