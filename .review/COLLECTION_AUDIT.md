# Collection audit (C1B §4)

A CURRENT-STATE classification of every persistent or repeatedly-queried collection in the repository, plus
the notable false positives. The binding collection law (CLAUDE.md rule 10 / ARCHITECTURE.md): a mature
standard collection is used for every identity-keyed or membership-only role; a `list` is retained only for
order / repetition / positional structure / stack / transport enumeration / derived map-set enumeration; Fido
authors NO collection storage or generic algorithm.

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
| `GoCompile.list_dir_count` / `PM.elements` in `prog_ok` | package proof enumerations | — | canonical | n/a | proof fold / forallb | derived `elements` / spec `list` | retained | proof/spec views over the canonical package-map enumeration, not storage |
| `GoEmit.DirectoryImage.di_go_files` | path → rendered bytes | `FilePath` | no | n/a | by path | **`FMapAVL`** (`FM.map render_file`) | retained | identity-keyed rendered `.go` map (the standard `map` of the source map) |
| `GoEmit.di_go_file_entries` | (path-string, bytes) transport | — | canonical | n/a | enumerate | `FileMap.elements` (derived) | retained | DERIVED canonical transport list; identity authority is `di_go_files` |
| `OccurrenceSpike.NodeTable` (`Collections.NodeMapBase`) | local id → NodeMeta | `positive` | no | n/a | by id | **`FMapPositive`** | retained | per-file local-node index; a thin sealed API delegating storage + ops to the standard positive map |
| `OccurrenceSpike.outer_of` | path → FileIndex | `FilePath` | no | n/a | by path | **`FMapAVL`** (`FileMapBase.map`) | retained | outer occurrence index keyed by path; no hidden slot |
| `OccurrenceSpike.TForest` | path → TSourceFile | `FilePath` | no | rejected | by path | **`FMapAVL`** | retained | toy source snapshot; the C1A slot machinery is deleted |
| `OccurrenceSpike.child_ids` / `all_ids` / `children_of` | occurrence ids / refs | — | source order | no (NoDup proved) | interval-jump / enumerate | `list` | retained | ordered canonical children / preorder enumeration; `NoDup` is a theorem ABOUT a derived list, not a stored-map invariant |
| `source_decls` / `SPrintln` args / `TFun` body / `list ImportSpecSyntax` | source syntax | — | yes (as written) | yes (positional) | positional | `list` | retained | ordered source grammar — repetition and position are semantic |

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
| `e2e/sink_test.ml` `faults` | fault tokens | `string` | no | no | membership | **`Fido_sink.SSet`** (`Set.Make(String)`) | **changed (C1B §7)** | membership-only fault flags — was `List.mem` over a `list`, now the sink's shared standard set |
| `Sys.readdir` results (`inspect` / `remove_stale_go`) | directory names | — | OS order | n/a | iterate | `array` (OS) | retained | filesystem enumeration returned by the OS; iterated once, no identity/membership storage |

## Notable false positives (searched, NOT collection defects)

- `List.mem` / `List.find` in Rocq/OCaml elsewhere: none used as identity/membership storage after C1B §7
  (the last one, `sink_test` faults, is now a set; the sink's stale check is `SSet.mem`).
- `NoDup` occurrences: all are theorems ABOUT a derived `elements`/children/path list (e.g.
  `render_image_keys_nodup`, `thm_children_of_nodup`), never a carried uniqueness field standing in for a map.
- `existsb` / `forallb` / `fold_left` / `fold_right`: proof/spec structure over canonical enumerations
  (`program_typedb`, `prog_ok`, `list_dir_count`, `pkg_foldl`) — not collection storage or repeated-scan lookup.
- `digits` list, `FilePath` path components, runtime `SPrintln` argument order: ordered source/leaf sequences.
- `Record`/`Inductive` names containing Map/Set/Table/Index (`GoFileMap`, `PackageSummary`, `SyntaxIndex_T`,
  `FileIndex`, `NodeTable`): all are aliases / thin wrappers / domain records over standard maps — none defines
  a recursive storage tree (the old `FMap.v` association list and the old `NodeTable` radix trie are deleted).

## Result

No project-authored general-purpose collection implementation remains. Every identity-keyed or membership-only
collection names a mature standard backing (`FMapAVL` / `FMapPositive` / `Map.Make` / `Set.Make` /
`Names.GlobRef.Set`); every retained `list` has an order / repetition / stack / transport / derived-enumeration
reason.
