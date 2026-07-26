# Collection audit

A CURRENT-STATE classification of every persistent or repeatedly-queried collection in the repository, plus
the notable false positives. The binding collection law (CLAUDE.md rule 10 / ARCHITECTURE.md): a mature
standard collection is used for every identity-keyed or membership-only role; a `list` is retained only for
order / repetition / positional structure / stack / transport enumeration / derived map-set enumeration; Fido
authors NO collection storage or generic **collection** algorithm. (Fido owns many legitimate compiler
algorithms — traversal, typing, rendering, occurrence indexing; the prohibition is only against reimplementing
generic COLLECTION machinery — map/set/dictionary/trie/balanced-tree storage and its find/insert/balance/union.)

**This is a living current-state inventory, maintained at every checkpoint rather than a frozen record.**

**What repair 13 changed.** The previous revision of this file classified `Compilable.WorkForest.forest_items` as an
ordered view that was "not identity storage" — and that was FALSE. `forest_member_at` searched `Compilable.forest_items` with
`List.find` on `nodekey_eqb`, keyed by `Index.Key`, using the carried `Compilable.forest_keys_nodup` field as its uniqueness
mechanism, in the live path `build_outcome_trace → build_conversion_step → build_conversion_work →
forest_member_at` — once per conversion. That was a `list + NoDup` keyed table: it survived proof erasure and
made a nested conversion chain's operand recovery quadratic. `forest_member_at` and its `List.find` are DELETED.
The identity role now belongs to a separate row below — the standard-map-backed `Compilable.WorkIndex` — and the item
list keeps ONLY its order role. The two site inventories at the end of this file are now explicit rather than
summary claims, because the summary form is what hid this defect.

Columns: **file / symbol** · **contents** · **identity key** · **order matters?** · **duplicates matter?** ·
**lookup pattern** · **selected backing** · **retained / change** · **reason**.

## Rocq — certified theory

| file / symbol | contents | key | order? | dups? | lookup | backing | verdict | reason |
|---|---|---|---|---|---|---|---|---|
| `Syntax.Files` (`Syntax.files`) | path → Syntax.File | `FilePath.T` | no | rejected | by path | **`FMapAVL`** (`Collections.FileMap`) | retained | identity-keyed program file storage; the map key is the file-root identity |
| `Syntax.files_of_nodes` input `list Syntax.FileNode` | construction nodes | — | no (permutation-invariant result) | preserved until validation | sequential fold | `list` | retained | a construction SEQUENCE feeding the duplicate-rejecting builder; duplicate evidence is preserved (build fails, never overwrites) |
| `Syntax.file_bindings` / `Syntax.program_bindings` | (path, source) pairs | — | canonical (key sort) | n/a | enumerate | `FileMap.elements` (derived) | retained | DERIVED canonical enumeration of the map; not an identity authority |
| `Syntax.file_paths` / `Syntax.program_keys` | paths | — | canonical | n/a | enumerate | `map fst file_bindings` (derived) | retained | derived key enumeration |
| `Compilable.package_summaries` | directory → PackageSummary | `string` (`FilePath.parent`) | no | summed once each | by directory | **`FMapAVL`** (`Collections.PackageMap`) | retained | identity-keyed package aggregation; one `FileMap.fold`, no O(files²) scan |
| `Compilable.list_dir_count` / `PackageMap.elements` in `source_spec_valid_b` | package proof enumerations | — | canonical | n/a | proof fold / forallb | derived `elements` / spec `list` | retained | proof/spec views over the canonical package-map enumeration, not storage |
| `Emit.Image.di_go_files` | path → rendered bytes | `FilePath.T` | no | n/a | by path | **`FMapAVL`** (`FileMap.map Render.file`) | retained | identity-keyed rendered `.go` map (the standard `map` of the source map) |
| `Emit.entries` | (path-string, bytes) transport | — | canonical | n/a | enumerate | `FileMap.elements` (derived) | retained | DERIVED canonical transport list; identity authority is `Emit.files` |
| `Index.Table` (`Collections.NodeMap`) | local id → Index.Meta | `positive` | no | n/a | by id | **`FMapPositive`** | retained | per-file local-node index; a thin SEALED API (`Module Table : TABLE`) delegating storage + the three laws to the standard positive map — no Fido-authored storage |
| `Index.outer_of` / `Snapshot.Syntax.si_outer` | path → Index.File | `FilePath.T` | no | n/a | by path | **`FMapAVL`** (`FileMap.map build_file`) | retained | outer program index keyed by path; one map lookup reaches a file's index — no hidden slot |
| `Index.child_ids` / `all_ids` / `Snapshot.children_of` / `Snapshot.file_refs` | occurrence ids / refs | — | source order | no (`NoDup` proved) | interval-jump / enumerate | `list` | retained | ordered canonical children / preorder reference enumeration; `NoDup` is a theorem ABOUT a derived list, not a stored-map invariant |
| `Index.occurrences_file` / `walk_file` / `Snapshot.visit_file` | (id or ref, source occurrence) pairs | — | source preorder | no (`NoDup` proved) | one structural pass | `list` | retained | the DERIVED canonical indexed-traversal enumeration; proved source-ordered + NoDup + exact vs `source_occurrence_at`; a transient traversal RESULT, never stored in `Syntax.Program`/`Index.Syntax`/semantic facts |
| `Compilable.elaborate` folds / `Compilable.occurrence_arg_typedb` over `Index.occurrences_file`/`visit_file` | per-occurrence typing bits + fact/diagnostic/bucket accumulation | — | source preorder | n/a | `forallb` / `fold_right` / `flat_map` over the retained visit stream | `list` | retained | Admissible's ONE indexed whole-program elaboration folds the derived traversal enumeration; a proof/computation view over canonical enumerations, not storage |
| **`Compilable.WorkForest` ordered views (`Compilable.forest_blocks` / `Compilable.forest_items`)** | per-file + flat `Compilable.Work` enumerations | — | **source / per-file order (semantic)** | no (`Compilable.forest_keys_nodup` proved) | **sequential processing ONLY** — bottom-up outcome/fact/diagnostic/context folds, the suffix split (`Compilable.forest_split`, `Compilable.forest_operand_in_tail`), and the trace's insertion order | `list` | **ORDER ROLE ONLY (repair 13)** | proof-BACKED ORDERED views over the ONE source AST; the order is semantic for bottom-up processing. **No keyed lookup goes through this list.** Its former `Index.Key` lookup (`forest_member_at`, `List.find`) is deleted; identity now lives in `Compilable.forest_index` (next row). `Compilable.forest_keys_nodup` remains as a fact about this enumeration — see the NoDup inventory |
| **`Compilable.WorkIndex` (`Compilable.forest_index` / `Compilable.index_map`)** *(NEW — repair 13)* | `Index.Key` → the retained `Compilable.Work` item | `Index.Key` (`Index.make_key FilePath.T positive`) | canonical (path then local id) | **impossible** — the builder DEMANDS the key-`NoDup` as a proof argument, and `Compilable.index_exact` is unsatisfiable for a duplicate-keyed list (two distinct equal-key items force `Some a = Some b`; `Compilable.index_key_inj`) | by Index.Key — ONE `KeyMap.find` (`index_member_at` / `forest_index_member_at`) | **`FMapAVL`** (`Index.KeyMap`) | **NEW — the exact identity index** | the ONE identity authority over the work items. Storage and lookup delegate ENTIRELY to the standard map — Fido authors no tree/bucket/find/add. Built ONCE from the ALREADY-BUILT item list (`work_index_map` takes the list, so it cannot re-traverse `Compilable.input_visit` or re-run `build_forest_blocks`); OVERWRITE-FREE (`work_index_fresh` / `work_index_add_fresh` prove each `add` writes an absent key); TOTAL with no option/fallback/empty-default because the `NoDup` precondition is a proof argument. The record is INDEXED BY `Compilable.forest_items`, so a foreign map is not pairable with a forest. `Compilable.index_exact` is the exact map/list relation in BOTH directions (sound + complete); `Compilable.index_domain` and `Compilable.index_key_inj` are DERIVED, never stored — no second domain or uniqueness authority. Wrong-kind and foreign keys are absent (`index_nonexpr_absent`, `index_no_foreign`) |
| `Compilable.AnnotatedWork` (`Compilable.annotated_items`) | retained `WorkMember` × enclosing-conversion context | — | **forest order (semantic)** | no (`Compilable.annotated_members` = exactly `Compilable.forest_items`, once each) | `flat_map` / `map` sequential folds only | `list` | retained | an ORDERED pairing of the retained members with their contexts; consumed positionally by the diagnostic fold. No keyed lookup — the annotated-member recovery in `retained_convfail_diag` is a Prop-level `in_map_iff` witness (erased, produces no code), not a runtime scan |
| `Compilable.Accumulator` (`Compilable.accumulator_map`) / `Compilable.Outcomes` (`Compilable.outcomes_acc`) | `Index.Key` → `Compilable.ExpressionOutcome` (the ONE expression-outcome authority) | `Index.Key` | canonical | no (ONE entry per unique work key; key uniqueness + the `Compilable.accumulator_domain` exact-domain fact prevent overwrite; **NO list bucket**) | by Index.Key | **`FMapAVL`** (`Index.KeyMap`) | retained UNCHANGED | identity-keyed TOTAL result lookup; exact domain = the retained forest / suffix members (`Compilable.accumulator_covers` / `Compilable.accumulator_domain`); `Compilable.Outcomes` pairs `Compilable.outcomes_acc` with the exact `Compilable.Trace` (`Compilable.outcomes_trace`) that built it; `elements` is a DERIVED enumeration, never a second identity authority |
| `Compilable.Trace` (`Compilable.outcomes_trace`) | the exact causal insertion history over the retained work order | — | **yes (predecessor / insertion order is semantic proof structure)** | no (one `Compilable.TraceStep` per work item — `outcome_trace_unique_step`) | structural projection (`trace_retained_cause`) | intrinsic inductive | retained UNCHANGED | the retained causal CONSTRUCTION history (exact tail trace + tail accumulator + current member + `StepCause`); a proof structure, NOT a general-purpose collection implementation |
| `Compilable.ExpressionFacts` (`Compilable.expression_facts_table`) / `Compilable.ExpressionFactTable` (`Compilable.program_expr_facts`) | `Index.Key` → `Compilable.ExpressionFact` for `Compilable.ExpressionSuccess` outcomes | `Index.Key` | canonical | no (one entry per occurrence) | by Index.Key | **`FMapAVL`** (the SAME `KeyMap` wrapper — no new collection) | retained UNCHANGED | the SEALED occurrence-keyed expression-fact table — the `Compilable.ExpressionSuccess` PROJECTION of the SAME `Compilable.Outcomes` (`Compilable.expression_facts_is_facts`), not an independently computed authority; validated occurrence NodeKeys (`Compilable.program_expr_facts_domain`); sealed into `Compilable.Facts` by object identity |
| `Compilable.TypeNameFacts` (`build_type_name_fact_table` / `Compilable.program_type_name_facts`) | type-name occurrence → `TypeNameFact` (the resolved `Typing.SemanticType` ONLY) | `Index.Key` | canonical | no (one entry per type-name occurrence) | by Index.Key | **`FMapAVL`** (the SAME `KeyMap` wrapper) | retained UNCHANGED | the SEPARATE SEALED occurrence-keyed type-name fact table (NOT part of any combined outcome root); domain = exactly the visited type-name occurrences (`Compilable.program_type_name_facts_domain`); the total `type_name_fact_at_table` query PROJECTS the sealed table |
| `Compilable.program_package_refs` package main-ref buckets | package dir → its `main` `DeclRef` list | `string` (`FilePath.parent`) | canonical | no (every main retained; `Compilable.program_package_step` prepends) | by package key | **`FMapAVL`** (`PackageMap`) | retained | one `fold_right` over the RETAINED visit stream; a bucket's length is the package's `main` count |
| `Compilable.root_layout` / `root_layout_of_keys` | root entry name → `FreshRootEntryKind` | `string` | canonical | no (disjoint keys) | `PackageMap.find` | **`FMapAVL`** (`PackageMap`) | retained | one `fold_right` over the canonical `file_bindings`; the cmd/go default-output preflight looks up the sole-main default exec name here |
| `Compilable.semantic_diagnostics` node buckets (`bucket_flatten`) / `erased_report` | node-primary diagnostics keyed by occurrence Index.Key (a `list` bucket value) ++ the package-primary list | `Index.Key` for the node buckets | canonical: strict Index.Key order then PackageMap key order | no (a `list` bucket value prevents a future map overwrite; buckets are singletons — NO project-authored sort) | by Index.Key then positional | **`FMapAVL`** (`KeyMap.t (list DiagnosticReason)`) + `list` | retained | the canonical diagnostic order, flattened by the standard map's canonical key-sorted `elements` (no roll-your-own sort) |
| `Syntax.declarations` / `Syntax.Println` args / `Syntax.Main` body (`list Syntax.Stmt`) / `Syntax.imports` (`list Syntax.ImportSpec`) | source syntax | — | yes (as written) | yes (positional) | positional | `list` | retained | ordered source grammar — repetition and position are semantic; `Syntax.Main : list Syntax.Stmt -> Syntax.Decl` is the current top-level function form, and `Syntax.ImportSpec` is currently an EMPTY inductive so `list Syntax.ImportSpec` can only be `nil` |
| `Names.all_type_names` | the sixteen `TypeName` descriptors | — | fixed literal order | no (16 distinct constructors) | `find` by spelling (`classify`) — see the find inventory | `list` | retained | a CLOSED literal enumeration of a sixteen-constructor inductive, not keyed storage; `classify`/`Names.type_name_spelling` are proved inverse (`classify_spelling`, `classify_sound`, `Names.type_name_spelling_inj`) |
| `Safe.eval_stmt` / `eval_decl` / `eval_file` | ordered runtime `println`-argument evaluation results | — | **yes (output order)** | yes (a repeated argument evaluates again) | `map` / `flat_map` | `list` | retained | the abstract runtime TRACE — argument/statement order is the observable output order; not identity/membership storage |

## OCaml — plugin + e2e

| file / symbol | contents | key | order? | dups? | lookup | backing | verdict | reason |
|---|---|---|---|---|---|---|---|---|
| `sink.ml` transport `entries` param | (path, bytes) | — | canonical (from Rocq) | rejected on validate | validated into map | `list` | retained | a certified transport ENUMERATION whose identity authority is the map it is validated into |
| `sink.ml` `desired_map` | rel-path → (target,parent,base,bytes) | `string` | no (path-sorted install) | **rejected before effect** | by path | **`Map.Make(String)`** | retained | desired-output identity map; duplicate rel path fails before any filesystem effect |
| `sink.ml` `desired_targets` | absolute target paths | `string` | no | n/a | membership | **`Set.Make(String)`** | retained | O(log n) stale-file membership (not `List.mem`) |
| `sink.ml` `temps` (abandoned) | temp paths | `string` | no | unique | membership / iterate | **`Set.Make(String)`** | retained | unordered-unique abandoned-temp set |
| `sink.ml` `created_dirs` / `created_temps` | rollback stack | — | **yes (reverse creation)** | n/a | iterate | `list` | retained | rollback order is meaningful — a stack, not identity/membership |
| `sink.ml` `cleanup_errors` | error strings | — | yes (accumulation) | n/a | append/print | `list` | retained | ordered error accumulation |
| `materialize.mlg` audit roots (`grefs`) | GlobRef roots | GlobRef | no | deduped | union → API list | **`Names.GlobRef.Set`** | retained | identity set of audit roots; converted to a list only at the `Assumptions.assumptions` boundary |
| `materialize.mlg` `decode_entries` result | (path, bytes) | — | canonical | n/a | fold-decode | `list` | retained | list decoder of the certified transport enumeration; validated into the sink map |
| `e2e/sink_test.ml` `faults` | fault tokens | `string` | no | no | membership | **`Sink.SSet`** (`Set.Make(String)`) | retained | membership-only fault flags over the sink's shared standard set |
| `Sys.readdir` results (`inspect` / `remove_stale_go`) | directory names | — | OS order | n/a | iterate | `array` (OS) | retained | filesystem enumeration returned by the OS; iterated once, no identity/membership storage |
| `apply.ml` `Sys.readdir` (`go_files`) | directory names | — | OS order | n/a | iterate | `array` (OS) | retained | filesystem enumeration; iterated once during the source-tree walk |
| `apply.ml` `go_files` accumulator / `entries` | (rel `.go` path, bytes) | — | walk order → `List.rev` | n/a (sink re-validates) | accumulate → validated into sink map | `list` | retained | a transport-ENUMERATION accumulator handed to `Sink.sync`; the identity authority is the sink map, not this list |

## `find` / list-scan site inventory (EXPLICIT — every site, not a summary)

Searched the whole tracked tree (`git grep` for `List.find`, `List.mem`, `List.existsb`, `find (fun`,
`List.assoc`, over `*.v`, `*.ml`, `*.mlg`). **Result: exactly ONE `find` site remains in the certified theory,
and ZERO in OCaml.** Do not restate this as "no `List.find` anywhere" — one site exists and is classified here.

| site | what it scans | classification |
|---|---|---|
| **`Names.classify`** (`Names.v`) — `find (fun t => String.eqb s (Names.type_name_spelling t)) all_type_names` | the FIXED CLOSED sixteen-element `all_type_names` descriptor enumeration | **RETAINED, not a collection defect.** This is spelling CLASSIFICATION of a source token against a closed literal enumeration of a sixteen-constructor inductive — it is decision, not persistent keyed storage. Nothing is stored in it, nothing is inserted into it, and it does not grow with program size; the whole enumeration is a compile-time constant. Its correctness is pinned by a proved inverse (`classify_spelling`, `classify_sound`, `Names.type_name_spelling_inj`), so it is a total decidable classifier, not a lookup table standing in for a map. A map keyed by `string` would add storage machinery with no semantic gain over a closed sixteen-way decision |
| **`Compilable.forest_member_at`** — `List.find (fun w => nodekey_eqb (node_ref_key (Compilable.work_node_ref w)) k) (Compilable.forest_items forest)` | the retained work item list, keyed by `Index.Key` | **DELETED (repair 13).** This WAS the defect: a persistent identity-keyed lookup implemented as a list scan, in the production conversion path, surviving proof erasure and quadratic in a nested chain. Replaced by `Compilable.WorkIndex` + `index_member_at` (one `KeyMap.find`) |

**The work-member lookup path now contains no keyed scan of any kind:**
`build_outcome_trace → build_conversion_step → build_conversion_work → forest_index_member_at →
index_member_at → KeyMap.find`.

`existsb` sites (`Compilable.list_dir_mem` / `package_present_b` and the `existsb_*` helper lemmas) are
SPEC-side package predicates and proof lemmas over canonical enumerations — the production package aggregation
is the `PackageMap` map (`package_summaries` / `Compilable.program_package_refs`). They are not identity-keyed storage
lookups. Prop-level `In` / `in_map_iff` reasoning (e.g. recovering the annotated member in
`retained_convfail_diag`) is proof structure that is fully erased and produces no runtime scan.

## `NoDup` site inventory (EXPLICIT)

Exactly **two** `NoDup` facts are carried as RECORD FIELDS in the whole theory; every other `NoDup` is a
`Lemma`/`Theorem`/sealed-module law about a derived list.

| carried field | statement | role |
|---|---|---|
| **`Compilable.forest_keys_nodup`** | `NoDup (map (fun w => node_ref_key (Compilable.work_node_ref w)) Compilable.forest_items)` | **A FACT about the ordered enumeration, and the LICENCE for the index build.** It is passed to `build_work_index` as the proof argument that makes the total, overwrite-free construction legitimate. It is **NOT** the backing store and **NOT** the lookup mechanism: nothing queries it at runtime, and `Compilable.forest_key_inj` (key uniqueness) is now derived from the STANDARD MAP via `Compilable.index_key_inj`, not from a hand-rolled induction over this list. Before repair 13 this field WAS the uniqueness half of a `list + NoDup` keyed table; that table is gone |
| **`Compilable.annotated_context_nodup`** | `forall x, In x Compilable.annotated_items -> NoDup (snd x)` | a fact about each annotated item's enclosing-conversion CONTEXT ref list — a derived per-item list consumed positionally by the diagnostic fold. No key, no lookup, no storage |

Non-field `NoDup` occurrences (`Index.occurrences_file_nodup`, `Index.children_of_nodup`, `file_refs_nodup`,
`visit_file_nodup`, `Emit.image_keys_nodup`, `Compilable.forest_pairs_nodup`, the `SS_nodup` /
`sorted_lt_nodup` helpers) are theorems about derived enumerations. **No `list + NoDup` identity table remains
anywhere in the repository.**

## Other notable false positives (searched, NOT collection defects)

- `List.mem` / `List.assoc`: ZERO real sites. The only textual matches are comments in `sink.ml` and
  `sink_test.ml` recording that the standard `Set.Make(String)` is used *instead of* `List.mem`.
- `forallb` / `fold_left` / `fold_right`: proof/spec structure over canonical enumerations
  (`program_typedb`, `source_spec_valid_b`, `list_dir_count`, `Compilable.package_foldl`) — not collection storage or
  repeated-scan lookup.
- `Decimal` digit list, `FilePath.T` path components, runtime `Syntax.Println` argument order: ordered source/leaf sequences.
- `Record`/`Inductive` names containing Map/Set/Table/Index (`Syntax.Files`, `PackageSummary`, `SyntaxIndex_T`,
  `Index.File`, `Table`, `Compilable.WorkIndex`): all are aliases / thin wrappers / domain records over standard
  maps — none defines a recursive storage tree (the old `FMap.v` association list and the old `Table` radix
  trie are deleted).

## Result

No project-authored general-purpose collection implementation remains, **and no identity-keyed role is served
by a list.** Every identity-keyed or membership-only collection names a mature standard backing (`FMapAVL` /
`FMapPositive` / `Map.Make` / `Set.Make` / `Names.GlobRef.Set`); every retained `list` has an order /
repetition / stack / transport / derived-enumeration reason, and for `Compilable.forest_items` that reason is now the ONLY
reason it is consulted at all. The one surviving `find` (`Names.classify`) is named above with its exact
justification rather than hidden inside a "no `List.find`" summary.

**Symbol-existence and role audit (current head).** Every code token named as current in this inventory was
confirmed to exist in the current theory, and its stated storage role / backing / order-and-duplicate claim was
checked against the current record or constructor — including the role check that the previous revision skipped:
for each `list`, whether anything looks it up BY KEY. The C4 objects are `Compilable.WorkForest` (ordered `Compilable.forest_blocks`
/ `Compilable.forest_items` views) + `Compilable.WorkIndex` (`Compilable.forest_index`, the `KeyMap` identity index),
`Compilable.AnnotatedWork` (ordered member/context pairing), `Compilable.Accumulator.accumulator_map` /
`Compilable.Outcomes.outcomes_acc` (the `KeyMap` FMapAVL outcome map — ONE entry per key, no list bucket, no
overwrite fallback), `Compilable.Trace` (the intrinsic causal inductive), `Compilable.ExpressionFacts`/`Compilable.ExpressionFactTable` (the
`Compilable.ExpressionSuccess` projection), and the separate `Compilable.TypeNameFacts`; the current top-level function form is
`Syntax.Main : list Syntax.Stmt -> Syntax.Decl`. Intentionally absent names are labeled as such and NOT listed as current
storage: `forest_member_at` (deleted by repair 13), the deleted `prog_conv_outcomes` combined-outcome root, the
`TFun` constructor, the old `FMap.v` association list, and the old radix-trie `Table` do not exist at the
current head and appear here only as rejected/historical.
