# Active task: the C4 exact performance comparison-series and run-identity closure candidate

Review: implementation

The exact `Analysis.Result` is a **sealed abstract authority**: the transparent canonical analysis is the record
`ResultData p`, `result_data p` is its one computation, and the singleton authority `Result p` is minted **only**
by `analyze`, with `result_unique : forall (r : Result p), r = analyze p` axiom-free. The `res_*` projections read
the canonical `ResultData` fields through `data_of_result`, never inspecting the opaque token, and the old public
record constructor `mk_result` is gone. Every public semantic type — fact rows, package decisions, child
prerequisites, diagnostics, boundaries, causes, issues and every Report view — is indexed by one exact `Result r`,
so a semantic object of Result A cannot inhabit Result B even when their `ResultData` are propositionally or
definitionally equal. `FactPhase` and `PackageFacts` are transparent fields of that `ResultData` (projected by
`res_facts`/`res_pkg`) for computation and proof, but no public reference, issue, Report reader, package decision
or fact lookup begins from an independently supplied product. The exact `Result` is also the transparent type
**index** of the sealed branch certificate rather than a field behind it. The branch decision reads its disposition
from one shared `ResultData` — the emptiness of diagnostics and boundaries computed without building the exact ref
lists — so the sealed dataless authority stays computationally irrelevant and never lands on a `vm_compute` goal.
`make check` is green on the pinned toolchain and the generated Go bytes are byte-identical.

The C4 static-authority subsystem is an exact-evidence DAG rooted at one `Compilable.Program p`:

- **Index** is the direct shallow occurrence authority — a finite file map of finite position maps of shallow
  cells, one source-ordered traversal; RNode trees, flat scans, and list-scan reads are gone.
- **PackageIdentity** retains the package surface, position-selector `PackageRef`s, exact module-path and
  complete-import-path components, and the default executable name over the complete import path (with terminal
  semantic-major stripping).
- **Bindings** is the structural binding foundation: establishments, scopes, ordinary resolution, declaration
  groups keyed by exact scope and spelling with unique/redeclared status, const-inheritance and short-declaration
  facts, and the fixed `func main()` as a real package-scope function declaration that joins the one declaration
  group keyed by scope and spelling (a redeclared `main` group is `OrdinaryRedeclared`) and resolves through
  ordinary scope (recursive/cross-file, with local `main` shadowing), `MainMissing`/`MainOne`/`MainMultiple` a
  distinguished projection over those declarations for executable-entry multiplicity.
- **Analysis** is the sole fact and issue authority. `Cause`/`Requirement`/`Dependency bp site kind` are indexed by
  exact phase, occurrence site and fact kind; each outcome accepts only its own site+kind payload, and the displayed
  family is a total site+kind projection. `FactPhase` is a transparent field of the canonical `ResultData` (read
  through `res_facts`), and a
  **`FactRowRef r`** is an exact ordinal into `result_fact_list r` (the retained row list of the one `r`) with the
  retained row and its `nth_error` membership proof. The row enumeration `fact_rows r` is exactly `result_fact_list r`,
  once, in retained order (complete, duplicate-free by ordinal, positionally unique); `fact_row_for r site kind`
  searches only those rows and is unique by exact site+kind, returning two distinct rows for an application's Value
  and Application keys. A retained row's outcome is exactly the `own_*` result the canonical one-pass `va_facts` /
  `occ_facts_va` builder selected, so no fabricated same-site same-kind peer belongs to the list.
  `InvalidFactRef r`/`UnmetFactRef r`/`DependentFactRef r` are case views over an exact `FactRowRef r` (the
  cause/requirement/dependency projected from the retained row, never caller-supplied).
  A statement's child dependency is no longer location-only: `DepChild` carries an exact `ChildFactEdge site kind`
  — the value child, or the application child with its exact `AppRef` — indexed by the parent site, so the child's
  node is a real structural descendant with strict positional progress — `node_parent child = parent` and
  `nr_pos parent < nr_pos child`, so the parent statement node is never its own child — and its kind is exactly
  value or application. There is exactly one executable complete fact construction, internal to `analyze`: `va_facts`
  computes each node's value and application facts once, `occ_facts_va` projects the canonical rows from that one
  `va`, and the raw list is that projection over every file. The expr-statement driver reads its child's negativity
  from that same `va` (never a rerun of `own_value`/`own_app`), and every retained-fact and child-prerequisite law is
  proved directly over that one builder — no second complete builder and no equality-to-a-peer-builder bridge exist.
  A `ChildDependentFactRef r` is a retained statement row of `r` whose outcome is exactly `SDependent (DepChild edge)`;
  a `NegativeFactRef` is the child row's own exact invalid/unmet/dependent case (a dependent child keeps its own exact
  dependency, unflattened); and a `ChildPrerequisiteRef r cdfr` retains the exact `fact_row_for r` result at the
  edge's child site+kind with that negative case — all in the same `r`. Completeness holds: every child-dependent
  parent row's exact negative child fact is retained in that same result, so `child_prerequisite` never fails, and
  `result_child_prerequisites r` enumerates one per child-dependent parent row in retained order. Dependent facts
  still emit no duplicate issue row. `Boundary r`, `Diagnostic r`, `IssueCause r` and `Issue r` are all indexed by the
  one exact `Result r`: a missing-main diagnostic retains an exact `MissingMainRef r` (its package's canonical
  decision IS `result_package_rule r pr = MainMissing`) and an output-collision diagnostic an exact `CollisionRef r`
  (the retained `result_preflight r` IS a `FreshCollision` at that package+root), so a raw `PackageRef` or
  package+root pair is not a package fact. `result_diagnostics r` projects those exact case builders
  (`result_missing_main_refs r` / `result_collision_ref r`), never re-testing the raw condition inline. Every issue
  has an exact ordinal identity — an `IssueRef r` into the one `result_issues r` sequence. The product makers/readers
  `facts`, `package_facts`, `fact_list`, `preflight`, `package_rule`, `diagnostics`, `boundaries` and
  `program_disposition` are gone from the public surface; the `result_*` projections are the sole public route.
- **Report** projects those exact row/case/issue identities and nothing else, with proved bidirectional-membership,
  exact identity, class-partition, no-collapse, payload, and stable-order laws; its bp-free `CauseView`/`ReqView`
  are one-way projections that cannot mint an exact Cause/Requirement/row. Its bp-free `ChildPrerequisiteView`
  projects a child prerequisite's exact parent/child sites and kinds and the child's negative class, one-way, and
  cannot mint an exact `ChildPrerequisiteRef` or `ChildDependentFactRef`.
- **Compilable** is the sealed `C4_PUBLIC` surface. The one transparent `compilation_data p := analyze p` is the
  canonical `Analysis.Result`; `disposition_of` decides the branch over that exact data; and the abstract
  `Compilation`/`Program`/`Rejection`/`Outside` are certificates **indexed by** that exact result — they carry
  logical evidence but no Result field. `compile` is the sole mint of the branch object, `outcome_result` reads the
  exact type index without opening the certificate, and `compilation_canonical` is proof authority, never the
  acquisition route. The record makers and the private composer are absent from the client namespace.
- **Emit** is one generic evidence-indexed boundary: `Emit.Image cp Evidence evidence`, `of_compiled`, and
  `of_evidence`, all over an exact compiled `Program` with no source/bytes route; `transport` is Render over the
  exact indexed source.

The formal-vs-Go acceptance differential begins from one named `Syntax.Program` per case: the formal side executes
`compile` (a proven disposition), the external side is pure Render of that same source run through the pinned Go
toolchain, and the two verdicts are compared. The gate corpus (layer policy, one-build, sealed-abstract-branch,
`neg_*` fact-row/certificate/package-decision/child-prerequisite/unforgeability controls, positive control, forge-provenance controls) and the
governing corpus are updated with the code.

## Status

The candidate is frozen `CANDIDATE_READY_FOR_REVIEW` for the whole-candidate review (all registered criteria); C4 is **not**
claimed accepted or complete, and only Rob accepts. The frozen lower stack stays `IMPLEMENTED_NOT_ACCEPTED` (C5
stays historically accepted; C6 roots beyond the cutover stay frozen until acceptance; `make check` on the pinned
toolchain is the supported run). Governing truth held by this candidate:

- `Analysis.Result` is a **sealed abstract authority**: the transparent canonical analysis is `ResultData p`,
  `result_data p` is its one computation, `analyze` is the sole mint, and `result_unique : forall (r : Result p), r =
  analyze p` holds axiom-free (`Result p := unit` under a sealed `RESULT_AUTHORITY` module; the whole-theory and e2e
  assumption audits stay clean). `data_of_result r := result_data p` reduces definitionally, the `res_*` projections
  read the canonical `ResultData` fields through it, and the old public record constructor `mk_result` is gone (the
  data maker `mk_result_data` builds `ResultData`, not authority). The dataless token never lands on a `vm_compute`
  goal: the branch disposition reads diagnostic/boundary emptiness from one shared `d` without building the exact ref
  lists, and `fact_rows` binds its row list once, so concrete computation stays cheap (a warm `make check` in the low-20s; a project-cold complete run is ~98s median).
- `FactPhase` and `PackageFacts` still exist and remain transparent retained fields of the canonical `ResultData`
  behind `Analysis.Result`, useful for finite computation and dependent proof factoring; they are no longer public
  semantic authority. Their eventual full deletion, if ever warranted, is a later C4 root.
- `Analysis.Result` is the sole public semantic acquisition boundary: every public fact-row, package-decision,
  child-prerequisite, diagnostic, boundary, cause, issue and Report object is indexed by one exact `Result r`. A
  semantic object of Result A cannot inhabit Result B even when both Results carry equal `ResultData`
  (the type is genuinely parameterized by the exact `r`). The peer product makers/readers (`facts`, `package_facts`,
  `fact_list`, `preflight`, `package_rule`, `diagnostics`, `boundaries`, `program_disposition`) are gone from the
  public surface — `@AN.<name>` is unresolvable — and the `result_*` projections are the sole public route.
- The child-prerequisite is exact same-`Result`: a `ChildDependentFactRef r`'s retained `DepChild` edge names the
  exact child row `fact_row_for r` selects, with that child's own exact negative case, and the parent consumes the
  one executable fact builder rather than rerunning `own_value`/`own_app`; the prerequisite carries strict
  `nr_pos parent < nr_pos child` progress (so the parent is never its own child), surfaced from the canonical
  numbering as the public `Index.node_parent_pos_lt` / `Index.Child.child_pos_gt_parent` without exposing Build
  internals.
- C4's requirement to decide every represented Go static fact remains authoritative, but that is the accepted
  ownership obligation, not a claim of completed rule coverage: the authority/provenance foundation is implemented,
  represented static-semantic completion remains open, and the exact unsupported requirements are honest temporary
  boundaries. Remaining static-semantic completeness, issue-order redesign, and post-C4 documentation normalization
  are later roots.
- Short-declaration structural legality is now decided exactly by one canonical `short_decl_decision` following the
  fixed precedence; a structurally valid short declaration carries an exact unmet `ReqShortUsage` and is
  `OutsideScope`, never a false diagnostic and never `SOK` (the generic `ReqDeclMeaningS` catch-all is deleted).
- **Exact positive requirement-case identity and full branch reflection are now closed.** Each positive short
  requirement is a Result-owned exact ref over retained rows — `ShortStatementFactRef` (the canonical retained
  statement fact, unique by site), `ShortRhsMeaningRef` (the first `VNonconst` RHS Value row and its exact child),
  `ShortRedeclarationTypesRef` (the aligned existing-variable pair list and New rows), `ShortUsageRef` (the canonical
  New rows) — never a raw list or a caller-supplied payload. `short_decl_decision_cases` reflects the one decision as
  exactly nine fixed-order cases (duplicate / count / blocker-nonvar / blocker-ambiguous / no-new / negative-RHS /
  RHS-meaning / redeclaration / usage), each with its exact retained outcome, discharged branch-by-branch by the
  per-case sound and completeness lemmas over free `bp`/`r`, with source-order firstness certificates and the
  result-level `short_case_for` projection; the decision is never `SOK` and no second evaluator exists.
- **Short-origin source-value meaning is now modeled.** A value-position name use resolving to a `DOShort` source
  object is a lawful nonconstant `VNonconst` value: the Result-owned exact `ShortOriginValueRef` retains the use
  site, spelling, exact `ResolutionRef`, `DOShort` origin, and the retained `VNonconst` Value row, so
  `ReqValueMeaning` no longer fires for short-origin uses (it is now the residual for `DOBinder` uses only).
  Whole-program success is unchanged: a structurally valid short declaration still carries the exact `ReqShortUsage`,
  so `x := 1; println(x)` stays `OutsideScope` and no new program is `Compiled`. Exact declared-and-unused
  local-variable usage analysis is the next slice; exact source-variable type equality (mixed redeclaration and
  binder value/type meaning) remains a later root — both honest temporary boundaries (decision `C4-SHORTDECL` in
  `DECISIONS.md`). Material performance opportunities remain explicit in `.review/PERFORMANCE_OPPORTUNITIES.tsv`.
  No C4 completion is claimed.
- **The active candidate is the exact performance comparison-series and run-identity closure; exact
  semantic outputs are unchanged.** Individual event graphs, the terminal-bound longest path, boundary
  work/span metrics, generated summaries, and typed metric references are already closed and preserved.
  This slice makes the governed run series intrinsic: `.review/PERFORMANCE.tsv` owns the exact series, the
  accounting engine (`tools/perf-work-span.py`) consumes the status-declared RunKeys
  `(basis, scenario, run_id)` — never a run-name prefix — and requires an exact bijection with the
  retained event graphs. Every retained current cold graph is governed and included in every median; the
  current cold series requires at least three unique comparable runs and uses the ordinary mathematical
  median (even count = mean of the two middle values); the historical baseline is the exact
  `comparison-baseline` row (verified basis `cb7e5810…@c13e3d5`), a single representative run, so the
  one-DAG delta is the current cold median versus that verified historical representative (a conservative
  lower bound), never a false `median_vs_entry`. Worker timing precision is direct and truthfully
  labelled: the chunk workers emit a monotonic `/proc/uptime` millisecond marker (`PROC_UPTIME_10MS`),
  every event states its clock and native resolution, and no row may claim finer precision than its
  source. The typed metric index gains `series.*` run-count and median metrics; the retained event table
  holds exactly one comparison baseline and the current cold graphs, nothing else. The theorem-backed
  evidence observation is **not** implemented (`realistic_expected_saving = UNKNOWN_PENDING_SPIKE`; a
  measurement-only spike remains later if the repaired evidence supports it), and exact declared-and-used
  local analysis remains the next semantic root. C4 remains implemented but not accepted or complete.
- **The retained single-build verification DAG; exact semantic outputs are unchanged.** One
  `theory-built` parent owns the one Docker copy of the certified source closure and the ONE
  `dune build @install @all`, snapshotting the exact cache-assisted `_build` into an ordinary immutable layer;
  the proof/audit branch and the emit branch both descend from it and never rerun Dune, and the final
  `generated-artifact` requires BOTH branch markers (`proof-ok`, `fresh-build-ok`) through a verified join
  that exports exactly the pristine generated module. `make check` and the staged pre-commit hook each issue
  ONE project-verification Buildx solve through `tools/build-verified-artifact.sh`; `make prove`/`emit`/
  `e2e`/`profile`/`regenerate` stay truthful over the shared parent. `tools/build-graph-gate.py` pins the
  topology (one Dune builder, shared ancestry, marker joins, artifact purity, one solve per path) and
  `tools/dag-guard-test.sh` proves the join load-bearing on the real final target. Caches remain optional
  (the empty-cache project-cold solve passes); an e2e-only edit rebuilds only the emit branch, and go-e2e
  re-validates only when the generated bytes change. Performance evidence distinguishes aggregate measured
  work from critical-path wall span, and the prior fixture repair (prelude + four cost-balanced chunks, the
  `p_two_iota` shared-observation bundle, the honest evidence validator) is preserved unchanged. The earlier
  fixture-slice history (fast-disposition REJECTED_MEASURED; chunking and bundles IMPLEMENTED) and the open
  material opportunities live in `.review/PERFORMANCE_OPPORTUNITIES.tsv`. Local declared-and-used analysis
  remains the next semantic root.
- The live classifications are exactly the Result-indexed diagnostics, boundaries and issues plus Compilable's
  three-way `Compiled`/`Rejected`/`OutsideScope` verdict; there is **no** separate Analysis summary algebra. The
  former dead five-way `Analysis.Disposition` summary and its whole-program projection were deleted this slice
  (external absence controls pin the exact removed names as unresolvable), and diagnostic/boundary coexistence is
  represented directly in the exact `result_issues` list (`d4_invalid_unsupported_coexist`).
- The implemented issue order is output-collision diagnostics, then main diagnostics, then redeclaration
  diagnostics, then occurrence diagnostics, then all boundaries. That order is category/class partitioned and
  stable; it is not claimed to be unified global source order.
- The large A–I/Q/S/K catalogue is a pinned-Go behaviour catalogue, while the named one-source cases (gate-enforced, currently fifteen rendered trees) are
  genuine formal-vs-Go comparisons.
- `.review/PERFORMANCE.tsv` is the live, digest-based **exact governed run-series authority**: it declares
  each measured run's exact series role (`comparison-baseline` / `final-candidate` / `tooling-baseline`),
  and the accounting engine consumes those declarations — keyed by the composite RunKey
  `(basis, scenario, run_id)` — as the sole source of series membership, in exact bijection with the
  retained event graphs. No run-name prefix (`entry*`/`final*`), row position, or notes string carries any
  selection authority. It is validated on the normal and staged complete paths, never treated as inert
  history.

## Stop conditions

Stop and ask Rob on a falsified accepted lower fact (which triggers targeted causal dependency retreat), a
representable case that cannot be classified `Compiled`/`Rejected`/`OutsideScope` without narrowing syntax, exact
fact-row or certificate identity that cannot be brought off the vm-compute cliff without weakening the topology, or
any scope or acceptance decision.
