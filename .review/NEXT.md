# Active task: the C4 Exact Same-FactPhase Child-Prerequisite candidate

Review: none

An Analysis fact is semantically authoritative only when it is the exact retained row of the canonical
`FactPhase`. Every invalid/unmet/dependent ref and every occurrence diagnostic/boundary is a dependent view of
that exact row, and the exact `Analysis.Result` is the transparent type **index** of the sealed branch
certificate rather than a field behind it. `make check` is green on the pinned toolchain and the generated Go
bytes are byte-identical.

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
  family is a total site+kind projection. `FactPhase bp` retains the canonical one-pass fact list, and a
  **`FactRowRef fp`** is an exact ordinal into `fact_list fp` with the retained row and its `nth_error` membership
  proof. The row enumeration `fact_rows fp` is exactly `fact_list fp`, once, in retained order (complete,
  duplicate-free by ordinal, positionally unique); `fact_row_for site kind` searches only those rows and is unique
  by exact site+kind, returning two distinct rows for an application's Value and Application keys. A retained row's
  outcome is exactly the `own_*` result the canonical `occ_facts` traversal selected, so no fabricated same-site
  same-kind peer belongs to the list. `InvalidFactRef`/`UnmetFactRef`/`DependentFactRef` are case views over an
  exact `FactRowRef` (the cause/requirement/dependency projected from the retained row, never caller-supplied).
  A statement's child dependency is no longer location-only: `DepChild` carries an exact `ChildFactEdge site kind`
  — the value child, or the application child with its exact `AppRef` — indexed by the parent site, so the child's
  node is a real structural descendant (`node_parent child = parent`) and its kind is exactly value or application.
  The parent statement consumes the one canonical child-fact computation: `va_facts` computes each node's value and
  application facts once, and the expr-statement driver reads that child's negativity from `va` (never a rerun of
  `own_value`/`own_app`), proven equal to the reference traversal by `occ_facts_va_eq`. A `ChildDependentFactRef fp`
  is a retained statement row whose outcome is exactly `SDependent (DepChild edge)`; a `NegativeFactRef` is the child
  row's own exact invalid/unmet/dependent case (a dependent child keeps its own exact dependency, unflattened); and a
  `ChildPrerequisiteRef` retains the exact `fact_row_for` result at the edge's child site+kind with that negative
  case — all in the same `FactPhase`. Completeness holds: every child-dependent parent row's exact negative child
  fact is retained in that same phase, so `child_prerequisite` never fails, and `child_prerequisite_refs` enumerates
  one per child-dependent parent row in retained order. Dependent facts still emit no duplicate issue row.
  `Boundary fp` is indexed by the exact fact phase, while `Diagnostic fp pf`/`IssueCause fp pf`/`Issue fp pf` are
  indexed by the exact fact phase AND the exact `PackageFacts`: a missing-main diagnostic retains an exact
  `MissingMainRef pf` (its package's canonical decision IS `package_rule pf pr = MainMissing`) and an
  output-collision diagnostic an exact `CollisionRef pf` (the retained `preflight pf` IS a `FreshCollision` at that
  package+root), so a raw `PackageRef` or package+root pair is not a package fact. `main_rows`/`collision_rows`
  project those exact case builders (`missing_main_refs`/`collision_ref`), never re-testing the raw condition inline.
  Every issue has an exact ordinal identity — an `IssueRef` into the one `result_issues` sequence.
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

The candidate is frozen `CANDIDATE_READY_FOR_REVIEW` for the sixteen-pass whole-candidate review; C4 is **not**
claimed accepted or complete, and only Rob accepts. The frozen lower stack stays `IMPLEMENTED_NOT_ACCEPTED` (C5
stays historically accepted; C6 roots beyond the cutover stay frozen until acceptance; `make check` on the pinned
toolchain is the supported run). Governing truth held by this candidate:

- `FactPhase` and `PackageFacts` still exist and remain fields of `Analysis.Result`; their full
  consolidation/deletion/sealing is a later C4 root.
- The included stack establishes exact retained fact-row identity, the transparent-data/sealed-certificate branch
  topology, and exact package-decision-case identity: a missing-main diagnostic retains an exact `MissingMainRef`
  case and an output-collision diagnostic an exact `CollisionRef` case, both indexed by the exact `PackageFacts`
  from the same Result (a diagnostic for one `PackageFacts` cannot inhabit another). It does not make `Result` the
  sole public semantic reader everywhere.
- This slice makes `DepChild` carry an exact structural `ChildFactEdge` and establishes the exact same-`FactPhase`
  child-prerequisite: a `ChildDependentFactRef`'s retained edge names the exact child row `fact_row_for` selects,
  with that child's own exact negative case, and the parent consumes the one canonical child-fact computation
  rather than rerunning `own_value`/`own_app`. Full Result/product consolidation of that prerequisite remains a
  later C4 root; `parent <> child` node distinctness awaits a `node_parent`-acyclicity primitive surfaced at the
  Index NodeRef API.
- C4's requirement to decide every represented Go static fact remains authoritative, but the implementation is not
  complete; the known missing static cases stay mandatory later work.
- The implemented issue order is output-collision diagnostics, then main diagnostics, then redeclaration
  diagnostics, then occurrence diagnostics, then all boundaries. That order is category/class partitioned and
  stable; it is not claimed to be unified global source order.
- The large A–I/Q/S/K catalogue is a pinned-Go behaviour catalogue, while the ten named one-source cases are
  genuine formal-vs-Go comparisons.
- `.review/PERFORMANCE.tsv` is historical evidence unless its commit/tree metadata matches the frozen candidate; it
  is not live gate authority.

## Stop conditions

Stop and ask Rob on a falsified accepted lower fact (which triggers targeted causal dependency retreat), a
representable case that cannot be classified `Compiled`/`Rejected`/`OutsideScope` without narrowing syntax, exact
fact-row or certificate identity that cannot be brought off the vm-compute cliff without weakening the topology, or
any scope or acceptance decision.
