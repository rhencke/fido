# Active task: the C4 Exact Retained Analysis Fact-Row candidate

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
  exact `FactRowRef` (the cause/requirement/dependency projected from the retained row, never caller-supplied), and
  `Diagnostic fp`/`Boundary fp`/`IssueCause fp`/`Issue fp` are indexed by the exact fact phase. Every issue has an
  exact ordinal identity — an `IssueRef` into the one `result_issues` sequence.
- **Report** projects those exact row/case/issue identities and nothing else, with proved bidirectional-membership,
  exact identity, class-partition, no-collapse, payload, and stable-order laws; its bp-free `CauseView`/`ReqView`
  are one-way projections that cannot mint an exact Cause/Requirement/row.
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
`neg_*` fact-row/certificate/unforgeability controls, positive control, forge-provenance controls) and the
governing corpus are updated with the code.

## Status

The candidate is frozen `CANDIDATE_READY_FOR_REVIEW` for the sixteen-pass whole-candidate review; C4 is **not**
claimed accepted or complete, and only Rob accepts. The frozen lower stack stays `IMPLEMENTED_NOT_ACCEPTED` (C5
stays historically accepted; C6 roots beyond the cutover stay frozen until acceptance; `make check` on the pinned
toolchain is the supported run). Governing truth held by this candidate:

- `FactPhase` and `PackageFacts` still exist and remain fields of `Analysis.Result`; their full
  consolidation/deletion/sealing is a later C4 root.
- This slice establishes exact retained fact-row identity and the transparent-data/sealed-certificate branch
  topology; it does not make `Result` the sole public semantic reader everywhere.
- `DepChild` remains location-only and same-`Result` prerequisite/child-fact identity is open.
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
