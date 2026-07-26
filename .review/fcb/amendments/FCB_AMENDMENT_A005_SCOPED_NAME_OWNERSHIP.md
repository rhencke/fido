# FCB Amendment A005 — Scoped Name Ownership

- **ID:** `FCB-A005-SCOPED-NAME-OWNERSHIP`
- **Status:** **ACCEPTED** — human owner Rob
- **Author:** the reviewer (delivered as the A005 scoped naming migration directive)
- **Committer:** Claude Code (applied the migration; authored nothing in this amendment)
- **Date:** `2026-07-26`
- **Reviewed repository head:** `52dd9746bc58e8a17e3784593c5d9c8c5237b262`
- **C4 semantic implementation candidate preserved by this migration:**
  `3386c023fe10df4ae433726044d61642f219309c`

> Rob's authorization, verbatim: *"Ruthlessly rename away."* — with the standing rule that the Go domain is
> implicit and must not be repeated in file or module names, that identifiers must not redeclare a scope
> their namespace or owning record already supplies, that abbreviations such as `cp_`, `ewf_`, `tnft_` must
> not survive as fake namespaces, and that the migration happens before the C4 review resumes.
>
> And the reading that settles every collision: *"distinguished names are the correct answer throughout. the
> qualified names are succinct and show where identifiers are defined. it's go-like."*

## New information

The theory encoded one scope twice. `GoCompile.CompilableProgram`, `GoIndex.IndexedProgram`,
`GoTypes.GoType`, `GoSafe.SafeProgram` and `GoEmit.DirectoryImage` each repeated their module's domain in the
declaration's own name, and records repeated their type through initials — `cp_program`, `ec_phase`,
`ewf_items`, `tnft_map`, `di_go_files`, `sp_compiled`.

Rocq's logical module already owns the domain and the value's type already supplies the local concept, so a
reader was decoding redundancy. Worse, the abbreviations were simulating structure: a large module grew
`cp_`, `ec_`, `pe_` families instead of admitting it wanted real namespaces.

## Settled law

1. A namespace states its domain once.
2. A declaration inside that namespace names only its role inside the domain.
3. Cross-namespace use is qualified when a short name could be ambiguous.
4. A semantic qualifier remains only when the containing namespace does not provide that distinction.
5. Cryptic initials are never a substitute for a real namespace or a real semantic word.
6. A collision is resolved with the smallest full semantic distinction, never by restoring an abbreviation.
7. Old names receive no aliases, compatibility modules, deprecated wrappers, or re-exports.
8. Git history is the only compatibility layer.

## Governance decision added

**D-25 — Names are owned by their scope.** A module, nested module, record, or other real namespace supplies
a concept's domain. Declarations do not repeat that domain through `Go` prefixes, type-name prefixes, or
initialisms such as `cp_`, `ewf_`, `tnft_`, `di_`. Where two declarations in one Rocq namespace need
different names, use full semantic words or a real subnamespace; never an abbreviation as a pseudo-namespace.
*Rationale:* redundant names obscure the authority chain, make qualified names noisy, and let a large module
simulate structure through prefixes. Scope-relative names expose the actual architecture, so a missing
abstraction or a bad module boundary becomes visible instead of hiding behind a prefix.

## Scope

Naming and dead-surface removal only. This amendment changes **no** Go-language meaning, theorem guarantee,
accepted program set, generated Go path, generated Go byte, target policy, proof assumption, or runtime
behaviour. No Closure Ledger row, Latitude Ledger row, Acceptance Gate, roadmap row assignment, checkpoint
order, or target/toolchain policy changes. C4 remains **not accepted**; C5 and post-C4 feature work remain
forbidden.

## Enforcement

`tools/naming-gate.py`, run by `make names` and wired into `make check` ahead of the proof and container
work. The Rocq compiler is already a total verifier for code — a missed rename simply fails to build — so the
gate exists for the surface that has no verifier at all: documentation, and the comments inside source files.
It carries an explicit old-name and forbidden-prefix table plus negative controls that prove it both fails
when it must and accepts when it must; it reports and never rewrites.

Rule 8 of the gate is deliberately narrow so history stays honest. A live document may write

> `GoCompile` was renamed to `Compilable` by A005.

because the line carries an explicit historical marker. It may not use `GoCompile` as the current authority.

## Forced deviations from the frozen map

Two frozen names could not be taken literally, and both are recorded rather than quietly worked around.

**1. The sealed `Snapshot` records keep a distinct private name.** Part C9 assigns `FileRef_T -> FileRef`,
`NodeRef_T -> NodeRef` and `SyntaxIndex_T -> Syntax`. Rocq refuses this: sealing `Parameter FileRef : … ->
Type` against a bare inductive fails with

> *Signature components for field FileRef do not match: a definition is expected. Hint: you can rename the
> inductive or constructor and add a definition mapping the old name to the new name.*

The two-name structure is Rocq's own prescribed workaround, so the underlying records keep a distinct name
while the **public** surface obeys A005 in full: `Index.Snapshot.FileRef`, `Index.Snapshot.NodeRef`,
`Index.Snapshot.Syntax`.

**2. `ModuleSpec` cannot take `path`/`version`.** Part C8 assigns `path` to both `FileNode` and `ModuleSpec`,
but Rocq record projections share one namespace and two `path`s will not compile. Applying rule 6 — the
smallest full semantic distinction, never an initialism — `FileNode` keeps `path`/`source` and `ModuleSpec`
takes `module_path`/`module_version`.

## Affected FCB files

`FIDO_FCB_GOVERNANCE.md` (D-25 and the amendment register), `FIDO_FCB_INDEX.md` (accepted-amendment banner),
`FIDO_FCB_HUMAN_REVIEW_INDEX.md` (A005 accepted; C4 review paused for the migration),
`FIDO_FCB_CHECKPOINT_AUTHORING_GUIDE.md` (the naming duty), and any live prose naming a Rocq symbol.
