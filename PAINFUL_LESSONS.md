# Fido — painful lessons (permanent)

The small set of EXPENSIVE, COUNTER-INTUITIVE traps this project actually fell into — where the wrong path
looked reasonable and we only learned by paying for it. Not a catalogue of the design (that is
`ARCHITECTURE.md`/`CLAUDE.md`) and not a status diary (`PROGRESS.md`). If a proposal resembles one of these,
stop. When an entry stops being a live temptation, delete it.

1. **A subset filter is not compiler admissibility — and this trap recurs in new disguises.** If the AST can
   represent a program the real toolchain ACCEPTS, a checker that rejects it is a supported-scope decision
   wearing a compiler-authority name (the printer-round-trip's compile analogue). The rule: model every
   represented form's *real* acceptance, or make unsupported forms UNREPRESENTABLE — never rejected by a
   guard. A representable program `go build ./...` accepts but GoCompile rejects is a MODEL BUG, not
   "unsupported syntax." (This is why `GoCompile` proves sound + complete against a declarative judgment and
   is attacked by differential experiments against real Go; a green boolean is not the authority.)

2. **The compile unit is the WHOLE program tree; paths, module identity, and the module file are semantic
   inputs.** Go groups files by directory into packages; one-main-per-package is a whole-program property; a
   raw `string` key is not a file path (package discovery depends on the extension, `_test`/GOOS suffixes,
   hidden dirs, directory identity). Single-file compiler semantics with `string` keys cannot model this.
   So: `GoProgram` pairs an intrinsic `ModuleSpec` (module path + Go version — the generated module's facts,
   NOT a target config) with a POSSIBLY-EMPTY finite map keyed by an INTRINSIC `FilePath` (the empty map is a
   valid module-only program — a nonemptiness restriction was a false narrowing); `GoCompile` consumes it all
   at once, all-or-nothing; package grouping / package name / entry-point status are COMPILATION RESULTS
   (`CompilationFacts`), never collapsed into a raw node like the deleted `MainFile`. The `go.mod` is PART of
   the generated program and is RENDERED in Rocq from the `ModuleSpec` (proved exact bytes) — never injected
   by hand in the build, and never smuggled into the `FilePath` map (it is not a `.go` path).

3. **Gate the invariant you advertise.** A functional first-match lookup theorem (`fm_MapsTo_fun`) holds even
   over a duplicate-keyed list, so it is NOT evidence of key uniqueness — that is `fm_keys_nodup` (the carried
   `NoDup` field) + `dup_key_unrepresentable`. Likewise "axiom-free" is necessary, never sufficient: a
   kernel-checked proof can still prove a weak/irrelevant/self-referential claim. Always check the STATEMENT.

4. **Handwritten OCaml is a TRANSPORT boundary, never a program decoder.** The deleted 82-line backend
   accepted an arbitrary `constr` and decoded it by application ARITY — term inspection masquerading as a
   transport. The permitted boundary is four steps: typecheck the image type, reject a non-empty assumption
   closure (a kernel provenance query — NOT decoding proofs or programs), decode ONLY the final
   `(go.mod bytes, (path, bytes) list)` transport with EXACT constructors (fail loud otherwise), then call
   the filesystem-only sink. It inspects no program/AST/behaviour/semantics. If that boundary cannot be met, delete the e2e — a
   false transport foundation is worse than no integration. (And emission is an EXPLICIT command, not a
   cached `.vo` side effect a warm cache would silently skip, nor a per-witness extracted executable.)

5. **Provenance is gated at the LIVE boundary, not by the type alone.** A `DirectoryImage` carries a proof
   ([di_prov]) it came from rendering a `SafeProgram`, and the map stays reducible (opaque Rocq modules
   would abstract it but break the reduction the transport command needs). But a proof can be POSTULATED —
   an `Axiom`/`Admitted`/section `Variable` gives a well-typed but uncertified image — so the type is not
   the gate. The gate is the emit command's assumption-closure check (it rejects any image whose proof
   depends on an assumption, descending Qed bodies), so a forged image cannot cross into filesystem effects.

6. **File emission became OVER-DESIGNED when a reviewer's hostile-filesystem concerns displaced the real
   single-owner threat model.** ⚠ The threat model here is ONE project owner + cooperating emitters
   serialized by one lock + a stable directory namespace + ordinary crashes/disk/permissions — NOT a
   malicious concurrent adversary or arbitrary unmount/remount. A whole stage-record / OS-nonce / local-
   stage-directory / record-driven-recovery subsystem was a disproportionate answer to that, and it was
   deleted. The durable shape: `<root>/.fido/` = exact marker + git-style `index.lock` ONLY, and each output
   stages into its RESERVED sibling temp `<final>.fido-tmp-v1` — because the lock serializes, the name needs
   NO nonce and recovery needs NO record (the final path is already known to the live sync). A regular
   reserved-suffix file WHOSE SUFFIX-STRIPPED PATH MAPS TO A FIDO FINAL PATH (root `go.mod` or an intrinsic
   `.go`) is, by PUBLIC (forgeable) CONVENTION, an abandoned Fido temp — an ACCEPTED tradeoff under this
   threat model; do NOT build a transaction log to make ownership unforgeable. The still-live
   sub-lessons: ⚠ a reviewer can name a real defect WITHOUT owning the replacement, and the current
   `.review/NEXT_STEPS.md` — not the reviewer's preferred architecture — is binding; a defect unfixable
   within it is an ARCHITECTURAL CONFLICT to escalate, never a quiet redesign. ⚠ STAGE THE COMPLETE IMAGE
   before any install (else a disk/permission failure leaves a MIXED generation); install is still
   nontransactional across the tree — say so. ⚠ Recovery is TWO-PHASE (inspect-collect, then delete) and
   fail-CLOSED; a symlink/dir/special reserved-suffix entry aborts + is preserved. ⚠ Handled-failure cleanup
   (immediate; this run's temps + empty parents; error-aggregating) is DIFFERENT from crash recovery (next
   run, after the stale lock is cleared) — a handled failure must not leave residue "for the next run". ⚠
   Filesystem discovery must distinguish MISSING (a confirmed `ENOENT`) from an operational error
   (EACCES/EIO/ELOOP/…) — never turn a readdir/lstat failure into "empty" or "no header"; that is fail-OPEN.
   ⚠ Validate the ROOT chain (a prefix symlink redirects every effect), reserve `.fido/`, reject a nested
   `.fido` of any type in the traversed namespace, and reject a cross-device rename fail-loud (no copy
   fallback). ⚠ Dirty FOREIGN Go contradicts a closed-world compile guarantee: a foreign `.go` in the
   Go-discovered namespace, or a foreign/nested `go.mod`, must REJECT the whole emission (fail-closed scan) —
   NOT preserved-and-merged into a tree we then claim compiles. Inject faults (real crash via `Unix._exit`, unlink failure, EXDEV) through operation
   PARAMETERS, never an ambient env branch or a real `chmod` in the production sink. ⚠ The GENERATED
   `FilePath` domain (what Fido would write — lowercase, no dotfiles/`_`/`testdata`/`vendor`) and the FOREIGN
   Go-discovery scan (what `go build ./...` would compile) have DIFFERENT responsibilities: the dirty-tree
   scan must skip only the directory trees Go itself ignores (`.`-prefixed incl. `.git`, `_`-prefixed,
   `testdata`, `vendor`) — NOT every path Fido would not generate — or a visible foreign package Go compiles
   slips past the foreign-Go rejection; and a `.git`-metadata blob merely NAMED like a `.go`/temp is preserved
   and ignored, never touched. ⚠ But that RUNTIME-sink skip is the OPPOSITE requirement from the STAGED-TREE
   VERIFICATION GATES: a repository-content gate (the OCaml-origin / generated-output / staged-generated-
   compare scripts over the exported index) must inspect EVERY tracked file at EVERY depth, pruning ONLY
   `.git` — never the sink's opaque dirs.  Reusing the sink's Go-discovery skip in a gate is a FAIL-OPEN: a
   rogue `.hidden/x.ml` escapes the OCaml allowlist and an unheaded/exec/symlink `.hidden/x.go` escapes the
   output policy, and since `.dockerignore` also hides tracked `.go` from Buildx, NO check would ever see it.
   A Buildx-free `precommit-selftest` demonstrates the gates reject these at every depth.  ⚠ A public temp
   suffix (`<final>.fido-tmp-v1`) is a forgeable convention, but
   ownership still requires the suffix-stripped path to map to a possible Fido final path (root `go.mod` or a
   valid intrinsic `.go`) before deletion — a non-mappable suffixed entry is preserved and refuses. ⚠ A
   source-LINE cap on the OCaml boundary is not a correctness invariant (the boundary is enforced by the
   allowlist + no-Rocq-terms + transport-only greps, not a byte budget) — do not gate on line count.

7. **Source-text scanning is not a sound zero-axiom gate — audit the compiled environment's CLOSURE.** Every
   text scanner leaked (a comment stripper missed an `Axiom` behind a `"(*"` string; a lexical scanner missed
   `Time Axiom …`, a no-space `#[global]Axiom`, module ALIASES). Text always has another escape. But checking
   each Fido constant's OWN body (Undef) is ALSO insufficient: a retained internal theorem can carry an
   opaque Qed body depending on an EXTERNAL axiom (functional extensionality) and escape unless it happens to
   be a selected public surface. Zero-axiom enforcement means the assumption CLOSURE over EVERY certified
   declaration CLASS — not only constants: seed the closure from every Fido constant AND every mutual
   INDUCTIVE (via `IndRef`) AND every surviving named assumption. An assumption attached DIRECTLY to a
   certified inductive — assumed positivity, disabled guardedness, type-in-type, UIP — is a `Printer.Axiom`
   variant on that `IndRef` that a constant-only audit MISSES when no retained constant references it. The
   sound gate unions those closures (descending opaque Qed bodies) and rejects every `Printer.Axiom` category
   AND `Printer.Variable` — catching a TRANSITIVE external axiom, an unused Fido axiom, AND an unreferenced
   assumption-bearing inductive, immune to lexical tricks. `Print Assumptions` on the public surfaces stays
   the complementary per-surface check; a coverage gate ties the audited module set to dune's `(modules …)`;
   the whole gate runs in `make prove`. And do NOT keep tracked axiom-bearing fixtures "to test the gate" —
   generate them transiently in the pinned environment.

8. **No raw/string-rescue escape hatch — the single most expensive mistake this project has paid for.** A
   structured-or-fail AST must never gain a raw/opaque/text fallback constructor. Unrepresentable ⇒ absent
   from the datatype, or rejected by the relation. (Its cousins: a copied compiled AST / second tree, and
   package/import metadata baked into raw file values.)

9. **Closed world or nothing.** No import syntax is representable today. When imports arrive, every import must
   resolve to an owned package derived from the SAME `GoProgram`, or the whole program is rejected — no
   stdlib / module-cache / network / vendor / workspace / ambient-filesystem escape unless a later reviewed
   foundation completely models that source. A half-modelled external escape is a fail-open foundation.

10. **Integration is the last-mile alarm, and differential experiments discover semantics but do not replace
    proofs.** The pinned-Go `go build ./...` over the WHOLE tree (never a hard-coded file copy) demonstrates
    wiring; a build failure after emission is always a Fido correctness failure, never a known issue. Real-Go
    experiments falsify model/real discrepancies; they are specification discovery, not kernel theorems. ⚠
    The formal compiler contract is `go build ./...` ACCEPTANCE, not `go vet` — a nonblocking diagnostic
    (vet's policy checks, which can false-positive) must stay DIAGNOSTIC-only, never a silent extra
    acceptance criterion the model does not claim.

11. **Foundations before floors — the meta-lesson under all the others.** Do not build features or proof
    families above an unsettled root; when many leaf proofs/guards compensate for one missing abstraction, the
    root is missing — replace it and delete the leaves. Trusted is not proven; stable output is not
    correctness; a printer's own inverse is not a Go-semantics theorem. Cut representable scope before
    weakening any proof.

12. **Generated Go can be TRACKED safely — as a derived artifact regenerated and compared, never as source.**
    The canonical generated module (root `go.mod` + recursive `.go`) is committed so the example builds/runs
    without Rocq/Docker, BUT the `.v`/proof sources stay authoritative: one pristine content-addressed Buildx
    `generated-module` layer is the output authority (built from generation inputs, never from the committed
    bytes, never a mutable cache mount), and the pre-commit hook exports the Git INDEX and verifies the STAGED
    tree byte-exact against it (never the unstaged working tree, never auto-staging). ⚠ A staged-tree verifier
    is only STAGED-AUTHORITATIVE when the gate IMPLEMENTATIONS themselves come from the staged export — running
    the working-tree copy of a gate/script against staged inputs lets a staged bad gate hide behind a safe
    working-tree one. ⚠ Pre-commit is a PROTOTYPE boundary — `--no-verify` bypasses it; the mandatory
    server-side PR CI comes later, and saying so is part of the honest guarantee. ⚠ Do NOT keep both a
    no-tracked-Go seal and the tracked-output model.

13. **A raw literal is an UNTYPED constant; a type system is EVIDENCE over the one AST, never a `TypedIR`.**
    The tempting shortcut is to bake a type into the literal (`EInt : … TInt`) or to build a parallel typed
    tree the "checked" program flows through. Both are wrong. Go's own model: a literal denotes an exact
    UNTYPED constant (arbitrary precision, no width), and only a USE CONTEXT chooses a default type and checks
    representability — so `const_value` stays exact (no range check), and defaulting/`ConstRepresentable` live
    in the resolution judgment. `GoTypes` is one authority whose `ResolveExpr`/`ProgramTyped` are relations
    over the SAME raw `GoAST`; there is NO typed AST, NO copied "resolved expression," NO second numeric-width
    or type authority, and NO placeholder/`unknown`/`opaque`/`raw`/`TString` type admitted ahead of the syntax
    that needs it. The one runtime type universe is the same `GoType` (`value_type`), and evaluation is that
    one constant interpretation mapped to a value — never a second evaluator. (Git history holds a deleted
    `CoreType.v` and much else: mine it for ideas, but a type constructor re-enters ONLY with the syntax and
    complete semantic obligations that need it — history is a quarry, not a branch to resurrect wholesale.)
