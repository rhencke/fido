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
   `(path, bytes)` transport with EXACT constructors (fail loud otherwise), then call the filesystem-only
   sink. It inspects no program/AST/behaviour/semantics. If that boundary cannot be met, delete the e2e — a
   false transport foundation is worse than no integration. (And emission is an EXPLICIT command, not a
   cached `.vo` side effect a warm cache would silently skip, nor a per-witness extracted executable.)

5. **Provenance is gated at the LIVE boundary, not by the type alone.** A `DirectoryImage` carries a proof
   ([di_prov]) it came from rendering a `SafeProgram`, and the map stays reducible (opaque Rocq modules
   would abstract it but break the reduction the transport command needs). But a proof can be POSTULATED —
   an `Axiom`/`Admitted`/section `Variable` gives a well-typed but uncertified image — so the type is not
   the gate. The gate is the emit command's assumption-closure check (it rejects any image whose proof
   depends on an assumption, descending Qed bodies), so a forged image cannot cross into filesystem effects.

6. **A directory sink SYNCHRONIZES a dirty tree; transient stages need durable root-owned RECORDS, and a
   review must not silently drop an agreed capability.** ⚠ A reviewer can identify a real defect (a
   forgeable staging protocol) WITHOUT owning the replacement architecture — and a central
   `<root>/.fido/staging/` "fix" silently DROPPED the agreed capability that generated files may live under
   nested mount points inside the target root (a same-parent rename is atomic; a central cross-device rename
   is not). Never trade a required capability for a simpler review; when a fix needs an architecture choice,
   escalate it, don't quietly redesign. The correct shape: one root-owned control namespace
   (`<root>/.fido/`: exact marker + lock + a `stage-records/` namespace holding RECORDS ONLY) plus RANDOM
   per-destination-parent local stage dirs (`<parent>/.fido-stage-<nonce>`, an OS `/dev/urandom` nonce —
   never OCaml `Random`). ⚠ Transient-stage ownership is a durable ROOT-OWNED RECORD, never a name, an inner
   marker, or the public installed-file header (none can tell our crashed stage from a foreign lookalike):
   the record is created atomically (`O_CREAT|O_EXCL`) and fully written BEFORE its stage dir, and removed
   only AFTER the stage dir is gone; recovery is RECORD-DRIVEN (never a name scan), validates every field,
   and fail-CLOSED refuses a malformed/escaping/mismatched/symlinked record (a recordless lookalike is
   preserved). ⚠ STAGE THE COMPLETE IMAGE before any install — else an ordinary staging failure (disk,
   permissions) leaves a MIXED generation. ⚠ Handled-failure cleanup (immediate; this run's
   stages/records/empty parents; error-aggregating) is DIFFERENT from crash recovery (record-driven, next
   run) — a handled failure must not leave residue "for the next run". ⚠ Filesystem discovery must
   distinguish MISSING (a confirmed `ENOENT`) from an operational error (EACCES/EIO/ELOOP/…) — never turn a
   readdir/lstat failure into "empty" or "no header"; that is fail-OPEN. ⚠ Validate the ROOT chain (a prefix
   symlink redirects every effect), reserve `.fido/`, and reject a cross-device rename fail-loud (no copy
   fallback). ⚠ Dirty FOREIGN Go contradicts a closed-world compile guarantee: a foreign `.go` anywhere, or
   a foreign/nested `go.mod`, must REJECT the whole emission (fail-closed scan) until foreign source is
   isolated or modeled — NOT preserved-and-merged into a tree we then claim compiles. Inject faults (nonce
   collision, real crash via `Unix._exit`, unlink failure) through operation PARAMETERS, never an ambient env
   branch or a real `chmod` in the production sink. Honest guarantee: NOT transactional, Linux/amd64 scope;
   normal completion releases the lock; a crash or lock-release failure leaves the lock and the next run
   refuses until it is deliberately removed.

7. **Source-text scanning is not a sound zero-axiom gate — audit the compiled environment's CLOSURE.** Every
   text scanner leaked (a comment stripper missed an `Axiom` behind a `"(*"` string; a lexical scanner missed
   `Time Axiom …`, a no-space `#[global]Axiom`, module ALIASES). Text always has another escape. But checking
   each Fido constant's OWN body (Undef) is ALSO insufficient: a retained internal theorem can carry an
   opaque Qed body depending on an EXTERNAL axiom (functional extensionality) and escape unless it happens to
   be a selected public surface. Zero-axiom enforcement means the assumption CLOSURE over EVERY certified
   constant: the sound gate computes the union of every Fido constant's assumption closure (descending opaque
   Qed bodies) and rejects any axiom/parameter/variable — catching a TRANSITIVE external axiom AND unused
   Fido axioms, immune to lexical tricks. `Print Assumptions` on the public surfaces stays the complementary
   per-surface check; a coverage gate ties the audited module set to dune's `(modules …)`. And do NOT keep
   tracked axiom-bearing fixtures "to test the gate" — generate them transiently in the pinned environment.

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
