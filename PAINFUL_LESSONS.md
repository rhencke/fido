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

2. **The compile unit is the WHOLE program tree, and paths + package identity are semantic inputs.** Go
   groups files by directory into packages; one-main-per-package is a whole-program property; a raw `string`
   key is not a file path (package discovery depends on the extension, `_test`/GOOS suffixes, hidden dirs,
   directory identity). Single-file compiler semantics with `string` keys cannot model this. So: `GoProgram`
   is a nonempty finite map keyed by an INTRINSIC `FilePath`; `GoCompile` consumes it all at once,
   all-or-nothing; package grouping / package name / entry-point status are COMPILATION RESULTS
   (`CompilationFacts`), never collapsed into a raw node like the deleted `MainFile`.

3. **Gate the invariant you advertise.** A functional first-match lookup theorem (`fm_MapsTo_fun`) holds even
   over a duplicate-keyed list, so it is NOT evidence of key uniqueness — that is `fm_keys_nodup` (the carried
   `NoDup` field) + `dup_key_unrepresentable`. Likewise "axiom-free" is necessary, never sufficient: a
   kernel-checked proof can still prove a weak/irrelevant/self-referential claim. Always check the STATEMENT.

4. **Handwritten OCaml is a TRANSPORT boundary, never a program decoder.** The deleted 82-line backend
   accepted an arbitrary `constr` and decoded it by application ARITY — term inspection masquerading as a
   transport. The permitted boundary decodes ONLY the final `(path, bytes)` transport with EXACT expected
   constructors, fails loud on anything else, and inspects no program/AST/certificate/proof; the sink is
   filesystem-only. If that boundary cannot be met, delete the e2e — a false transport foundation is worse
   than no integration. (And emission is an EXPLICIT command, not a cached `.vo` side effect a warm cache
   would silently skip, nor a per-witness extracted executable.)

5. **The image must be provenance-gated but still reducible.** A `DirectoryImage` carries a proof it came from
   rendering a `SafeProgram`, so there is no arbitrary-map → image escape that would emit uncertified bytes.
   Opaque Rocq modules would give that abstraction but break the reduction the transport command needs — the
   provenance proof is the right gate (abstraction without opacity).

6. **A directory sink SYNCHRONIZES a dirty tree; ownership is positive, marked, and rechecked.** A filesystem
   lock only coordinates cooperating emitters — it is not ownership. A `.go` is Fido-owned iff its first line
   is the exact header; a control/stage directory is owned iff it carries the exact marker; ownership is
   rechecked immediately before every overwrite/delete (lstat, never follow a symlink). Foreign files, dirs,
   symlinks, and unmarked control/stage lookalikes are never touched; stale cleanup is by header +
   desired-key-set, never timestamps or a manifest. State the guarantee honestly: convergent on rerun, NOT a
   transactional whole-directory commit (a crash may leave a mixed generation; the next run converges).

7. **Source-text scanning is not a sound zero-axiom gate — audit the compiled environment instead.** Every
   text scanner leaked: a naive comment stripper missed an `Axiom` behind a `"(*"` string; a smarter lexical
   scanner still missed `Time Axiom …`, a no-space `#[global]Axiom`, and module ALIASES that look like scopes.
   Text always has another escape. The sound gate enumerates the compiled global environment and rejects any
   Fido constant with an axiomatic body (Undef) — catching UNUSED axioms too, immune to lexical tricks.
   `Print Assumptions` on the public surfaces stays the complementary check for EXTERNAL axioms in a closure.

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
    experiments falsify model/real discrepancies; they are specification discovery, not kernel theorems.

11. **Foundations before floors — the meta-lesson under all the others.** Do not build features or proof
    families above an unsettled root; when many leaf proofs/guards compensate for one missing abstraction, the
    root is missing — replace it and delete the leaves. Trusted is not proven; stable output is not
    correctness; a printer's own inverse is not a Go-semantics theorem. Cut representable scope before
    weakening any proof.
