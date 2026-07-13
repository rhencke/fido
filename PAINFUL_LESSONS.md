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

6. **A directory sink SYNCHRONIZES a dirty tree; put TRANSIENT ownership in a structured namespace, distinct
   from installed-file ownership.** A filesystem lock only coordinates cooperating emitters — it is not
   ownership. ⚠ Every attempt to mark a scattered per-file staging object failed: an inner marker is deleted
   before its directory (a failed `rmdir` leaves an unrecognizable husk); a control-dir record is forgeable
   (a symlink record followed on read, a truncating non-exclusive create, a stage that outlives a crash
   before its record); and reusing the INSTALLED-file header for a temp is BOTH non-atomic (the header is
   written after the file appears, so a crash orphans an empty temp) and forgeable (a public header cannot
   tell our crashed temp from a foreign lookalike). The fix is a RESERVED, mechanically-quarantined
   NAMESPACE: reserve `<root>/.fido/` (reject any desired path inside it BEFORE any effect — the sink is
   generic over raw strings, so it cannot trust the caller) and stage inside `.fido/staging/`. Location is a
   NAMESPACE POLICY, not provenance: it works only because `.fido/` is reserved AND recovery accepts ONLY
   the exact flat form the builder emits. ⚠ "everything under staging is ours" is NOT a license to
   recursively delete: `stage_temp` makes only flat regular `O_EXCL` temps whose names are `string_of_int`
   of a nonnegative index, so recovery must REFUSE (fail-loud, never traverse or delete) any directory /
   symlink / special file / non-canonical name — otherwise a nested tree or a mount under staging gets
   recursively removed. "Exact form" must be EXACT and SEALED: recovery checked-PARSES the name and
   RESERIALIZES it for equality (a digit-shaped superset admits an oversized decimal the generator overflows
   on), the constructor cannot serialize an invalid index, and the successor FAILS at max_int rather than
   wrapping negative — so the counter can never hold an out-of-range state (validity is structural, not a
   caller side condition). ⚠ Also validate the ROOT itself: `lstat` spares only
   the final component, so a symlink in ANY prefix of `root` is followed by ordinary resolution and
   redirects every effect into the referent — reject a non-real-directory in the whole ancestor chain before
   any effect. Create each temp `O_CREAT|O_EXCL` then atomically rename (reject a cross-filesystem target first). Recovery
   inspects that ONE directory, recover-all-or-REJECT and fail-CLOSED (any readdir/lstat/removal error but a
   confirmed `ENOENT` aborts before any effect); it NEVER scans the tree, so a header-forging foreign file is
   untouched. Keep installed-`.go` ownership (header first line, lstat S_REG) SEPARATE. Inject cleanup/
   recovery failure — and a REAL crash (`Unix._exit`, no finalizer, lock stays held) — via `unlink`/
   `after_stage` PARAMETERS through the real algorithm, never an ambient env branch or a real `chmod` in the
   production sink (a caught exception is not a crash; a `chmod` makes destructive behaviour reachable and
   mutates foreign metadata). State the guarantee honestly: NOT transactional; normal completion (success or a handled
   failure) releases the lock so an immediate rerun proceeds, but a crash — or a lock-release failure —
   leaves the lock and the next run refuses until it is deliberately removed.

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
