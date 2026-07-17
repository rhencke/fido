# Fido — painful lessons (permanent)

The small set of EXPENSIVE, COUNTER-INTUITIVE traps this project actually fell into — where the wrong path
looked reasonable and we only learned by paying for it. Not a catalogue of the design (that is
`ARCHITECTURE.md`/`CLAUDE.md`) and not a status diary (`PROGRESS.md`). If a proposal resembles one of these,
stop. When an entry stops being a live temptation, delete it.

1. **A subset filter is not exact compiler admissibility.** If the AST can represent a program the real
   toolchain ACCEPTS, a checker that rejects it is a supported-scope decision wearing a compiler-authority
   name. Model every represented form's real acceptance, or make unsupported forms UNREPRESENTABLE — never
   rejected by a guard. A representable program `go build ./...` accepts but `GoCompile` rejects is a MODEL
   BUG, not "unsupported syntax." (Hence `GoCompile` is proved sound + complete against a declarative
   judgment and attacked by differential experiments; a green boolean is not the authority.)

2. **The Go compilation unit is the WHOLE module tree.** Go groups files by directory into packages;
   one-main-per-package is a whole-program property; paths, module identity, and the module file are semantic
   inputs (a raw `string` key is not a file path — discovery depends on the extension, `_test`/GOOS suffixes,
   hidden dirs, directory identity). So `GoProgram` = an intrinsic `ModuleSpec` + a POSSIBLY-EMPTY finite map
   keyed by intrinsic `FilePath` (the empty map is a valid module-only program); `GoCompile` consumes it all
   at once, all-or-nothing; package grouping / name / entry status are COMPILATION RESULTS, never collapsed
   into a raw node. The `go.mod` is part of the program, RENDERED in Rocq from the `ModuleSpec`, never a
   `FilePath` key.

3. **Gate the invariant you actually advertise.** A functional first-match lookup theorem holds even over a
   duplicate-keyed list, so it is NOT evidence of key uniqueness. (Fido once carried key uniqueness as a
   `NoDup` field beside an exposed association list; that was the wrong foundation — see lesson 14 — and is now
   a STANDARD finite map whose keys are unique by construction.) "Axiom-free" is necessary, never sufficient:
   a kernel-checked proof can still prove a weak/irrelevant/self-referential claim. Always check the STATEMENT.

4. **Handwritten OCaml is TRANSPORT, never language semantics.** The permitted boundary typechecks the image
   type, rejects a non-empty assumption closure (a kernel provenance query — NOT decoding proofs/programs),
   decodes ONLY the final `(go.mod bytes, (path, bytes) list)` transport with exact constructors (fail loud),
   then calls the filesystem-only sink. It inspects no program/AST/behaviour/semantics. If that boundary
   cannot be met, delete the e2e — a false transport foundation is worse than none. (Emission is an EXPLICIT
   command, not a cached `.vo` side effect a warm cache would silently skip.)

5. **Proof-carrying provenance still requires a LIVE assumption-closure gate.** A `DirectoryImage` carries a
   proof it came from rendering a `SafeProgram`, but a proof can be POSTULATED (`Axiom`/`Admitted`/section
   `Variable` → a well-typed but uncertified image), so the type is not the gate. The gate is the emit
   command's assumption-closure check, which rejects any image whose proof depends on an assumption before any
   filesystem effect.

6. **Review rigor must match the component's DECLARED guarantee and threat model.** The sink's threat model is
   ONE owner + cooperating emitters serialized by one lock + ordinary crashes/disk/permissions — NOT a
   malicious concurrent adversary or arbitrary unmount/remount; a reviewer can name a real defect without
   owning the replacement, and `.review/NEXT_STEPS.md` (not the reviewer's preferred architecture) is binding
   — a defect unfixable within it is an ARCHITECTURAL CONFLICT to escalate, never a quiet redesign. The
   durable sink shape: one lock (`.fido/` marker + `index.lock`); each output staged into its RESERVED sibling
   temp; the COMPLETE image staged before any install; fail-CLOSED ordinary filesystem observation
   (distinguish a confirmed `ENOENT` from an operational error — never turn a `readdir`/`lstat` failure into
   "empty"); a foreign `.go` in the Go-discovered namespace or a foreign/nested `go.mod` REJECTS the whole
   emission; and NO transaction-log / stage-record / OS-nonce / central-staging subsystem. (Deliberate edits
   to the verifier ITSELF are OUT OF SCOPE per `.review/CODEX_REVIEW_POLICY.md` — build no self-test fortress.)

7. **Audit the compiled assumption CLOSURE, not source text.** Every text scanner leaks (an `Axiom` behind a
   string, `Time Axiom`, a no-space `#[global]Axiom`, module aliases). Checking each constant's own body is
   also insufficient: a retained internal lemma can carry an opaque Qed body depending on an EXTERNAL axiom
   (functional extensionality) and escape. Sound enforcement seeds the closure from every Fido constant AND
   every mutual INDUCTIVE (via `IndRef`) AND every surviving named assumption, unions the closures (descending
   opaque Qed bodies), and rejects every `Printer.Axiom` category AND `Printer.Variable`. `Print Assumptions`
   on public surfaces is the complementary per-surface check; a coverage gate ties the audited set to dune's
   `(modules …)`. No tracked axiom-bearing fixtures — generate them transiently.

8. **No raw escape hatch, typed AST, copied program, or parallel semantic authority.** A structured-or-fail
   AST must never gain a raw/opaque/text fallback constructor — the single most expensive mistake this project
   has paid for. Unrepresentable ⇒ absent from the datatype, or rejected by the relation. Its cousins: a
   copied compiled AST / second tree, package/import metadata baked into raw file values, and a second
   numeric-width or type authority beside the one.

9. **Untyped constants, typed constants, and runtime values are DISTINCT.** A raw literal denotes an exact
   UNTYPED constant (arbitrary-precision `Z`, no width) — its exact value is just that `GoConst`
   (`const_info_exact` of `const_info`), no range check, no wrap. A use context or an explicit conversion yields
   a TYPED constant (the intrinsic dependently-typed `TypedConst` — a mismatched/out-of-range one
   UNREPRESENTABLE) that retains its exact value AND its type and does not default again. A runtime value
   carries the same `GoType`. Defaulting/representability
   live in the resolution judgment, never baked into the literal (`EInt : … TInteger IInt` is wrong) and never a
   parallel typed tree.

10. **Integration / differential tests are ALARMS, not proofs.** The pinned-Go `go build ./...` over the whole
    tree demonstrates wiring; a build failure after emission is always a Fido correctness failure, never a
    known issue. Real-Go experiments falsify model/real discrepancies — specification discovery, not kernel
    theorems. The formal contract is `go build ./...` ACCEPTANCE, not `go vet` (a nonblocking diagnostic that
    can false-positive and must stay diagnostic-only).

11. **Foundations before feature breadth.** Do not build features or proof families above an unsettled root;
    when many leaf proofs/guards compensate for one missing abstraction, the root is missing — replace it and
    delete the leaves. Trusted is not proven; stable output is not correctness; a printer's own inverse is not
    a Go-semantics theorem. Cut representable scope before weakening any proof.

12. **Generated Go may be TRACKED only as a derived artifact checked against the certified output.** The
    canonical module (root `go.mod` + recursive `.go`) is committed so the example builds without Rocq/Docker,
    but the `.v` sources stay authoritative: one pristine content-addressed Buildx `generated-module` layer is
    the output authority (built from generation inputs, never the committed bytes, never a mutable cache
    mount), and the pre-commit hook verifies the STAGED tree byte-exact against it using gate implementations
    that ALSO come from the staged export (a working-tree gate run over staged inputs lets a staged bad gate
    hide). Pre-commit is a PROTOTYPE boundary — `--no-verify` bypasses it; the mandatory server-side PR CI
    comes later, and saying so is part of the honest guarantee.

13. **String value is BYTES; source spelling is a separate canonical proved encoding.** A string value is an
    exact byte sequence (`string`/`ascii`), not UTF-8 / code-points / runes. Fido emits ONE canonical source
    spelling per byte sequence; its INDEPENDENT certified decoder assigns exact byte meaning to that spelling
    and MAY ALSO accept semantically equivalent noncanonical spellings. The proved property is the byte round
    trip `decode_string_literal (render_string_literal s) = Some s`; NO source-spelling inverse
    `render (decode source) = source` is claimed, and the decoder is not narrowed to make that prose easier.
    The decoder is a DENOTATION tool, not a general Go parser — real-Go parse acceptance is external adequacy
    (the differential + boundary-byte e2e). No string operations exist yet: bytes in, canonical ASCII literal
    out (bytes ≥ 128 only via `\xhh`).

14. **The collection algebra is part of the model; a list with a uniqueness proof is not a map.** Fido used
    exposed association lists plus `NoDup` as finite maps. That looked small and proof-friendly, but lookup
    and construction were linear/quadratic, physical order leaked into compiler definitions, and every consumer
    needed permutation/congruence proofs to recover the semantics the datatype should have expressed.
    Identity-keyed state uses mature Rocq finite maps (`FMapAVL` behind a `FilePath`/`String` key, `FMapPositive`
    for positive keys); membership-only state uses mature finite sets; duplicate-invalid source bindings use
    maps to occurrence buckets until validation; ordered syntax/execution stays a list; map/set lists are
    DERIVED enumerations only (`elements` of an ordered map is a function of the map's meaning, so extensionally
    equal maps enumerate identically). A thin domain wrapper is welcome. A project-authored general collection
    implementation is not. The standard map's `add` OVERWRITES, so a source builder must DETECT a duplicate key
    before insertion (fail loud) rather than erase the evidence a diagnostic will need — the same discipline in
    OCaml transport (`Map.Make`/`Set.Make`, `GlobRef.Set`), never a raw `List.mem`/`::` identity authority.
