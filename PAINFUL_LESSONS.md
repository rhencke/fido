# Fido — painful lessons (permanent)

Why the rejected architectures must never reappear. Each was actually built, actually cost, and actually
deleted. Git carries the code; this file carries the reasons. Read it before proposing anything it warns
against.

1. **Trusted is not proven.** A component that "worked for years" is still outside the proof. The handwritten
   OCaml backend + extraction plugin should have died the moment a Rocq authority could replace them; keeping
   them made "certified" a lie. All language decisions live in proved Rocq now.

2. **Stable output is not correctness.** Golden/integration output detects *change*; it does not prove the
   original bytes were *right*. Goldens are human-reviewed integration facts, never a correctness authority.

3. **Round-trip is self-consistency, not adequacy.** `AST → print → parse → AST` can faithfully preserve a
   shared misunderstanding, and a grammar defined by the printer's own policy validates itself. That is why
   there is **no lexer, parser, tokenizer, or round-trip** in the certified path: renderer correctness is
   proved structurally over the intrinsically-grammatical AST. (The deleted `GoPrint.CanonExpr` self-mirrored
   the printer and proved no Go-parse adequacy.)

4. **The AST is sufficient.** A Rocq term already supplies the input boundary. A text IR, Lisp/WAT, lexers,
   and parsers add moving parts without strengthening the experiment. The AST *is* the IR.

5. **The printer does not compile.** `GoCompile` settles names, types, constants, declarations, and legality
   into the decorated `CompiledFile`; `GoRender` only serializes it. The renderer never resolves, infers,
   rejects, or repairs.

6. **Shrink syntax before weakening GoCompile.** If exact compiler acceptance is not modelled for a
   constructor, the constructor must not exist. Never a conservative checker with a final-sounding name.
   (The deleted boolean `GoCompile` fail-open-accepted an unresolved named type Go rejects.)

7. **A boolean is not the compile authority.** Compile-admissibility is a declarative relation with an
   executable checker proved sound AND complete against it — never `check p = true`. A green boolean is not
   compiler admissibility.

8. **SafeProgram is a certificate, not another AST**, and "safe" is not a rhetorical umbrella. `BehaviorSafe`
   is a real property (no panic) of an operational semantics, proved — not a synonym for "it compiles". The
   deleted `BehaviorSafe := GoCompile` was circular and had no model.

9. **Extensibility is refinement, not forks.** User/LLM lemmas layer over `GoSafe` on the same
   `CompiledFile`. They never create a competing compiler, semantics, or renderer.

10. **No handwritten semantic OCaml.** Exactly one tiny transparent transport glue is permitted (`Fido Emit`:
    reduce a proved `DirectoryImage`, decode path+bytes, write). It decides nothing. A second glue file, or
    any OCaml that inspects/lowers/validates, is forbidden.

11. **Integration is the last-mile alarm.** The pinned-Go build/run demonstrates wiring. A failure indicates
    a deeper proof/target/transport error or a wrong golden — never a "known issue". **An expected Go compiler
    failure is forbidden**: an invalid candidate dies in Rocq before any file is created.

12. **No transition artifacts.** Nobody depends on the repo. Weak/legacy/demo paths are deleted, not preserved
    for compatibility. There is only the intended architecture and things to delete.

13. **Foundations before floors.** Do not build features or proof families above an unsettled root. When
    twenty leaf proofs/guards cover one missing abstraction, the root is missing — replace it, delete the
    leaves. (~11,500 lines of duplicate `Surface`/`TypedIR`/grammar/token machinery collapsed into five
    modules, and the proofs got *stronger*.)

14. **No raw/string-rescue escape hatch.** A structured-or-fail AST must never gain a raw/opaque/text
    fallback constructor. That "escape hatch" is the single most expensive mistake this project has paid for.
    Unrepresentable ⇒ absent from the datatype, or rejected by the relation.

15. **Axiom-free is not automatically correct.** A kernel-checked proof can still prove a weak, irrelevant, or
    self-referential claim. Zero-axiom is necessary, never sufficient — always ask whether the theorem's
    *statement* is the right one.

16. **Target assumptions have one authority.** Go version, GOOS/GOARCH, int width, and `println` availability
    come from one `TargetConfig`, consumed by derivation — never restated in the elaborator, renderer, or a
    test.

17. **No fuel, ever.** No gas, step budget, max-depth, or bounded runner. Totality comes from decreasing
    structure. A bounded run is not a proof; a timeout is not nontermination.
