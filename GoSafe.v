(** ============================================================================
    GoSafe — the universal SAFETY floor over a compiled [GoAST], and [SafeProgram], the
    only program value emission accepts.

    [SafeProgram] does NOT duplicate the tree: it is a [GoFile] plus its proofs.  Emission
    is gated on it.

    EXACT safety for THIS fragment: the admitted language is straight-line [println] of
    representable primitive literals.  It has NO panic source (no division, indexing,
    nil deref, type assertion, channel, ...) and NO nontermination source (no loops,
    recursion, goroutines) — every constructor present in GoAST is total and panic-free by
    construction.  So the exact behavioral obligation for this fragment IS its
    compile-validity: [BehaviorSafe p := GoCompile p].  This is not a rhetorical umbrella —
    it is the complete safety statement for a fragment with no unsafe constructs, and it
    gains real content (a denotational/operational model, panic/termination obligations)
    the moment an unsafe-capable constructor enters GoAST, at which point it stops being
    definitionally [GoCompile].

    Extensibility: users/LLMs layer arbitrary stronger predicates over the SAME [GoFile]
    ([Definition MyInvariant (p:GoFile) := ...]) and package refinements that project back
    to [SafeProgram] for emission — without forking GoCompile, GoSafe, or GoRender.
    ============================================================================ *)
From Stdlib Require Import String.
From Fido Require Import GoAST GoCompile.

Definition BehaviorSafe (p : GoFile) : Prop := GoCompile p.

Record SafeProgram : Type := mkSafe {
  sp_file : GoFile;
  sp_safe : BehaviorSafe sp_file
}.

(** The compiled program's static validity (available to the renderer/emitter). *)
Lemma sp_compiles : forall sp, GoCompile (sp_file sp).
Proof. intros [p Hp]. exact Hp. Qed.

(** For this fragment, a compile proof is exactly a safety proof, so it builds a
    [SafeProgram] (this constructor is where the fragment's safety obligation is
    discharged; it becomes non-trivial as unsafe constructs are added). *)
Definition safe_of_compile (p : GoFile) (H : GoCompile p) : SafeProgram := mkSafe p H.
