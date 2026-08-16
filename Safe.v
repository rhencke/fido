From Fido Require Import Syntax Compilable.

(* Trivial today, because the fragment has no unsafe operation; this is the permanent extension point.
   C4 does not strengthen it into runtime safety. *)
Definition Property {p} {c : Compilable.Compilation p} (_ : Compilable.Prog.Program c) : Prop := True.

(* A certificate is a transparent record: it retains the exact source, the one compilation built over it,
   the exact compiled capability paired with that compilation, and the proof of its safety property.
   Every field is a projection, so a certified program's source and phases compute.  Primitive projections
   keep [safe_src] a true field read: rendering a certified program's source must never co-normalize the
   retained [safe_comp]/[safe_prog] phases, which reduce to a large normal form. *)
#[projections(primitive)]
Record Program : Type := certify {
  safe_src  : Syntax.Program ;
  safe_comp : Compilable.Compilation safe_src ;
  safe_prog : Compilable.Prog.Program safe_comp ;
  safe_ok   : Property safe_prog
}.

(* The certified source: [Emit] reaches it via this projection, then [Render] traverses that raw [Syntax]. *)
Definition source (sp : Program) : Syntax.Program := safe_src sp.

(* Retention over any certificate, not only a freshly built one: the stored compilation and capability are
   exactly the ones supplied, recovered by projection with no recomputation. *)
Theorem safe_retains_program :
  forall src comp prog ok,
    safe_comp (certify src comp prog ok) = comp /\ safe_prog (certify src comp prog ok) = prog.
Proof. intros; split; reflexivity. Qed.
