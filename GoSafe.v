(** ============================================================================
    GoSafe — an operational semantics over the decorated [CompiledFile], the universal
    safety floor [BehaviorSafe], and [SafeProgram], the only value emission accepts.

    The point of this module (doc §3, PAINFUL_LESSONS #15): safety is a property of the
    program's BEHAVIOUR under a real semantics — NOT a synonym for "it compiles".  The
    earlier [BehaviorSafe := GoCompile] was circular and had no model; this replaces it.

    The semantics.  Evaluating a [CompiledFile] yields a [Behavior]: the ordered trace of
    [println] events (each event is the list of argument VALUES printed) and a terminal
    [Outcome].  [Outcome] genuinely admits [Panicked] — the framework can express a
    panicking run — so [BehaviorSafe c := run outcome is Returned] is a real no-panic
    obligation, not a tautology.  For THIS fragment (straight-line [println] of primitive
    values: no division, indexing, nil deref, assertion, channel, goroutine, loop, or
    recursion) there is no panic or nontermination source, so evaluation is a total
    function and the outcome is always [Returned] — [fragment_never_panics] discharges the
    obligation by that structural fact, not by assumption.  When a panic-capable constructor
    later enters [GoAST], [eval_file] gains a [Panicked] branch and this theorem gains real
    premises; the FLOOR (no-panic) is what stays fixed.

    Note on OUTPUT: the trace records WHICH values each [println] prints, in order.  It does
    NOT claim the exact stdout BYTES — [println]'s formatting (separators, bool spelling) is
    implementation-specific and is pinned-toolchain integration evidence (the e2e), never a
    portable theorem (see [TargetConfig]).

    [SafeProgram] ties the three layers together: a raw [GoFile], its compilation, the proof
    they are related ([sp_compiles]), and the proof the compiled behaviour is safe
    ([sp_safe]).  It duplicates no tree.  Emission is gated on it.  Users/LLMs layer stronger
    predicates over the same [CompiledFile] and project back to [SafeProgram] — without
    forking GoCompile, GoSafe, or GoRender.
    ============================================================================ *)
From Stdlib Require Import String NArith List.
From Fido Require Import GoAST GoCompile.
Import ListNotations.

(** ---- Observable values and terminal outcomes ---- *)

Inductive Outcome : Type := Returned | Panicked.

Inductive PrintedVal : Type :=
| PVBool : bool -> PrintedVal
| PVInt  : N -> PrintedVal
| PVNeg  : N -> PrintedVal
| PVStr  : string -> PrintedVal.

Record Behavior : Type := mkBehavior {
  beh_prints  : list (list PrintedVal);   (* one entry per println call, in program order *)
  beh_outcome : Outcome
}.

(** ---- The denotation ---- *)

Definition pval (c : CompiledExpr) : PrintedVal :=
  match c with
  | CBool b  => PVBool b
  | CInt n _ => PVInt n
  | CNeg n _ => PVNeg n
  | CStr s _ => PVStr s
  end.

Definition eval_stmt (s : CompiledStmt) : list PrintedVal :=
  match s with CPrintln args => map pval args end.

Definition eval_file (c : CompiledFile) : Behavior :=
  mkBehavior (map eval_stmt (cf_body c)) Returned.

(** ---- The universal safety floor: the run does not panic ---- *)

Definition BehaviorSafe (c : CompiledFile) : Prop := beh_outcome (eval_file c) = Returned.

(** Discharged for the whole fragment by construction — no constructor can panic. *)
Theorem fragment_never_panics : forall c, BehaviorSafe c.
Proof. intro c. reflexivity. Qed.

(** ---- The emission certificate ---- *)

Record SafeProgram : Type := mkSafe {
  sp_raw      : GoFile;
  sp_compiled : CompiledFile;
  sp_compiles : CompilesFile sp_raw sp_compiled;   (* it is a genuine compilation of sp_raw *)
  sp_safe     : BehaviorSafe sp_compiled            (* whose behaviour is safe *)
}.

(** The canonical way to build a certificate: a compilation proof suffices (this fragment's
    safety obligation is discharged automatically), so nothing unsafe can be certified —
    [sp_compiles] is a real gate.  As unsafe constructs arrive, a [BehaviorSafe] proof stops
    being free and must be supplied. *)
Definition certify (raw : GoFile) (c : CompiledFile) (H : CompilesFile raw c) : SafeProgram :=
  mkSafe raw c H (fragment_never_panics c).

(** The certified program erases to its raw source (faithfulness of the whole gate). *)
Lemma sp_erases : forall sp, erase_file (sp_compiled sp) = sp_raw sp.
Proof. intros [raw c Hc Hs]. simpl. apply compiled_erases_to_raw; exact Hc. Qed.
