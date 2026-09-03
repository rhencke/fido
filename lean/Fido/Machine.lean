-- Port of Machine.v (lean/README.md).
import Fido.Prelude

/-! divergences:
  * `CoInductive InfiniteRun` is the greatest fixed point with an explicit invariant (README — Lean 4 has no
    coinductives): `InfiniteRun m s` is `∃ R, R s ∧ ∀ s, R s → ∃ l s', m.step s l s' ∧ R s'`.  Rocq's
    constructor `InfiniteStep` becomes the theorem `InfiniteRun.InfiniteStep` (the introduction rule, proved
    by enlarging the invariant by one state), and Rocq's `destruct` of an `InfiniteRun` becomes the theorem
    `InfiniteRun.inv` (the unfolding); `infinite_run_from_absorbing_final` is proved against the encoding.
  * `Enabled`, a `sigT` whose innermost family is the `Prop` `step m s l s'` (Rocq lifts it by cumulativity),
    is the `PSigma` chain `(l : m.Label) ×' (s' : m.State) ×' m.step s l s'` — Lean's `Sigma` admits no
    `Prop` component; likewise `EnabledDecision`'s `+` over a `Type` and a `Prop` is `⊕'` (`PSum`).
  * `Record T`, whose fields are `Type`s, lives in `Type 1` (Rocq's `T : Type` is the same universe bump,
    written implicitly).  Its constructor keeps the name `Make`.
  * `Trace` is an `abbrev` (reducible), so the list notations and `++` instance see through it the way Rocq's
    transparent `Definition` does.
-/

namespace Fido.Machine

/-- The one labelled-transition base every later runtime milestone shares; it fixes no Go feature. -/
structure T where Make ::
  State  : Type
  Start  : Type
  Label  : Type
  Result : Type

  initial : Start → State
  step    : State → Label → State → Prop
  final   : State → Result → Prop

abbrev Trace (m : T) : Type := List m.Label

/-- A finite run is built only from real steps, so its trace is exactly the labels it consumed. -/
inductive FiniteRun (m : T) : m.State → Trace m → m.State → Prop
  | FiniteRefl :
      ∀ s,
        FiniteRun m s [] s
  | FiniteStep :
      ∀ s l s' trace s'',
        m.step s l s' →
        FiniteRun m s' trace s'' →
        FiniteRun m s (l :: trace) s''

/-- An infinite run observes one real step at a time and never terminates: the greatest fixed point of
    Rocq's `InfiniteStep`, as a state predicate closed under taking one real step. -/
def InfiniteRun (m : T) (s : m.State) : Prop :=
  ∃ R : m.State → Prop, R s ∧ ∀ s, R s → ∃ l s', m.step s l s' ∧ R s'

/-- Rocq's constructor `InfiniteStep`, derived for the encoding. -/
theorem InfiniteRun.InfiniteStep :
  ∀ (m : T) s l s',
    m.step s l s' →
    InfiniteRun m s' →
    InfiniteRun m s := by
  intro m s l s' Hstep ⟨R, HRs', Hclosed⟩
  refine ⟨fun t => t = s ∨ R t, Or.inl rfl, ?_⟩
  intro t Ht
  cases Ht with
  | inl Heq => exact ⟨l, s', Heq ▸ Hstep, Or.inr HRs'⟩
  | inr HRt =>
    obtain ⟨l', t', Hst, HRt'⟩ := Hclosed t HRt
    exact ⟨l', t', Hst, Or.inr HRt'⟩

/-- Rocq's `destruct` of an `InfiniteRun`: one real step, then an infinite run again. -/
theorem InfiniteRun.inv :
  ∀ (m : T) s,
    InfiniteRun m s →
    ∃ l s', m.step s l s' ∧ InfiniteRun m s' := by
  intro m s ⟨R, HRs, Hclosed⟩
  obtain ⟨l, s', Hst, HRs'⟩ := Hclosed s HRs
  exact ⟨l, s', Hst, R, HRs', Hclosed⟩

def Reachable (m : T) (s : m.State) : Prop :=
  ∃ start trace,
    FiniteRun m (m.initial start) trace s

/-- Enabledness carries the witnessing label and successor, so a decision procedure can return them. -/
def Enabled (m : T) (s : m.State) : Type :=
  (l : m.Label) ×' (s' : m.State) ×' m.step s l s'

def Disabled (m : T) (s : m.State) : Prop :=
  ∀ l s', ¬ m.step s l s'

/-- The one decision shape later machines must prove from the same relational step. -/
def EnabledDecision (m : T) : Type :=
  ∀ s,
    Reachable m s →
    Enabled m s ⊕' Disabled m s

def FinalAbsorbing (m : T) : Prop :=
  ∀ s r,
    m.final s r →
    Disabled m s

def Stuck (m : T) (s : m.State) : Prop :=
  Disabled m s ∧ ∀ r, ¬ m.final s r

theorem finite_run_app :
  ∀ m s trace1 s' trace2 s'',
    FiniteRun m s trace1 s' →
    FiniteRun m s' trace2 s'' →
    FiniteRun m s (trace1 ++ trace2) s'' := by
  intro m s trace1 s' trace2 s'' Hrun1
  induction Hrun1 with
  | FiniteRefl s0 =>
    intro Hrun2
    exact Hrun2
  | FiniteStep s0 l s1 tr s2 Hstep Hrun IH =>
    intro Hrun2
    exact FiniteRun.FiniteStep s0 l s1 (tr ++ trace2) s'' Hstep (IH Hrun2)

theorem initial_reachable :
  ∀ m start,
    Reachable m (m.initial start) := by
  intro m start
  exact ⟨start, [], FiniteRun.FiniteRefl _⟩

theorem reachable_step :
  ∀ m s l s',
    Reachable m s →
    m.step s l s' →
    Reachable m s' := by
  intro m s l s' ⟨start, trace, Hrun⟩ Hstep
  refine ⟨start, trace ++ [l], finite_run_app m _ trace s [l] s' Hrun ?_⟩
  exact FiniteRun.FiniteStep s l s' [] s' Hstep (FiniteRun.FiniteRefl s')

theorem final_absorbing_no_step :
  ∀ m s r l s',
    FinalAbsorbing m →
    m.final s r →
    ¬ m.step s l s' := by
  intro m s r l s' Habsorbing Hfinal
  exact Habsorbing s r Hfinal l s'

theorem finite_run_from_absorbing_final :
  ∀ m s r trace s',
    FinalAbsorbing m →
    m.final s r →
    FiniteRun m s trace s' →
    trace = [] ∧ s' = s := by
  intro m s r trace s' Habsorbing Hfinal Hrun
  cases Hrun with
  | FiniteRefl _ => exact ⟨rfl, rfl⟩
  | FiniteStep _ l s1 _ _ Hstep _ => exact absurd Hstep (Habsorbing s r Hfinal l s1)

theorem infinite_run_from_absorbing_final :
  ∀ m s r,
    FinalAbsorbing m →
    m.final s r →
    ¬ InfiniteRun m s := by
  intro m s r Habsorbing Hfinal Hrun
  obtain ⟨l, s1, Hstep, _⟩ := InfiniteRun.inv m s Hrun
  exact Habsorbing s r Hfinal l s1 Hstep

end Fido.Machine
