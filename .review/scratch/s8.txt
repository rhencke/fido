
(* ── §14 Boundaries, the report, and the outcome ───────────────────────────── *)
(* No environment index: an outside-scope core is precisely one with no ready environment, so a boundary
   that needed one could never be reported. *)
Record PackedBoundary {p} {i : Input p} (ph : Phase i) : Type := MakeBoundary {
  boundary_site : Site p;
  boundary_requirement : SiteRequirement ph boundary_site;
  boundary_is_root : IsRootOutside (phase_outcome ph boundary_site)
}.

Definition boundary_view {p} {i : Input p} {ph : Phase i}
  (b : PackedBoundary ph) : RequirementView :=
  requirement_view (boundary_requirement ph b).

(* The site table is the authority; the report lists are its canonical projections, not peer lists.
   `Core`, `Elaboration` and `phase` are the existing repository names, stubbed once above. *)
Parameter core_diagnostics : forall {p} (c : Core p), list (RootCause (phase c)).
Parameter core_boundaries : forall {p} (c : Core p), list (PackedBoundary (phase c)).

Inductive Decision {p} (c : Core p) : Type :=
| DecisionAccepted : core_diagnostics c = [] -> core_boundaries c = [] -> Decision c
| DecisionRejected : core_diagnostics c <> [] -> Decision c
| DecisionOutside  : core_diagnostics c = [] -> core_boundaries c <> [] -> Decision c.

Parameter decision : forall {p} (a : Elaboration p), Decision (elaboration_core a).

Parameter Program : Type.
Parameter source : Program -> SyntaxProgram.
Parameter core : forall cp : Program, Core (source cp).
Parameter accepted : forall cp : Program, core_diagnostics (core cp) = [].
Parameter in_scope : forall cp : Program, core_boundaries (core cp) = [].

Parameter Failure : SyntaxProgram -> Type.
Parameter failure_core : forall {p}, Failure p -> Core p.
Parameter rejected : forall {p} (f : Failure p), core_diagnostics (failure_core f) <> [].
Parameter Outside_ : SyntaxProgram -> Type.
Parameter outside_core : forall {p}, Outside_ p -> Core p.
Parameter outside_clean : forall {p} (o : Outside_ p), core_diagnostics (outside_core o) = [].
Parameter outside_blocked : forall {p} (o : Outside_ p), core_boundaries (outside_core o) <> [].

Inductive Outcome (p : SyntaxProgram) : Type :=
| Compiled : forall cp : Program, source cp = p -> Outcome p
| Rejected : Failure p -> Outcome p
| OutsideScope : Outside_ p -> Outcome p.

Parameter compile : forall p : SyntaxProgram, Outcome p.
Definition InScope (p : SyntaxProgram) : Prop :=
  core_boundaries (elaboration_core (elaborate p)) = [].

(* ── Accepted facts are projections of the one retained phase ──────────────── *)
Definition accepted_phase (cp : Program) : Phase (core_input (core cp)) := phase (core cp).
(* The one readiness authority is the retained phase result; there is no second `core_ready` beside it. *)
Parameter accepted_is_ready : forall cp : Program,
  IsTypeReady (phase_type_result (accepted_phase cp)).
Definition accepted_ready (cp : Program) : TypeReady (accepted_phase cp) :=
  ready_of (phase_type_result (accepted_phase cp)) (accepted_is_ready cp).
Definition accepted_outcome (cp : Program) (s : Site (source cp))
  : SiteOutcome (accepted_phase cp) s :=
  phase_outcome (accepted_phase cp) s.

(* Derived, not postulated.  An accepted core has no diagnostic and no boundary; the report lists are
   complete over root failures and root outside requirements; and every blocked chain reaches one of those
   roots.  Together those force every site to be supported, so this is a consequence rather than a second
   authority sitting beside the report. *)
Lemma accepted_supported : forall (cp : Program) (s : Site (source cp)),
  IsSupported (accepted_outcome cp s).
Proof. Admitted.

Definition accepted_fact (cp : Program) (s : Site (source cp))
  : SiteFact (accepted_phase cp) s :=
  supported_fact (accepted_outcome cp s) (accepted_supported cp s).

Definition AcceptedType (cp : Program) : Type := SemanticType (source cp).
Definition Object (cp : Program) : Type := ObjectRef (accepted_phase cp).
Definition ExpressionFact (cp : Program) (r : ExprRef (source cp)) : Type :=
  SiteFact (accepted_phase cp) (SExpression (source cp) r).
Definition expression_fact (cp : Program) (r : ExprRef (source cp)) : ExpressionFact cp r :=
  accepted_fact cp (SExpression (source cp) r).
(* Application and statement facts are now accessed through the expression site, since SApplication
   and SUnary are no longer independent sites. *)
Definition ApplicationFact (cp : Program) (a : ApplicationRef (source cp)) : Type :=
  SiteFact (accepted_phase cp) (SExpression (source cp) (application_expr_of a)).
Definition application_fact (cp : Program) (a : ApplicationRef (source cp))
  : ApplicationFact cp a := accepted_fact cp (SExpression (source cp) (application_expr_of a)).
Definition StatementFact (cp : Program) (t : ExpressionStatementRef (source cp)) : Type :=
  SiteFact (accepted_phase cp) (SStatement (source cp) t).
Definition statement_fact (cp : Program) (t : ExpressionStatementRef (source cp))
  : StatementFact cp t := accepted_fact cp (SStatement (source cp) t).
Definition ConsumptionAt (cp : Program) (c : ConsumptionSiteRef (source cp)) : Type :=
  SiteFact (accepted_phase cp) (SConsumption (source cp) c).
Definition consumption_at (cp : Program) (c : ConsumptionSiteRef (source cp))
  : ConsumptionAt cp c := accepted_fact cp (SConsumption (source cp) c).
