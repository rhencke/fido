
(* ── §9 Requirements are exact missing facts ───────────────────────────────── *)
(* Each constructor retains the exact partial facts already established at that site, so a requirement
   cannot pair an arbitrary use with an arbitrary object, and satisfaction never asks whether the outcome
   is already supported. *)
(* No environment index: a requirement is reportable for an arbitrary core.  Each constructor carries the
   exact readiness the partial facts it retains were established at. *)
Inductive SiteRequirement {p} {i : Input p} (ph : Phase i) : Site p -> Type :=
(* The requirement retains the exact use, its exact binding, and thereby the exact bound object's total
   descriptor.  It does not retain a successful meaning: that is precisely what it reports as missing. *)
| NeedTypeMeaning : forall (u : NameUseRef p) (bf : BindingFact ph u),
    SiteRequirement ph (SBinding p u)
| NeedValueMeaning : forall (u : NameUseRef p) (bf : BindingFact ph u),
    SiteRequirement ph (SBinding p u)
(* §15 A missing application rule retains the exact head fact, the exact target derived from it, the exact
   ordered argument facts and the exact derived profile. *)
| NeedApplication : forall  (a : ApplicationRef p)
    (hf : ResultFormAt ph) (tgt : ApplicationTarget ph)
    (args : list (ResultAtomAt ph)),
    ExprFact ph (application_head a) hf ->
    ArgFacts ph (application_argument_uses a) args ->
    ErasedProfile -> SiteRequirement ph (SExpression p (application_expr_of a))
| NeedStatement : forall  (s : ExpressionStatementRef p) (a : ApplicationRef p)
    (hf : ResultFormAt ph),
    statement_application s = Some a ->
    ExprFact ph (application_head a) hf -> SiteRequirement ph (SStatement p s)
| NeedUnary : forall  (n : UnaryRef p) (opa : ResultAtomAt ph),
    ResultUseFactAt ph (DirectUse p (unary_operand_use n)) opa ->
    SiteRequirement ph (SExpression p (unary_expr n)).

(* Satisfaction is a question about the fact families, not about the site table. *)
(* Every case is a positive semantic relation over the exact facts the requirement retains.  None asks
   whether the successful site fact happens to be inhabited: that would decide whether a requirement is met
   by checking for the very thing the requirement reports as missing. *)
Definition RequirementSatisfied {p} {i : Input p} {ph : Phase i} {s}
  (r : SiteRequirement ph s) : Prop :=
  match r with
  | NeedTypeMeaning _ u bf =>
      match type_role_decision ph (bound_object ph u bf) with
      | TypeRoleAdmitted _ _ => True | _ => False end
  | NeedValueMeaning _ u bf =>
      match value_role_decision ph (bound_object ph u bf) with
      | ValueRoleConstant _ _ | ValueRoleVariable _ _ | ValueRoleContextual _ _ => True
      | _ => False end
  | NeedApplication _ _ _ tgt args _ _ _ => ApplicationRuleCovers tgt args
  | NeedStatement _ _ a _ _ _ => StatementRuleCovers ph a
  | NeedUnary _ _ opa _ => UnaryRuleCovers opa
  end.

Parameter requirement_dec : forall {p} {i : Input p} {ph : Phase i} {s}
  (r : SiteRequirement ph s),
  { RequirementSatisfied r } + { ~ RequirementSatisfied r }.

(* The exact bound object a name requirement is about is read off its binding fact, never supplied. *)
Definition requirement_object {p} {i : Input p} {ph : Phase i} {s}
  (r : SiteRequirement ph s) : option (ObjectRef ph) :=
  match r with
  | NeedTypeMeaning _ u bf => Some (bound_object ph u bf)
  | NeedValueMeaning _ u bf => Some (bound_object ph u bf)
  | _ => None
  end.

Parameter requirement_view : forall {p} {i : Input p} {ph : Phase i} {s},
  SiteRequirement ph s -> RequirementView.
