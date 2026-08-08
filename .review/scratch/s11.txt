
(* ── §9 Statement classification is intrinsic ──────────────────────────────── *)
Definition builtin_forbidden_as_statement (n : PredeclaredName) : bool :=
  match n with
  | PAppend | PCap | PComplex | PImag | PLen | PMake | PNew | PReal | PMin | PMax => true
  | _ => false
  end.

Definition builtin_admitted_as_statement (n : PredeclaredName) : bool :=
  match n with
  | PClear | PClose | PCopy | PDelete | PPanic | PPrint | PPrintln | PRecover => true
  | _ => false
  end.

Parameter StatementApplication : forall (cp : Program),
  ExpressionStatementRef (source cp) -> ApplicationRef (source cp) -> Prop.

(* One constructor: only a successful `println` application is a C6 statement call.  A conversion or a
   `complex` application cannot inhabit this type at all. *)
Inductive StatementCall (cp : Program) (s : ExpressionStatementRef (source cp)) : Type :=
| StmtPrintln : forall (a : ApplicationRef (source cp))
    (c : HeadCallable (app_head_fact cp a)),
    StatementApplication cp s a ->
    app_target cp a = CallableTarget (app_head_fact cp a) c ->
    callable_name c = PPrintln -> PrintlnRule cp a -> StatementCall cp s.

Inductive StatementClass (cp : Program) (s : ExpressionStatementRef (source cp)) : Type :=
| StatementEligible : StatementCall cp s -> StatementClass cp s
| StatementDefiniteFailure : StatementReason -> StatementClass cp s
| StatementOutside :
    SiteRequirement (accepted_phase cp) (SStatement (source cp) s) -> StatementClass cp s
| StatementBlocked : Site (source cp) -> StatementClass cp s.

Parameter statement_class : forall (cp : Program) (s : ExpressionStatementRef (source cp)),
  StatementClass cp s.

(* ── §10 One result-consumption authority ──────────────────────────────────── *)
Inductive ConsumptionTarget (p : SyntaxProgram) : Type :=
| NamedTarget : BindingSiteRef p -> ConsumptionTarget p
| BlankTarget : BlankRef p -> ConsumptionTarget p.

(* The exact defaulting / representability / assignability evidence an entry must carry. *)
Inductive AtomFitsTarget (cp : Program) : ResultAtom cp -> AcceptedType cp -> Prop :=
| FitUntyped : forall c t, AcceptedRepresentable cp t c ->
    AtomFitsTarget cp (UntypedConstant cp c) t
| FitTyped : forall (s : AcceptedType cp) ct t, AcceptedAssignable cp s t ->
    AtomFitsTarget cp (TypedConstantAtom cp s ct) t
| FitValue : forall (s : AcceptedType cp) t, AcceptedAssignable cp s t ->
    AtomFitsTarget cp (ValueResult cp s) t.

Inductive ConstAtom (cp : Program) : ResultAtom cp -> Prop :=
| CAUntyped : forall c, ConstAtom cp (UntypedConstant cp c)
| CATyped   : forall t ct, ConstAtom cp (TypedConstantAtom cp t ct).

Record ConstEntry (cp : Program) : Type := MakeConstEntry {
  ce_target : ConsumptionTarget (source cp);
  ce_occurrence : ResultOccurrence cp;
  ce_constant : ConstAtom cp (occurrence_atom ce_occurrence)
}.

Record VarEntry (cp : Program) : Type := MakeVarEntry {
  ve_target : ConsumptionTarget (source cp);
  ve_occurrence : ResultOccurrence cp;
  ve_type : AcceptedType cp;
  ve_fits : AtomFitsTarget cp (occurrence_atom ve_occurrence) ve_type
}.

Inductive ShortDisposition (cp : Program) : Type :=
| ShortNew   : ShortDisposition cp
| ShortReuse : Object cp -> ShortDisposition cp.

(* Blank short entries carry no disposition and no target type: the context decides. *)
Inductive ShortEntry (cp : Program) : Type :=
| ShortNamed : forall (b : BindingSiteRef (source cp)) (d : ShortDisposition cp)
    (o : ResultOccurrence cp) (t : AcceptedType cp),
    AtomFitsTarget cp (occurrence_atom o) t -> ShortEntry cp
| ShortBlankEntry : BlankRef (source cp) -> ResultOccurrence cp -> ShortEntry cp.

Inductive ConsumptionPlan (cp : Program) : Type :=
| ConstPlan : list (ConstEntry cp) -> ConsumptionPlan cp
| VarPlan   : list (VarEntry cp) -> ConsumptionPlan cp
| ShortPlan : list (ShortEntry cp) -> ConsumptionPlan cp.

Parameter consumption_plan : forall {cp} {s}, Consumption cp s -> ConsumptionPlan cp.

Definition short_entry_target (cp : Program) (e : ShortEntry cp)
  : ConsumptionTarget (source cp) :=
  match e with
  | ShortNamed _ b _ _ _ _ => NamedTarget (source cp) b
  | ShortBlankEntry _ k _ => BlankTarget (source cp) k
  end.

Definition short_entry_occurrence (cp : Program) (e : ShortEntry cp) : ResultOccurrence cp :=
  match e with
  | ShortNamed _ _ _ o _ _ => o
  | ShortBlankEntry _ _ o => o
  end.

Definition plan_targets (cp : Program) (pl : ConsumptionPlan cp)
  : list (ConsumptionTarget (source cp)) :=
  match pl with
  | ConstPlan _ l => List.map (ce_target cp) l
  | VarPlan _ l => List.map (ve_target cp) l
  | ShortPlan _ l => List.map (short_entry_target cp) l
  end.

Definition plan_occurrences (cp : Program) (pl : ConsumptionPlan cp)
  : list (ResultOccurrence cp) :=
  match pl with
  | ConstPlan _ l => List.map (ce_occurrence cp) l
  | VarPlan _ l => List.map (ve_occurrence cp) l
  | ShortPlan _ l => List.map (short_entry_occurrence cp) l
  end.

(* The plan IS the authority: the source uses it consumes are the uses of its own occurrences. *)
Definition plan_sources (cp : Program) (pl : ConsumptionPlan cp)
  : list (ExprUseRef (source cp)) :=
  List.map (occ_use cp) (plan_occurrences cp pl).
