
(* ── §4.2 Requirement satisfaction is defined from retained phase facts ────── *)
(* It mentions no `Program`, so it is the decision that can produce an OutsideScope result. *)
Definition RequirementSatisfied {p} {i : Input p} (ph : Phase i) (s : Site p)
  (r : SiteRequirement ph s) : Prop :=
  match r with
  | NeedTypeMeaning _ _ o => inhabited (PhaseTypeMeaning ph o)
  | NeedValueMeaning _ _ o =>
      inhabited (PhaseValueMeaning ph o) \/ inhabited (PhaseConstantMeaning ph o) \/
      inhabited (PhaseStaticVariable ph o) \/ inhabited (PhaseIotaMeaning ph o) \/
      inhabited (PhaseNilMeaning ph o)
  | NeedApplication _ a => IsSupported (phase_outcome ph (SApplication p a))
  | NeedStatement _ t => IsSupported (phase_outcome ph (SStatement p t))
  | NeedUnary _ n => IsSupported (phase_outcome ph (SUnary p n))
  end.

Parameter requirement_dec : forall {p} {i : Input p} (ph : Phase i) (s : Site p)
  (r : SiteRequirement ph s),
  { RequirementSatisfied ph s r } + { ~ RequirementSatisfied ph s r }.

(* ── §14 Rendering: contexts, and predicates that say something ────────────── *)
Inductive RenderContext : Type :=
| TopContext | UnaryOperandContext | ApplicationHeadContext | ApplicationArgumentContext.

Parameter needs_parens : RenderContext -> Expr -> bool.
Parameter render_in : RenderContext -> Expr -> string.
Parameter render_expr : Expr -> string.
Parameter render_type_expr : TypeExpr -> string.
Parameter render_file : SyntaxFile -> string.
Parameter render_program : SyntaxProgram -> list (FilePathT * string).
Parameter render_gomod : ModuleSpec -> string.

Fixpoint InString (c : ascii) (s : string) : Prop :=
  match s with EmptyString => False | String c' rest => c = c' \/ InString c rest end.

Definition first_char (s : string) : option ascii :=
  match s with EmptyString => None | String c _ => Some c end.

Fixpoint last_char (s : string) : option ascii :=
  match s with
  | EmptyString => None
  | String c EmptyString => Some c
  | String _ rest => last_char rest
  end.

(* Exactly two adjacent bytes, so the property is about a token boundary and not about scanning contents. *)
Fixpoint HasAdjacent (a b : ascii) (s : string) : Prop :=
  match s with
  | EmptyString => False
  | String c rest => (c = a /\ first_char rest = Some b) \/ HasAdjacent a b rest
  end.

Definition NewlineChar : ascii := ascii_of_nat 10.
Definition SpaceChar : ascii := ascii_of_nat 32.
Definition TabChar : ascii := ascii_of_nat 9.

Definition StartsWithMinus (s : string) : Prop := first_char s = Some "-"%char.
Definition AsciiOnly (s : string) : Prop := forall c, InString c s -> (nat_of_ascii c < 128)%nat.
Definition Parenthesized (s : string) : Prop := exists inner, s = ("(" ++ inner ++ ")")%string.

(* No line ends in a space or a tab, and the file's final byte is a newline. *)
Definition NoTrailingBlank (s : string) : Prop :=
  ~ HasAdjacent SpaceChar NewlineChar s /\
  ~ HasAdjacent TabChar NewlineChar s /\
  last_char s = Some NewlineChar.

(* ── Remaining relations named by the theorems ─────────────────────────────── *)
Parameter InnermostDeclaring : forall (cp : Program),
  NameUseRef (source cp) -> BindingSiteRef (source cp) -> Prop.
Parameter SameBlockEarlier_DELETED : forall (cp : Program),
  BindingSiteRef (source cp) -> Object cp -> Prop.
Parameter ReadsVariableAt : forall {p} {i : Input p} (ph : Phase i), VariableSiteRef p -> Prop.
Parameter FullyAnalyzedLocal : forall {p} {i : Input p} (ph : Phase i),
  VariableSiteRef p -> Prop.
Parameter LocalVariableSite : forall {p} {i : Input p} (ph : Phase i),
  VariableSiteRef p -> Prop.
Parameter ScopesFileOrderIndependent : forall {p} {i : Input p}, Phase i -> Prop.
Parameter bound_object : forall {cp : Program} {u}, BindingFact cp u -> Object cp.
Parameter binding_use_role : forall {cp : Program} {u}, BindingFact cp u -> UseRole.
Parameter binding_package : forall {cp : Program} {u},
  BindingFact cp u -> PackageRef (source cp).
