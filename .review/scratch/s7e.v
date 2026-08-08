
(* ── §14 One closed root-cause authority ───────────────────────────────────── *)
(* A diagnostic is a sealed view of one exact root cause.  Every cause is a constructor of this sum,
   so completeness and soundness are constructive rather than asserted. *)
Inductive RootCause {p} {i : Input p} (ph : Phase i) : Type :=
| RCSiteFailure : forall s : Site p, SiteFailure ph s -> RootCause ph
| RCTypeCycle   : TypeCycle (phase_equations ph) -> RootCause ph
| RCMainRedeclared : forall later earlier : ObjectSiteRef p, RootCause ph
| RCMissingMain : PackageRef p -> RootCause ph
| RCBuildOutputDir : PackageRef p -> string -> RootCause ph.

Definition site_failure_code {p} {i : Input p} {ph : Phase i} {s}
  (f : SiteFailure ph s) : DiagnosticCode :=
  match f with
  | FUnresolvedName _ _ _ => CodeUnresolvedName
  | FWrongRole _ _ _ _ _ => CodeUnresolvedName
  | FDuplicateDeclaration _ _ _ _ => CodeDuplicateDeclaration
  | FPackageInitReserved _ _ _ => CodeContext
  | FNotAStatement _ _ _ => CodeNotAStatement
  | FResultCountWrong _ _ _ _ => CodeResultCount
  | FNotAssignableAt _ _ _ _ _ _ => CodeNotAssignable
  | FNotRepresentableAt _ _ _ _ _ _ => CodeNotRepresentable
  | FConstInitNotConstant _ _ _ _ _ _ => CodeConstInitializerNotConstant
  | FNoNewVariable _ _ _ => CodeNoNewVariable
  | FShortReuseMismatch _ _ _ _ _ _ _ _ => CodeNotAssignable
  | FContext _ _ _ => CodeContext
  | FDefaultNotRepresentable _ _ _ _ => CodeDefaultNotRepresentable
  | FUnusedLocal _ _ _ _ _ => CodeUnusedLocal
  | FInitializationCycle _ _ _ => CodeInitializationCycle
  end.

Definition root_cause_code {p} {i : Input p} {ph : Phase i}
  (rc : RootCause ph) : DiagnosticCode :=
  match rc with
  | RCSiteFailure _ _ f     => site_failure_code f
  | RCTypeCycle _ _         => CodeTypeCycle
  | RCMainRedeclared _ _ _  => CodeMainRedeclared
  | RCMissingMain _ _       => CodeMissingMainEntry
  | RCBuildOutputDir _ _ _  => CodeBuildOutputIsDirectory
  end.

Record ErasedDiagnostic : Type := MakeErasedDiagnostic {
  erased_code   : DiagnosticCode;
  erased_primary : ErasedAnchor;
  erased_related : list ErasedAnchor;
  erased_target  : option TypeView;
  erased_output  : option string;
  erased_source_target : option TypeExpr
}.

Parameter diagnostic_primary : forall {p} {i : Input p} {ph : Phase i},
  RootCause ph -> DiagnosticAnchor p.
Parameter diagnostic_related : forall {p} {i : Input p} {ph : Phase i},
  RootCause ph -> list (DiagnosticAnchor p).
Parameter erase_anchor : forall {p}, DiagnosticAnchor p -> ErasedAnchor.
Parameter diagnostic_compare : forall {p} {i : Input p} {ph : Phase i},
  RootCause ph -> RootCause ph -> comparison.

Definition diagnostic_target {p} {i : Input p} {ph : Phase i}
  (rc : RootCause ph) : option TypeView :=
  match rc with
  | RCSiteFailure _ _ f =>
      match f with
      | FDefaultNotRepresentable _ _ _ t => Some t
      | FNotAssignableAt _ _ _ _ _ t => Some (type_view t)
      | FNotRepresentableAt _ _ _ _ _ t => Some (type_view t)
      | _ => None
      end
  | _ => None
  end.

Definition diagnostic_output {p} {i : Input p} {ph : Phase i}
  (rc : RootCause ph) : option string :=
  match rc with RCBuildOutputDir _ _ nm => Some nm | _ => None end.

Parameter diagnostic_source_target : forall {p} {i : Input p} {ph : Phase i},
  RootCause ph -> option TypeExpr.

Definition erase_diagnostic {p} {i : Input p} {ph : Phase i}
  (rc : RootCause ph) : ErasedDiagnostic :=
  MakeErasedDiagnostic (root_cause_code rc) (erase_anchor (diagnostic_primary rc))
    (List.map erase_anchor (diagnostic_related rc))
    (diagnostic_target rc) (diagnostic_output rc) (diagnostic_source_target rc).
