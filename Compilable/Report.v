(* Report — diagnostics (definite errors) and requirements (outside boundaries); each retains its exact site key. *)
From Stdlib Require Import String.
From Fido Require Import Syntax Index Compilable.TypeResolution.

Inductive RootCause : Type :=
| RCUnresolvedName        : Index.Key -> RootCause
| RCInvalidConversion     : Index.Key -> Compilable.TypeResolution.SemanticType -> Syntax.Expr -> RootCause
| RCDefaultNotRepresentable : Index.Key -> Compilable.TypeResolution.Constant -> RootCause
| RCUnaryTypeMismatch     : Index.Key -> Syntax.Expr -> RootCause
| RCComplexTypeMismatch   : Index.Key -> RootCause
| RCConversionArity       : Index.Key -> RootCause
| RCComplexArity          : Index.Key -> RootCause
| RCNotCallable           : Index.Key -> RootCause
| RCTypeAsValue           : Index.Key -> RootCause
| RCNoValueUsed           : Index.Key -> RootCause
| RCIllegalStatement      : Index.Key -> RootCause
| RCMainRedeclared        : string -> RootCause
| RCMissingMain           : string -> RootCause
| RCBuildOutputDir        : string -> string -> RootCause.

Inductive Requirement : Type :=
| ReqValueMeaning : option Index.Key -> Requirement
| ReqApplication  : Requirement
| ReqStatement    : Requirement
| ReqDeclaration  : Requirement
| ReqUnary        : Requirement.

Record Boundary : Type := MakeBoundary { boundary_site : Index.Key ; boundary_req : Requirement }.
