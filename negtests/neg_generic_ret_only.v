(* EXPECT: appears only in the RETURN type *)
(* A generic function whose type variable has NO inference source: Go call sites never
   carry explicit type arguments, so a tvar occurring only in the RETURN type can never
   be inferred ("cannot infer").  Extraction MUST abort when the DECLARATION is emitted;
   a regression emits a function no Go call can instantiate.  ([ret_only] must be a
   top-level decl — the extraction ROOT itself inlines into [main] with erased types. *)
From Fido Require Import preamble.
Definition ret_only {A B : Type} (x : A) : list B := nil.
Extraction NoInline ret_only.
Definition neg_bad (x : GoI64) : list GoI64 := ret_only x.
Go Main Extraction neg_out "neg_bad".
