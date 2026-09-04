(* Hostile mutations of the use judgment: each mutant is defined, then must fail the exact law it neuters *)
From Stdlib Require Import List ZArith.
From Fido Require Import Names Syntax Index Compilable.TypeResolution Compilable.PackageIdentity Compilable.Bindings Compilable.Analysis.
Import ListNotations.
Module AN := Compilable.Analysis.
Module TR := Compilable.TypeResolution.
Module BN := Compilable.Bindings.

(* the shared proof script of the ancestry law: it proves completeness for the canonical root and fails a mutant *)
Ltac ancestry := intros; match goal with H : AN.ConstRootOf _ _ _ _ |- _ => induction H end; cbn; try reflexivity; assumption.

(* positive control: the canonical computed root proves the ancestry law with exactly this script *)
Definition positive_ancestry
  : forall p (idx : Index.ProgramIndex p) (r : Index.NodeRef idx) (path : Index.Edges.ExprUsePath r)
      (sp : Index.Refs.SpecRef idx Index.Model.ConstSpecF) (j : nat) (e : Index.Edges.SpecValueEdge sp j),
      AN.ConstRootOf path sp j e -> AN.path_const_root path = Some (existT _ sp (existT _ j e))
  := ltac:(ancestry).

(* m1: initializer ancestry dropped at an application-argument link *)
Module M1ArgDropped.
Fixpoint mutant_root {p} {idx : Index.ProgramIndex p} {r : Index.NodeRef idx} (path : Index.Edges.ExprUsePath r)
  : option { sp : Index.Refs.SpecRef idx Index.Model.ConstSpecF & { j : nat & Index.Edges.SpecValueEdge sp j } } :=
  match path with
  | Index.Edges.EUPConst sp j e => Some (existT _ sp (existT _ j e))
  | Index.Edges.EUPUnary _ _ sub => mutant_root sub
  | Index.Edges.EUPArg _ _ _ _ => None
  | Index.Edges.EUPHead _ _ sub => mutant_root sub
  | _ => None
  end.
Fail Definition mutant_ancestry
  : forall p (idx : Index.ProgramIndex p) (r : Index.NodeRef idx) (path : Index.Edges.ExprUsePath r)
      (sp : Index.Refs.SpecRef idx Index.Model.ConstSpecF) (j : nat) (e : Index.Edges.SpecValueEdge sp j),
      AN.ConstRootOf path sp j e -> mutant_root path = Some (existT _ sp (existT _ j e))
  := ltac:(ancestry).
End M1ArgDropped.

(* m2: initializer ancestry dropped at an application-head link *)
Module M2HeadDropped.
Fixpoint mutant_root {p} {idx : Index.ProgramIndex p} {r : Index.NodeRef idx} (path : Index.Edges.ExprUsePath r)
  : option { sp : Index.Refs.SpecRef idx Index.Model.ConstSpecF & { j : nat & Index.Edges.SpecValueEdge sp j } } :=
  match path with
  | Index.Edges.EUPConst sp j e => Some (existT _ sp (existT _ j e))
  | Index.Edges.EUPUnary _ _ sub => mutant_root sub
  | Index.Edges.EUPArg _ _ _ sub => mutant_root sub
  | Index.Edges.EUPHead _ _ _ => None
  | _ => None
  end.
Fail Definition mutant_ancestry
  : forall p (idx : Index.ProgramIndex p) (r : Index.NodeRef idx) (path : Index.Edges.ExprUsePath r)
      (sp : Index.Refs.SpecRef idx Index.Model.ConstSpecF) (j : nat) (e : Index.Edges.SpecValueEdge sp j),
      AN.ConstRootOf path sp j e -> mutant_root path = Some (existT _ sp (existT _ j e))
  := ltac:(ancestry).
End M2HeadDropped.

(* the link-order law over any link projection: the subject's own link first, exactly the constructor order *)
Definition links_order {p} {idx : Index.ProgramIndex p}
  (links : forall {r : Index.NodeRef idx}, Index.Edges.ExprUsePath r -> list (AN.Link idx)) : Prop :=
  forall (r : Index.NodeRef idx) (path : Index.Edges.ExprUsePath r),
    match path with
    | Index.Edges.EUPUnary u _ sub => links path = AN.LUnary u :: links sub
    | Index.Edges.EUPArg a i _ sub => links path = AN.LArg a i :: links sub
    | Index.Edges.EUPHead a _ sub => links path = AN.LHead a :: links sub
    | _ => links path = []
    end.
(* positive control: the canonical link projection satisfies the order law by the one-line script *)
Definition positive_links_order p (idx : Index.ProgramIndex p) : @links_order p idx (@AN.path_links p idx)
  := ltac:(intros r path; destruct path; reflexivity).

(* m3a: links appended outward-last, so a mixed chain is permuted *)
Module M3Reordered.
Fixpoint mutant_links {p} {idx : Index.ProgramIndex p} {r : Index.NodeRef idx} (path : Index.Edges.ExprUsePath r)
  : list (AN.Link idx) :=
  match path with
  | Index.Edges.EUPUnary u _ sub => mutant_links sub ++ [AN.LUnary u]
  | Index.Edges.EUPArg a i _ sub => mutant_links sub ++ [AN.LArg a i]
  | Index.Edges.EUPHead a _ sub => mutant_links sub ++ [AN.LHead a]
  | _ => []
  end.
Fail Definition mutant_order p (idx : Index.ProgramIndex p) : @links_order p idx (@mutant_links p idx)
  := ltac:(intros r path; destruct path; reflexivity).
End M3Reordered.

(* m3b: a unary-only classifier: argument and head links are discarded *)
Module M3UnaryOnly.
Fixpoint mutant_links {p} {idx : Index.ProgramIndex p} {r : Index.NodeRef idx} (path : Index.Edges.ExprUsePath r)
  : list (AN.Link idx) :=
  match path with
  | Index.Edges.EUPUnary u _ sub => AN.LUnary u :: mutant_links sub
  | Index.Edges.EUPArg _ _ _ sub => mutant_links sub
  | Index.Edges.EUPHead _ _ sub => mutant_links sub
  | _ => []
  end.
Fail Definition mutant_order p (idx : Index.ProgramIndex p) : @links_order p idx (@mutant_links p idx)
  := ltac:(intros r path; destruct path; reflexivity).
End M3UnaryOnly.

(* m4: a failed mandatory default reported as the neutral VNonconst instead of the exact DefaultOverflow *)
Module M4DefaultNonconst.
Definition mutant_default {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) (r : Index.NodeRef idx) (Hdef : AN.is_value_default_node r = true) (c : TR.Constant)
  : AN.ValueOutcome bp r :=
  match TR.default_constant c with Some rc => AN.VOK rc | None => AN.VNonconst end.
(* positive control: the canonical default verdict is exactly the DefaultOverflow on failure *)
Definition positive_default {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) (r : Index.NodeRef idx) (Hdef : AN.is_value_default_node r = true) (c : TR.Constant)
  (Hn : TR.default_constant c = None) : AN.default_verdict bp r Hdef c = AN.VInvalid (AN.DefaultOverflow Hdef c)
  := ltac:(unfold AN.default_verdict; rewrite Hn; reflexivity).
Fail Definition mutant_failure {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) (r : Index.NodeRef idx) (Hdef : AN.is_value_default_node r = true) (c : TR.Constant)
  (Hn : TR.default_constant c = None) : mutant_default bp r Hdef c = AN.VInvalid (AN.DefaultOverflow Hdef c)
  := ltac:(unfold mutant_default; rewrite Hn; reflexivity).
End M4DefaultNonconst.

(* m5: the invalid-form and absent-rule conversion categories collapsed onto one another *)
Module M5Collapsed.
Definition mutant_failure {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) {r : Index.NodeRef idx} (Hv : Index.node_view r = Index.Model.VApplication)
  (t : TR.TypeForm) (x : Index.NodeRef idx) {t' : TR.TypeForm} (res : TR.ConversionResult t') : AN.ValueOutcome bp r :=
  match res with
  | TR.Converted _ => AN.VNonconst
  | TR.Overflows _ => AN.VInvalid (AN.ConversionOverflow Hv t x)
  | TR.NotRepresentable _ => AN.VInvalid (AN.ConversionNotRepresentable Hv t x)
  | TR.InvalidForm _ => AN.VUnmet (AN.RConversionUnmet Hv t x)
  | TR.Unmet _ => AN.VInvalid (AN.ConversionNotRepresentable Hv t x)
  end.
Fail Definition mutant_invalid_form {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) {r : Index.NodeRef idx} (Hv : Index.node_view r = Index.Model.VApplication)
  (t : TR.TypeForm) (x : Index.NodeRef idx) (ci : TR.ConstantInfo)
  : mutant_failure bp Hv t x (@TR.InvalidForm t ci) = AN.VInvalid (AN.ConversionNotRepresentable Hv t x)
  := ltac:(reflexivity).
Fail Definition mutant_unmet {p} {idx : Index.ProgramIndex p} {s : BN.PI.PackageSurface idx} {bd : BN.PhaseData s}
  (bp : BN.BindingPhase s bd) {r : Index.NodeRef idx} (Hv : Index.node_view r = Index.Model.VApplication)
  (t : TR.TypeForm) (x : Index.NodeRef idx) (ci : TR.ConstantInfo)
  : mutant_failure bp Hv t x (@TR.Unmet t ci) = AN.VUnmet (AN.RConversionUnmet Hv t x)
  := ltac:(reflexivity).
End M5Collapsed.

(* m6a: an ASCII-only integer-to-string encoder cannot round-trip through the canonical decoder at 0x80 *)
Module M6AsciiOnly.
Definition mutant_bytes (z : Z) : list Z := [z].
Definition positive_round_trip : TR.utf8_decode (TR.utf8_bytes 0x80) = Some 0x80 := ltac:(vm_compute; reflexivity).
Fail Definition mutant_round_trip : TR.utf8_decode (mutant_bytes 0x80) = Some 0x80 := ltac:(vm_compute; reflexivity).
End M6AsciiOnly.

(* m6b: an encoder without the replacement character has no decodable image for a non-scalar *)
Module M6NoReplacement.
Definition mutant_bytes (z : Z) : list Z := if TR.unicode_scalarb z then TR.utf8_bytes_scalar z else [].
Definition positive_replacement : TR.utf8_decode (TR.utf8_bytes (-1)) = Some 0xFFFD := ltac:(vm_compute; reflexivity).
Fail Definition mutant_replacement : TR.utf8_decode (mutant_bytes (-1)) = Some 0xFFFD := ltac:(vm_compute; reflexivity).
End M6NoReplacement.
