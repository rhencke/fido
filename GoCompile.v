(** GoCompile — the EXACT acceptance model for the pinned one-shot `go build ./...`, as EVIDENCE over the ONE
    raw program (the [GoProgram]: a [ModuleSpec] + a possibly-EMPTY standard [FilePath] map of files
    [GoFileMap]): [GoCompile p := fresh_build_preflight_ok p /\ SourceProgramValid p] — the cmd/go default-
    OUTPUT fresh-build preflight AND the LIVE factored source judgment [SourceProgramValid]
    (= [ProgramTyped] /\ the factored package rules [PackageDeclsUnique] + [MainPackagesHaveEntry]) over
    that same program.  It is built by the ONE elaboration root [elaborate] — the single indexed whole-program
    pass over [GoIndex]'s [visit_file] traversal — and [go_compile] PROJECTS that elaboration (no second
    checker).  The empty program is accepted (no packages, one go.mod).

    The package CLAUSE is SOURCE syntax (rendered by GoRender); package GROUPING (by [fp_parent], one
    directory = one package, via the one-pass [PackageMap]) and main/entry validity are whole-program
    COMPILATION RESULTS, all-or-nothing.  The layer charter is ARCHITECTURE.md; it is not restated here.

    HONESTY — two distinct claims.  (A) KERNEL-internal exactness, PROVED here: [go_compile] succeeds exactly
    for the declarative judgment ([go_compile_ok_valid] + [go_compile_complete]; [elaborate_ok_iff_GoCompile])
    — sound + complete.  (B) EXTERNAL adequacy, the GOAL attacked by differential `go build ./...` experiments
    and NEVER a kernel theorem: the judgment matches real cmd/go on every representable rendered program. *)
From Stdlib Require Import NArith ZArith List Bool String Ascii Arith Lia.
From Stdlib Require Import SetoidList Permutation.
From Fido Require Import Ints Floats Complexes FilePath ModulePath Collections GoAST GoIndex GoTypes.
From Stdlib Require Import Eqdep_dec.
Import ListNotations.
Open Scope Z_scope.

(** ---- the compiler-owned predeclared type context (§7): the ONE source-name-to-semantic-type resolver ----

    [GoCompile] owns the current predeclared type context.  A conversion's SOURCE type name ([TypeSyntax])
    resolves to its semantic [GoType] HERE — never in [GoAST], [GoTypes], or [GoRender].  The current language
    has no named declarations or imports, so this is a compact TOTAL function over the closed sixteen-name
    lexical class [GoNames.TypeName]: [byte]/[uint8] and [rune]/[int32] resolve to EQUAL semantic types while
    remaining DISTINCT source symbols.  The interface makes ownership explicit so later declaration shadowing can
    extend the lookup rather than rewrite the AST.  Every C4-live [TypeNameSyntax] resolves by construction, so
    C4 has no unresolved-type-name diagnostic. *)
Definition predeclared_type_of_name (n : GoNames.TypeName) : GoType :=
  match n with
  | GoNames.TNint    => TInteger IInt    | GoNames.TNint8  => TInteger IInt8
  | GoNames.TNint16  => TInteger IInt16  | GoNames.TNint32 => TInteger IInt32
  | GoNames.TNint64  => TInteger IInt64
  | GoNames.TNuint   => TInteger IUint   | GoNames.TNuint8  => TInteger IUint8
  | GoNames.TNuint16 => TInteger IUint16 | GoNames.TNuint32 => TInteger IUint32
  | GoNames.TNuint64 => TInteger IUint64
  | GoNames.TNfloat32 => TFloat F32 | GoNames.TNfloat64 => TFloat F64
  | GoNames.TNcomplex64 => TComplex C64 | GoNames.TNcomplex128 => TComplex C128
  | GoNames.TNbyte => TInteger IUint8 | GoNames.TNrune => TInteger IInt32
  end.

Definition predeclared_type (ts : GoAST.TypeSyntax) : GoType :=
  predeclared_type_of_name (GoAST.ts_name ts).

(** Within [GoCompile] the resolver is FIXED to [predeclared_type]; these parsing notations specialize the
    [GoTypes] index-free typing spec (§9) at that ONE compiler-owned resolver, so the production occurrence
    pass and its exactness proofs read against a single context. *)
Local Notation const_info        := (GoTypes.const_info predeclared_type) (only parsing).
Local Notation const_info_step   := (GoTypes.const_info_step predeclared_type) (only parsing).
Local Notation resolve_expr_const := (GoTypes.resolve_expr_const predeclared_type) (only parsing).
Local Notation resolve_expr      := (GoTypes.resolve_expr predeclared_type) (only parsing).
Local Notation expr_typedb       := (GoTypes.expr_typedb predeclared_type) (only parsing).
Local Notation stmt_typedb       := (GoTypes.stmt_typedb predeclared_type) (only parsing).
Local Notation decl_typedb       := (GoTypes.decl_typedb predeclared_type) (only parsing).
Local Notation file_typedb       := (GoTypes.file_typedb predeclared_type) (only parsing).
Local Notation source_file_typedb := (GoTypes.source_file_typedb predeclared_type) (only parsing).
Local Notation program_typedb    := (GoTypes.program_typedb predeclared_type) (only parsing).
Local Notation ProgramTyped      := (GoTypes.ProgramTyped predeclared_type) (only parsing).
Local Notation ResolveExpr       := (GoTypes.ResolveExpr predeclared_type) (only parsing).
Local Notation StmtTyped         := (GoTypes.StmtTyped predeclared_type) (only parsing).
Local Notation DeclTyped         := (GoTypes.DeclTyped predeclared_type) (only parsing).
Local Notation FileTyped         := (GoTypes.FileTyped predeclared_type) (only parsing).
Local Notation SourceFileTyped   := (GoTypes.SourceFileTyped predeclared_type) (only parsing).

(** ---- static admissibility is TYPING (GoTypes, the one type authority) ----

    Per-file/decl/statement/expression admissibility is [GoTypes.ProgramTyped]/[program_typedb] over the
    SAME raw AST: every [println] argument must RESOLVE under [UsePrintlnArg] to a [GoType] (a typing failure
    is a constant fitting no integer type, a bare float overflowing its default [float64], an invalid
    invalid [EConvert] — a float or complex-component overflow, a fractional or
    out-of-range float->integer, a nonzero-imaginary complex->scalar, a wrong-type or
    nested-invalid conversion; bools and strings always resolve).  There is no separate GoCompile static-
    admissibility family; the deleted [ExprOk]/[StmtOk]/[DeclOk]/[FileOk] are subsumed by the type judgment. *)

(** ---- main-declaration counting (entry-point status is a compilation result) ---- *)

Definition decl_is_main (d : GoDecl) : bool := match d with DMain _ => true end.
Definition file_main_count (decls : list GoDecl) : nat := List.length (List.filter decl_is_main decls).

Module PM := Collections.PackageMapBase.
Module PMF := Collections.PackageMapFacts.
Module PMP := Collections.PackageMapProps.

(** a package (directory) SUMMARY carries only the LIVE fact the current fragment needs — the package's total
    `main` declaration count.  (No speculative method/import/type fields; a new fact lands with its proofs.) *)
Record PackageSummary : Type := mkPkgSummary { ps_main_count : nat }.
Definition ps_count (o : option PackageSummary) : nat := match o with Some s => ps_main_count s | None => 0 end.

(** accumulate one file's `main` count into its parent-directory package summary. *)
Definition pm_add_main (dir : string) (n : nat) (acc : PM.t PackageSummary) : PM.t PackageSummary :=
  PM.add dir (mkPkgSummary (n + ps_count (PM.find dir acc))) acc.
Definition pkg_step (path : FilePath) (sf : GoSourceFile) (acc : PM.t PackageSummary) : PM.t PackageSummary :=
  pm_add_main (fp_parent path) (file_main_count (source_decls sf)) acc.

(** ONE pass over the file MAP: a single [FM.fold] over the source forest, each file contributing its
    `main` count EXACTLY ONCE to its parent-directory package summary via one logarithmic [PackageMap] update —
    NOT a repeated O(files²) file scan (the deleted [main_count_in_dir] scanned all entries per file). *)
Definition package_summaries (fm : GoFileMap) : PM.t PackageSummary :=
  GoAST.FM.fold pkg_step fm (PM.empty PackageSummary).

(** ---- the declarative validity of the whole program ---- *)

(** [current_grammar_one_main] is the grammar CONSEQUENCE (NOT a source root): for the CURRENT grammar (every
    package is `package main`, every `DMain` is `func main()`) the LIVE factored package rules
    [PackageRulesValid] (= [PackageDeclsUnique] + [MainPackagesHaveEntry]) coincide with "every package has
    exactly one `main`".  It survives ONLY as the RHS of the retained universal CONSEQUENCE theorem
    [current_package_rules_exactly_one] and the LENGTH-based diagnostic bridge — it is NEVER the executable
    decision (which reflects the two factored roots below), NEVER a peer source authority.  The SOLE live
    source-validity judgment is [SourceProgramValid] (= [ProgramTyped] /\ [PackageRulesValid]); the decidable
    [source_spec_valid_b] reflects it DIRECTLY via the two factored reflections ([source_spec_valid_b_iff], below).
    There is NO [ProgValid] Prop and NO [prog_ok] bool. *)
Definition current_grammar_one_main (p : GoProgram) : Prop :=
  forall dir s, PM.MapsTo dir s (package_summaries (prog_files p)) -> ps_main_count s = 1%nat.

(** [source_spec_package_rules_b] is the readable, index-free SPECIFICATION package decision (for fixtures and
    proof convenience — vm-computable, no [GoIndex]): the conjunction of the TWO factored package rules as
    SEPARATE decidable roots: [pkg_decls_unique_b] = at most one `main` per package (block uniqueness →
    [PackageDeclsUnique]); [main_pkgs_have_entry_b] = at least one `main` per package (entry →
    [MainPackagesHaveEntry]).  It is NOT the production decision — production elaboration decides from the
    retained-bucket diagnostic pass ([pkg_diags]); the two are proved to reflect the SAME factored Props,
    never one through the other.  Neither the combined "=1" nor [current_grammar_one_main] is executed — that is
    only a downstream CONSEQUENCE ([current_package_rules_exactly_one]). *)
Definition pkg_decls_unique_b (p : GoProgram) : bool :=
  forallb (fun b => Nat.leb (ps_main_count (snd b)) 1) (PM.elements (package_summaries (prog_files p))).
Definition main_pkgs_have_entry_b (p : GoProgram) : bool :=
  forallb (fun b => Nat.leb 1 (ps_main_count (snd b))) (PM.elements (package_summaries (prog_files p))).
Definition source_spec_package_rules_b (p : GoProgram) : bool := pkg_decls_unique_b p && main_pkgs_have_entry_b p.

Definition source_spec_valid_b (p : GoProgram) : bool := program_typedb p && source_spec_package_rules_b p.

(** the TWO FACTORED PACKAGE ROOTS and their reflections, defined HERE (early, beside the executable
    [source_spec_package_rules_b]) so BOTH the [package_summaries] view (fixtures) AND the retained-bucket production decision
    root DIRECTLY in them (see [pkg_diags_empty_iff_rules] below).  [PackageDeclsUnique] = at most one `main` per
    package (block uniqueness); [MainPackagesHaveEntry] = at least one (entry); [PackageRulesValid] is their
    conjunction (the SOURCE half of GoCompile, packaged with [ProgramTyped] into [SourceProgramValid]).
    The exactly-one "every package has one main" is ONLY a downstream CONSEQUENCE
    ([current_package_rules_exactly_one]), NEVER the executable decision or a peer authority. *)
Definition PackageDeclsUnique (p : GoProgram) : Prop :=
  forall dir s, PM.MapsTo dir s (package_summaries (prog_files p)) -> (ps_main_count s <= 1)%nat.
Definition MainPackagesHaveEntry (p : GoProgram) : Prop :=
  forall dir s, PM.MapsTo dir s (package_summaries (prog_files p)) -> (1 <= ps_main_count s)%nat.
Definition PackageRulesValid (p : GoProgram) : Prop := PackageDeclsUnique p /\ MainPackagesHaveEntry p.

(** the two factored roots reflect their Props DIRECTLY: [pkg_decls_unique_b] ↔ [PackageDeclsUnique],
    [main_pkgs_have_entry_b] ↔ [MainPackagesHaveEntry] — the SPECIFICATION's factored package reflections. *)
Lemma pkg_decls_unique_b_iff : forall p, pkg_decls_unique_b p = true <-> PackageDeclsUnique p.
Proof.
  intro p. unfold pkg_decls_unique_b, PackageDeclsUnique.
  rewrite (forallb_Forall (fun b => Nat.leb (ps_main_count (snd b)) 1%nat) (fun b => (ps_main_count (snd b) <= 1)%nat)
             (PM.elements (package_summaries (prog_files p))) (fun b => Nat.leb_le (ps_main_count (snd b)) 1%nat)).
  split.
  - intros Hf dir s Hmt.
    apply PMF.elements_mapsto_iff, InA_alt in Hmt. destruct Hmt as [[k' s'] [Heq Hin]].
    destruct Heq as [_ Hs]. cbn in *. rewrite Forall_forall in Hf. specialize (Hf (k', s') Hin).
    cbn in Hf. rewrite Hs. exact Hf.
  - intros Hall. apply Forall_forall. intros [dir s] Hin. cbn.
    apply (Hall dir s), PMF.elements_mapsto_iff, InA_alt.
    exists (dir, s). split; [ split; reflexivity | exact Hin ].
Qed.

Lemma main_pkgs_have_entry_b_iff : forall p, main_pkgs_have_entry_b p = true <-> MainPackagesHaveEntry p.
Proof.
  intro p. unfold main_pkgs_have_entry_b, MainPackagesHaveEntry.
  rewrite (forallb_Forall (fun b => Nat.leb 1%nat (ps_main_count (snd b))) (fun b => (1 <= ps_main_count (snd b))%nat)
             (PM.elements (package_summaries (prog_files p))) (fun b => Nat.leb_le 1%nat (ps_main_count (snd b)))).
  split.
  - intros Hf dir s Hmt.
    apply PMF.elements_mapsto_iff, InA_alt in Hmt. destruct Hmt as [[k' s'] [Heq Hin]].
    destruct Heq as [_ Hs]. cbn in *. rewrite Forall_forall in Hf. specialize (Hf (k', s') Hin).
    cbn in Hf. rewrite Hs. exact Hf.
  - intros Hall. apply Forall_forall. intros [dir s] Hin. cbn.
    apply (Hall dir s), PMF.elements_mapsto_iff, InA_alt.
    exists (dir, s). split; [ split; reflexivity | exact Hin ].
Qed.

(** the SPECIFICATION package decision [source_spec_package_rules_b] reflects the factored [PackageRulesValid]
    DIRECTLY — the conjunction of the two factored reflections, no combined "=1" and no [current_grammar_one_main]
    intermediary. *)
Lemma source_spec_package_rules_b_PackageRulesValid : forall p, source_spec_package_rules_b p = true <-> PackageRulesValid p.
Proof.
  intro p. unfold source_spec_package_rules_b, PackageRulesValid.
  rewrite Bool.andb_true_iff, pkg_decls_unique_b_iff, main_pkgs_have_entry_b_iff. reflexivity.
Qed.

(** ---- PACKAGE-SUMMARY EXACTNESS: the single [FM.fold] is characterized EXACTLY, so package grouping is
    provably a one-pass, order-independent, map-extensional aggregation. ---- *)

(* the SPEC: the total `main` count files whose parent directory is [dir] contribute to that package. *)
Fixpoint list_dir_count (dir : string) (l : list (FilePath * GoSourceFile)) : nat :=
  match l with
  | [] => 0
  | b :: rest =>
      (if String.eqb (fp_parent (fst b)) dir then file_main_count (source_decls (snd b)) else 0)
      + list_dir_count dir rest
  end.
Definition list_dir_mem (dir : string) (l : list (FilePath * GoSourceFile)) : bool :=
  existsb (fun b => String.eqb (fp_parent (fst b)) dir) l.

Lemma list_dir_count_0 : forall dir l, list_dir_mem dir l = false -> list_dir_count dir l = 0%nat.
Proof.
  intros dir l; induction l as [|b rest IH]; simpl; [ reflexivity | ].
  unfold list_dir_mem in *; simpl; intro H. apply Bool.orb_false_iff in H as [Hb Hr].
  rewrite Hb; simpl; apply IH; exact Hr.
Qed.

(* list-level order-independence: both the presence flag and the count are permutation-invariant sums. *)
Lemma list_dir_mem_perm : forall dir l1 l2, Permutation l1 l2 -> list_dir_mem dir l1 = list_dir_mem dir l2.
Proof.
  intros dir l1 l2 H; unfold list_dir_mem; induction H; simpl; try reflexivity.
  - rewrite IHPermutation; reflexivity.
  - destruct (String.eqb (fp_parent (fst y)) dir), (String.eqb (fp_parent (fst x)) dir); reflexivity.
  - rewrite IHPermutation1; exact IHPermutation2.
Qed.
Lemma list_dir_count_perm : forall dir l1 l2, Permutation l1 l2 -> list_dir_count dir l1 = list_dir_count dir l2.
Proof.
  intros dir l1 l2 H; induction H; simpl; lia.
Qed.

(* the left fold matching [FM.fold] over the element list. *)
Definition pkg_foldl (l : list (FilePath * GoSourceFile)) (acc : PM.t PackageSummary) : PM.t PackageSummary :=
  fold_left (fun a p => pkg_step (fst p) (snd p) a) l acc.
Lemma pkg_foldl_cons : forall k e rest acc,
  pkg_foldl ((k, e) :: rest) acc = pkg_foldl rest (pkg_step k e acc).
Proof. reflexivity. Qed.
Lemma package_summaries_foldl : forall fm,
  package_summaries fm = pkg_foldl (GoAST.file_bindings fm) (PM.empty PackageSummary).
Proof. intro fm. unfold package_summaries, pkg_foldl. rewrite GoAST.FM.fold_1. reflexivity. Qed.

(* the fold CHARACTERIZATION: [find dir] is present iff a file belongs to [dir], and equals the exact sum. *)
Lemma pkg_foldl_find : forall l acc dir,
  PM.find dir (pkg_foldl l acc)
  = (if list_dir_mem dir l
     then Some (mkPkgSummary (list_dir_count dir l + ps_count (PM.find dir acc)))
     else PM.find dir acc).
Proof.
  induction l as [|[k e] rest IH]; intros acc dir; [ reflexivity | ].
  rewrite pkg_foldl_cons, (IH (pkg_step k e acc) dir).
  unfold list_dir_mem; simpl existsb; simpl list_dir_count; cbn [fst snd].
  destruct (String.eqb (fp_parent k) dir) eqn:Edir; cbn [orb].
  - apply String.eqb_eq in Edir.
    unfold pkg_step, pm_add_main. rewrite !PMF.add_eq_o by exact Edir.
    cbn [ps_count ps_main_count]. rewrite !Edir.
    destruct (existsb (fun b => String.eqb (fp_parent (fst b)) dir) rest) eqn:Erest;
      [ | rewrite (list_dir_count_0 dir rest Erest) ]; f_equal; f_equal; lia.
  - apply String.eqb_neq in Edir.
    unfold pkg_step, pm_add_main. rewrite !PMF.add_neq_o by exact Edir. reflexivity.
Qed.

Definition pkg_main_count (dir : string) (fm : GoFileMap) : nat := list_dir_count dir (GoAST.file_bindings fm).

Lemma package_summaries_find : forall fm dir,
  PM.find dir (package_summaries fm)
  = (if list_dir_mem dir (GoAST.file_bindings fm)
     then Some (mkPkgSummary (pkg_main_count dir fm)) else None).
Proof.
  intros fm dir. rewrite package_summaries_foldl, pkg_foldl_find. unfold pkg_main_count.
  rewrite PMF.empty_o. cbn [ps_count].
  destruct (list_dir_mem dir (GoAST.file_bindings fm)); [ f_equal; f_equal; lia | reflexivity ].
Qed.

(* THEOREM: every represented file contributes to its OWN parent-directory package (which is present). *)
Theorem file_in_package : forall fm path sf,
  GoAST.maps_to_file path sf fm -> PM.In (fp_parent path) (package_summaries fm).
Proof.
  intros fm path sf Hmt.
  assert (Hin : In (path, sf) (GoAST.file_bindings fm)).
  { unfold GoAST.file_bindings. apply GoAST.FMF.elements_mapsto_iff in Hmt. apply InA_alt in Hmt.
    destruct Hmt as [[k' e'] [[Hk He] Hin']]. cbn in Hk, He. subst. exact Hin'. }
  exists (mkPkgSummary (pkg_main_count (fp_parent path) fm)).
  apply PMF.find_mapsto_iff. rewrite package_summaries_find.
  assert (Hmem : list_dir_mem (fp_parent path) (GoAST.file_bindings fm) = true).
  { unfold list_dir_mem. apply existsb_exists. exists (path, sf).
    split; [ exact Hin | cbn [fst]; apply String.eqb_refl ]. }
  rewrite Hmem. reflexivity.
Qed.

(* THEOREM: no package summary exists without a file — a present [dir] is witnessed by a real file. *)
Theorem package_no_empty : forall fm dir,
  PM.In dir (package_summaries fm) ->
  exists b, In b (GoAST.file_bindings fm) /\ fp_parent (fst b) = dir.
Proof.
  intros fm dir [s Hmt]. apply PMF.find_mapsto_iff in Hmt. rewrite package_summaries_find in Hmt.
  destruct (list_dir_mem dir (GoAST.file_bindings fm)) eqn:Emem; [ | discriminate ].
  unfold list_dir_mem in Emem. apply existsb_exists in Emem. destruct Emem as [b [Hin Heq]].
  apply String.eqb_eq in Heq. exists b. split; [ exact Hin | exact Heq ].
Qed.

(* THEOREM: a package summary's main count IS the sum of [file_main_count] over its files. *)
Theorem package_summary_main_count : forall fm dir s,
  PM.MapsTo dir s (package_summaries fm) -> ps_main_count s = pkg_main_count dir fm.
Proof.
  intros fm dir s Hmt. apply PMF.find_mapsto_iff in Hmt. rewrite package_summaries_find in Hmt.
  destruct (list_dir_mem dir (GoAST.file_bindings fm)); [ | discriminate ].
  injection Hmt as <-. reflexivity.
Qed.

(* THEOREM: the empty file map yields the empty package map. *)
Theorem package_summaries_empty : forall dir,
  PM.find dir (package_summaries empty_files) = None.
Proof.
  intro dir. rewrite package_summaries_find.
  replace (GoAST.file_bindings empty_files) with (@nil (FilePath * GoSourceFile)); [ reflexivity | ].
  unfold GoAST.file_bindings, empty_files. symmetry. apply Collections.FileMapProps.elements_empty.
Qed.

(* THEOREM: map-equal file collections yield map-equal package summaries — order/structure of the
   backing tree never leaks.  Proved by the standard [fold_Equal] (the aggregation is a proper, key-transpose
   fold), so no element-list reasoning is needed. *)
Instance PM_Equal_Equiv : Equivalence (@PM.Equal PackageSummary).
Proof.
  constructor.
  - intros m k; reflexivity.
  - intros m1 m2 H k; symmetry; apply H.
  - intros m1 m2 m3 H1 H2 k; transitivity (PM.find k m2); [ apply H1 | apply H2 ].
Qed.
Lemma pkg_step_Proper : Proper (GoAST.FM.E.eq ==> eq ==> PM.Equal ==> PM.Equal) pkg_step.
Proof.
  intros k1 k2 Hk e1 e2 He a1 a2 Ha dk.
  assert (Hkk : k1 = k2) by exact Hk. subst k2. subst e2.
  unfold pkg_step, pm_add_main.
  destruct (String.eqb (fp_parent k1) dk) eqn:E.
  - apply String.eqb_eq in E. rewrite !PMF.add_eq_o by exact E. rewrite (Ha (fp_parent k1)); reflexivity.
  - apply String.eqb_neq in E. rewrite !PMF.add_neq_o by exact E. apply Ha.
Qed.
Lemma pkg_foldl_permutation : forall l1 l2 acc,
  Permutation l1 l2 -> PM.Equal (pkg_foldl l1 acc) (pkg_foldl l2 acc).
Proof.
  intros l1 l2 acc Hperm dir. rewrite !pkg_foldl_find.
  rewrite (list_dir_mem_perm dir l1 l2 Hperm), (list_dir_count_perm dir l1 l2 Hperm). reflexivity.
Qed.
Lemma pkg_step_transpose : Collections.FileMapProps.transpose_neqkey PM.Equal pkg_step.
Proof.
  intros k1 k2 e1 e2 a _.
  change (pkg_step k1 e1 (pkg_step k2 e2 a)) with (pkg_foldl ((k2, e2) :: (k1, e1) :: nil) a).
  change (pkg_step k2 e2 (pkg_step k1 e1 a)) with (pkg_foldl ((k1, e1) :: (k2, e2) :: nil) a).
  apply pkg_foldl_permutation. apply perm_swap.
Qed.
Theorem package_summaries_Equal : forall fm1 fm2,
  GoAST.FilesEqual fm1 fm2 -> PM.Equal (package_summaries fm1) (package_summaries fm2).
Proof.
  intros fm1 fm2 Heq. unfold package_summaries.
  apply (Collections.FileMapProps.fold_Equal PM_Equal_Equiv pkg_step_Proper pkg_step_transpose). exact Heq.
Qed.

(* THEOREM: reordered construction yields map-equal package summaries — a permuted node list builds a
   [FilesEqual] map, so its package aggregation is unchanged. *)
Theorem package_summaries_build_permutation : forall ms nodes1 nodes2 p1 p2,
  Permutation nodes1 nodes2 ->
  build_program ms nodes1 = Some p1 -> build_program ms nodes2 = Some p2 ->
  PM.Equal (package_summaries (prog_files p1)) (package_summaries (prog_files p2)).
Proof.
  intros ms nodes1 nodes2 p1 p2 Hperm Hb1 Hb2. apply package_summaries_Equal.
  unfold build_program in *.
  destruct (filemap_of_nodes nodes1) as [fm1|] eqn:F1; [ | discriminate ].
  destruct (filemap_of_nodes nodes2) as [fm2|] eqn:F2; [ | discriminate ].
  injection Hb1 as <-. injection Hb2 as <-. cbn [prog_files].
  exact (filemap_of_nodes_permutation nodes1 nodes2 fm1 fm2 Hperm F1 F2).
Qed.

(** ---- whole-program admissibility over the SAME program ---- *)

(* PackageRef: a VALIDATED absence anchor for package-level diagnostics.  A package spans files and is
   not one AST node, so a missing-main diagnostic anchors at a proof-backed package handle, never a fake source
   node.  Identity is the package KEY (parent-directory string); the proof field is a BOOLEAN membership
   equation (UIP over bool), so key equality determines the ref AND a PackageRef cannot name a package with no
   represented file. *)

Definition package_present_b (p : GoProgram) (key : string) : bool :=
  list_dir_mem key (GoAST.file_bindings (prog_files p)).

Record PackageRef (p : GoProgram) : Type := mkPackageRef {
  package_ref_key : string ;
  package_ref_ok  : package_present_b p package_ref_key = true
}.
Arguments package_ref_key {p} _.
Arguments package_ref_ok {p} _.

(** represented-package witness: a PackageRef's key names a real file in [p]. *)
Lemma package_ref_present : forall p (r : PackageRef p),
  exists path sf, GoAST.maps_to_file path sf (prog_files p) /\ fp_parent path = package_ref_key r.
Proof.
  intros p [k ok]; cbn. unfold package_present_b, list_dir_mem in ok.
  apply existsb_exists in ok. destruct ok as [b [Hin Heqb]]. apply String.eqb_eq in Heqb.
  exists (fst b), (snd b). split; [ | exact Heqb ].
  unfold GoAST.maps_to_file. apply GoAST.FMF.find_mapsto_iff.
  exact (GoAST.file_bindings_find (prog_files p) b Hin).
Qed.

(** identity IS key identity (the boolean proof field is irrelevant by UIP over bool — no axiom). *)
Lemma package_ref_key_inj : forall p (r1 r2 : PackageRef p),
  package_ref_key r1 = package_ref_key r2 -> r1 = r2.
Proof.
  intros p [k1 ok1] [k2 ok2] Heq; cbn in Heq; subst k2.
  f_equal. apply (Eqdep_dec.UIP_dec Bool.bool_dec).
Qed.

Definition package_ref_eq_dec : forall p (r1 r2 : PackageRef p), {r1 = r2} + {r1 <> r2}.
Proof.
  intros p r1 r2. destruct (string_dec (package_ref_key r1) (package_ref_key r2)) as [He|Hne].
  - left. apply package_ref_key_inj; exact He.
  - right. intro H; apply Hne; rewrite H; reflexivity.
Defined.

(** construction from a real file binding: its package (parent directory) is present (the binding witnesses it). *)
Definition package_ref_of_binding (p : GoProgram) (b : FilePath * GoSourceFile)
  (Hin : In b (GoAST.file_bindings (prog_files p))) : PackageRef p.
Proof.
  refine (mkPackageRef p (fp_parent (fst b)) _).
  unfold package_present_b, list_dir_mem. apply existsb_exists.
  exists b. split; [ exact Hin | apply String.eqb_refl ].
Defined.

Lemma package_ref_of_binding_key : forall p b Hin,
  package_ref_key (package_ref_of_binding p b Hin) = fp_parent (fst b).
Proof. reflexivity. Qed.

(** construction from a validated file reference: the ref's own path witnesses its package. *)
Definition package_ref_of_fileref {p} (fr : GoIndex.Snap.FileRef p) : PackageRef p.
Proof.
  refine (mkPackageRef p (fp_parent (GoIndex.Snap.file_ref_path fr)) _).
  unfold package_present_b, list_dir_mem. apply existsb_exists.
  exists (GoIndex.Snap.file_ref_path fr, GoIndex.Snap.file_ref_source fr). split.
  - apply GoAST.find_file_bindings.
    apply (GoIndex.Snap.file_of_path_source_exact p (GoIndex.Snap.file_ref_path fr) fr).
    apply GoIndex.Snap.file_of_path_complete.
  - apply String.eqb_refl.
Defined.

Lemma package_ref_of_fileref_key : forall p (fr : GoIndex.Snap.FileRef p),
  package_ref_key (package_ref_of_fileref fr) = fp_parent (GoIndex.Snap.file_ref_path fr).
Proof. reflexivity. Qed.

(* the structured diagnostic core.  Every anchor is an EXACT-SNAPSHOT handle (a NodeRef / FileRef /
   PackageRef of [p], or the whole program); the four current diagnostic reasons carry TYPED references
   (ExprRef / DeclRef) and structured values, so an invalid anchor/category combination is unrepresentable.
   The core carries codes + valid anchors + structured values — NO authoritative English prose (a pure report
   projection produces readable text later). *)

Inductive DiagnosticAnchor (p : GoProgram) : Type :=
| AtNode    : GoIndex.Snap.NodeRef p -> DiagnosticAnchor p
| AtFile    : GoIndex.Snap.FileRef p -> DiagnosticAnchor p
| AtPackage : PackageRef p -> DiagnosticAnchor p
| AtProgram : DiagnosticAnchor p.
Arguments AtNode {p} _.  Arguments AtFile {p} _.  Arguments AtPackage {p} _.  Arguments AtProgram {p}.

(* the four current diagnostic reasons.  Nested invalid conversions: [primary] is the INNERMOST failing
   conversion, [outer_context] the enclosing conversions (nearest first).  Duplicate main: [later_primary]
   the later declaration, [earlier_related] the first (canonical-order) main. *)
Inductive DiagnosticReason (p : GoProgram) : Type :=
| DRInvalidConversion
    (primary : GoIndex.ExprRef p) (target_ref : GoIndex.TypeNameRef p) (operand_ref : GoIndex.ExprRef p)
    (outer_context : list (GoIndex.ExprRef p))
    (target : GoType) (operand_status : ConstInfo)
| DRDefaultNotRepresentable
    (primary : GoIndex.ExprRef p) (exact_constant : GoConst) (default_target : GoType)
| DRMainRedeclared
    (later_primary : GoIndex.DeclRef p) (earlier_related : GoIndex.DeclRef p)
| DRMissingMainEntry
    (package_primary : PackageRef p)
(* the fresh-build cmd/go COMMAND-level failure: a sole selected main package whose default
   executable name is an existing root DIRECTORY.  Anchored at the sole [PackageRef]; carries the exact default
   output name.  This is NOT a source/typing/package-count reason — it is a build-OUTPUT-planning reason. *)
| DRBuildOutputIsDirectory
    (package_primary : PackageRef p) (output_name : string).
Arguments DRInvalidConversion {p} _ _ _ _ _ _.  Arguments DRDefaultNotRepresentable {p} _ _ _.
Arguments DRMainRedeclared {p} _ _.  Arguments DRMissingMainEntry {p} _.  Arguments DRBuildOutputIsDirectory {p} _ _.

Inductive DiagnosticCode : Type :=
| DCInvalidConversion | DCDefaultNotRepresentable | DCMainRedeclared | DCMissingMainEntry | DCBuildOutputIsDirectory.

Definition diagnostic_code {p} (d : DiagnosticReason p) : DiagnosticCode :=
  match d with
  | DRInvalidConversion _ _ _ _ _ _ => DCInvalidConversion
  | DRDefaultNotRepresentable _ _ _ => DCDefaultNotRepresentable
  | DRMainRedeclared _ _           => DCMainRedeclared
  | DRMissingMainEntry _               => DCMissingMainEntry
  | DRBuildOutputIsDirectory _ _  => DCBuildOutputIsDirectory
  end.

Definition diagnostic_primary {p} (d : DiagnosticReason p) : DiagnosticAnchor p :=
  match d with
  | DRInvalidConversion pr _ _ _ _ _  => AtNode (GoIndex.erase_ref pr)
  | DRDefaultNotRepresentable pr _ _  => AtNode (GoIndex.erase_ref pr)
  | DRMainRedeclared later _           => AtNode (GoIndex.erase_ref later)
  | DRMissingMainEntry pk                  => AtPackage pk
  | DRBuildOutputIsDirectory pk _     => AtPackage pk
  end.

Definition diagnostic_related {p} (d : DiagnosticReason p) : list (DiagnosticAnchor p) :=
  match d with
  | DRInvalidConversion _ _ _ outer _ _ => map (fun r => AtNode (GoIndex.erase_ref r)) outer
  | DRDefaultNotRepresentable _ _ _   => []
  | DRMainRedeclared _ earlier         => [AtNode (GoIndex.erase_ref earlier)]
  | DRMissingMainEntry _                   => []
  | DRBuildOutputIsDirectory _ _      => []
  end.

(** the primary anchor is always an exact-snapshot handle whose CODE matches the reason. *)
Lemma diagnostic_code_primary_consistent : forall p (d : DiagnosticReason p),
  match diagnostic_code d, diagnostic_primary d with
  | DCMissingMainEntry, AtPackage _ | DCBuildOutputIsDirectory, AtPackage _ => True
  | DCInvalidConversion, AtNode _ | DCDefaultNotRepresentable, AtNode _ | DCMainRedeclared, AtNode _ => True
  | _, _ => False
  end.
Proof. intros p [pr tr o t s|pr c dt|l e|pk|pk nm]; cbn; exact I. Qed.

(* ERASED cross-snapshot reports.  A [DiagnosticReason p] is indexed by the snapshot [p], so
   two snapshots' diagnostics have DIFFERENT dependent types.  [erase_diagnostic] projects a reason to a
   snapshot-INDEPENDENT [ErasedDiagnostic] (code + erased anchors carrying only NodeKey / FilePath /
   package-string identity + a STABLE payload — the conversion/default-target [GoType] AND the retained SOURCE
   type-name spelling ([erased_source_target], so [byte] and [uint8] reports stay distinguishable)), so reports
   from two snapshots are compared by plain [=] on erased values, never an unsafe dependent transport.  The exact
   source expression stays reachable through the original typed anchor WHILE inside one [p]. *)

Inductive ErasedAnchor : Type :=
| EANode    : GoIndex.NodeKey -> ErasedAnchor
| EAFile    : FilePath -> ErasedAnchor
| EAPackage : string -> ErasedAnchor
| EAProgram : ErasedAnchor.

Definition erase_anchor {p} (a : DiagnosticAnchor p) : ErasedAnchor :=
  match a with
  | AtNode r     => EANode (GoIndex.Snap.node_ref_key r)
  | AtFile fr    => EAFile (GoIndex.Snap.file_ref_path fr)
  | AtPackage pk => EAPackage (package_ref_key pk)
  | AtProgram    => EAProgram
  end.

Record ErasedDiagnostic : Type := mkErasedDiagnostic {
  ed_code    : DiagnosticCode ;
  ed_primary : ErasedAnchor ;
  ed_related : list ErasedAnchor ;
  ed_target  : option GoType ;
  (* the STABLE build-OUTPUT payload: the exact planned default executable NAME for a
     [DRBuildOutputIsDirectory] reason (the directory the fresh-image `go build` output would collide with),
     [None] for every other reason.  Carried across snapshots so two erased build-output reports for DIFFERENT
     collision names compare UNEQUAL. *)
  ed_output  : option string ;
  (* §4 the STABLE SOURCE-TARGET payload of an invalid conversion: the exact source [TypeSyntax] recovered
     THROUGH the retained target [TypeNameRef] (never reverse-mapped from the resolved [GoType]), so an invalid
     [byte(...)] and an invalid [uint8(...)] — same resolved [ed_target = uint8] — erase to DIFFERENT source
     targets (byte vs uint8) and compare UNEQUAL; [None] for every non-conversion reason. *)
  ed_source_target : option GoAST.TypeSyntax
}.

(* the STABLE erased payload: the conversion TARGET / default target [GoType] where the reason carries one —
   NO source expression (the exact operand stays reachable through the typed anchor inside one [p]). *)
Definition erased_target {p} (d : DiagnosticReason p) : option GoType :=
  match d with
  | DRInvalidConversion _ _ _ _ t _  => Some t
  | DRDefaultNotRepresentable _ _ dt => Some dt
  | DRMainRedeclared _ _              => None
  | DRMissingMainEntry _                  => None
  | DRBuildOutputIsDirectory _ _     => None
  end.

(* the erased build-output NAME payload: the sole [DRBuildOutputIsDirectory] reason carries the exact planned
   default executable name; every other reason carries none. *)
Definition erased_output {p} (d : DiagnosticReason p) : option string :=
  match d with
  | DRInvalidConversion _ _ _ _ _ _  => None
  | DRDefaultNotRepresentable _ _ _  => None
  | DRMainRedeclared _ _              => None
  | DRMissingMainEntry _                  => None
  | DRBuildOutputIsDirectory _ nm    => Some nm
  end.

(* the STABLE erased SOURCE-TARGET payload, derived THROUGH the retained target [TypeNameRef]
   ([type_name_ref_syntax] recovers the exact raw spelling from the reference) — NOT reverse-mapped from the
   resolved [GoType].  [None] for every non-conversion reason. *)
Definition erased_source_target {p} (d : DiagnosticReason p) : option GoAST.TypeSyntax :=
  match d with
  | DRInvalidConversion _ tr _ _ _ _ => GoIndex.type_name_ref_syntax tr
  | _ => None
  end.

Definition erase_diagnostic {p} (d : DiagnosticReason p) : ErasedDiagnostic :=
  mkErasedDiagnostic (diagnostic_code d) (erase_anchor (diagnostic_primary d))
    (map erase_anchor (diagnostic_related d)) (erased_target d) (erased_output d) (erased_source_target d).

(* intra-snapshot preservation: erasing keeps the CODE, the primary anchor's KEY identity, and the related
   anchors AS A MAP (so their canonical order is preserved). *)
Lemma erase_diagnostic_code {p} (d : DiagnosticReason p) : ed_code (erase_diagnostic d) = diagnostic_code d.
Proof. reflexivity. Qed.

Lemma erase_diagnostic_primary {p} (d : DiagnosticReason p) :
  ed_primary (erase_diagnostic d) = erase_anchor (diagnostic_primary d).
Proof. reflexivity. Qed.

Lemma erase_diagnostic_related {p} (d : DiagnosticReason p) :
  ed_related (erase_diagnostic d) = map erase_anchor (diagnostic_related d).
Proof. reflexivity. Qed.

Lemma erase_diagnostic_related_length {p} (d : DiagnosticReason p) :
  length (ed_related (erase_diagnostic d)) = length (diagnostic_related d).
Proof.
  cbn [ed_related erase_diagnostic].
  induction (diagnostic_related d) as [|x xs IH]; cbn [map length]; [ reflexivity | rewrite IH; reflexivity ].
Qed.

Lemma erase_diagnostic_output {p} (d : DiagnosticReason p) :
  ed_output (erase_diagnostic d) = erased_output d.
Proof. reflexivity. Qed.

(* the erased build-output NAME is present EXACTLY for a build-output-directory reason (and then it is the
   reason's exact planned output name) — so the erased report retains the collision name it must, and drops it
   everywhere else. *)
Lemma erased_output_iff_build_output {p} (d : DiagnosticReason p) :
  (exists nm, ed_output (erase_diagnostic d) = Some nm) <-> diagnostic_code d = DCBuildOutputIsDirectory.
Proof. destruct d; cbn; split; try (intros [nm H]; discriminate); try discriminate; eauto. Qed.

(* occurrence-keyed expression facts.  ONE fact value per expression occurrence: its exact constant
   status ([const_info]) plus, ONLY for a use-context (println-argument) occurrence, its resolved constant
   ([resolve_expr_const UsePrintlnArg]).  Type and resolved exact value are PROJECTIONS from the one
   [ResolvedConst] — no parallel type map that could disagree.  Facts store semantic values only (never a
   GoExpr / SourceOccurrence / rewritten syntax). *)

Record ExprFact : Type := mkExprFact {
  ef_const_status : ConstInfo ;
  ef_use_resolved : option ResolvedConst
}.

Definition resolved_type_at (f : ExprFact) : option GoType :=
  option_map resolved_const_type (ef_use_resolved f).
Definition resolved_constant_at (f : ExprFact) : option GoConst :=
  option_map resolved_const_exact (ef_use_resolved f).

(** the use-context resolution an occurrence carries: [Some rc] EXACTLY for a println-argument expression that
    resolves, else [None] (a conversion operand / internal expression, or a non-resolving argument). *)
Definition occ_use_resolved (o : GoIndex.SourceOccurrence) : option ResolvedConst :=
  match GoIndex.occurrence_role o with
  | GoIndex.RPrintlnArg _ =>
      match GoIndex.view_expr o with Some e => resolve_expr_const UsePrintlnArg e | None => None end
  | _ => None
  end.

(** §3.5 use-context resolution from the ALREADY-COMPUTED status: a println-argument's stored [ConstInfo] is
    resolved through [resolve_const_info] + [use_allowsb] (NEVER a raw-expression rescan — this touches only the
    role and the given [ci], not the [GoExpr]).  Production fills [ef_use_resolved] with THIS, so it never calls
    [const_info]/[resolve_expr_const] a second time; [use_resolved_of_ci_eq] proves it agrees with the
    [occ_use_resolved] specification when [ci] is the occurrence's status. *)
Definition use_resolved_of_ci (role : GoIndex.NodeRole) (ci : ConstInfo) : option ResolvedConst :=
  match role with
  | GoIndex.RPrintlnArg _ =>
      match resolve_const_info ci with
      | Some rc => if use_allowsb UsePrintlnArg (resolved_const_type rc) then Some rc else None
      | None => None
      end
  | _ => None
  end.

Lemma use_resolved_of_ci_eq : forall o e ci,
  GoIndex.view_expr o = Some e -> const_info e = Some ci ->
  use_resolved_of_ci (GoIndex.occurrence_role o) ci = occ_use_resolved o.
Proof.
  intros o e ci Hv Hc. unfold use_resolved_of_ci, occ_use_resolved.
  destruct (GoIndex.occurrence_role o) as [ | | ai | si | ain | | ]; try reflexivity.
  rewrite Hv. unfold resolve_expr_const. rewrite Hc. reflexivity.
Qed.

(** the fact of a single occurrence: [Some] exactly for an expression occurrence whose [const_info] succeeds. *)
Definition occ_expr_fact (o : GoIndex.SourceOccurrence) : option ExprFact :=
  match GoIndex.view_expr o with
  | Some e => match const_info e with
              | Some ci => Some (mkExprFact ci (occ_use_resolved o))
              | None => None
              end
  | None => None
  end.

(** an occurrence has a fact IFF it is an expression whose const_info succeeds; the fact's status is exactly
    that [const_info], and its resolved field is exactly the occurrence's use-context resolution. *)
Lemma occ_expr_fact_status : forall o e ci,
  GoIndex.view_expr o = Some e -> const_info e = Some ci ->
  occ_expr_fact o = Some (mkExprFact ci (occ_use_resolved o)).
Proof. intros o e ci Hv Hc. unfold occ_expr_fact. rewrite Hv, Hc. reflexivity. Qed.

Lemma occ_expr_fact_none_nonexpr : forall o,
  GoIndex.view_expr o = None -> occ_expr_fact o = None.
Proof. intros o Hv. unfold occ_expr_fact. rewrite Hv. reflexivity. Qed.

(** ---- §3.4/§3.6 the ONE production expression outcome authority (indexed by the snapshot [p], so its failure
    evidence carries RETAINED TYPED REFERENCES): bottom-up, a conversion reads its target [TypeNameFact] (through
    the retained target [TypeNameRef]) + its operand's already-computed outcome (through the retained operand
    [ExprRef]) and calls [convert_const] ONCE, storing SUCCESS (the expression fact), a LOCAL invalid conversion
    (the exact conversion / target / operand refs + resolved target + operand status — no second [convert_const],
    no diagnostic re-mint), or BLOCKED-BY-CHILD (the operand's own outcome was a real non-success). ---- *)
Inductive ExprOutcome (p : GoProgram) : Type :=
  | EOOk       : ExprFact -> ExprOutcome p                 (* a leaf or a successful conversion *)
  | EOConvFail : GoIndex.ExprRef p -> GoIndex.TypeNameRef p -> GoIndex.ExprRef p -> GoType -> ConstInfo -> ExprOutcome p
      (* a LOCAL invalid conversion: the conversion ExprRef, its target TypeNameRef, its operand ExprRef,
         the resolved target GoType (from the stored TypeNameFact), and the operand status (from the operand fact) *)
  | EOChildFail : ExprOutcome p.                           (* blocked: the operand's outcome was a real non-success *)
Arguments EOOk {p} _.  Arguments EOConvFail {p} _ _ _ _ _.  Arguments EOChildFail {p}.

(** the per-file expression-fact map: fold the visit stream, keying each occurrence's fact by its NodeKey.
    Non-expression / const_info-failed occurrences contribute nothing.  Because [visit_file] keys are DISTINCT
    (NoDup), the fold never overwrites, and the stored fact at each ref's key is EXACTLY that occurrence's fact. *)
Definition add_occ_fact {p} (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)
    (m : GoIndex.NodeKeyMapBase.t ExprFact) : GoIndex.NodeKeyMapBase.t ExprFact :=
  match occ_expr_fact (snd ro) with
  | Some f => GoIndex.NodeKeyMapBase.add (GoIndex.Snap.node_ref_key (fst ro)) f m
  | None => m
  end.

Lemma NoDup_map_inj {A B} (f : A -> B) (l : list A) :
  (forall x y, f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros Hinj H. induction H as [|x l Hx Hnd IH]; simpl; constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Hfy Hiny]]. apply Hinj in Hfy. subst y. contradiction.
  - exact IH.
Qed.

(** the [visit_file] refs have DISTINCT NodeKeys (same file, distinct local ids). *)
Lemma visit_file_key_nodup {p} (fr : GoIndex.Snap.FileRef p) :
  NoDup (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) (GoIndex.Snap.visit_file fr)).
Proof.
  assert (Hmap : map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) (GoIndex.Snap.visit_file fr)
    = map (fun ro => GoIndex.mkKey (GoIndex.Snap.file_ref_path fr) (GoIndex.Snap.node_ref_local (fst ro)))
          (GoIndex.Snap.visit_file fr)).
  { apply map_ext_in. intros [r occ] Hin. cbn [fst]. rewrite GoIndex.Snap.node_ref_key_eq.
    destruct (GoIndex.Snap.visit_file_view p fr r occ Hin) as [_ Hf]. rewrite Hf. reflexivity. }
  rewrite Hmap, <- (map_map (fun ro => GoIndex.Snap.node_ref_local (fst ro))
                            (GoIndex.mkKey (GoIndex.Snap.file_ref_path fr))).
  apply NoDup_map_inj; [ intros x y H; injection H as H; exact H | apply GoIndex.Snap.visit_file_nodup ].
Qed.

Lemma facts_not_in_domain {p} (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) (k : GoIndex.NodeKey) :
  ~ In k (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) l) ->
  GoIndex.NodeKeyMapBase.find k (fold_right add_occ_fact (GoIndex.NodeKeyMapBase.empty ExprFact) l) = None.
Proof.
  induction l as [|[r0 occ0] rest IH]; intros Hni; simpl.
  - apply GoIndex.NodeKeyMapFacts.empty_o.
  - simpl in Hni.
    assert (Hne : GoIndex.Snap.node_ref_key r0 <> k) by (intro H; apply Hni; left; exact H).
    assert (Hrest : ~ In k (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) rest))
      by (intro H; apply Hni; right; exact H).
    unfold add_occ_fact; cbn [snd fst]. destruct (occ_expr_fact occ0) as [f|].
    + rewrite GoIndex.nodekeymap_add_neq by exact Hne. exact (IH Hrest).
    + exact (IH Hrest).
Qed.

Lemma fold_facts_find {p} (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) r occ :
  NoDup (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) l) ->
  In (r, occ) l ->
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key r)
    (fold_right add_occ_fact (GoIndex.NodeKeyMapBase.empty ExprFact) l) = occ_expr_fact occ.
Proof.
  induction l as [|[r0 occ0] rest IH]; intros Hnd Hin; [ destruct Hin |].
  simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hni Hnd'].
  simpl. destruct Hin as [Heq | Hin].
  - injection Heq as <- <-. unfold add_occ_fact; cbn [snd fst].
    destruct (occ_expr_fact occ0) as [f|] eqn:Ef.
    + rewrite GoIndex.nodekeymap_add_eq. reflexivity.
    + apply facts_not_in_domain. exact Hni.
  - assert (Hin' : In (GoIndex.Snap.node_ref_key r)
             (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) rest)).
    { apply in_map_iff. exists (r, occ). split; [reflexivity | exact Hin]. }
    assert (Hkr : GoIndex.Snap.node_ref_key r <> GoIndex.Snap.node_ref_key r0)
      by (intro Hk; apply Hni; rewrite <- Hk; exact Hin').
    unfold add_occ_fact; cbn [snd fst]. destruct (occ_expr_fact occ0) as [f0|].
    + rewrite GoIndex.nodekeymap_add_neq by (intro Hk; apply Hkr; symmetry; exact Hk).
      exact (IH Hnd' Hin).
    + exact (IH Hnd' Hin).
Qed.


(* ---- program-wide visit stream + fact map (lifted to the whole program) ---- *)

Lemma map_flat_map {A B C} (f : B -> C) (g : A -> list B) (l : list A) :
  map f (flat_map g l) = flat_map (fun x => map f (g x)) l.
Proof. induction l as [|a l IH]; simpl; [reflexivity | rewrite map_app, IH; reflexivity]. Qed.

Lemma nodup_app {A} (l1 l2 : list A) :
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> NoDup (l1 ++ l2).
Proof.
  induction l1 as [|a l1 IH]; simpl; intros H1 H2 Hd; [exact H2|].
  inversion H1 as [|? ? Hni Hnd]; subst. constructor.
  - rewrite in_app_iff. intros [Hin|Hin]; [ apply Hni; exact Hin | apply (Hd a); [left; reflexivity | exact Hin] ].
  - apply IH; [ exact Hnd | exact H2 | intros x Hx; apply Hd; right; exact Hx ].
Qed.

Lemma nodup_flat_map_tag {A B T} (g : A -> list B) (tag : B -> T) (key : A -> T) (l : list A) :
  (forall a, In a l -> NoDup (g a)) ->
  (forall a b, In a l -> In b (g a) -> tag b = key a) ->
  NoDup (map key l) ->
  NoDup (flat_map g l).
Proof.
  induction l as [|a l IH]; simpl; intros Hnd Htag Hkey; [constructor|].
  inversion Hkey as [|? ? Hni Hkey' Heq]; subst.
  apply nodup_app.
  - apply Hnd; left; reflexivity.
  - apply IH; [ intros a' Ha'; apply Hnd; right; exact Ha'
              | intros a' b Ha' Hb; apply (Htag a' b); [right; exact Ha' | exact Hb]
              | exact Hkey' ].
  - intros x Hx1 Hx2.
    assert (Htx : tag x = key a) by (apply (Htag a x); [left; reflexivity | exact Hx1]).
    apply in_flat_map in Hx2. destruct Hx2 as [a' [Ha' Hb']].
    assert (Htx' : tag x = key a') by (apply (Htag a' x); [right; exact Ha' | exact Hb']).
    apply Hni. assert (Hka : key a = key a') by (rewrite <- Htx; exact Htx').
    rewrite Hka. apply in_map; exact Ha'.
Qed.

(** the visit stream of one file binding (empty for an unminted path — unreachable for a real binding). *)
Definition binding_visit (p : GoProgram) (b : FilePath * GoSourceFile)
  : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) :=
  match GoIndex.Snap.file_of_path p (fst b) with
  | Some fr => GoIndex.Snap.visit_file fr
  | None => []
  end.

(** the RETAINED per-file visit blocks: each file's stream, visited ONCE, in canonical FileMap path order.
    [elaborate_indexed] retains this and derives BOTH the flattened elaboration stream ([prog_visit] = [concat])
    AND the enclosing-context annotations ([annotate_program]) from it — one [Snap.visit_file] per file. *)
Definition prog_blocks (p : GoProgram) : list (list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) :=
  map (binding_visit p) (GoAST.file_bindings (prog_files p)).

(** the WHOLE-PROGRAM visit stream: the retained blocks flattened (each file visited once, path order). *)
Definition prog_visit (p : GoProgram) : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) :=
  concat (prog_blocks p).

(** the flattened stream IS the per-binding flat_map (used by the existing membership/fold proofs). *)
Lemma prog_visit_flat_map (p : GoProgram) :
  prog_visit p = flat_map (binding_visit p) (GoAST.file_bindings (prog_files p)).
Proof. unfold prog_visit, prog_blocks. rewrite flat_map_concat_map. reflexivity. Qed.

(** every visited pair's occurrence IS its reference's own source occurrence (the visit delivers each node
    paired with [source_occurrence_of_ref]); so a visited [(r, occ)] has [occ = source_occurrence_of_ref r]. *)
Lemma prog_visit_occ_is_source (p : GoProgram) (r : GoIndex.Snap.NodeRef p) occ :
  In (r, occ) (prog_visit p) -> occ = GoIndex.Snap.source_occurrence_of_ref r.
Proof.
  intro Hin. rewrite prog_visit_flat_map in Hin. apply in_flat_map in Hin. destruct Hin as [b [_ Hrb]].
  unfold binding_visit in Hrb. destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|]; [|destruct Hrb].
  destruct (GoIndex.Snap.visit_file_view p fr r occ Hrb) as [Ho _]. exact Ho.
Qed.

(** a visited EXPRESSION occurrence's reference refines: [as_expr] succeeds and erases back to [r]. *)
Lemma prog_visit_as_expr (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p) (r : GoIndex.Snap.NodeRef p) occ e :
  In (r, occ) (prog_visit p) -> GoIndex.view_expr occ = Some e ->
  exists er, GoIndex.as_expr idx r = Some er /\ GoIndex.erase_ref er = r.
Proof.
  intros Hin Hv. rewrite (prog_visit_occ_is_source p r occ Hin) in Hv.
  assert (Hk : GoIndex.Snap.node_kind idx r = GoIndex.KExpression)
    by (rewrite (GoIndex.Snap.node_kind_matches_source p idx r); exact (GoIndex.view_expr_kind _ e Hv)).
  destruct (GoIndex.as_kind_complete idx r GoIndex.KExpression Hk) as [er [Hae Her]].
  exists er. split; [ exact Hae | exact Her ].
Qed.

(** every key in one binding's block has that binding's path (used for cross-file disjointness). *)
Lemma binding_visit_key_file : forall p b k,
  In k (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) (binding_visit p b)) ->
  GoIndex.nk_file k = fst b.
Proof.
  intros p b k Hin. unfold binding_visit in Hin.
  destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|] eqn:Ef; [| destruct Hin].
  apply in_map_iff in Hin. destruct Hin as [[r occ] [Hk Hin]]. cbn [fst] in Hk. subst k.
  rewrite GoIndex.Snap.node_ref_key_eq. cbn [GoIndex.nk_file].
  destruct (GoIndex.Snap.visit_file_view p fr r occ Hin) as [_ Hf]. rewrite Hf.
  exact (GoIndex.Snap.file_of_path_sound p (fst b) fr Ef).
Qed.

(** program-wide keys are DISTINCT: distinct locals within a file, distinct paths across files. *)
Lemma prog_visit_key_nodup (p : GoProgram) :
  NoDup (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) (prog_visit p)).
Proof.
  rewrite prog_visit_flat_map, map_flat_map.
  apply (nodup_flat_map_tag
           (fun b => map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) (binding_visit p b))
           GoIndex.nk_file (fun b => fst b) (GoAST.file_bindings (prog_files p))).
  - intros b _. unfold binding_visit.
    destruct (GoIndex.Snap.file_of_path p (fst b)); [ apply visit_file_key_nodup | constructor ].
  - intros b k _ Hin. exact (binding_visit_key_file p b k Hin).
  - apply GoAST.file_bindings_nodup_keys.
Qed.

(* [prog_expr_facts] is the source-determined SPECIFICATION ([add_occ_fact] per node); the production fact map
   [phase_expr_facts] is a TOTAL PROJECTION of the retained [ExprOutcomeTable] (extract each occurrence's [EOOk]
   fact via [total_outcome_at] — no per-occurrence [const_info] rescan), proved EQUAL to this specification by
   [phase_expr_facts_eq_spec]. *)


(* the ONE expression-outcome authority is the proof-carrying [ExprOutcomeTable] ([build_outcome_table] wrapping
   the bottom-up [build_outcomes] fold over the retained [CompilationInput]'s visit, paired with its
   completeness proof [eot_ok]) and CONSUMING the once-built [TypeNameFactTable] object; every production
   expression fact AND every conversion diagnostic PROJECTS this single table by the TOTAL [total_outcome_at]
   query, never a second [const_info]/[convert_const] pass and never a fail-open [find]. *)

(* ---- OPERAND ADJACENCY: a conversion occurrence at [me] has its TYPE-NAME occurrence at [Pos.succ me] and its
   operand occurrence at [Pos.succ (Pos.succ me)] (the two-child conversion layout: target type name, then
   operand subtree).  This adjacency is what lets [conversion_target_ref] / [conversion_operand_ref] MINT the
   conversion's target [TypeNameRef] and operand [ExprRef] THROUGH the retained index; the bottom-up accumulator
   then reads the operand's ALREADY-COMPUTED outcome from the processed suffix — no [const_info] rescan. ---- *)

Lemma occs_expr_head_ex : forall e parent role start,
  exists occ, In (start, occ) (GoIndex.occs_expr parent role start e) /\ GoIndex.view_expr occ = Some e.
Proof. intros e parent role start; destruct e; cbn [GoIndex.occs_expr]; eexists; (split; [left; reflexivity|reflexivity]). Qed.

(* the HEAD of [occs_expr parent role start e] additionally carries EXACTLY the passed [role] (so a conversion's
   operand subtree head — built with [RConversionOperand] — has that role). *)
Lemma occs_expr_head_role : forall e parent role start,
  exists occ, In (start, occ) (GoIndex.occs_expr parent role start e)
    /\ GoIndex.view_expr occ = Some e /\ GoIndex.occurrence_role occ = role.
Proof.
  intros e parent role start; destruct e; cbn [GoIndex.occs_expr]; eexists;
    (split; [left; reflexivity | split; [reflexivity | cbn [GoIndex.occurrence_role]; reflexivity]]).
Qed.

Lemma occs_expr_operand : forall e parent role start me occ ce x,
  In (me, occ) (GoIndex.occs_expr parent role start e) ->
  GoIndex.view_expr occ = Some ce -> expr_child ce = Some x ->
  exists occ', In (Pos.succ (Pos.succ me), occ') (GoIndex.occs_expr parent role start e)
    /\ GoIndex.view_expr occ' = Some x /\ GoIndex.occurrence_role occ' = GoIndex.RConversionOperand.
Proof.
  induction e as [ b|n1|n2|s| df | dcx | ts y IHy ]; intros parent role start me occ ce x Hin Hv Hc.
  (* leaves: the only occurrence is the leaf, whose view has no expr_child *)
  1,2,3,4,5,6: cbn [GoIndex.occs_expr] in Hin; destruct Hin as [Heq|Hf]; [| destruct Hf];
               injection Heq as <- <-; cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv;
               injection Hv as Hce; subst ce; cbn [expr_child] in Hc; discriminate Hc.
  (* conversion: [(start, conv)], then the type-name occurrence at [Pos.succ start] (view = None, discriminated),
     then the operand subtree from [Pos.succ (Pos.succ start)] (IH).  The operand is TWO past the conversion. *)
  cbn [GoIndex.occs_expr] in Hin. destruct Hin as [Heq|Hin].
  - injection Heq as Hid Hocc; rewrite <- Hid; rewrite <- Hocc in Hv;
    cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv; injection Hv as Hce; subst ce;
    cbn [expr_child] in Hc; injection Hc as Hx; subst x.
    destruct (occs_expr_head_role y start GoIndex.RConversionOperand (Pos.succ (Pos.succ start)))
      as [occ' [Hin' [Hv' Hr']]].
    exists occ'; split; [right; right; exact Hin' | split; [exact Hv' | exact Hr']].
  - destruct Hin as [Heq|Hin].
    + (* the type-name occurrence has no expression view *)
      injection Heq as <- <-; cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv; discriminate Hv.
    + destruct (IHy start GoIndex.RConversionOperand (Pos.succ (Pos.succ start)) me occ ce x Hin Hv Hc)
        as [occ' [Hin' [Hv' Hr']]].
      exists occ'; split; [right; right; exact Hin' | split; [exact Hv' | exact Hr']].
Qed.

Lemma in_app_operand {L1 L2 : list (positive * GoIndex.SourceOccurrence)} me occ x :
  (forall M O ce X, In (M, O) L1 -> GoIndex.view_expr O = Some ce -> expr_child ce = Some X ->
     exists O', In (Pos.succ (Pos.succ M), O') L1 /\ GoIndex.view_expr O' = Some X /\ GoIndex.occurrence_role O' = GoIndex.RConversionOperand) ->
  (forall M O ce X, In (M, O) L2 -> GoIndex.view_expr O = Some ce -> expr_child ce = Some X ->
     exists O', In (Pos.succ (Pos.succ M), O') L2 /\ GoIndex.view_expr O' = Some X /\ GoIndex.occurrence_role O' = GoIndex.RConversionOperand) ->
  forall ce, In (me, occ) (L1 ++ L2) -> GoIndex.view_expr occ = Some ce -> expr_child ce = Some x ->
  exists occ', In (Pos.succ (Pos.succ me), occ') (L1 ++ L2) /\ GoIndex.view_expr occ' = Some x /\ GoIndex.occurrence_role occ' = GoIndex.RConversionOperand.
Proof.
  intros H1 H2 ce Hin Hv Hc. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - destruct (H1 me occ ce x Hin Hv Hc) as [occ' [Hin' Hv']]. exists occ'. split; [apply in_or_app; left; exact Hin' | exact Hv'].
  - destruct (H2 me occ ce x Hin Hv Hc) as [occ' [Hin' Hv']]. exists occ'. split; [apply in_or_app; right; exact Hin' | exact Hv'].
Qed.

Lemma occs_args_operand : forall es parent aidx start me occ ce x,
  In (me, occ) (GoIndex.occs_args parent aidx start es) ->
  GoIndex.view_expr occ = Some ce -> expr_child ce = Some x ->
  exists occ', In (Pos.succ (Pos.succ me), occ') (GoIndex.occs_args parent aidx start es) /\ GoIndex.view_expr occ' = Some x /\ GoIndex.occurrence_role occ' = GoIndex.RConversionOperand.
Proof.
  induction es as [|e rest IH]; intros parent aidx start me occ ce x Hin Hv Hc; cbn [GoIndex.occs_args] in *; [destruct Hin|].
  eapply in_app_operand; [ | | exact Hin | exact Hv | exact Hc ].
  - intros M O ce0 X HinM HvM HcM. unfold GoIndex.occs_arg. eapply occs_expr_operand; eauto.
  - intros M O ce0 X HinM HvM HcM. eapply IH; eauto.
Qed.

Lemma occs_stmt_operand : forall s parent sidx start me occ ce x,
  In (me, occ) (GoIndex.occs_stmt parent sidx start s) ->
  GoIndex.view_expr occ = Some ce -> expr_child ce = Some x ->
  exists occ', In (Pos.succ (Pos.succ me), occ') (GoIndex.occs_stmt parent sidx start s) /\ GoIndex.view_expr occ' = Some x /\ GoIndex.occurrence_role occ' = GoIndex.RConversionOperand.
Proof.
  intros [args] parent sidx start me occ ce x Hin Hv Hc. cbn [GoIndex.occs_stmt] in *.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv. discriminate Hv.
  - destruct (occs_args_operand args start 0 (Pos.succ start) me occ ce x Hin Hv Hc) as [occ' [Hin' Hv']].
    exists occ'. split; [right; exact Hin' | exact Hv'].
Qed.

Lemma occs_stmts_operand : forall ss parent sidx start me occ ce x,
  In (me, occ) (GoIndex.occs_stmts parent sidx start ss) ->
  GoIndex.view_expr occ = Some ce -> expr_child ce = Some x ->
  exists occ', In (Pos.succ (Pos.succ me), occ') (GoIndex.occs_stmts parent sidx start ss) /\ GoIndex.view_expr occ' = Some x /\ GoIndex.occurrence_role occ' = GoIndex.RConversionOperand.
Proof.
  induction ss as [|s rest IH]; intros parent sidx start me occ ce x Hin Hv Hc; cbn [GoIndex.occs_stmts] in *; [destruct Hin|].
  eapply in_app_operand; [ | | exact Hin | exact Hv | exact Hc ].
  - intros M O ce0 X HinM HvM HcM. eapply occs_stmt_operand; eauto.
  - intros M O ce0 X HinM HvM HcM. eapply IH; eauto.
Qed.

Lemma occs_decl_operand : forall d parent didx start me occ ce x,
  In (me, occ) (GoIndex.occs_decl parent didx start d) ->
  GoIndex.view_expr occ = Some ce -> expr_child ce = Some x ->
  exists occ', In (Pos.succ (Pos.succ me), occ') (GoIndex.occs_decl parent didx start d) /\ GoIndex.view_expr occ' = Some x /\ GoIndex.occurrence_role occ' = GoIndex.RConversionOperand.
Proof.
  intros [body] parent didx start me occ ce x Hin Hv Hc. cbn [GoIndex.occs_decl] in *.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv. discriminate Hv.
  - destruct (occs_stmts_operand body start 0 (Pos.succ start) me occ ce x Hin Hv Hc) as [occ' [Hin' Hv']].
    exists occ'. split; [right; exact Hin' | exact Hv'].
Qed.

Lemma occs_decls_operand : forall ds parent didx start me occ ce x,
  In (me, occ) (GoIndex.occs_decls parent didx start ds) ->
  GoIndex.view_expr occ = Some ce -> expr_child ce = Some x ->
  exists occ', In (Pos.succ (Pos.succ me), occ') (GoIndex.occs_decls parent didx start ds) /\ GoIndex.view_expr occ' = Some x /\ GoIndex.occurrence_role occ' = GoIndex.RConversionOperand.
Proof.
  induction ds as [|d rest IH]; intros parent didx start me occ ce x Hin Hv Hc; cbn [GoIndex.occs_decls] in *; [destruct Hin|].
  eapply in_app_operand; [ | | exact Hin | exact Hv | exact Hc ].
  - intros M O ce0 X HinM HvM HcM. eapply occs_decl_operand; eauto.
  - intros M O ce0 X HinM HvM HcM. eapply IH; eauto.
Qed.

Lemma occs_file_operand : forall f me occ ce x,
  In (me, occ) (GoIndex.occs_file f) ->
  GoIndex.view_expr occ = Some ce -> expr_child ce = Some x ->
  exists occ', In (Pos.succ (Pos.succ me), occ') (GoIndex.occs_file f) /\ GoIndex.view_expr occ' = Some x /\ GoIndex.occurrence_role occ' = GoIndex.RConversionOperand.
Proof.
  intros f me occ ce x Hin Hv Hc. unfold GoIndex.occs_file in *.
  destruct (source_imports f) as [|i tl]; [| destruct i].
  destruct Hin as [Heq|[Heq|Hin]].
  - injection Heq as <- <-. cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv. discriminate Hv.
  - injection Heq as <- <-. cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv. discriminate Hv.
  - destruct (occs_decls_operand (source_decls f) GoIndex.root_id 0 (Pos.succ GoIndex.pkg_id) me occ ce x Hin Hv Hc)
      as [occ' [Hin' Hv']].
    exists occ'. split; [right; right; exact Hin' | exact Hv'].
Qed.

(* ---- TYPE-NAME ADJACENCY (§3.3): a conversion occurrence at [me] has its SOURCE type-name occurrence at
   [Pos.succ me] (the target child), whose [view_typename] is the exact source [TypeSyntax] — mirrors the
   operand adjacency, one child earlier.  The production path reads the retained type-name fact at this key. ---- *)

(* the conversion target's SOURCE syntax projection (mirrors [expr_child] for the target child). *)
Definition expr_conv_target (e : GoExpr) : option GoAST.TypeSyntax :=
  match e with EConvert ts _ => Some ts | _ => None end.

Lemma expr_conv_target_some : forall e ts, expr_conv_target e = Some ts -> exists x, e = EConvert ts x.
Proof.
  intros e ts H. destruct e as [ | | | | | | ts0 x]; cbn in H; try discriminate H.
  injection H as H0. subst ts0. exists x. reflexivity.
Qed.

Lemma occs_expr_type_name : forall e parent role start me occ ts x,
  In (me, occ) (GoIndex.occs_expr parent role start e) ->
  GoIndex.view_expr occ = Some (EConvert ts x) ->
  exists occ', In (Pos.succ me, occ') (GoIndex.occs_expr parent role start e) /\ GoIndex.view_typename occ' = Some ts.
Proof.
  induction e as [ b|n1|n2|s| df | dcx | ty y IHy ]; intros parent role start me occ ts x Hin Hv.
  1,2,3,4,5,6: cbn [GoIndex.occs_expr] in Hin; destruct Hin as [Heq|Hf]; [| destruct Hf];
    injection Heq as <- <-; cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv; discriminate Hv.
  cbn [GoIndex.occs_expr] in Hin. destruct Hin as [Heq|Hin].
  - injection Heq as <- <-; cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv; injection Hv as <- <-.
    eexists. split; [ right; left; reflexivity | cbn [GoIndex.view_typename GoIndex.occurrence_view]; reflexivity ].
  - destruct Hin as [Heq|Hin].
    + injection Heq as <- <-; cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv; discriminate Hv.
    + destruct (IHy start GoIndex.RConversionOperand (Pos.succ (Pos.succ start)) me occ ts x Hin Hv) as [occ' [Hin' Hv']].
      exists occ'; split; [ right; right; exact Hin' | exact Hv' ].
Qed.

Lemma in_app_type_name {L1 L2 : list (positive * GoIndex.SourceOccurrence)} me occ ts x :
  (forall M O T X, In (M, O) L1 -> GoIndex.view_expr O = Some (EConvert T X) ->
     exists O', In (Pos.succ M, O') L1 /\ GoIndex.view_typename O' = Some T) ->
  (forall M O T X, In (M, O) L2 -> GoIndex.view_expr O = Some (EConvert T X) ->
     exists O', In (Pos.succ M, O') L2 /\ GoIndex.view_typename O' = Some T) ->
  In (me, occ) (L1 ++ L2) -> GoIndex.view_expr occ = Some (EConvert ts x) ->
  exists occ', In (Pos.succ me, occ') (L1 ++ L2) /\ GoIndex.view_typename occ' = Some ts.
Proof.
  intros H1 H2 Hin Hv. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - destruct (H1 me occ ts x Hin Hv) as [occ' [Hin' Hv']]. exists occ'. split; [apply in_or_app; left; exact Hin' | exact Hv'].
  - destruct (H2 me occ ts x Hin Hv) as [occ' [Hin' Hv']]. exists occ'. split; [apply in_or_app; right; exact Hin' | exact Hv'].
Qed.

Lemma occs_args_type_name : forall es parent aidx start me occ ts x,
  In (me, occ) (GoIndex.occs_args parent aidx start es) ->
  GoIndex.view_expr occ = Some (EConvert ts x) ->
  exists occ', In (Pos.succ me, occ') (GoIndex.occs_args parent aidx start es) /\ GoIndex.view_typename occ' = Some ts.
Proof.
  induction es as [|e rest IH]; intros parent aidx start me occ ts x Hin Hv; cbn [GoIndex.occs_args] in *; [destruct Hin|].
  eapply in_app_type_name; [ | | exact Hin | exact Hv ].
  - intros M O T X HinM HvM. unfold GoIndex.occs_arg. eapply occs_expr_type_name; eauto.
  - intros M O T X HinM HvM. eapply IH; eauto.
Qed.

Lemma occs_stmt_type_name : forall s parent sidx start me occ ts x,
  In (me, occ) (GoIndex.occs_stmt parent sidx start s) ->
  GoIndex.view_expr occ = Some (EConvert ts x) ->
  exists occ', In (Pos.succ me, occ') (GoIndex.occs_stmt parent sidx start s) /\ GoIndex.view_typename occ' = Some ts.
Proof.
  intros [args] parent sidx start me occ ts x Hin Hv. cbn [GoIndex.occs_stmt] in *.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv. discriminate Hv.
  - destruct (occs_args_type_name args start 0 (Pos.succ start) me occ ts x Hin Hv) as [occ' [Hin' Hv']].
    exists occ'. split; [right; exact Hin' | exact Hv'].
Qed.

Lemma occs_stmts_type_name : forall ss parent sidx start me occ ts x,
  In (me, occ) (GoIndex.occs_stmts parent sidx start ss) ->
  GoIndex.view_expr occ = Some (EConvert ts x) ->
  exists occ', In (Pos.succ me, occ') (GoIndex.occs_stmts parent sidx start ss) /\ GoIndex.view_typename occ' = Some ts.
Proof.
  induction ss as [|s rest IH]; intros parent sidx start me occ ts x Hin Hv; cbn [GoIndex.occs_stmts] in *; [destruct Hin|].
  eapply in_app_type_name; [ | | exact Hin | exact Hv ].
  - intros M O T X HinM HvM. eapply occs_stmt_type_name; eauto.
  - intros M O T X HinM HvM. eapply IH; eauto.
Qed.

Lemma occs_decl_type_name : forall d parent didx start me occ ts x,
  In (me, occ) (GoIndex.occs_decl parent didx start d) ->
  GoIndex.view_expr occ = Some (EConvert ts x) ->
  exists occ', In (Pos.succ me, occ') (GoIndex.occs_decl parent didx start d) /\ GoIndex.view_typename occ' = Some ts.
Proof.
  intros [body] parent didx start me occ ts x Hin Hv. cbn [GoIndex.occs_decl] in *.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv. discriminate Hv.
  - destruct (occs_stmts_type_name body start 0 (Pos.succ start) me occ ts x Hin Hv) as [occ' [Hin' Hv']].
    exists occ'. split; [right; exact Hin' | exact Hv'].
Qed.

Lemma occs_decls_type_name : forall ds parent didx start me occ ts x,
  In (me, occ) (GoIndex.occs_decls parent didx start ds) ->
  GoIndex.view_expr occ = Some (EConvert ts x) ->
  exists occ', In (Pos.succ me, occ') (GoIndex.occs_decls parent didx start ds) /\ GoIndex.view_typename occ' = Some ts.
Proof.
  induction ds as [|d rest IH]; intros parent didx start me occ ts x Hin Hv; cbn [GoIndex.occs_decls] in *; [destruct Hin|].
  eapply in_app_type_name; [ | | exact Hin | exact Hv ].
  - intros M O T X HinM HvM. eapply occs_decl_type_name; eauto.
  - intros M O T X HinM HvM. eapply IH; eauto.
Qed.

Lemma occs_file_type_name : forall f me occ ts x,
  In (me, occ) (GoIndex.occs_file f) ->
  GoIndex.view_expr occ = Some (EConvert ts x) ->
  exists occ', In (Pos.succ me, occ') (GoIndex.occs_file f) /\ GoIndex.view_typename occ' = Some ts.
Proof.
  intros f me occ ts x Hin Hv. unfold GoIndex.occs_file in *.
  destruct (source_imports f) as [|i tl]; [| destruct i].
  destruct Hin as [Heq|[Heq|Hin]].
  - injection Heq as <- <-. cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv. discriminate Hv.
  - injection Heq as <- <-. cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv. discriminate Hv.
  - destruct (occs_decls_type_name (source_decls f) GoIndex.root_id 0 (Pos.succ GoIndex.pkg_id) me occ ts x Hin Hv)
      as [occ' [Hin' Hv']].
    exists occ'. split; [right; right; exact Hin' | exact Hv'].
Qed.

(* ---- TARGET ROLE: any visited occurrence whose [view_typename] is [Some] is a conversion TARGET
   (role [RConversionTarget]) — the ONLY occurrence kind carrying a [ViewTypeName] view is the conversion's
   type-name child, built with that role.  Mirrors the [_type_name] adjacency chain (view identifies it). ---- *)

Lemma occs_expr_typename_role : forall e parent role start me occ ts,
  In (me, occ) (GoIndex.occs_expr parent role start e) ->
  GoIndex.view_typename occ = Some ts -> GoIndex.occurrence_role occ = GoIndex.RConversionTarget.
Proof.
  induction e as [ b|n1|n2|s| df | dcx | ty y IHy ]; intros parent role start me occ ts Hin Hv.
  1,2,3,4,5,6: cbn [GoIndex.occs_expr] in Hin; destruct Hin as [Heq|Hf]; [| destruct Hf];
    injection Heq as <- <-; cbn [GoIndex.view_typename GoIndex.occurrence_view] in Hv; discriminate Hv.
  cbn [GoIndex.occs_expr] in Hin. destruct Hin as [Heq|Hin].
  - injection Heq as <- <-; cbn [GoIndex.view_typename GoIndex.occurrence_view] in Hv; discriminate Hv.
  - destruct Hin as [Heq|Hin].
    + injection Heq as <- <-; cbn [GoIndex.occurrence_role]; reflexivity.
    + exact (IHy start GoIndex.RConversionOperand (Pos.succ (Pos.succ start)) me occ ts Hin Hv).
Qed.

Lemma in_app_typename_role {L1 L2 : list (positive * GoIndex.SourceOccurrence)} me occ ts :
  (forall M O T, In (M, O) L1 -> GoIndex.view_typename O = Some T -> GoIndex.occurrence_role O = GoIndex.RConversionTarget) ->
  (forall M O T, In (M, O) L2 -> GoIndex.view_typename O = Some T -> GoIndex.occurrence_role O = GoIndex.RConversionTarget) ->
  In (me, occ) (L1 ++ L2) -> GoIndex.view_typename occ = Some ts -> GoIndex.occurrence_role occ = GoIndex.RConversionTarget.
Proof.
  intros H1 H2 Hin Hv. apply in_app_or in Hin. destruct Hin as [Hin|Hin];
    [ exact (H1 me occ ts Hin Hv) | exact (H2 me occ ts Hin Hv) ].
Qed.

Lemma occs_args_typename_role : forall es parent aidx start me occ ts,
  In (me, occ) (GoIndex.occs_args parent aidx start es) ->
  GoIndex.view_typename occ = Some ts -> GoIndex.occurrence_role occ = GoIndex.RConversionTarget.
Proof.
  induction es as [|e rest IH]; intros parent aidx start me occ ts Hin Hv; cbn [GoIndex.occs_args] in *; [destruct Hin|].
  eapply in_app_typename_role; [ | | exact Hin | exact Hv ].
  - intros M O T HinM HvM. unfold GoIndex.occs_arg. eapply occs_expr_typename_role; eauto.
  - intros M O T HinM HvM. eapply IH; eauto.
Qed.

Lemma occs_stmt_typename_role : forall s parent sidx start me occ ts,
  In (me, occ) (GoIndex.occs_stmt parent sidx start s) ->
  GoIndex.view_typename occ = Some ts -> GoIndex.occurrence_role occ = GoIndex.RConversionTarget.
Proof.
  intros [args] parent sidx start me occ ts Hin Hv. cbn [GoIndex.occs_stmt] in *.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. cbn [GoIndex.view_typename GoIndex.occurrence_view] in Hv. discriminate Hv.
  - exact (occs_args_typename_role args start 0 (Pos.succ start) me occ ts Hin Hv).
Qed.

Lemma occs_stmts_typename_role : forall ss parent sidx start me occ ts,
  In (me, occ) (GoIndex.occs_stmts parent sidx start ss) ->
  GoIndex.view_typename occ = Some ts -> GoIndex.occurrence_role occ = GoIndex.RConversionTarget.
Proof.
  induction ss as [|s rest IH]; intros parent sidx start me occ ts Hin Hv; cbn [GoIndex.occs_stmts] in *; [destruct Hin|].
  eapply in_app_typename_role; [ | | exact Hin | exact Hv ].
  - intros M O T HinM HvM. eapply occs_stmt_typename_role; eauto.
  - intros M O T HinM HvM. eapply IH; eauto.
Qed.

Lemma occs_decl_typename_role : forall d parent didx start me occ ts,
  In (me, occ) (GoIndex.occs_decl parent didx start d) ->
  GoIndex.view_typename occ = Some ts -> GoIndex.occurrence_role occ = GoIndex.RConversionTarget.
Proof.
  intros [body] parent didx start me occ ts Hin Hv. cbn [GoIndex.occs_decl] in *.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. cbn [GoIndex.view_typename GoIndex.occurrence_view] in Hv. discriminate Hv.
  - exact (occs_stmts_typename_role body start 0 (Pos.succ start) me occ ts Hin Hv).
Qed.

Lemma occs_decls_typename_role : forall ds parent didx start me occ ts,
  In (me, occ) (GoIndex.occs_decls parent didx start ds) ->
  GoIndex.view_typename occ = Some ts -> GoIndex.occurrence_role occ = GoIndex.RConversionTarget.
Proof.
  induction ds as [|d rest IH]; intros parent didx start me occ ts Hin Hv; cbn [GoIndex.occs_decls] in *; [destruct Hin|].
  eapply in_app_typename_role; [ | | exact Hin | exact Hv ].
  - intros M O T HinM HvM. eapply occs_decl_typename_role; eauto.
  - intros M O T HinM HvM. eapply IH; eauto.
Qed.

Lemma occs_file_typename_role : forall f me occ ts,
  In (me, occ) (GoIndex.occs_file f) ->
  GoIndex.view_typename occ = Some ts -> GoIndex.occurrence_role occ = GoIndex.RConversionTarget.
Proof.
  intros f me occ ts Hin Hv. unfold GoIndex.occs_file in *.
  destruct (source_imports f) as [|i tl]; [| destruct i].
  destruct Hin as [Heq|[Heq|Hin]].
  - injection Heq as <- <-. cbn [GoIndex.view_typename GoIndex.occurrence_view] in Hv. discriminate Hv.
  - injection Heq as <- <-. cbn [GoIndex.view_typename GoIndex.occurrence_view] in Hv. discriminate Hv.
  - exact (occs_decls_typename_role (source_decls f) GoIndex.root_id 0 (Pos.succ GoIndex.pkg_id) me occ ts Hin Hv).
Qed.

(* EXPRESSION-FACT TOTALITY GROUNDWORK.  On a TYPED program every visited expression occurrence has a
   successful [const_info] (hence an exact fact).  Three facts compose it: a typed println argument's
   [const_info] SUCCEEDS ([expr_typedb_const_info]); [const_info]'s recursion propagates success DOWNWARD to
   every conversion operand ([const_info_child_some], lifted structurally through the occurrence enumeration);
   and the whole-file / whole-program traversal visits exactly those subexpressions.  So on [ProgramTyped]
   every visited expression occurrence's [const_info] is [Some] — the fact query is TOTAL. *)

(* a typed argument's constant status succeeds (its whole conversion chain is representable). *)
Lemma expr_typedb_const_info : forall u e, expr_typedb u e = true -> exists ci, const_info e = Some ci.
Proof.
  intros u e H. unfold expr_typedb in H.
  destruct (resolve_expr u e) as [t|] eqn:Hr; [|discriminate H].
  unfold resolve_expr in Hr.
  destruct (resolve_expr_const u e) as [rc|] eqn:Hrc; cbn [option_map] in Hr; [|discriminate Hr].
  destruct (GoTypes.resolve_expr_const_sound predeclared_type u e rc Hrc) as [ci [Hci _]]. exists ci; exact Hci.
Qed.

(* one downward step: a node whose [const_info] succeeds has an expression child whose [const_info] succeeds. *)
Lemma const_info_child_some : forall e x ci,
  expr_child e = Some x -> const_info e = Some ci -> exists cix, const_info x = Some cix.
Proof.
  intros e x ci Hc Hci. rewrite const_info_step_reflect, Hc in Hci.
  destruct e as [ b|n1|n2|s| df | dcx | ts y ]; cbn [expr_child] in Hc; try discriminate Hc;
    cbn [GoTypes.const_info_step] in Hci;
    (destruct (const_info x) as [cix|]; [ exists cix; reflexivity | discriminate Hci ]).
Qed.

(* the const_info of EVERY occurrence in [occs_expr ... e] is [Some], given [const_info e] is: leaves view [e]
   itself; a conversion's head is [e] (Some given), and its operand subtree inherits Some by [const_info_child_some]. *)
Lemma occs_expr_const_info_some : forall e parent role pos me occ e' ci,
  const_info e = Some ci ->
  In (me, occ) (GoIndex.occs_expr parent role pos e) ->
  GoIndex.view_expr occ = Some e' -> exists ci', const_info e' = Some ci'.
Proof.
  induction e as [ b|n1|n2|s| df | dcx | ts y IHy ];
    intros parent role pos me occ e' ci Hci Hin Hv.
  1,2,3,4,5,6: cbn [GoIndex.occs_expr] in Hin; destruct Hin as [Heq|[]];
    injection Heq as <- <-; cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv;
    injection Hv as <-; exists ci; exact Hci.
  (* conversion: conv head (view = the conversion), type-name (view = None, discriminated), operand subtree (IH) *)
  cbn [GoIndex.occs_expr] in Hin. destruct Hin as [Heq|Hin].
  - injection Heq as <- <-; cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv;
    injection Hv as <-; exists ci; exact Hci.
  - destruct Hin as [Heq|Hin].
    + injection Heq as <- <-; cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv; discriminate Hv.
    + assert (Hy : exists ciy, const_info y = Some ciy)
        by (cbn [GoTypes.const_info] in Hci; destruct (const_info y) as [ciy|];
            [ eexists; reflexivity | discriminate Hci ]);
      destruct Hy as [ciy Hciy];
      exact (IHy pos GoIndex.RConversionOperand (Pos.succ (Pos.succ pos)) me occ e' ciy Hciy Hin Hv).
Qed.

Lemma in_app_const_info_some {L1 L2 : list (positive * GoIndex.SourceOccurrence)} me occ e' :
  (forall M O E, In (M, O) L1 -> GoIndex.view_expr O = Some E -> exists ci, const_info E = Some ci) ->
  (forall M O E, In (M, O) L2 -> GoIndex.view_expr O = Some E -> exists ci, const_info E = Some ci) ->
  In (me, occ) (L1 ++ L2) -> GoIndex.view_expr occ = Some e' -> exists ci, const_info e' = Some ci.
Proof.
  intros H1 H2 Hin Hv. apply in_app_or in Hin. destruct Hin as [Hin|Hin];
    [ exact (H1 me occ e' Hin Hv) | exact (H2 me occ e' Hin Hv) ].
Qed.

Lemma occs_arg_const_info_some : forall e parent aidx pos me occ e',
  expr_typedb GoTypes.UsePrintlnArg e = true ->
  In (me, occ) (GoIndex.occs_arg parent aidx pos e) ->
  GoIndex.view_expr occ = Some e' -> exists ci, const_info e' = Some ci.
Proof.
  intros e parent aidx pos me occ e' Ht Hin Hv. unfold GoIndex.occs_arg in Hin.
  destruct (expr_typedb_const_info GoTypes.UsePrintlnArg e Ht) as [ci Hci].
  exact (occs_expr_const_info_some e parent (GoIndex.RPrintlnArg aidx) pos me occ e' ci Hci Hin Hv).
Qed.

Lemma occs_args_const_info_some : forall es parent aidx pos me occ e',
  forallb (expr_typedb GoTypes.UsePrintlnArg) es = true ->
  In (me, occ) (GoIndex.occs_args parent aidx pos es) ->
  GoIndex.view_expr occ = Some e' -> exists ci, const_info e' = Some ci.
Proof.
  induction es as [|e rest IH]; intros parent aidx pos me occ e' Ht Hin Hv;
    cbn [GoIndex.occs_args] in Hin; [destruct Hin|].
  cbn [forallb] in Ht. apply Bool.andb_true_iff in Ht. destruct Ht as [Hte Htr].
  eapply in_app_const_info_some; [ | | exact Hin | exact Hv ].
  - intros M O E HinM HvM. exact (occs_arg_const_info_some e parent aidx pos M O E Hte HinM HvM).
  - intros M O E HinM HvM. exact (IH parent (S aidx) (Pos.succ (GoIndex.end_expr pos e)) M O E Htr HinM HvM).
Qed.

Lemma occs_stmt_const_info_some : forall s parent sidx pos me occ e',
  stmt_typedb s = true ->
  In (me, occ) (GoIndex.occs_stmt parent sidx pos s) ->
  GoIndex.view_expr occ = Some e' -> exists ci, const_info e' = Some ci.
Proof.
  intros [args] parent sidx pos me occ e' Ht Hin Hv. cbn [GoIndex.occs_stmt] in Hin.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv. discriminate Hv.
  - cbn [GoTypes.stmt_typedb] in Ht.
    exact (occs_args_const_info_some args pos 0 (Pos.succ pos) me occ e' Ht Hin Hv).
Qed.

Lemma occs_stmts_const_info_some : forall ss parent sidx pos me occ e',
  forallb stmt_typedb ss = true ->
  In (me, occ) (GoIndex.occs_stmts parent sidx pos ss) ->
  GoIndex.view_expr occ = Some e' -> exists ci, const_info e' = Some ci.
Proof.
  induction ss as [|s rest IH]; intros parent sidx pos me occ e' Ht Hin Hv;
    cbn [GoIndex.occs_stmts] in Hin; [destruct Hin|].
  cbn [forallb] in Ht. apply Bool.andb_true_iff in Ht. destruct Ht as [Hts Htr].
  eapply in_app_const_info_some; [ | | exact Hin | exact Hv ].
  - intros M O E HinM HvM. exact (occs_stmt_const_info_some s parent sidx pos M O E Hts HinM HvM).
  - intros M O E HinM HvM. exact (IH parent (S sidx) (Pos.succ (GoIndex.end_stmt pos s)) M O E Htr HinM HvM).
Qed.

Lemma occs_decl_const_info_some : forall d parent didx pos me occ e',
  decl_typedb d = true ->
  In (me, occ) (GoIndex.occs_decl parent didx pos d) ->
  GoIndex.view_expr occ = Some e' -> exists ci, const_info e' = Some ci.
Proof.
  intros [body] parent didx pos me occ e' Ht Hin Hv. cbn [GoIndex.occs_decl] in Hin.
  destruct Hin as [Heq|Hin].
  - injection Heq as <- <-. cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv. discriminate Hv.
  - cbn [GoTypes.decl_typedb] in Ht.
    exact (occs_stmts_const_info_some body pos 0 (Pos.succ pos) me occ e' Ht Hin Hv).
Qed.

Lemma occs_decls_const_info_some : forall ds parent didx pos me occ e',
  forallb decl_typedb ds = true ->
  In (me, occ) (GoIndex.occs_decls parent didx pos ds) ->
  GoIndex.view_expr occ = Some e' -> exists ci, const_info e' = Some ci.
Proof.
  induction ds as [|d rest IH]; intros parent didx pos me occ e' Ht Hin Hv;
    cbn [GoIndex.occs_decls] in Hin; [destruct Hin|].
  cbn [forallb] in Ht. apply Bool.andb_true_iff in Ht. destruct Ht as [Htd Htr].
  eapply in_app_const_info_some; [ | | exact Hin | exact Hv ].
  - intros M O E HinM HvM. exact (occs_decl_const_info_some d parent didx pos M O E Htd HinM HvM).
  - intros M O E HinM HvM. exact (IH parent (S didx) (Pos.succ (GoIndex.end_decl pos d)) M O E Htr HinM HvM).
Qed.

Lemma occs_file_const_info_some : forall f me occ e',
  source_file_typedb f = true ->
  In (me, occ) (GoIndex.occs_file f) ->
  GoIndex.view_expr occ = Some e' -> exists ci, const_info e' = Some ci.
Proof.
  intros f me occ e' Ht Hin Hv. unfold GoIndex.occs_file in Hin.
  destruct (source_imports f) as [|i tl]; [| destruct i].
  destruct Hin as [Heq|[Heq|Hin]].
  - injection Heq as <- <-. cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv. discriminate Hv.
  - injection Heq as <- <-. cbn [GoIndex.view_expr GoIndex.occurrence_view] in Hv. discriminate Hv.
  - unfold GoTypes.source_file_typedb, file_typedb in Ht.
    exact (occs_decls_const_info_some (source_decls f) GoIndex.root_id 0 (Pos.succ GoIndex.pkg_id) me occ e' Ht Hin Hv).
Qed.

(* the WHOLE-PROGRAM statement: on [program_typedb] every visited expression occurrence's [const_info] is [Some]. *)
Lemma prog_visit_const_info_some (p : GoProgram) :
  program_typedb p = true ->
  forall r occ e', In (r, occ) (prog_visit p) -> GoIndex.view_expr occ = Some e' -> exists ci, const_info e' = Some ci.
Proof.
  intros Hpt r occ e' Hin Hv. rewrite prog_visit_flat_map in Hin. apply in_flat_map in Hin.
  destruct Hin as [b [Hb Hrb]]. unfold binding_visit in Hrb.
  destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|] eqn:Ef; [|destruct Hrb].
  pose proof (GoIndex.Snap.visit_file_view p fr r occ Hrb) as [Hocc Hfile].
  assert (Hsrc_at : GoIndex.source_occurrence_at (GoIndex.Snap.file_ref_source fr) (GoIndex.Snap.node_ref_local r) = Some occ).
  { pose proof (GoIndex.Snap.source_occ_of_ref_eq r) as Hso. rewrite Hfile in Hso. rewrite Hso, Hocc. reflexivity. }
  apply GoIndex.occs_file_exact in Hsrc_at.
  unfold program_typedb in Hpt.
  pose proof (proj1 (forallb_forall (fun b => source_file_typedb (snd b))
                (GoAST.file_bindings (prog_files p))) Hpt b Hb) as Htb.
  cbv beta in Htb.
  assert (Hsrceq : snd b = GoIndex.Snap.file_ref_source fr).
  { pose proof (GoAST.file_bindings_find (prog_files p) b Hb) as Hfb.
    pose proof (GoIndex.Snap.file_of_path_source_exact p (fst b) fr Ef) as Hfe.
    rewrite Hfb in Hfe. injection Hfe as Heq; exact Heq. }
  rewrite Hsrceq in Htb.
  exact (occs_file_const_info_some (GoIndex.Snap.file_ref_source fr) (GoIndex.Snap.node_ref_local r) occ e' Htb Hsrc_at Hv).
Qed.

(* a NodeRef is ALWAYS visited (its file is represented, and [visit_file] is complete over the file). *)
Lemma noderef_in_prog_visit (p : GoProgram) (r : GoIndex.Snap.NodeRef p) :
  In (r, GoIndex.Snap.source_occurrence_of_ref r) (prog_visit p).
Proof.
  pose proof (GoIndex.Snap.file_of_path_complete p (GoIndex.Snap.node_ref_file r)) as Hcomp.
  pose proof (GoIndex.Snap.file_of_path_source_exact p
                (GoIndex.Snap.file_ref_path (GoIndex.Snap.node_ref_file r))
                (GoIndex.Snap.node_ref_file r) Hcomp) as Hfind.
  pose proof (GoAST.find_file_bindings (prog_files p)
                (GoIndex.Snap.file_ref_path (GoIndex.Snap.node_ref_file r))
                (GoIndex.Snap.file_ref_source (GoIndex.Snap.node_ref_file r)) Hfind) as Hin_b.
  rewrite prog_visit_flat_map. apply in_flat_map.
  exists (GoIndex.Snap.file_ref_path (GoIndex.Snap.node_ref_file r),
          GoIndex.Snap.file_ref_source (GoIndex.Snap.node_ref_file r)).
  split; [exact Hin_b|]. unfold binding_visit; cbn [fst].
  rewrite Hcomp. apply GoIndex.Snap.visit_file_complete. reflexivity.
Qed.

(* the conversion-child KEYS over the DELIVERED visit stream (no separate source recursion).  [operand_key r] is
   the canonical operand key of a conversion at [r] (same file, [Pos.succ (Pos.succ local)] — the operand is TWO
   past the conversion, since [Pos.succ local] is the type-name occurrence).  [conversion_operand_ref] mints the
   operand [ExprRef] at this key through the retained index; the bottom-up accumulator reads that ref's
   ALREADY-COMPUTED outcome from the processed suffix.  [prog_visit_operand] proves the operand really is a
   visited occurrence at [operand_key] whose view is the conversion's operand (the soundness of the minted ref). *)

Definition operand_key {p} (r : GoIndex.Snap.NodeRef p) : GoIndex.NodeKey :=
  GoIndex.mkKey (GoIndex.nk_file (GoIndex.Snap.node_ref_key r)) (Pos.succ (Pos.succ (GoIndex.Snap.node_ref_local r))).

(* the operand of a visited conversion is ITSELF a visited occurrence whose key is [operand_key] and whose view is the
   operand expression (minted through the index from its exact local id). *)
Lemma prog_visit_operand (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p)
    (r : GoIndex.Snap.NodeRef p) occ e x :
  In (r, occ) (prog_visit p) -> GoIndex.view_expr occ = Some e -> expr_child e = Some x ->
  exists r', In (r', GoIndex.Snap.source_occurrence_of_ref r') (prog_visit p)
    /\ GoIndex.Snap.node_ref_key r' = operand_key r
    /\ GoIndex.view_expr (GoIndex.Snap.source_occurrence_of_ref r') = Some x
    /\ GoIndex.occurrence_role (GoIndex.Snap.source_occurrence_of_ref r') = GoIndex.RConversionOperand.
Proof.
  intros Hin Hv Hc.
  rewrite prog_visit_flat_map in Hin. apply in_flat_map in Hin. destruct Hin as [b [Hb Hrb]].
  unfold binding_visit in Hrb. destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|] eqn:Ef; [|destruct Hrb].
  pose proof (GoIndex.Snap.visit_file_view p fr r occ Hrb) as [Hocc Hfile].
  assert (Hsrc : GoIndex.source_occurrence_at (GoIndex.Snap.file_ref_source fr) (GoIndex.Snap.node_ref_local r) = Some occ).
  { pose proof (GoIndex.Snap.source_occ_of_ref_eq r) as Hso. rewrite Hfile in Hso. rewrite Hso, Hocc. reflexivity. }
  apply GoIndex.occs_file_exact in Hsrc.
  destruct (occs_file_operand (GoIndex.Snap.file_ref_source fr) (GoIndex.Snap.node_ref_local r) occ e x Hsrc Hv Hc)
    as [occ' [Hin' [Hvx Hrole]]].
  apply GoIndex.occs_file_exact in Hin'.
  assert (Hvalid : GoIndex.valid_localb (GoIndex.Snap.file_ref_source fr) (Pos.succ (Pos.succ (GoIndex.Snap.node_ref_local r))) = true).
  { unfold GoIndex.valid_localb.
    rewrite (GoIndex.source_occurrence_meta (GoIndex.Snap.file_ref_source fr)
               (Pos.succ (Pos.succ (GoIndex.Snap.node_ref_local r))) occ' Hin'). reflexivity. }
  pose proof (GoIndex.Snap.file_of_path_source_exact p (fst b) fr Ef) as Hfind.
  pose proof (GoIndex.Snap.file_of_path_sound p (fst b) fr Ef) as Hpath.
  assert (Hfind' : GoAST.find_file (GoIndex.Snap.file_ref_path fr) (prog_files p) = Some (GoIndex.Snap.file_ref_source fr))
    by (rewrite Hpath; exact Hfind).
  destruct (GoIndex.Snap.ref_of_key_source p idx
              (GoIndex.Snap.file_ref_path fr) (GoIndex.Snap.file_ref_source fr)
              (Pos.succ (Pos.succ (GoIndex.Snap.node_ref_local r))) Hfind' Hvalid) as [r' [Hrok [Hrlocal Hrsrc]]].
  exists r'.
  assert (Hkey : GoIndex.Snap.node_ref_key r' = operand_key r).
  { pose proof (GoIndex.Snap.ref_of_key_sound p idx _ r' Hrok) as Hk.
    rewrite Hk. unfold operand_key. rewrite GoIndex.Snap.node_ref_key_eq. cbn [GoIndex.nk_file]. rewrite Hfile. reflexivity. }
  assert (Hsor : GoIndex.Snap.source_occurrence_of_ref r' = occ').
  { pose proof (GoIndex.Snap.source_occ_of_ref_eq r') as Hso'.
    rewrite Hrlocal, Hrsrc in Hso'.
    rewrite Hin' in Hso'. injection Hso' as ->. reflexivity. }
  split; [ | split; [ | split ] ].
  - apply noderef_in_prog_visit.
  - exact Hkey.
  - rewrite Hsor; exact Hvx.
  - rewrite Hsor; exact Hrole.
Qed.

(* the SOURCE type-name occurrence of a conversion at [r] has key [type_name_key r] (same file, [Pos.succ local]
   — the target child, one before the operand). *)
Definition type_name_key {p} (r : GoIndex.Snap.NodeRef p) : GoIndex.NodeKey :=
  GoIndex.mkKey (GoIndex.nk_file (GoIndex.Snap.node_ref_key r)) (Pos.succ (GoIndex.Snap.node_ref_local r)).

(* the target child key is INJECTIVE in the conversion's own key: two conversions at DISTINCT keys have DISTINCT
   target type-name keys (so distinct target refs) — occurrence identity, not name identity. *)
Lemma type_name_key_inj {p} (r1 r2 : GoIndex.Snap.NodeRef p) :
  type_name_key r1 = type_name_key r2 -> GoIndex.Snap.node_ref_key r1 = GoIndex.Snap.node_ref_key r2.
Proof.
  unfold type_name_key. rewrite !GoIndex.Snap.node_ref_key_eq. cbn [GoIndex.nk_file].
  intro H. injection H as Hf Hl. apply Pos.succ_inj in Hl. rewrite Hf, Hl. reflexivity.
Qed.

(* the target type-name of a visited conversion is ITSELF a visited occurrence whose key is [type_name_key] and
   whose [view_typename] is the exact source [TypeSyntax] (minted through the index from its exact local id). *)
Lemma prog_visit_type_name (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p)
    (r : GoIndex.Snap.NodeRef p) occ ts x :
  In (r, occ) (prog_visit p) -> GoIndex.view_expr occ = Some (EConvert ts x) ->
  exists r', In (r', GoIndex.Snap.source_occurrence_of_ref r') (prog_visit p)
    /\ GoIndex.Snap.node_ref_key r' = type_name_key r
    /\ GoIndex.view_typename (GoIndex.Snap.source_occurrence_of_ref r') = Some ts
    /\ GoIndex.occurrence_role (GoIndex.Snap.source_occurrence_of_ref r') = GoIndex.RConversionTarget.
Proof.
  intros Hin Hv.
  rewrite prog_visit_flat_map in Hin. apply in_flat_map in Hin. destruct Hin as [b [Hb Hrb]].
  unfold binding_visit in Hrb. destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|] eqn:Ef; [|destruct Hrb].
  pose proof (GoIndex.Snap.visit_file_view p fr r occ Hrb) as [Hocc Hfile].
  assert (Hsrc : GoIndex.source_occurrence_at (GoIndex.Snap.file_ref_source fr) (GoIndex.Snap.node_ref_local r) = Some occ).
  { pose proof (GoIndex.Snap.source_occ_of_ref_eq r) as Hso. rewrite Hfile in Hso. rewrite Hso, Hocc. reflexivity. }
  apply GoIndex.occs_file_exact in Hsrc.
  destruct (occs_file_type_name (GoIndex.Snap.file_ref_source fr) (GoIndex.Snap.node_ref_local r) occ ts x Hsrc Hv)
    as [occ' [Hin' Hvts]].
  pose proof (occs_file_typename_role (GoIndex.Snap.file_ref_source fr)
                (Pos.succ (GoIndex.Snap.node_ref_local r)) occ' ts Hin' Hvts) as Hrole.
  apply GoIndex.occs_file_exact in Hin'.
  assert (Hvalid : GoIndex.valid_localb (GoIndex.Snap.file_ref_source fr) (Pos.succ (GoIndex.Snap.node_ref_local r)) = true).
  { unfold GoIndex.valid_localb.
    rewrite (GoIndex.source_occurrence_meta (GoIndex.Snap.file_ref_source fr)
               (Pos.succ (GoIndex.Snap.node_ref_local r)) occ' Hin'). reflexivity. }
  pose proof (GoIndex.Snap.file_of_path_source_exact p (fst b) fr Ef) as Hfind.
  pose proof (GoIndex.Snap.file_of_path_sound p (fst b) fr Ef) as Hpath.
  assert (Hfind' : GoAST.find_file (GoIndex.Snap.file_ref_path fr) (prog_files p) = Some (GoIndex.Snap.file_ref_source fr))
    by (rewrite Hpath; exact Hfind).
  destruct (GoIndex.Snap.ref_of_key_source p idx
              (GoIndex.Snap.file_ref_path fr) (GoIndex.Snap.file_ref_source fr)
              (Pos.succ (GoIndex.Snap.node_ref_local r)) Hfind' Hvalid) as [r' [Hrok [Hrlocal Hrsrc]]].
  exists r'.
  assert (Hkey : GoIndex.Snap.node_ref_key r' = type_name_key r).
  { pose proof (GoIndex.Snap.ref_of_key_sound p idx _ r' Hrok) as Hk.
    rewrite Hk. unfold type_name_key. rewrite GoIndex.Snap.node_ref_key_eq. cbn [GoIndex.nk_file]. rewrite Hfile. reflexivity. }
  assert (Hsor : GoIndex.Snap.source_occurrence_of_ref r' = occ').
  { pose proof (GoIndex.Snap.source_occ_of_ref_eq r') as Hso'.
    rewrite Hrlocal, Hrsrc in Hso'.
    rewrite Hin' in Hso'. injection Hso' as ->. reflexivity. }
  split; [ | split; [ | split ] ].
  - apply noderef_in_prog_visit.
  - exact Hkey.
  - rewrite Hsor; exact Hvts.
  - rewrite Hsor; exact Hrole.
Qed.

(* §3.3 the total structural helper: a conversion [ExprRef]'s exact target [TypeNameRef], minted THROUGH the
   retained index (`ref_of_key` at the target child key [type_name_key], refined to [KTypeName]).  For a LIVE
   conversion it yields the exact target ref: KTypeName (by type), the direct [type_name_key] child, role
   [RConversionTarget], recovering the exact raw source [TypeSyntax] through the ref.  The production path uses
   THIS typed ref — never a raw source-name lookup. *)
Definition conversion_target_ref {p} (idx : GoIndex.Snap.SyntaxIndex p) (er : GoIndex.ExprRef p)
  : option (GoIndex.TypeNameRef p) :=
  match GoIndex.Snap.ref_of_key p idx (type_name_key (GoIndex.erase_ref er)) with
  | Some r => GoIndex.as_type_name idx r
  | None => None
  end.

Lemma conversion_target_ref_conv {p} (idx : GoIndex.Snap.SyntaxIndex p)
    (r : GoIndex.Snap.NodeRef p) occ (er : GoIndex.ExprRef p) ts x :
  In (r, occ) (prog_visit p) ->
  GoIndex.view_expr occ = Some (EConvert ts x) ->
  GoIndex.as_expr idx r = Some er ->
  exists tr, conversion_target_ref idx er = Some tr
    /\ GoIndex.Snap.node_ref_key (GoIndex.erase_ref tr) = type_name_key r
    /\ GoIndex.occurrence_role (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref tr)) = GoIndex.RConversionTarget
    /\ GoIndex.type_name_ref_syntax tr = Some ts.
Proof.
  intros Hin Hv Hae.
  pose proof (GoIndex.erase_as_kind idx r GoIndex.KExpression er Hae) as Her.
  destruct (prog_visit_type_name p idx r occ ts x Hin Hv) as [r' [Hin' [Hkey [Hvts Hrole]]]].
  assert (Hkind : GoIndex.Snap.node_kind idx r' = GoIndex.KTypeName).
  { rewrite (GoIndex.Snap.node_kind_matches_source p idx r'). exact (GoIndex.view_typename_kind _ ts Hvts). }
  destruct (GoIndex.as_kind_complete idx r' GoIndex.KTypeName Hkind) as [tr [Hastr Hetr]].
  exists tr.
  assert (Hcompute : conversion_target_ref idx er = Some tr).
  { unfold conversion_target_ref. rewrite Her, <- Hkey, GoIndex.Snap.ref_of_key_complete.
    unfold GoIndex.as_type_name. exact Hastr. }
  split; [ exact Hcompute | ].
  split; [ rewrite Hetr; exact Hkey | ].
  split; [ rewrite Hetr; exact Hrole | ].
  unfold GoIndex.type_name_ref_syntax. rewrite Hetr. exact Hvts.
Qed.

(* §3.2 the conversion OPERAND ref, minted THROUGH the retained index at [operand_key] — the mirror of
   [conversion_target_ref]; for a LIVE conversion it is the exact direct [RConversionOperand] child recovering
   the exact raw operand.  The production path recurses into the operand through THIS typed ref. *)
Definition conversion_operand_ref {p} (idx : GoIndex.Snap.SyntaxIndex p) (er : GoIndex.ExprRef p)
  : option (GoIndex.ExprRef p) :=
  match GoIndex.Snap.ref_of_key p idx (operand_key (GoIndex.erase_ref er)) with
  | Some r => GoIndex.as_expr idx r
  | None => None
  end.

Lemma conversion_operand_ref_conv {p} (idx : GoIndex.Snap.SyntaxIndex p)
    (r : GoIndex.Snap.NodeRef p) occ (er : GoIndex.ExprRef p) ts x :
  In (r, occ) (prog_visit p) ->
  GoIndex.view_expr occ = Some (EConvert ts x) ->
  GoIndex.as_expr idx r = Some er ->
  exists opr, conversion_operand_ref idx er = Some opr
    /\ GoIndex.Snap.node_ref_key (GoIndex.erase_ref opr) = operand_key r
    /\ GoIndex.occurrence_role (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref opr)) = GoIndex.RConversionOperand
    /\ GoIndex.view_expr (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref opr)) = Some x.
Proof.
  intros Hin Hv Hae.
  pose proof (GoIndex.erase_as_kind idx r GoIndex.KExpression er Hae) as Her.
  destruct (prog_visit_operand p idx r occ (EConvert ts x) x Hin Hv eq_refl) as [r' [Hin' [Hkey [Hvx Hrole]]]].
  assert (Hkind : GoIndex.Snap.node_kind idx r' = GoIndex.KExpression).
  { rewrite (GoIndex.Snap.node_kind_matches_source p idx r'). exact (GoIndex.view_expr_kind _ x Hvx). }
  destruct (GoIndex.as_kind_complete idx r' GoIndex.KExpression Hkind) as [opr [Haopr Heopr]].
  exists opr.
  assert (Hcompute : conversion_operand_ref idx er = Some opr).
  { unfold conversion_operand_ref. rewrite Her, <- Hkey, GoIndex.Snap.ref_of_key_complete.
    unfold GoIndex.as_expr. exact Haopr. }
  split; [ exact Hcompute | ].
  split; [ rewrite Heopr; exact Hkey | ].
  split; [ rewrite Heopr; exact Hrole | ].
  rewrite Heopr; exact Hvx.
Qed.

(* an [ExprRef] refines its OWN erased node (axiom-free: distinct refs of the same kind are decided by their
   NodeKey, [noderefof_key_inj], NOT by proof irrelevance). *)
Lemma as_expr_erase {p} (idx : GoIndex.Snap.SyntaxIndex p) (er : GoIndex.ExprRef p) :
  GoIndex.as_expr idx (GoIndex.erase_ref er) = Some er.
Proof.
  assert (Hk : GoIndex.Snap.node_kind idx (GoIndex.erase_ref er) = GoIndex.KExpression).
  { rewrite (GoIndex.Snap.node_kind_matches_source p idx (GoIndex.erase_ref er)). exact (GoIndex.noderefof_kind er). }
  destruct (GoIndex.as_kind_complete idx (GoIndex.erase_ref er) GoIndex.KExpression Hk) as [er' [Ha He']].
  unfold GoIndex.as_expr. rewrite Ha. f_equal. apply GoIndex.noderefof_key_inj. rewrite He'. reflexivity.
Qed.

(* the typed conversion children FROM THE REF'S OWN SOURCE VIEW: for any [ExprRef] whose source view is a
   conversion, its target/operand refs are minted through the retained index (every ref's node is visited,
   [noderef_in_prog_visit]).  These are the total-form witnesses the production recursion consumes. *)
Lemma conversion_target_ref_of_view {p} (idx : GoIndex.Snap.SyntaxIndex p) (er : GoIndex.ExprRef p) ts x :
  GoIndex.view_expr (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) = Some (EConvert ts x) ->
  exists tr, conversion_target_ref idx er = Some tr
    /\ GoIndex.Snap.node_ref_key (GoIndex.erase_ref tr) = type_name_key (GoIndex.erase_ref er)
    /\ GoIndex.occurrence_role (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref tr)) = GoIndex.RConversionTarget
    /\ GoIndex.type_name_ref_syntax tr = Some ts.
Proof.
  intro Hview.
  exact (conversion_target_ref_conv idx (GoIndex.erase_ref er) (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er))
           er ts x (noderef_in_prog_visit p (GoIndex.erase_ref er)) Hview (as_expr_erase idx er)).
Qed.

Lemma conversion_operand_ref_of_view {p} (idx : GoIndex.Snap.SyntaxIndex p) (er : GoIndex.ExprRef p) ts x :
  GoIndex.view_expr (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) = Some (EConvert ts x) ->
  exists opr, conversion_operand_ref idx er = Some opr
    /\ GoIndex.Snap.node_ref_key (GoIndex.erase_ref opr) = operand_key (GoIndex.erase_ref er)
    /\ GoIndex.occurrence_role (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref opr)) = GoIndex.RConversionOperand
    /\ GoIndex.view_expr (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref opr)) = Some x.
Proof.
  intro Hview.
  exact (conversion_operand_ref_conv idx (GoIndex.erase_ref er) (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er))
           er ts x (noderef_in_prog_visit p (GoIndex.erase_ref er)) Hview (as_expr_erase idx er)).
Qed.

Lemma conversion_target_ref_not_none {p} (idx : GoIndex.Snap.SyntaxIndex p) (er : GoIndex.ExprRef p) ts x :
  GoIndex.view_expr (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) = Some (EConvert ts x) ->
  conversion_target_ref idx er <> None.
Proof. intro Hv. destruct (conversion_target_ref_of_view idx er ts x Hv) as [tr [Hc _]]. rewrite Hc. discriminate. Qed.

Lemma conversion_operand_ref_not_none {p} (idx : GoIndex.Snap.SyntaxIndex p) (er : GoIndex.ExprRef p) ts x :
  GoIndex.view_expr (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) = Some (EConvert ts x) ->
  conversion_operand_ref idx er <> None.
Proof. intro Hv. destruct (conversion_operand_ref_of_view idx er ts x Hv) as [opr [Hc _]]. rewrite Hc. discriminate. Qed.

(* the generic total projection of a proved-non-[None] option (the [False_rect] discharges the impossible
   branch by the SAME proof — never a semantic fallback). *)
Definition from_some {A} (o : option A) (H : o <> None) : A :=
  match o return o <> None -> A with Some a => fun _ => a | None => fun H0 => False_rect A (H0 eq_refl) end H.
Lemma from_some_eq {A} (o : option A) (H : o <> None) (a : A) : o = Some a -> from_some o H = a.
Proof. intro Heq. subst o. reflexivity. Qed.

(* §3.2 the TOTAL typed conversion children on the live path: given the ref's source view IS a conversion, the
   target/operand refs are obtained THROUGH the retained index with NO [None] fallback (the impossible branch is
   [False_rect] of the [not_none] proof).  The production recursion consumes exactly these. *)
Definition conversion_target_ref_tot {p} (idx : GoIndex.Snap.SyntaxIndex p) (er : GoIndex.ExprRef p) ts x
    (Hv : GoIndex.view_expr (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) = Some (EConvert ts x))
  : GoIndex.TypeNameRef p :=
  from_some (conversion_target_ref idx er) (conversion_target_ref_not_none idx er ts x Hv).
Definition conversion_operand_ref_tot {p} (idx : GoIndex.Snap.SyntaxIndex p) (er : GoIndex.ExprRef p) ts x
    (Hv : GoIndex.view_expr (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) = Some (EConvert ts x))
  : GoIndex.ExprRef p :=
  from_some (conversion_operand_ref idx er) (conversion_operand_ref_not_none idx er ts x Hv).

Lemma conversion_target_ref_tot_eq {p} (idx : GoIndex.Snap.SyntaxIndex p) (er : GoIndex.ExprRef p) ts x Hv tr :
  conversion_target_ref idx er = Some tr -> conversion_target_ref_tot idx er ts x Hv = tr.
Proof. intro Heq. unfold conversion_target_ref_tot. apply from_some_eq. exact Heq. Qed.
Lemma conversion_operand_ref_tot_eq {p} (idx : GoIndex.Snap.SyntaxIndex p) (er : GoIndex.ExprRef p) ts x Hv opr :
  conversion_operand_ref idx er = Some opr -> conversion_operand_ref_tot idx er ts x Hv = opr.
Proof. intro Heq. unfold conversion_operand_ref_tot. apply from_some_eq. exact Heq. Qed.

(* the total children recover their exact source facts (via the [_of_view] witnesses + the [_tot_eq] projection):
   the operand ref's view is the exact operand [x]; the target ref recovers the exact source syntax [ts]. *)
Lemma conversion_operand_ref_tot_view {p} (idx : GoIndex.Snap.SyntaxIndex p) (er : GoIndex.ExprRef p) ts x Hv :
  GoIndex.view_expr (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref (conversion_operand_ref_tot idx er ts x Hv))) = Some x.
Proof.
  destruct (conversion_operand_ref_of_view idx er ts x Hv) as [opr [Hc [_ [_ Hview]]]].
  rewrite (conversion_operand_ref_tot_eq idx er ts x Hv opr Hc). exact Hview.
Qed.

(* the constant status of a CONVERSION node in terms of its operand's status (one [convert_const]): the ONE
   place production reduces [const_info (EConvert …)] to expose the operand status, WITHOUT [cbn]-expanding the
   operand's own [const_info] into a stuck match. *)
Lemma const_info_conv_eq : forall ts x,
  const_info (EConvert ts x)
  = match const_info x with
    | Some ci => option_map (CITyped (predeclared_type ts)) (convert_const (predeclared_type ts) ci)
    | None => None
    end.
Proof. intros ts x. reflexivity. Qed.

(* ---- §8 OCCURRENCE-KEYED TYPE-NAME FACTS: a conversion's SOURCE type name resolves (§7) to a semantic
   [GoType]; the fact stores THAT resolved type ONLY (no syntax copy — the retained [TypeNameRef] + source view
   carry source identity, so [byte]/[uint8] stay distinct SOURCES with EQUAL facts).  One sealed NodeKey-keyed
   standard map, built by the ONE retained visit fold (never a second AST walk), analogous to [ExprFactTable]. *)

Record TypeNameFact : Type := mkTypeNameFact { tnf_type : GoType }.

(* the type-name fact of a single occurrence: [Some] EXACTLY for a KTypeName occurrence, resolving its retained
   source [TypeSyntax] through the predeclared context; non-type-name occurrences contribute nothing. *)
Definition occ_type_name_fact (o : GoIndex.SourceOccurrence) : option TypeNameFact :=
  match GoIndex.view_typename o with
  | Some ts => Some (mkTypeNameFact (predeclared_type ts))
  | None => None
  end.

Lemma occ_type_name_fact_some : forall o ts,
  GoIndex.view_typename o = Some ts -> occ_type_name_fact o = Some (mkTypeNameFact (predeclared_type ts)).
Proof. intros o ts H. unfold occ_type_name_fact. rewrite H. reflexivity. Qed.
Lemma occ_type_name_fact_none : forall o,
  GoIndex.view_typename o = None -> occ_type_name_fact o = None.
Proof. intros o H. unfold occ_type_name_fact. rewrite H. reflexivity. Qed.

Definition add_tn_fact {p} (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)
    (m : GoIndex.NodeKeyMapBase.t TypeNameFact) : GoIndex.NodeKeyMapBase.t TypeNameFact :=
  match occ_type_name_fact (snd ro) with
  | Some f => GoIndex.NodeKeyMapBase.add (GoIndex.Snap.node_ref_key (fst ro)) f m
  | None => m
  end.

Lemma tn_facts_not_in_domain {p} (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) (k : GoIndex.NodeKey) :
  ~ In k (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) l) ->
  GoIndex.NodeKeyMapBase.find k (fold_right add_tn_fact (GoIndex.NodeKeyMapBase.empty TypeNameFact) l) = None.
Proof.
  induction l as [|[r0 occ0] rest IH]; intros Hni; simpl.
  - apply GoIndex.NodeKeyMapFacts.empty_o.
  - simpl in Hni.
    assert (Hne : GoIndex.Snap.node_ref_key r0 <> k) by (intro H; apply Hni; left; exact H).
    assert (Hrest : ~ In k (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) rest))
      by (intro H; apply Hni; right; exact H).
    unfold add_tn_fact; cbn [snd fst]. destruct (occ_type_name_fact occ0) as [f|].
    + rewrite GoIndex.nodekeymap_add_neq by exact Hne. exact (IH Hrest).
    + exact (IH Hrest).
Qed.

Lemma tn_fold_facts_find {p} (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) r occ :
  NoDup (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) l) ->
  In (r, occ) l ->
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key r)
    (fold_right add_tn_fact (GoIndex.NodeKeyMapBase.empty TypeNameFact) l) = occ_type_name_fact occ.
Proof.
  induction l as [|[r0 occ0] rest IH]; intros Hnd Hin; [ destruct Hin |].
  simpl in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hni Hnd'].
  simpl. destruct Hin as [Heq | Hin].
  - injection Heq as <- <-. unfold add_tn_fact; cbn [snd fst].
    destruct (occ_type_name_fact occ0) as [f|] eqn:Ef.
    + rewrite GoIndex.nodekeymap_add_eq. reflexivity.
    + apply tn_facts_not_in_domain. exact Hni.
  - assert (Hin' : In (GoIndex.Snap.node_ref_key r)
             (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) rest)).
    { apply in_map_iff. exists (r, occ). split; [reflexivity | exact Hin]. }
    assert (Hkr : GoIndex.Snap.node_ref_key r <> GoIndex.Snap.node_ref_key r0)
      by (intro Hk; apply Hni; rewrite <- Hk; exact Hin').
    unfold add_tn_fact; cbn [snd fst]. destruct (occ_type_name_fact occ0) as [f0|].
    + rewrite GoIndex.nodekeymap_add_neq by (intro Hk; apply Hkr; symmetry; exact Hk).
      exact (IH Hnd' Hin).
    + exact (IH Hnd' Hin).
Qed.

Lemma tn_fold_facts_domain {p} (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) k f :
  GoIndex.NodeKeyMapBase.find k (fold_right add_tn_fact (GoIndex.NodeKeyMapBase.empty TypeNameFact) l) = Some f ->
  exists ro, In ro l /\ GoIndex.Snap.node_ref_key (fst ro) = k /\ occ_type_name_fact (snd ro) = Some f.
Proof.
  induction l as [|ro rest IH]; intro Hf.
  - rewrite GoIndex.NodeKeyMapFacts.empty_o in Hf; discriminate Hf.
  - cbn [fold_right] in Hf. unfold add_tn_fact in Hf.
    destruct (occ_type_name_fact (snd ro)) as [f0|] eqn:Ef.
    + destruct (GoIndex.thm8_nodekey_eq_dec (GoIndex.Snap.node_ref_key (fst ro)) k) as [He|Hne].
      * subst k. rewrite GoIndex.nodekeymap_add_eq in Hf. injection Hf as <-.
        exists ro. split; [left; reflexivity | split; [reflexivity | exact Ef]].
      * rewrite GoIndex.nodekeymap_add_neq in Hf by exact Hne.
        destruct (IH Hf) as [ro' [Hin [Hk Hfe]]]. exists ro'. split; [right; exact Hin | split; [exact Hk | exact Hfe]].
    + destruct (IH Hf) as [ro' [Hin [Hk Hfe]]]. exists ro'. split; [right; exact Hin | split; [exact Hk | exact Hfe]].
Qed.

Definition prog_type_name_facts (p : GoProgram) : GoIndex.NodeKeyMapBase.t TypeNameFact :=
  fold_right add_tn_fact (GoIndex.NodeKeyMapBase.empty TypeNameFact) (prog_visit p).

Lemma prog_type_name_facts_find (p : GoProgram) (r : GoIndex.Snap.NodeRef p) occ :
  In (r, occ) (prog_visit p) ->
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key r) (prog_type_name_facts p) = occ_type_name_fact occ.
Proof. intro Hin. apply tn_fold_facts_find; [ apply prog_visit_key_nodup | exact Hin ]. Qed.

Lemma prog_type_name_facts_domain (p : GoProgram) k f :
  GoIndex.NodeKeyMapBase.find k (prog_type_name_facts p) = Some f ->
  exists (r : GoIndex.Snap.NodeRef p) occ, In (r, occ) (prog_visit p)
    /\ GoIndex.Snap.node_ref_key r = k /\ occ_type_name_fact occ = Some f.
Proof.
  intro Hf. destruct (tn_fold_facts_domain (prog_visit p) k f Hf) as [[r occ] [Hin [Hk Hfe]]].
  exists r, occ. cbn [fst snd] in *. split; [exact Hin | split; [exact Hk | exact Hfe]].
Qed.

(** the SEALED type-name-fact table: the standard NodeKey map + domain (keys are EXACTLY the visited
    type-name occurrences — no expression/statement/file/package/foreign key) + completeness (each visited
    occurrence's fact is exact).  Mirrors [ExprFactTable]; a forged foreign-key table is unrepresentable. *)
(* [ip] is intentionally ABSENT: the table's contents and its domain/completeness proofs speak only of [p] (the
   snapshot), so a single table object serves any indexing of [p].  This is what lets the production outcome path
   and the diagnostics thread the SAME [idx]-parameterized authority without an [IndexedProgram] cascade. *)
Record TypeNameFactTable (p : GoProgram) : Type := mkTypeNameFactTable {
  tnft_map      : GoIndex.NodeKeyMapBase.t TypeNameFact ;
  tnft_domain   : forall k f, GoIndex.NodeKeyMapBase.find k tnft_map = Some f ->
                    exists (r : GoIndex.Snap.NodeRef p) occ, In (r, occ) (prog_visit p)
                      /\ GoIndex.Snap.node_ref_key r = k /\ occ_type_name_fact occ = Some f ;
  tnft_complete : forall r occ, In (r, occ) (prog_visit p) ->
                    GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key r) tnft_map = occ_type_name_fact occ
}.
Arguments mkTypeNameFactTable {p} _ _ _.
Arguments tnft_map {p} _.
Arguments tnft_domain {p} _.
Arguments tnft_complete {p} _.

(** §3.3 the TABLE-LEVEL total query the production outcome path CONSUMES: given the retained
    [TypeNameFactTable] OBJECT, project its stored entry for a [TypeNameRef].  Totality comes from the table's own
    [tnft_complete] proof (every KTypeName occurrence resolves), NOT from re-resolving; it never calls
    [predeclared_type] and never rebuilds the map.  [elaborate] passes the SAME object to the outcome builder and
    seals it into [ElaborationFacts]; the public [type_name_fact_at] delegates to THIS query. *)
Lemma tnft_table_not_none {p} (tnft : TypeNameFactTable p) (tr : GoIndex.TypeNameRef p) :
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref tr)) (tnft_map tnft) <> None.
Proof.
  destruct (GoIndex.kind_view_typename _ (GoIndex.noderefof_kind tr)) as [ts Hv].
  rewrite (tnft_complete tnft (GoIndex.erase_ref tr) (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref tr))
             (noderef_in_prog_visit p (GoIndex.erase_ref tr))).
  rewrite (occ_type_name_fact_some _ ts Hv). discriminate.
Qed.
Definition type_name_fact_at_table {p} (tnft : TypeNameFactTable p) (tr : GoIndex.TypeNameRef p) : TypeNameFact :=
  from_some (GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref tr)) (tnft_map tnft))
            (tnft_table_not_none tnft tr).
Lemma type_name_fact_at_table_find {p} (tnft : TypeNameFactTable p) (tr : GoIndex.TypeNameRef p) f :
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref tr)) (tnft_map tnft) = Some f ->
  type_name_fact_at_table tnft tr = f.
Proof. intro Hf. unfold type_name_fact_at_table. apply from_some_eq. exact Hf. Qed.
Lemma type_name_fact_at_table_resolves {p} (tnft : TypeNameFactTable p) (tr : GoIndex.TypeNameRef p) ts :
  GoIndex.type_name_ref_syntax tr = Some ts -> type_name_fact_at_table tnft tr = mkTypeNameFact (predeclared_type ts).
Proof.
  intro Hts. unfold GoIndex.type_name_ref_syntax in Hts. apply type_name_fact_at_table_find.
  rewrite (tnft_complete tnft (GoIndex.erase_ref tr) (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref tr))
             (noderef_in_prog_visit p (GoIndex.erase_ref tr))).
  exact (occ_type_name_fact_some _ ts Hts).
Qed.

(* ---- OPERAND-CLOSURE of the visit stream (the bottom-up accumulator's totality): a conversion's operand is a
   LATER preorder node in the SAME file, so it lies in the ALREADY-FOLDED tail [l2] — its outcome is already in
   the accumulator when the conversion step reads it. ---- *)
Lemma SS_prefix_lt {A} (R : A -> A -> Prop) (a : list A) (v : A) (b : list A) :
  StronglySorted R (a ++ v :: b) -> Forall (fun z => R z v) a.
Proof.
  induction a as [|y a IH]; intro Hss; [constructor|].
  cbn [app] in Hss. apply StronglySorted_inv in Hss. destruct Hss as [Hss Hall].
  constructor; [ rewrite Forall_forall in Hall; apply Hall, in_or_app; right; left; reflexivity | apply IH; exact Hss ].
Qed.

Lemma ss_after_local {p} (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) P y S :
  StronglySorted Pos.lt (map (fun rc => GoIndex.Snap.node_ref_local (fst rc)) l) ->
  l = P ++ y :: S ->
  forall z, In z l -> (GoIndex.Snap.node_ref_local (fst y) < GoIndex.Snap.node_ref_local (fst z))%positive -> In z S.
Proof.
  intros Hss Hsplit z Hz Hlt. subst l. rewrite map_app in Hss. cbn [map] in Hss.
  pose proof (SS_prefix_lt _ (map (fun rc => GoIndex.Snap.node_ref_local (fst rc)) P)
                (GoIndex.Snap.node_ref_local (fst y))
                (map (fun rc => GoIndex.Snap.node_ref_local (fst rc)) S) Hss) as Hpre.
  apply in_app_or in Hz. destruct Hz as [HzP | [Hzy | HzS]].
  - exfalso. rewrite Forall_forall in Hpre.
    assert (Hzin : In (GoIndex.Snap.node_ref_local (fst z)) (map (fun rc => GoIndex.Snap.node_ref_local (fst rc)) P))
      by (apply in_map_iff; exists z; split; [reflexivity | exact HzP]).
    exact (Pos.lt_irrefl _ (Pos.lt_trans _ _ _ Hlt (Hpre _ Hzin))).
  - subst z. exact (False_ind _ (Pos.lt_irrefl _ Hlt)).
  - exact HzS.
Qed.

Lemma split_unique {A} (x : A) (l1 l2 a b : list A) :
  l1 ++ x :: l2 = a ++ x :: b -> ~ In x l1 -> ~ In x a -> l2 = b.
Proof.
  revert a; induction l1 as [|y l1 IH]; intros a Heq Hnl1 Hna.
  - destruct a as [|z a]; cbn [app] in Heq.
    + injection Heq as Hrest. exact Hrest.
    + injection Heq as He Hrest. exfalso. apply Hna. left. symmetry; exact He.
  - destruct a as [|z a]; cbn [app] in Heq.
    + injection Heq as He Hrest. exfalso. apply Hnl1. left. exact He.
    + injection Heq as He Hrest. apply (IH a Hrest);
        [ intro Hbad; apply Hnl1; right; exact Hbad | intro Hbad; apply Hna; right; exact Hbad ].
Qed.

Lemma prog_visit_not_in_prefix {p} (L : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) l1 r occ l2 :
  NoDup (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) L) -> L = l1 ++ (r, occ) :: l2 -> ~ In (r, occ) l1.
Proof.
  intros Hnd HL Hbad. rewrite HL, map_app in Hnd. cbn [map fst] in Hnd.
  apply NoDup_remove_2 in Hnd. apply Hnd, in_or_app. left.
  apply in_map_iff. exists (r, occ). split; [reflexivity | exact Hbad].
Qed.

Lemma prog_visit_operand_closed (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p) :
  forall l1 r occ l2, prog_visit p = l1 ++ (r, occ) :: l2 ->
    forall e x, GoIndex.view_expr occ = Some e -> expr_child e = Some x ->
    exists r' occ', GoIndex.Snap.node_ref_key r' = operand_key r /\ GoIndex.view_expr occ' = Some x /\ In (r', occ') l2.
Proof.
  intros l1 r occ l2 Hsplit e x Hv Hc.
  assert (Hin_ro : In (r, occ) (prog_visit p)) by (rewrite Hsplit; apply in_or_app; right; left; reflexivity).
  destruct (prog_visit_operand p idx r occ e x Hin_ro Hv Hc) as [r' [Hin'p [Hkey [Hvx _]]]].
  exists r', (GoIndex.Snap.source_occurrence_of_ref r'). split; [exact Hkey | split; [exact Hvx |]].
  pose proof Hin_ro as Hb0. rewrite prog_visit_flat_map in Hb0. apply in_flat_map in Hb0. destruct Hb0 as [b [Hb Hrb]].
  unfold binding_visit in Hrb. destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|] eqn:Ef; [|destruct Hrb].
  pose proof (GoIndex.Snap.visit_file_view p fr r occ Hrb) as [_ Hfile].
  pose proof (GoIndex.Snap.node_ref_key_eq r') as Hk'. rewrite Hkey in Hk'. unfold operand_key in Hk'.
  rewrite GoIndex.Snap.node_ref_key_eq in Hk'. cbn [GoIndex.nk_file] in Hk'. rewrite Hfile in Hk'.
  injection Hk' as Hpatheq Hloceq.
  assert (Hfile' : GoIndex.Snap.node_ref_file r' = fr) by (apply GoIndex.Snap.file_ref_path_inj; symmetry; exact Hpatheq).
  pose proof (GoIndex.Snap.visit_file_complete p fr r' Hfile') as Hin'block.
  apply in_split in Hrb. destruct Hrb as [P [S Hvfsplit]].
  assert (Hin'S : In (r', GoIndex.Snap.source_occurrence_of_ref r') S).
  { apply (ss_after_local (GoIndex.Snap.visit_file fr) P (r, occ) S (GoIndex.Snap.visit_file_order p fr) Hvfsplit
             (r', GoIndex.Snap.source_occurrence_of_ref r') Hin'block).
    cbn [fst]. rewrite <- Hloceq. lia. }
  apply in_split in Hb. destruct Hb as [B1 [B2 Hbsplit]].
  assert (Hbv : binding_visit p b = GoIndex.Snap.visit_file fr) by (unfold binding_visit; rewrite Ef; reflexivity).
  assert (Hpv : prog_visit p = (flat_map (binding_visit p) B1 ++ P) ++ (r, occ) :: (S ++ flat_map (binding_visit p) B2)).
  { rewrite prog_visit_flat_map, Hbsplit, flat_map_app. cbn [flat_map]. rewrite Hbv, Hvfsplit.
    rewrite <- !app_assoc. reflexivity. }
  pose proof (prog_visit_key_nodup p) as Hnd.
  assert (Hl2 : l2 = S ++ flat_map (binding_visit p) B2).
  { apply (split_unique (r, occ) l1 l2 (flat_map (binding_visit p) B1 ++ P) (S ++ flat_map (binding_visit p) B2)).
    - rewrite <- Hsplit. exact Hpv.
    - exact (prog_visit_not_in_prefix (prog_visit p) l1 r occ l2 Hnd Hsplit).
    - exact (prog_visit_not_in_prefix (prog_visit p) (flat_map (binding_visit p) B1 ++ P) r occ
               (S ++ flat_map (binding_visit p) B2) Hnd Hpv). }
  rewrite Hl2. apply in_or_app. left. exact Hin'S.
Qed.

(* ---- §3.4 THE ONE PROOF-CARRYING BOTTOM-UP OUTCOME ACCUMULATOR.  Fold-right over the retained source-order
   visit (§3.4 "another exact source-order stream" — a conversion's operand is a LATER preorder node, hence in
   the already-folded suffix).  Each conversion step queries the passed-in [TypeNameFactTable] OBJECT at its
   target ref, reads its operand's ALREADY-COMPUTED outcome from the accumulator at the operand ref (TOTAL, via
   [from_some] of the operand-closure proof — never a fallback), and calls [convert_const] ONCE.  No structural
   recursion on the GoExpr, no [const_info] on the live path. ---- *)

(* the use-context role an expression reference carries (its source occurrence's role). *)
Definition expr_ref_role {p} (er : GoIndex.ExprRef p) : GoIndex.NodeRole :=
  GoIndex.occurrence_role (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)).

(* one conversion's outcome from its target-table query + operand outcome — ONE convert_const. *)
Definition conv_outcome {p} (tnft : TypeNameFactTable p) (er : GoIndex.ExprRef p)
    (tr : GoIndex.TypeNameRef p) (opr : GoIndex.ExprRef p) (oo : ExprOutcome p) : ExprOutcome p :=
  match oo with
  | EOOk opf =>
      match convert_const (tnf_type (type_name_fact_at_table tnft tr)) (ef_const_status opf) with
      | Some tc => EOOk (mkExprFact (CITyped (tnf_type (type_name_fact_at_table tnft tr)) tc)
                          (use_resolved_of_ci (expr_ref_role er)
                             (CITyped (tnf_type (type_name_fact_at_table tnft tr)) tc)))
      | None    => EOConvFail er tr opr (tnf_type (type_name_fact_at_table tnft tr)) (ef_const_status opf)
      end
  | _ => EOChildFail
  end.

(* a LEAF's constant — NO fake [EConvert] case (a dependent proof the constructor is a leaf). *)
Lemma expr_child_leaf_absurd (ts : GoAST.TypeSyntax) (x : GoExpr) : expr_child (EConvert ts x) = None -> False.
Proof. cbn [expr_child]. discriminate. Qed.
Definition leaf_const (e : GoExpr) : expr_child e = None -> ConstInfo :=
  match e return expr_child e = None -> ConstInfo with
  | EBool b     => fun _ => CIUntyped (CBool b)
  | EInt n      => fun _ => CIUntyped (CInt (Z.of_N n))
  | ENeg n      => fun _ => CIUntyped (CInt (- Z.of_N n))
  | EString s   => fun _ => CIUntyped (CString s)
  | EFloat d    => fun _ => CIUntyped (CFloat (decimal_value d))
  | EComplex dc => fun _ => CIUntyped (CComplex (decimal_complex_value dc))
  | EConvert ts x => fun H => False_rect ConstInfo (expr_child_leaf_absurd ts x H)
  end.
Lemma leaf_const_status (e : GoExpr) (H : expr_child e = None) : const_info e = Some (leaf_const e H).
Proof. destruct e as [ b|n|n0|s|d|dc| ts x ]; try reflexivity. exfalso. exact (expr_child_leaf_absurd ts x H). Qed.

(* a leaf occurrence's outcome — its untyped fact + its use-context resolution from that same status. *)
Definition leaf_outcome {p} (er : GoIndex.ExprRef p) (ci : ConstInfo) : ExprOutcome p :=
  EOOk (mkExprFact ci (use_resolved_of_ci (expr_ref_role er) ci)).

(* the accumulator EXISTENCE invariant: every visited expression occurrence in [l] has an entry. *)
Definition outcome_covers {p} (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence))
    (m : GoIndex.NodeKeyMapBase.t (ExprOutcome p)) : Prop :=
  forall r occ e, In (r, occ) l -> GoIndex.view_expr occ = Some e ->
    GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key r) m <> None.

(* a conversion's operand entry is present in a suffix-complete accumulator (operand-closure + covers). *)
Lemma operand_covered (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p) l1 r occ l2 ts x
    (m : GoIndex.NodeKeyMapBase.t (ExprOutcome p)) :
  prog_visit p = l1 ++ (r, occ) :: l2 -> GoIndex.view_expr occ = Some (EConvert ts x) ->
  outcome_covers l2 m ->
  GoIndex.NodeKeyMapBase.find (operand_key r) m <> None.
Proof.
  intros Hsplit Hv Hcov.
  destruct (prog_visit_operand_closed p idx l1 r occ l2 Hsplit (EConvert ts x) x Hv eq_refl)
    as [r' [occ' [Hkey [Hvx Hin']]]].
  rewrite <- Hkey. exact (Hcov r' occ' x Hin' Hvx).
Qed.

(** a conversion whose operand succeeds but whose own conversion step fails — returns (target, operand status).
    (Moved above the outcome accumulator so the accumulator invariant can name the LOCAL invalid-conversion
    evidence it stores.) *)
Definition local_conv_failure (e : GoExpr) : option (GoType * ConstInfo) :=
  match e with
  | EConvert ts x =>
      match const_info x with
      | Some ci => match convert_const (predeclared_type ts) ci with
                   | None => Some (predeclared_type ts, ci) | Some _ => None end
      | None => None end
  | _ => None
  end.

(** ---- §3.4/§3.6 THE STORED OUTCOME'S PROJECTION INVARIANT.  The accumulator invariant carried by
    [build_outcomes]: every visited expression occurrence has a stored outcome that MATCHES the occurrence —
    an EOOk fact is EXACTLY [occ_expr_fact]; an [EOConvFail] carries the occurrence's OWN ExprRef, its retained
    target/operand refs, and a genuine [local_conv_failure] (its convert_const-rejects evidence); a non-EOOk
    outcome has no fact.  Discharged IN PLACE at each fold step (leaf / conversion), so the whole projection —
    facts AND diagnostics — is [proj2_sig] of the fold, with NO post-hoc reduction of the fold term. ---- *)

(* the LOCAL invalid-conversion evidence an [EOConvFail] must carry: the failing occurrence's OWN ExprRef, its
   retained target + operand refs, and a genuine [local_conv_failure] to the stored (target, operand status). *)
Definition outcome_convfail_ev {p} (idx : GoIndex.Snap.SyntaxIndex p) (r : GoIndex.Snap.NodeRef p)
    (occ : GoIndex.SourceOccurrence) (er2 : GoIndex.ExprRef p) (tr2 : GoIndex.TypeNameRef p)
    (opr2 : GoIndex.ExprRef p) (t : GoType) (ci : ConstInfo) : Prop :=
  GoIndex.as_expr idx r = Some er2
  /\ (exists e, GoIndex.view_expr occ = Some e /\ local_conv_failure e = Some (t, ci))
  /\ conversion_target_ref idx er2 = Some tr2
  /\ conversion_operand_ref idx er2 = Some opr2.

Definition outcome_matches {p} (idx : GoIndex.Snap.SyntaxIndex p) (r : GoIndex.Snap.NodeRef p)
    (occ : GoIndex.SourceOccurrence) (out : ExprOutcome p) : Prop :=
  match out with
  | EOOk f => occ_expr_fact occ = Some f
  | EOConvFail er2 tr2 opr2 t ci => occ_expr_fact occ = None /\ outcome_convfail_ev idx r occ er2 tr2 opr2 t ci
  (* blocked-by-child: the operand failed, so this occurrence is a conversion whose OWN step is NOT a local
     invalid conversion ([local_conv_failure] = None) — the diagnostic is anchored at the operand, not here. *)
  | EOChildFail => occ_expr_fact occ = None /\ (exists e, GoIndex.view_expr occ = Some e /\ local_conv_failure e = None)
  end.

(* the FACT-only projection (facts layer): an EOOk fact is exact, any other outcome has no fact. *)
Definition outcome_proj_fact {p} (out : ExprOutcome p) (occ : GoIndex.SourceOccurrence) : Prop :=
  match out with
  | EOOk f => occ_expr_fact occ = Some f
  | _      => occ_expr_fact occ = None
  end.

Lemma outcome_matches_proj {p} (idx : GoIndex.Snap.SyntaxIndex p) r occ (out : ExprOutcome p) :
  outcome_matches idx r occ out -> outcome_proj_fact out occ.
Proof. destruct out as [f|? ? ? ? ?| ]; cbn [outcome_matches outcome_proj_fact]; intro H; [exact H | exact (proj1 H) | exact (proj1 H)]. Qed.

Definition outcomes_ok {p} (idx : GoIndex.Snap.SyntaxIndex p)
    (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence))
    (m : GoIndex.NodeKeyMapBase.t (ExprOutcome p)) : Prop :=
  forall r occ e, In (r, occ) l -> GoIndex.view_expr occ = Some e ->
    exists out, GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key r) m = Some out
             /\ outcome_matches idx r occ out.

Lemma outcomes_ok_covers {p} (idx : GoIndex.Snap.SyntaxIndex p)
    (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) m :
  outcomes_ok idx l m -> outcome_covers l m.
Proof. intros H r occ e Hin Hv. destruct (H r occ e Hin Hv) as [out [Hf _]]. rewrite Hf. discriminate. Qed.

(** ═══ §6 THE DIRECT OUTCOME-CAUSE RELATION ═══ the PRODUCTION cause of a stored outcome, read entirely off the
    retained phase: the table query at the retained target ref, the operand's ALREADY-COMPUTED outcome in the
    processed accumulator [prior], and ONE [convert_const] — NEVER [local_conv_failure], [conv_targets], a
    resolver call, or a recursive [const_info] of the conversion subtree.  This is the invariant the outcome
    table CARRIES (§2.5–§2.7); the bridge to the index-free source specification is a SEPARATE theorem. *)
Definition outcome_is_fail {p} (o : ExprOutcome p) : Prop :=
  match o with EOOk _ => False | _ => True end.

Inductive OutcomeCause {p} (idx : GoIndex.Snap.SyntaxIndex p) (tnft : TypeNameFactTable p)
    (prior : GoIndex.NodeKeyMapBase.t (ExprOutcome p))
    (r : GoIndex.Snap.NodeRef p) (occ : GoIndex.SourceOccurrence) : ExprOutcome p -> Prop :=
| OCLeaf : forall (er : GoIndex.ExprRef p) e ci,
    GoIndex.as_expr idx r = Some er -> GoIndex.erase_ref er = r ->
    GoIndex.view_expr occ = Some e -> expr_child e = None -> const_info e = Some ci ->
    OutcomeCause idx tnft prior r occ (leaf_outcome er ci)
| OCConvOk : forall (er : GoIndex.ExprRef p) ts x (tr : GoIndex.TypeNameRef p) (opr : GoIndex.ExprRef p) opf tc,
    GoIndex.as_expr idx r = Some er -> GoIndex.erase_ref er = r ->
    GoIndex.view_expr occ = Some (EConvert ts x) ->
    conversion_target_ref idx er = Some tr -> conversion_operand_ref idx er = Some opr ->
    GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref opr)) prior = Some (EOOk opf) ->
    convert_const (tnf_type (type_name_fact_at_table tnft tr)) (ef_const_status opf) = Some tc ->
    OutcomeCause idx tnft prior r occ
      (EOOk (mkExprFact (CITyped (tnf_type (type_name_fact_at_table tnft tr)) tc)
               (use_resolved_of_ci (expr_ref_role er)
                  (CITyped (tnf_type (type_name_fact_at_table tnft tr)) tc))))
| OCConvFail : forall (er : GoIndex.ExprRef p) ts x (tr : GoIndex.TypeNameRef p) (opr : GoIndex.ExprRef p) opf,
    GoIndex.as_expr idx r = Some er -> GoIndex.erase_ref er = r ->
    GoIndex.view_expr occ = Some (EConvert ts x) ->
    conversion_target_ref idx er = Some tr -> conversion_operand_ref idx er = Some opr ->
    GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref opr)) prior = Some (EOOk opf) ->
    convert_const (tnf_type (type_name_fact_at_table tnft tr)) (ef_const_status opf) = None ->
    OutcomeCause idx tnft prior r occ
      (EOConvFail er tr opr (tnf_type (type_name_fact_at_table tnft tr)) (ef_const_status opf))
| OCChildFail : forall (er : GoIndex.ExprRef p) ts x (tr : GoIndex.TypeNameRef p) (opr : GoIndex.ExprRef p) oout,
    GoIndex.as_expr idx r = Some er -> GoIndex.erase_ref er = r ->
    GoIndex.view_expr occ = Some (EConvert ts x) ->
    conversion_target_ref idx er = Some tr -> conversion_operand_ref idx er = Some opr ->
    GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref opr)) prior = Some oout ->
    outcome_is_fail oout ->
    OutcomeCause idx tnft prior r occ EOChildFail.

(* the computed LEAF outcome is directly caused: [leaf_outcome er ci] is [OCLeaf]. *)
Lemma leaf_outcome_cause {p} (idx : GoIndex.Snap.SyntaxIndex p) (tnft : TypeNameFactTable p) prior
    (r : GoIndex.Snap.NodeRef p) occ (er : GoIndex.ExprRef p) e ci :
  GoIndex.as_expr idx r = Some er -> GoIndex.erase_ref er = r ->
  GoIndex.view_expr occ = Some e -> expr_child e = None -> const_info e = Some ci ->
  OutcomeCause idx tnft prior r occ (leaf_outcome er ci).
Proof. intros; eapply OCLeaf; eassumption. Qed.

(* the computed CONVERSION outcome is directly caused: [conv_outcome tnft er tr opr oo] — where [oo] is the
   operand's outcome ALREADY stored in [prior] at the operand ref — satisfies [OutcomeCause] by ONE
   [convert_const] on the table query + operand-outcome status.  No source recomputation. *)
Lemma conv_outcome_cause {p} (idx : GoIndex.Snap.SyntaxIndex p) (tnft : TypeNameFactTable p) prior
    (r : GoIndex.Snap.NodeRef p) occ (er : GoIndex.ExprRef p) ts x
    (tr : GoIndex.TypeNameRef p) (opr : GoIndex.ExprRef p) oo :
  GoIndex.as_expr idx r = Some er -> GoIndex.erase_ref er = r ->
  GoIndex.view_expr occ = Some (EConvert ts x) ->
  conversion_target_ref idx er = Some tr -> conversion_operand_ref idx er = Some opr ->
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref opr)) prior = Some oo ->
  OutcomeCause idx tnft prior r occ (conv_outcome tnft er tr opr oo).
Proof.
  intros Hae Her Hv Htr Hopr Hfind. destruct oo as [opf | er2 tr2 opr2 t2 ci2 | ]; cbn [conv_outcome].
  - destruct (convert_const (tnf_type (type_name_fact_at_table tnft tr)) (ef_const_status opf)) as [tc|] eqn:E.
    + eapply OCConvOk; eassumption.
    + eapply OCConvFail; eassumption.
  - eapply OCChildFail; try eassumption. exact I.
  - eapply OCChildFail; try eassumption. exact I.
Qed.

(* [OutcomeCause] is PRESERVED when the accumulator is extended with a FRESH key (one not already present): the
   operand lookup the cause reads is at a key already in [prior] (its find is [Some]), so it is unaffected by an
   add at a fresh key.  This is what lets the bottom-up fold state each entry's cause against the FINAL map. *)
Lemma OutcomeCause_add_fresh {p} (idx : GoIndex.Snap.SyntaxIndex p) (tnft : TypeNameFactTable p)
    (prior : GoIndex.NodeKeyMapBase.t (ExprOutcome p)) k v
    (r : GoIndex.Snap.NodeRef p) occ out :
  GoIndex.NodeKeyMapBase.find k prior = None ->
  OutcomeCause idx tnft prior r occ out ->
  OutcomeCause idx tnft (GoIndex.NodeKeyMapBase.add k v prior) r occ out.
Proof.
  intros Hfresh HC. destruct HC as
    [ er e ci Hae Her Hv Hchild Hci
    | er ts x tr opr opf tc Hae Her Hv Htr Hopr Hfind Hcv
    | er ts x tr opr opf Hae Her Hv Htr Hopr Hfind Hcv
    | er ts x tr opr oout Hae Her Hv Htr Hopr Hfind Hfail ].
  - eapply OCLeaf; eassumption.
  - assert (Hne : k <> GoIndex.Snap.node_ref_key (GoIndex.erase_ref opr))
      by (intro Heq; rewrite Heq, Hfind in Hfresh; discriminate).
    eapply OCConvOk; try eassumption. rewrite GoIndex.nodekeymap_add_neq by exact Hne. exact Hfind.
  - assert (Hne : k <> GoIndex.Snap.node_ref_key (GoIndex.erase_ref opr))
      by (intro Heq; rewrite Heq, Hfind in Hfresh; discriminate).
    eapply OCConvFail; try eassumption. rewrite GoIndex.nodekeymap_add_neq by exact Hne. exact Hfind.
  - assert (Hne : k <> GoIndex.Snap.node_ref_key (GoIndex.erase_ref opr))
      by (intro Heq; rewrite Heq, Hfind in Hfresh; discriminate).
    eapply OCChildFail; try eassumption. rewrite GoIndex.nodekeymap_add_neq by exact Hne. exact Hfind.
Qed.

(* the CARRIED-CAUSE accumulator invariant: every visited expression occurrence has a stored outcome that is
   DIRECTLY CAUSED off the retained phase ([OutcomeCause] against the FINAL map), NOT a source-spec witness.
   This is what the [ExprOutcomeTable] carries (replacing the [outcome_convfail_ev]-based [outcome_matches] as the
   causal invariant); the bridge to the source specification is a separate exactness theorem. *)
Definition outcomes_caused {p} (idx : GoIndex.Snap.SyntaxIndex p) (tnft : TypeNameFactTable p)
    (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence))
    (m : GoIndex.NodeKeyMapBase.t (ExprOutcome p)) : Prop :=
  forall r occ e, In (r, occ) l -> GoIndex.view_expr occ = Some e ->
    exists out, GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key r) m = Some out
             /\ OutcomeCause idx tnft m r occ out.

(* the EXACT-DOMAIN invariant (§7): the stored map has NO key beyond the visited occurrences' keys — every
   present key is some visited occurrence's node key.  (This is also what supplies the fold's freshness
   [find (node_ref_key r) m_rest = None] from the visit-level [suffix_head_key_fresh].) *)
Definition outcome_dom_ok {p} (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence))
    (m : GoIndex.NodeKeyMapBase.t (ExprOutcome p)) : Prop :=
  forall k, GoIndex.NodeKeyMapBase.find k m <> None ->
    exists (r : GoIndex.Snap.NodeRef p) occ, In (r, occ) l /\ GoIndex.Snap.node_ref_key r = k.

Lemma outcome_dom_ok_empty {p} :
  outcome_dom_ok (@nil (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) (GoIndex.NodeKeyMapBase.empty (ExprOutcome p)).
Proof. intros k Hk. exfalso. apply Hk. apply GoIndex.NodeKeyMapFacts.empty_o. Qed.

Lemma outcome_dom_ok_skip {p} (r : GoIndex.Snap.NodeRef p) (occ : GoIndex.SourceOccurrence)
    (rest : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) m_rest :
  outcome_dom_ok rest m_rest -> outcome_dom_ok ((r, occ) :: rest) m_rest.
Proof.
  intros Hdom k Hk. destruct (Hdom k Hk) as [r0 [occ0 [Hin0 Hk0]]].
  exists r0, occ0. split; [right; exact Hin0 | exact Hk0].
Qed.

Lemma outcome_dom_ok_add {p} (r : GoIndex.Snap.NodeRef p) (occ : GoIndex.SourceOccurrence)
    (rest : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) m_rest (v : ExprOutcome p) :
  outcome_dom_ok rest m_rest ->
  outcome_dom_ok ((r, occ) :: rest) (GoIndex.NodeKeyMapBase.add (GoIndex.Snap.node_ref_key r) v m_rest).
Proof.
  intros Hdom k Hk.
  assert (HIn : GoIndex.NodeKeyMapBase.In k
                  (GoIndex.NodeKeyMapBase.add (GoIndex.Snap.node_ref_key r) v m_rest))
    by (rewrite GoIndex.NodeKeyMapFacts.in_find_iff; exact Hk).
  apply GoIndex.NodeKeyMapFacts.add_in_iff in HIn. destruct HIn as [Heq | HIn0].
  - exists r, occ. split; [left; reflexivity | exact Heq].
  - assert (Hkm : GoIndex.NodeKeyMapBase.find k m_rest <> None)
      by (rewrite <- GoIndex.NodeKeyMapFacts.in_find_iff; exact HIn0).
    destruct (Hdom k Hkm) as [r0 [occ0 [Hin0 Hk0]]].
    exists r0, occ0. split; [right; exact Hin0 | exact Hk0].
Qed.

(* the FRESH-KEY fact the fold needs: a suffix head's key is absent from the accumulator (its domain is the
   tail's visited keys, and the head key is fresh by [suffix_head_key_fresh]). *)
Lemma outcome_dom_head_fresh {p} (r : GoIndex.Snap.NodeRef p) (occ : GoIndex.SourceOccurrence)
    (rest : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) m_rest :
  outcome_dom_ok rest m_rest ->
  ~ In (GoIndex.Snap.node_ref_key r) (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) rest) ->
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key r) m_rest = None.
Proof.
  intros Hdom Hnd. destruct (GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key r) m_rest) as [w|] eqn:E;
    [exfalso | reflexivity].
  destruct (Hdom (GoIndex.Snap.node_ref_key r) (ltac:(rewrite E; discriminate))) as [r1 [occ1 [Hin1 Hk1]]].
  apply Hnd. rewrite <- Hk1. apply in_map_iff. exists (r1, occ1). split; [reflexivity | exact Hin1].
Qed.

Lemma outcomes_caused_skip {p} (idx : GoIndex.Snap.SyntaxIndex p) (tnft : TypeNameFactTable p)
    (r : GoIndex.Snap.NodeRef p) (occ : GoIndex.SourceOccurrence)
    (rest : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) m_rest :
  outcomes_caused idx tnft rest m_rest -> GoIndex.view_expr occ = None ->
  outcomes_caused idx tnft ((r, occ) :: rest) m_rest.
Proof.
  intros Hc Hv r0 occ0 e0 Hin0 Hv0. destruct Hin0 as [Heq | Hin0].
  - injection Heq as Hr0 Ho0. subst r0 occ0. rewrite Hv in Hv0; discriminate Hv0.
  - exact (Hc r0 occ0 e0 Hin0 Hv0).
Qed.

Lemma outcomes_caused_add {p} (idx : GoIndex.Snap.SyntaxIndex p) (tnft : TypeNameFactTable p)
    (r : GoIndex.Snap.NodeRef p) (occ : GoIndex.SourceOccurrence)
    (rest : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) e m_rest (v : ExprOutcome p) :
  outcomes_caused idx tnft rest m_rest -> outcome_dom_ok rest m_rest ->
  ~ In (GoIndex.Snap.node_ref_key r) (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) rest) ->
  GoIndex.view_expr occ = Some e ->
  OutcomeCause idx tnft (GoIndex.NodeKeyMapBase.add (GoIndex.Snap.node_ref_key r) v m_rest) r occ v ->
  outcomes_caused idx tnft ((r, occ) :: rest) (GoIndex.NodeKeyMapBase.add (GoIndex.Snap.node_ref_key r) v m_rest).
Proof.
  intros Hc Hdom Hnd Hv Hhead.
  pose proof (outcome_dom_head_fresh r occ rest m_rest Hdom Hnd) as Hfr.
  intros r0 occ0 e0 Hin0 Hv0. destruct Hin0 as [Heq | Hin0].
  - injection Heq as Hr0 Ho0. subst r0 occ0. exists v.
    split; [ apply GoIndex.nodekeymap_add_eq | exact Hhead ].
  - destruct (Hc r0 occ0 e0 Hin0 Hv0) as [out [Hf HC]]. exists out. split.
    + rewrite GoIndex.nodekeymap_add_neq;
        [ exact Hf | intro Hbad; apply Hnd; rewrite Hbad; apply in_map_iff; exists (r0, occ0); split; [reflexivity | exact Hin0] ].
    + exact (OutcomeCause_add_fresh idx tnft m_rest (GoIndex.Snap.node_ref_key r) v r0 occ0 out Hfr HC).
Qed.

(* the resolved target of a conversion's minted target ref, read from the passed-in TABLE OBJECT (not recomputed):
   the table's stored fact for [conversion_target_ref_tot …] is [predeclared_type ts]. *)
Lemma conv_target_table_type {p} (idx : GoIndex.Snap.SyntaxIndex p) (tnft : TypeNameFactTable p)
    (er : GoIndex.ExprRef p) ts x Hv :
  tnf_type (type_name_fact_at_table tnft (conversion_target_ref_tot idx er ts x Hv))
  = predeclared_type ts.
Proof.
  destruct (conversion_target_ref_of_view idx er ts x Hv) as [tr0 [Hc [_ [_ Hsyn]]]].
  rewrite (conversion_target_ref_tot_eq idx er ts x Hv tr0 Hc).
  rewrite (type_name_fact_at_table_resolves tnft tr0 ts Hsyn). reflexivity.
Qed.

(* a leaf occurrence's stored outcome matches (EOOk fact = exact [occ_expr_fact]).  The stored [ci] is the
   occurrence's own [const_info] (no fake fallback: the stored value carries no proof term). *)
Lemma leaf_stored_matches {p} (idx : GoIndex.Snap.SyntaxIndex p) (r : GoIndex.Snap.NodeRef p)
    (er : GoIndex.ExprRef p) occ e (ci : ConstInfo)
    (Hv : GoIndex.view_expr occ = Some e)
    (Hrole : GoIndex.occurrence_role occ = expr_ref_role er)
    (Hci : const_info e = Some ci) :
  outcome_matches idx r occ (leaf_outcome er ci).
Proof.
  cbn [outcome_matches leaf_outcome].
  rewrite (occ_expr_fact_status occ e ci Hv Hci).
  do 2 f_equal. rewrite <- Hrole. symmetry.
  exact (use_resolved_of_ci_eq occ e ci Hv Hci).
Qed.

(* a conversion occurrence's stored outcome ([conv_outcome] of the table query + the operand's outcome) matches:
   a successful operand's resolved-target [convert_const] IS the conversion's [const_info] step (EOOk fact, or a
   genuine [local_conv_failure] with the retained refs on reject); a failed operand has no fact (blocked). *)
Lemma conv_stored_matches {p} (idx : GoIndex.Snap.SyntaxIndex p) (tnft : TypeNameFactTable p)
    (r : GoIndex.Snap.NodeRef p) (er opr : GoIndex.ExprRef p) (tr : GoIndex.TypeNameRef p) occ operand_occ ts x
    (Hae : GoIndex.as_expr idx r = Some er)
    (Hv : GoIndex.view_expr occ = Some (EConvert ts x))
    (Hrole : GoIndex.occurrence_role occ = expr_ref_role er)
    (Htr : tnf_type (type_name_fact_at_table tnft tr) = predeclared_type ts)
    (Htr_ref : conversion_target_ref idx er = Some tr)
    (Hopr_ref : conversion_operand_ref idx er = Some opr)
    (operand_out : ExprOutcome p)
    (Hout_proj : outcome_proj_fact operand_out operand_occ)
    (Hopr_view : GoIndex.view_expr operand_occ = Some x) :
  outcome_matches idx r occ (conv_outcome tnft er tr opr operand_out).
Proof.
  unfold conv_outcome. destruct operand_out as [opf|c1 c2 c3 c4 c5| ].
  - (* operand succeeded: opf carries [const_info x] *)
    cbn [outcome_proj_fact] in Hout_proj. unfold occ_expr_fact in Hout_proj. rewrite Hopr_view in Hout_proj.
    destruct (const_info x) as [cx|] eqn:Ecx; [| discriminate Hout_proj].
    injection Hout_proj as Hopf. subst opf. cbn [ef_const_status].
    rewrite Htr.
    destruct (convert_const (predeclared_type ts) cx) as [tc|] eqn:Ecv.
    + (* conversion succeeds: EOOk typed fact = occurrence's [const_info] *)
      assert (Hci : const_info (EConvert ts x) = Some (CITyped (predeclared_type ts) tc)).
      { rewrite const_info_conv_eq, Ecx. cbn [option_map]. rewrite Ecv. reflexivity. }
      cbn [outcome_matches].
      rewrite (occ_expr_fact_status occ (EConvert ts x) (CITyped (predeclared_type ts) tc) Hv Hci).
      do 2 f_equal. rewrite <- Hrole. symmetry.
      exact (use_resolved_of_ci_eq occ (EConvert ts x) (CITyped (predeclared_type ts) tc) Hv Hci).
    + (* conversion rejects: EOConvFail carrying a genuine [local_conv_failure] + retained refs *)
      assert (Hlcf : local_conv_failure (EConvert ts x) = Some (predeclared_type ts, cx))
        by (cbn [local_conv_failure]; rewrite Ecx, Ecv; reflexivity).
      cbn [outcome_matches]. split.
      * unfold occ_expr_fact. rewrite Hv, const_info_conv_eq, Ecx. cbn [option_map]. rewrite Ecv. reflexivity.
      * unfold outcome_convfail_ev.
        split; [ exact Hae
               | split; [ exists (EConvert ts x); split; [exact Hv | exact Hlcf]
                        | split; [ exact Htr_ref | exact Hopr_ref ] ] ].
  - (* operand was a local invalid conversion: no operand fact => blocked, no fact + no local failure here *)
    cbn [outcome_proj_fact] in Hout_proj. unfold occ_expr_fact in Hout_proj. rewrite Hopr_view in Hout_proj.
    destruct (const_info x) as [cx|] eqn:Ecx; [discriminate Hout_proj|].
    cbn [outcome_matches]. split.
    + unfold occ_expr_fact. rewrite Hv, const_info_conv_eq, Ecx. reflexivity.
    + exists (EConvert ts x). split; [exact Hv | cbn [local_conv_failure]; rewrite Ecx; reflexivity].
  - (* operand was blocked-by-child: same *)
    cbn [outcome_proj_fact] in Hout_proj. unfold occ_expr_fact in Hout_proj. rewrite Hopr_view in Hout_proj.
    destruct (const_info x) as [cx|] eqn:Ecx; [discriminate Hout_proj|].
    cbn [outcome_matches]. split.
    + unfold occ_expr_fact. rewrite Hv, const_info_conv_eq, Ecx. reflexivity.
    + exists (EConvert ts x). split; [exact Hv | cbn [local_conv_failure]; rewrite Ecx; reflexivity].
Qed.

(* the fold step preserves the invariant: adding a matching outcome at a FRESH key keeps [outcomes_ok]. *)
Lemma outcomes_ok_add {p} (idx : GoIndex.Snap.SyntaxIndex p) (r : GoIndex.Snap.NodeRef p) occ rest e
    (m_rest : GoIndex.NodeKeyMapBase.t (ExprOutcome p)) (v : ExprOutcome p)
    (Hok_rest : outcomes_ok idx rest m_rest)
    (Hnd : ~ In (GoIndex.Snap.node_ref_key r) (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) rest))
    (Hv : GoIndex.view_expr occ = Some e)
    (Hvproj : outcome_matches idx r occ v) :
  outcomes_ok idx ((r, occ) :: rest) (GoIndex.NodeKeyMapBase.add (GoIndex.Snap.node_ref_key r) v m_rest).
Proof.
  intros r0 occ0 e0 Hin0 Hv0. destruct Hin0 as [Heq | Hin0].
  - injection Heq as Hr0 Ho0. subst r0 occ0. exists v. split; [ apply GoIndex.nodekeymap_add_eq | exact Hvproj ].
  - destruct (Hok_rest r0 occ0 e0 Hin0 Hv0) as [out [Hf Hpf]]. exists out. split; [| exact Hpf].
    rewrite GoIndex.nodekeymap_add_neq;
      [ exact Hf
      | intro Hbad; apply Hnd; rewrite Hbad; apply in_map_iff; exists (r0, occ0); split; [reflexivity | exact Hin0] ].
Qed.

(* a non-expression head keeps the tail's invariant (it contributes no entry). *)
Lemma outcomes_ok_skip {p} (idx : GoIndex.Snap.SyntaxIndex p) (r : GoIndex.Snap.NodeRef p) occ rest
    (m_rest : GoIndex.NodeKeyMapBase.t (ExprOutcome p))
    (Hok_rest : outcomes_ok idx rest m_rest) (Hv : GoIndex.view_expr occ = None) :
  outcomes_ok idx ((r, occ) :: rest) m_rest.
Proof.
  intros r0 occ0 e0 Hin0 Hv0. destruct Hin0 as [Heq | Hin0].
  - injection Heq as Hr0 Ho0. subst occ0. rewrite Hv in Hv0. discriminate Hv0.
  - exact (Hok_rest r0 occ0 e0 Hin0 Hv0).
Qed.

(* the operand entry of a conversion head is present in an ok suffix accumulator. *)
Lemma outcomes_ok_operand_present {p} (idx : GoIndex.Snap.SyntaxIndex p) l1 (r : GoIndex.Snap.NodeRef p) occ l2 ts x
    (m : GoIndex.NodeKeyMapBase.t (ExprOutcome p)) :
  prog_visit p = l1 ++ (r, occ) :: l2 -> GoIndex.view_expr occ = Some (EConvert ts x) ->
  outcomes_ok idx l2 m -> GoIndex.NodeKeyMapBase.find (operand_key r) m <> None.
Proof.
  intros Hsplit Hv Hok.
  exact (operand_covered p idx l1 r occ l2 ts x m Hsplit Hv (outcomes_ok_covers idx l2 m Hok)).
Qed.

(* the head of a suffix of the visit stream has a FRESH key (distinct from every tail key), by the visit's
   whole-program NodeKey [NoDup]. *)
Lemma suffix_head_key_fresh {p} pre (r : GoIndex.Snap.NodeRef p) occ rest :
  prog_visit p = pre ++ (r, occ) :: rest ->
  ~ In (GoIndex.Snap.node_ref_key r) (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) rest).
Proof.
  intro Hpre. pose proof (prog_visit_key_nodup p) as Hnd0.
  rewrite Hpre, map_app in Hnd0. cbn [map fst] in Hnd0.
  apply NoDup_remove_2 in Hnd0.
  intro Hbad. apply Hnd0. apply in_or_app. right. exact Hbad.
Qed.

(* a visited expression occurrence's ExprRef as DATA (option -> Type via [from_some]): total minting, no
   [as_expr = None => skip] (a Some-expression view's ref cannot be [None]). *)
Lemma prog_visit_as_expr_not_none {p} (idx : GoIndex.Snap.SyntaxIndex p) (r : GoIndex.Snap.NodeRef p) occ e :
  In (r, occ) (prog_visit p) -> GoIndex.view_expr occ = Some e -> GoIndex.as_expr idx r <> None.
Proof. intros Hin Hv. destruct (prog_visit_as_expr p idx r occ e Hin Hv) as [er [Hae _]]. rewrite Hae. discriminate. Qed.
Definition prog_visit_expr_ref {p} (idx : GoIndex.Snap.SyntaxIndex p) (r : GoIndex.Snap.NodeRef p) occ e
    (Hin : In (r, occ) (prog_visit p)) (Hv : GoIndex.view_expr occ = Some e)
  : { er : GoIndex.ExprRef p | GoIndex.as_expr idx r = Some er /\ GoIndex.erase_ref er = r }.
Proof.
  destruct (GoIndex.as_expr idx r) as [er|] eqn:E.
  - exists er. split; [reflexivity | exact (GoIndex.erase_as_kind idx r GoIndex.KExpression er E)].
  - exfalso. exact (prog_visit_as_expr_not_none idx r occ e Hin Hv E).
Defined.

(* the sig-fold: fold the source-order visit suffix into an outcome map CARRYING its fact-projection invariant
   ([outcomes_fact_ok]).  Each conversion step reads its operand's already-computed outcome from the suffix
   accumulator (TOTAL, [from_some] of the operand-closure proof — no fallback) and calls [convert_const] ONCE;
   the projection is discharged in place (leaf/conversion), so [proj2_sig] IS the soundness proof. *)
Definition build_outcomes {p} (idx : GoIndex.Snap.SyntaxIndex p) (tnft : TypeNameFactTable p) :
  forall (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)),
    (exists pre, prog_visit p = pre ++ l) ->
    { m : GoIndex.NodeKeyMapBase.t (ExprOutcome p) | outcomes_ok idx l m }.
Proof.
  induction l as [| [r occ] rest IH]; intro Hsuf.
  - exists (GoIndex.NodeKeyMapBase.empty (ExprOutcome p)). intros r0 occ0 e0 Hin0 _. destruct Hin0.
  - assert (Hsuf_rest : exists pre, prog_visit p = pre ++ rest).
    { destruct Hsuf as [pre Hpre]. exists (pre ++ [(r, occ)]). rewrite <- app_assoc. exact Hpre. }
    destruct (IH Hsuf_rest) as [m_rest Hok_rest].
    assert (Hin : In (r, occ) (prog_visit p))
      by (destruct Hsuf as [pre Hpre]; rewrite Hpre; apply in_or_app; right; left; reflexivity).
    assert (Hnd : ~ In (GoIndex.Snap.node_ref_key r) (map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) rest)).
    { destruct Hsuf as [pre Hpre]. exact (suffix_head_key_fresh pre r occ rest Hpre). }
    destruct (GoIndex.view_expr occ) as [e|] eqn:Hv.
    + destruct (prog_visit_expr_ref idx r occ e Hin Hv) as [er [Hae Her]].
      assert (Hocc : occ = GoIndex.Snap.source_occurrence_of_ref r) by exact (prog_visit_occ_is_source p r occ Hin).
      assert (Hrole : GoIndex.occurrence_role occ = expr_ref_role er)
        by (unfold expr_ref_role; rewrite Her, Hocc; reflexivity).
      destruct e as [ b|nn|n0|s|dd|dc| ts x ].
      (* the six leaf occurrences: store the untyped fact; it matches [occ_expr_fact] via [leaf_stored_matches] *)
      1-6: eexists;
           eapply outcomes_ok_add;
           [ exact Hok_rest | exact Hnd | exact Hv
           | eapply (leaf_stored_matches idx r er occ); [exact Hv | exact Hrole | reflexivity] ].
      (* the conversion occurrence: mint target + operand refs, read the operand's outcome, one [convert_const] *)
      assert (Hview : GoIndex.view_expr (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er))
                        = Some (EConvert ts x)) by (rewrite Her, <- Hocc; exact Hv).
      pose (opr := conversion_operand_ref_tot idx er ts x Hview).
      pose (tr := conversion_target_ref_tot idx er ts x Hview).
      assert (Htr_ref : conversion_target_ref idx er = Some tr).
      { destruct (conversion_target_ref_of_view idx er ts x Hview) as [tr0 [Hc0 _]].
        unfold tr. rewrite (conversion_target_ref_tot_eq idx er ts x Hview tr0 Hc0). exact Hc0. }
      assert (Hopr_ref : conversion_operand_ref idx er = Some opr).
      { destruct (conversion_operand_ref_of_view idx er ts x Hview) as [opr0 [Hc0 _]].
        unfold opr. rewrite (conversion_operand_ref_tot_eq idx er ts x Hview opr0 Hc0). exact Hc0. }
      assert (Hkopr : GoIndex.Snap.node_ref_key (GoIndex.erase_ref opr) = operand_key r).
      { destruct (conversion_operand_ref_of_view idx er ts x Hview) as [opr0 [Hc [Hk _]]].
        unfold opr. rewrite (conversion_operand_ref_tot_eq idx er ts x Hview opr0 Hc).
        rewrite Hk, Her. reflexivity. }
      assert (Hpres : GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref opr)) m_rest <> None).
      { destruct Hsuf as [pre Hpre]. rewrite Hkopr.
        exact (outcomes_ok_operand_present idx pre r occ rest ts x m_rest Hpre Hv Hok_rest). }
      exists (GoIndex.NodeKeyMapBase.add (GoIndex.Snap.node_ref_key r)
                (conv_outcome tnft er tr opr (from_some (GoIndex.NodeKeyMapBase.find
                   (GoIndex.Snap.node_ref_key (GoIndex.erase_ref opr)) m_rest) Hpres)) m_rest).
      apply (outcomes_ok_add idx r occ rest (EConvert ts x) m_rest _ Hok_rest Hnd Hv).
      (* the stored conversion outcome matches: the operand's outcome is the tail entry proven by [Hok_rest] *)
      destruct Hsuf as [pre Hpre].
      destruct (prog_visit_operand_closed p idx pre r occ rest Hpre (EConvert ts x) x Hv eq_refl)
        as [r' [occ' [Hkey' [Hvx' Hin']]]].
      destruct (Hok_rest r' occ' x Hin' Hvx') as [out' [Hf' Hpf']].
      assert (Hoo : from_some (GoIndex.NodeKeyMapBase.find
                       (GoIndex.Snap.node_ref_key (GoIndex.erase_ref opr)) m_rest) Hpres = out').
      { apply from_some_eq. rewrite Hkopr, <- Hkey'. exact Hf'. }
      rewrite Hoo.
      exact (conv_stored_matches idx tnft r er opr tr occ occ' ts x Hae Hv Hrole
               (conv_target_table_type idx tnft er ts x Hview) Htr_ref Hopr_ref out'
               (outcome_matches_proj idx r' occ' out' Hpf') Hvx').
    + exists m_rest. exact (outcomes_ok_skip idx r occ rest m_rest Hok_rest Hv).
Defined.


(* every [ExprRef] views an expression: the total view + its defining equation (the convoy witness).  Used by the
   TOTAL outcome/diagnostic queries to name a ref's own syntax without an option. *)
Definition expr_ref_view_opt {p} (er : GoIndex.ExprRef p) : option GoExpr :=
  GoIndex.view_expr (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)).
Lemma expr_ref_view_not_none {p} (er : GoIndex.ExprRef p) : expr_ref_view_opt er <> None.
Proof.
  unfold expr_ref_view_opt.
  destruct (GoIndex.kind_view_expr _ (GoIndex.noderefof_kind er)) as [e Hv]. rewrite Hv. discriminate.
Qed.
Definition expr_ref_view {p} (er : GoIndex.ExprRef p) : GoExpr :=
  from_some (expr_ref_view_opt er) (expr_ref_view_not_none er).
Lemma expr_ref_view_eq {p} (er : GoIndex.ExprRef p) :
  GoIndex.view_expr (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) = Some (expr_ref_view er).
Proof.
  destruct (GoIndex.kind_view_expr _ (GoIndex.noderefof_kind er)) as [e Hv].
  assert (E : expr_ref_view_opt er = Some e) by exact Hv.
  unfold expr_ref_view. rewrite (from_some_eq _ (expr_ref_view_not_none er) e E). exact Hv.
Qed.

(** ═══ §3 THE RETAINED COMPILATION INPUT ═══ derived evidence over the ONE [GoProgram]: the retained index, the
    per-file visit BLOCKS, and their flattened visit — held as STORED VALUES with a source-provenance proof that
    they are the exact traversal of the snapshot.  [elaborate] builds this ONCE; every production C4 builder
    consumes THIS object (its stored [ci_blocks]/[ci_visit]/[ci_idx]), never re-invoking [prog_blocks]/[prog_visit]/
    [index_program].  Specification theorems compare the stored values to the canonical helpers by [ci_blocks_ok]. *)
Record CompilationInput (p : GoProgram) : Type := mkCompilationInput {
  ci_ip     : GoIndex.IndexedProgram p ;
  ci_blocks : list (list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) ;
  ci_visit  : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) ;   (* STORED once, consumed by every builder *)
  ci_blocks_ok    : ci_blocks = prog_blocks p ;   (* PROVENANCE (spec): the stored blocks ARE the snapshot's *)
  ci_visit_blocks : ci_visit  = concat ci_blocks  (* COHERENCE: the stored visit IS its blocks' flattening *)
}.
Arguments mkCompilationInput {p} _ _ _ _ _.
Arguments ci_ip {p} _.  Arguments ci_blocks {p} _.  Arguments ci_visit {p} _.
Arguments ci_blocks_ok {p} _.  Arguments ci_visit_blocks {p} _.

Definition ci_idx {p} (input : CompilationInput p) : GoIndex.Snap.SyntaxIndex p :=
  GoIndex.indexed_syntax (ci_ip input).

(* the STORED visit IS the snapshot's canonical [prog_visit] (spec equality via the two coherence proofs; the DATA
   is the retained field, not a re-flattening). *)
Lemma ci_visit_ok {p} (input : CompilationInput p) : ci_visit input = prog_visit p.
Proof. unfold prog_visit. rewrite (ci_visit_blocks input), (ci_blocks_ok input). reflexivity. Qed.

(* elaborate builds the ONE input value; this is the SOLE call to [prog_blocks p]/[prog_visit p] (elaborate is not
   a builder "called by elaborate" — it is elaborate).  Everything downstream consumes the stored fields. *)
Definition build_compilation_input (p : GoProgram) (ip : GoIndex.IndexedProgram p) : CompilationInput p :=
  mkCompilationInput ip (prog_blocks p) (prog_visit p) eq_refl eq_refl.

(** ═══ §5 THE RETAINED-INPUT TYPE-NAME FACT TABLE ═══ built from the exact retained [ci_visit input] (the DATA is
    the stored visit); its domain/completeness proofs transport the canonical [prog_type_name_facts] exactness via
    [ci_visit_ok].  This is the object passed to outcome construction and later SEALED. *)
Lemma tn_input_map_eq {p} (input : CompilationInput p) :
  fold_right add_tn_fact (GoIndex.NodeKeyMapBase.empty TypeNameFact) (ci_visit input) = prog_type_name_facts p.
Proof. unfold prog_type_name_facts. rewrite (ci_visit_ok input). reflexivity. Qed.

Definition build_type_name_fact_table {p} (input : CompilationInput p) : TypeNameFactTable p.
Proof.
  refine (mkTypeNameFactTable
            (fold_right add_tn_fact (GoIndex.NodeKeyMapBase.empty TypeNameFact) (ci_visit input)) _ _).
  - intros k f Hf. rewrite (tn_input_map_eq input) in Hf. exact (prog_type_name_facts_domain p k f Hf).
  - intros r occ Hin. rewrite (tn_input_map_eq input). exact (prog_type_name_facts_find p r occ Hin).
Defined.

(* the retained-input table's map IS [prog_type_name_facts p] (spec); its total query resolves the source name. *)
Lemma build_tnft_map {p} (input : CompilationInput p) :
  tnft_map (build_type_name_fact_table input) = prog_type_name_facts p.
Proof. exact (tn_input_map_eq input). Qed.

(** ═══ §6 THE PROOF-CARRYING OUTCOME TABLE ═══ the outcome map PAIRED with its completeness/match proof over the
    retained visit — the proof STAYS on the production path.  [total_outcome_at] returns an [ExprOutcome] (NOT an
    option): a missing entry is eliminated by [eot_ok], so facts and diagnostics never see a fail-open [None]. *)
Record ExprOutcomeTable {p} (input : CompilationInput p) (tnft : TypeNameFactTable p) : Type :=
  mkExprOutcomeTable {
    eot_map : GoIndex.NodeKeyMapBase.t (ExprOutcome p) ;
    eot_ok  : outcomes_ok (ci_idx input) (ci_visit input) eot_map
  }.
Arguments mkExprOutcomeTable {p input tnft} _ _.
Arguments eot_map {p input tnft} _.  Arguments eot_ok {p input tnft} _.

Definition build_outcome_table {p} (input : CompilationInput p) (tnft : TypeNameFactTable p)
  : ExprOutcomeTable input tnft :=
  let bo := build_outcomes (ci_idx input) tnft (ci_visit input)
              (ex_intro _ (@nil (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) (eq_sym (ci_visit_ok input))) in
  mkExprOutcomeTable (proj1_sig bo) (proj2_sig bo).

(* the TOTAL outcome query: for any [ExprRef], its stored outcome — [from_some] of the table's own completeness
   proof (the None branch is [False_rect], never a semantic default). *)
Lemma eot_at_not_none {p} {input : CompilationInput p} {tnft} (ot : ExprOutcomeTable input tnft)
    (er : GoIndex.ExprRef p) :
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref er)) (eot_map ot) <> None.
Proof.
  assert (Hin : In (GoIndex.erase_ref er, GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) (ci_visit input)).
  { rewrite (ci_visit_ok input). apply noderef_in_prog_visit. }
  destruct (eot_ok ot (GoIndex.erase_ref er) (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er))
              (expr_ref_view er) Hin (expr_ref_view_eq er)) as [out [Hf _]].
  rewrite Hf. discriminate.
Qed.
Definition total_outcome_at {p} {input : CompilationInput p} {tnft} (ot : ExprOutcomeTable input tnft)
    (er : GoIndex.ExprRef p) : ExprOutcome p :=
  from_some (GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref er)) (eot_map ot))
            (eot_at_not_none ot er).

(* the TOTAL query MATCHES the occurrence — the direct table→production interface (no raw option, no [find]). *)
Lemma total_outcome_at_matches {p} {input : CompilationInput p} {tnft} (ot : ExprOutcomeTable input tnft)
    (r : GoIndex.Snap.NodeRef p) occ (er : GoIndex.ExprRef p) e :
  In (r, occ) (prog_visit p) -> GoIndex.view_expr occ = Some e ->
  GoIndex.as_expr (ci_idx input) r = Some er -> GoIndex.erase_ref er = r ->
  outcome_matches (ci_idx input) r occ (total_outcome_at ot er).
Proof.
  intros Hin Hv Hae Her.
  assert (Hin' : In (r, occ) (ci_visit input)) by (rewrite (ci_visit_ok input); exact Hin).
  destruct (eot_ok ot r occ e Hin' Hv) as [out [Hf Hm]].
  rewrite <- Her in Hf.
  unfold total_outcome_at.
  rewrite (from_some_eq _ (eot_at_not_none ot er) out Hf). exact Hm.
Qed.

(** ═══ §4 THE TYPED WORK INTERFACE ═══ minting a visited expression occurrence's [ExprRef] is TOTAL (never an
    [as_expr = None] skip): a Some-view occurrence's ref cannot be [None].  [total_outcome_at] over this ref is
    the shared phase-indexed total query the fact + diagnostic projections both use. *)
Lemma from_some_some {A} (o : option A) (H : o <> None) : o = Some (from_some o H).
Proof. destruct o as [a|]; [reflexivity | exfalso; apply H; reflexivity]. Qed.

(* the membership-carrying enumeration of a list: each element paired with a proof it belongs to the whole list;
   [fold_self_mem_ext] folds it as if folding the list, when the step is proof-irrelevant on the membership. *)
Lemma fold_ext_in {A B} (f g : A -> B -> B) (init : B) (l : list A) :
  (forall a b, In a l -> f a b = g a b) -> fold_right f init l = fold_right g init l.
Proof.
  induction l as [|a l IH]; intro H; [reflexivity|].
  cbn [fold_right]. rewrite IH by (intros a' b Ha'; apply H; right; exact Ha').
  apply H; left; reflexivity.
Qed.
Lemma fold_right_map {A B C} (f : B -> C -> C) (g : A -> B) (init : C) (l : list A) :
  fold_right f init (map g l) = fold_right (fun x => f (g x)) init l.
Proof. induction l as [|a l IH]; [reflexivity | cbn [map fold_right]; rewrite IH; reflexivity]. Qed.

(** ═══ §4 THE EXACT TYPED WORK DOMAIN ═══ one proof-backed expression-work item per LIVE expression occurrence.
    Each [ExprWork] CARRIES its exact [ExprRef], source view, and the membership/view/as_expr/erase proofs — so
    every downstream consumer (facts, outcomes, diagnostics, context annotation) reads [ew_expr_ref] directly and
    NEVER calls an optional [as_expr] with a fail-open [None] branch.  The work builder is the SINGLE place that
    inspects a raw occurrence and decides expression-ness. *)
Record ExprWork {p} (input : CompilationInput p) : Type := mkExprWork {
  ew_node_ref   : GoIndex.Snap.NodeRef p ;
  ew_occurrence : GoIndex.SourceOccurrence ;
  ew_expr_ref   : GoIndex.ExprRef p ;
  ew_expr       : GoExpr ;
  ew_in_visit      : In (ew_node_ref, ew_occurrence) (ci_visit input) ;
  ew_view_exact    : GoIndex.view_expr ew_occurrence = Some ew_expr ;
  ew_as_expr_exact : GoIndex.as_expr (ci_idx input) ew_node_ref = Some ew_expr_ref ;
  ew_erase_exact   : GoIndex.erase_ref ew_expr_ref = ew_node_ref
}.
Arguments mkExprWork {p input} _ _ _ _ _ _ _ _.
Arguments ew_node_ref {p input} _.  Arguments ew_occurrence {p input} _.
Arguments ew_expr_ref {p input} _.  Arguments ew_expr {p input} _.
Arguments ew_in_visit {p input} _.  Arguments ew_view_exact {p input} _.
Arguments ew_as_expr_exact {p input} _.  Arguments ew_erase_exact {p input} _.

(* the work item's role, DERIVED from its exact ExprRef (not a stored duplicate). *)
Definition ew_role {p} {input : CompilationInput p} (w : ExprWork input) : GoIndex.NodeRole :=
  expr_ref_role (ew_expr_ref w).

(* whole-visit membership transports to [prog_visit] membership through the retained coherence [ci_visit_ok]. *)
Definition ci_in_prog {p} {input : CompilationInput p} {ro} (H : In ro (ci_visit input)) : In ro (prog_visit p) :=
  eq_ind (ci_visit input) (fun L => In ro L) H (prog_visit p) (ci_visit_ok input).

(* build the exact work enumeration from a sublist [l] of the retained visit, CARRYING (like [build_outcomes])
   the fold-relation as an INTERNAL property: because each [ExprWork] carries a [view_expr occ]-dependent proof,
   the builder's step cannot be reduced by any external tactic — so the fold relation is proven DURING
   construction (where [destruct (view_expr occ) eqn] works) and travels in the sig.  The carried property: for
   ANY per-work step [fw] that agrees with a per-occurrence step [fo] on every work item, where [fo] is a no-op on
   non-expression occurrences, folding [fw] over the work list EQUALS folding [fo] over [l].  This is what lets
   the fact/diagnostic projections consume the work domain (each item carrying its [ExprRef]) yet equal the source
   specification — with NO optional [as_expr] below the work builder. *)
Definition build_work_sig {p} (input : CompilationInput p) :
  forall (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)),
    (forall ro, In ro l -> In ro (ci_visit input)) ->
    { w : list (ExprWork input) |
        forall B (fw : ExprWork input -> B -> B)
               (fo : (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) -> B -> B) (init : B),
          (forall (wi : ExprWork input) b, fw wi b = fo (ew_node_ref wi, ew_occurrence wi) b) ->
          (forall r occ b, In (r, occ) (ci_visit input) -> GoIndex.view_expr occ = None -> fo (r, occ) b = b) ->
          fold_right fw init w = fold_right fo init l }.
Proof.
  induction l as [| [r occ] rest IH]; intro H.
  - exists nil. intros. reflexivity.
  - assert (Hin : In (r, occ) (ci_visit input)) by (apply H; left; reflexivity).
    destruct (IH (fun ro Hro => H ro (or_intror Hro))) as [wrest Hrest].
    destruct (GoIndex.view_expr occ) as [e|] eqn:Hv.
    + assert (Hinp : In (r, occ) (prog_visit p)) by (rewrite <- (ci_visit_ok input); exact Hin).
      destruct (prog_visit_expr_ref (ci_idx input) r occ e Hinp Hv) as [er [Hae Her]].
      exists (mkExprWork r occ er e Hin Hv Hae Her :: wrest).
      intros B fw fo init Hagree Hskip.
      cbn [fold_right]. rewrite (Hrest B fw fo init Hagree Hskip).
      rewrite (Hagree (mkExprWork r occ er e Hin Hv Hae Her) (fold_right fo init rest)).
      cbn [ew_node_ref ew_occurrence]. reflexivity.
    + exists wrest. intros B fw fo init Hagree Hskip.
      cbn [fold_right]. rewrite (Hrest B fw fo init Hagree Hskip).
      rewrite (Hskip r occ (fold_right fo init rest) Hin Hv). reflexivity.
Defined.

Definition prog_work {p} (input : CompilationInput p) : list (ExprWork input) :=
  proj1_sig (build_work_sig input (ci_visit input) (fun ro H => H)).

Definition prog_work_fold {p} (input : CompilationInput p) {B}
    (fw : ExprWork input -> B -> B)
    (fo : (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) -> B -> B) (init : B)
    (Hagree : forall (wi : ExprWork input) b, fw wi b = fo (ew_node_ref wi, ew_occurrence wi) b)
    (Hskip : forall r occ b, In (r, occ) (ci_visit input) -> GoIndex.view_expr occ = None -> fo (r, occ) b = b) :
  fold_right fw init (prog_work input) = fold_right fo init (ci_visit input) :=
  proj2_sig (build_work_sig input (ci_visit input) (fun ro H => H)) B fw fo init Hagree Hskip.
Fixpoint self_mem {A} (l : list A) : list { a : A | In a l } :=
  match l with
  | nil => nil
  | a :: rest => exist _ a (or_introl eq_refl)
                 :: map (fun s => exist (fun x => In x (a :: rest)) (proj1_sig s) (or_intror (proj2_sig s)))
                        (self_mem rest)
  end.
Lemma fold_self_mem_proj {A B} (l : list A) (g : A -> B -> B) (init : B) :
  fold_right (fun s => g (proj1_sig s)) init (self_mem l) = fold_right g init l.
Proof.
  induction l as [|a rest IH]; [reflexivity|].
  cbn [self_mem fold_right]. rewrite fold_right_map. cbn [proj1_sig]. rewrite IH. reflexivity.
Qed.
Lemma fold_self_mem_ext {A B} (l : list A) (f : { a : A | In a l } -> B -> B) (g : A -> B -> B) (init : B) :
  (forall a (H : In a l) b, f (exist _ a H) b = g a b) ->
  fold_right f init (self_mem l) = fold_right g init l.
Proof.
  intro Hfg. rewrite <- (fold_self_mem_proj l g init).
  apply fold_ext_in. intros [a H] b _. cbn [proj1_sig]. exact (Hfg a H b).
Qed.

(** ═══ §9.1 THE TOTAL FACT PROJECTION ═══ each EXACT [ExprWork] item carries its own [ExprRef] ([ew_expr_ref]);
    its stored outcome is queried TOTALLY ([total_outcome_at], never a raw [find] option): an [EOOk] contributes
    its exact fact keyed by the work's own node key; every other outcome contributes nothing.  There is NO
    optional [as_expr] and NO missing-ref/missing-outcome case — the projection consumes the typed work domain. *)
Definition work_fact {p} {input : CompilationInput p} {tnft : TypeNameFactTable p}
    (ot : ExprOutcomeTable input tnft) (w : ExprWork input)
    (m : GoIndex.NodeKeyMapBase.t ExprFact) : GoIndex.NodeKeyMapBase.t ExprFact :=
  match total_outcome_at ot (ew_expr_ref w) with
  | EOOk f => GoIndex.NodeKeyMapBase.add (GoIndex.Snap.node_ref_key (ew_node_ref w)) f m
  | _ => m
  end.
Definition phase_expr_facts {p} (input : CompilationInput p) (tnft : TypeNameFactTable p)
    (ot : ExprOutcomeTable input tnft) : GoIndex.NodeKeyMapBase.t ExprFact :=
  fold_right (work_fact ot) (GoIndex.NodeKeyMapBase.empty ExprFact) (prog_work input).

(* the WORK-item projection step EQUALS the [add_occ_fact] specification at the work's occurrence — the total
   outcome query at the work's OWN [ExprRef] MATCHES [occ_expr_fact] ([total_outcome_at_matches] discharged from
   the work item's own carried proofs; [outcome_matches_proj]).  No [as_expr], no case split on a missing ref. *)
Lemma work_fact_eq {p} {input : CompilationInput p} {tnft : TypeNameFactTable p}
    (ot : ExprOutcomeTable input tnft) (w : ExprWork input) m :
  work_fact ot w m = add_occ_fact (ew_node_ref w, ew_occurrence w) m.
Proof.
  unfold work_fact, add_occ_fact. cbn [fst snd].
  pose proof (total_outcome_at_matches ot (ew_node_ref w) (ew_occurrence w) (ew_expr_ref w) (ew_expr w)
                (ci_in_prog (ew_in_visit w)) (ew_view_exact w) (ew_as_expr_exact w) (ew_erase_exact w)) as Hm.
  pose proof (outcome_matches_proj (ci_idx input) (ew_node_ref w) (ew_occurrence w)
                (total_outcome_at ot (ew_expr_ref w)) Hm) as Hpf.
  destruct (total_outcome_at ot (ew_expr_ref w)) as [f|c1 c2 c3 c4 c5| ];
    cbn [outcome_proj_fact] in Hpf; rewrite Hpf; reflexivity.
Qed.

(** the source-determined expression-fact map (the SPECIFICATION): each visited occurrence's [occ_expr_fact]
    keyed by its NodeKey.  The PRODUCTION fact map is [phase_expr_facts] (the TOTAL projection of the retained
    [ExprOutcomeTable]), proved EQUAL to this specification by [phase_expr_facts_eq_spec]. *)
Definition prog_expr_facts (p : GoProgram) : GoIndex.NodeKeyMapBase.t ExprFact :=
  fold_right add_occ_fact (GoIndex.NodeKeyMapBase.empty ExprFact) (prog_visit p).

(** ═══ §9.1 THE TOTAL FACT PROJECTION EQUALS THE SPECIFICATION ═══ folding the total per-occurrence outcome
    query over the retained visit yields EXACTLY [prog_expr_facts p] — so the [ExprFactTable] built from the
    proof-carrying [ExprOutcomeTable] inherits the source-determined domain + exactness, with NO fail-open. *)
Lemma phase_expr_facts_eq_spec {p} (input : CompilationInput p) (tnft : TypeNameFactTable p)
    (ot : ExprOutcomeTable input tnft) :
  phase_expr_facts input tnft ot = prog_expr_facts p.
Proof.
  assert (Hskip : forall r occ b, In (r, occ) (ci_visit input) -> GoIndex.view_expr occ = None ->
                    add_occ_fact (r, occ) b = b).
  { intros r occ b _ Hvn. unfold add_occ_fact. cbn [fst snd].
    rewrite (occ_expr_fact_none_nonexpr occ Hvn). reflexivity. }
  unfold phase_expr_facts, prog_expr_facts.
  rewrite (prog_work_fold input (work_fact ot) add_occ_fact (GoIndex.NodeKeyMapBase.empty ExprFact)
             (fun w b => work_fact_eq ot w b) Hskip).
  rewrite (ci_visit_ok input). reflexivity.
Qed.

Lemma prog_expr_facts_eq_spec (p : GoProgram) :
  prog_expr_facts p = fold_right add_occ_fact (GoIndex.NodeKeyMapBase.empty ExprFact) (prog_visit p).
Proof. reflexivity. Qed.

(** PROGRAM-LEVEL FACT EXACTNESS: the fact at a program-visited ref's key is EXACTLY that occurrence's fact
    (the single-pass map agrees with the [occ_expr_fact] specification). *)
Lemma prog_expr_facts_find (p : GoProgram) (r : GoIndex.Snap.NodeRef p) occ :
  In (r, occ) (prog_visit p) ->
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key r) (prog_expr_facts p) = occ_expr_fact occ.
Proof.
  intro Hin. rewrite prog_expr_facts_eq_spec. apply fold_facts_find; [ apply prog_visit_key_nodup | exact Hin ].
Qed.

(** DOMAIN EXACTNESS: EVERY key with an entry is a VISITED occurrence's key whose fact is exactly the stored
    one — so no non-expression / file-root / foreign key can carry a fact (a forged entry is unrepresentable). *)
Lemma fold_add_occ_fact_domain {p} (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) k f :
  GoIndex.NodeKeyMapBase.find k (fold_right add_occ_fact (GoIndex.NodeKeyMapBase.empty ExprFact) l) = Some f ->
  exists ro, In ro l /\ GoIndex.Snap.node_ref_key (fst ro) = k /\ occ_expr_fact (snd ro) = Some f.
Proof.
  induction l as [|ro rest IH]; intro Hf.
  - rewrite GoIndex.NodeKeyMapFacts.empty_o in Hf; discriminate Hf.
  - cbn [fold_right] in Hf. unfold add_occ_fact in Hf.
    destruct (occ_expr_fact (snd ro)) as [f0|] eqn:Ef.
    + destruct (GoIndex.thm8_nodekey_eq_dec (GoIndex.Snap.node_ref_key (fst ro)) k) as [He|Hne].
      * subst k. rewrite GoIndex.nodekeymap_add_eq in Hf. injection Hf as <-.
        exists ro. split; [left; reflexivity | split; [reflexivity | exact Ef]].
      * rewrite GoIndex.nodekeymap_add_neq in Hf by exact Hne.
        destruct (IH Hf) as [ro' [Hin [Hk Hfe]]]. exists ro'. split; [right; exact Hin | split; [exact Hk | exact Hfe]].
    + destruct (IH Hf) as [ro' [Hin [Hk Hfe]]]. exists ro'. split; [right; exact Hin | split; [exact Hk | exact Hfe]].
Qed.

Lemma prog_expr_facts_domain (p : GoProgram) k f :
  GoIndex.NodeKeyMapBase.find k (prog_expr_facts p) = Some f ->
  exists (r : GoIndex.Snap.NodeRef p) occ, In (r, occ) (prog_visit p)
    /\ GoIndex.Snap.node_ref_key r = k /\ occ_expr_fact occ = Some f.
Proof.
  rewrite prog_expr_facts_eq_spec. intro Hf.
  destruct (fold_add_occ_fact_domain (prog_visit p) k f Hf) as [[r occ] [Hin [Hk Hfe]]].
  exists r, occ. cbn [fst snd] in *. split; [exact Hin | split; [exact Hk | exact Hfe]].
Qed.

Record ExprFactTable (p : GoProgram) (ip : GoIndex.IndexedProgram p) : Type := mkExprFactTable {
  eft_map      : GoIndex.NodeKeyMapBase.t ExprFact ;
  eft_domain   : forall k f, GoIndex.NodeKeyMapBase.find k eft_map = Some f ->
                   exists (r : GoIndex.Snap.NodeRef p) occ, In (r, occ) (prog_visit p)
                     /\ GoIndex.Snap.node_ref_key r = k /\ occ_expr_fact occ = Some f ;
  eft_complete : forall r occ, In (r, occ) (prog_visit p) ->
                   GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key r) eft_map = occ_expr_fact occ
}.
Arguments mkExprFactTable {p ip} _ _ _.
Arguments eft_map {p ip} _.
Arguments eft_domain {p ip} _.
Arguments eft_complete {p ip} _.

(** §9 the proof-backed ExprFactTable OBJECT projected from the phase's [ExprOutcomeTable] — its map is
    [phase_expr_facts] (the TOTAL success projection, definitionally), carrying the source-determined
    domain + completeness against [prog_visit p].  ONE such object is retained in the [ExpressionPhase]
    ([ep_eft]) and later stored into [ElaborationFacts] by OBJECT IDENTITY (§2.8), never rebuilt. *)
Definition build_expr_fact_table {p} (input : CompilationInput p) (tnft : TypeNameFactTable p)
    (ot : ExprOutcomeTable input tnft) : ExprFactTable p (ci_ip input).
Proof.
  refine (mkExprFactTable (phase_expr_facts input tnft ot) _ _).
  - intros k f Hf. rewrite (phase_expr_facts_eq_spec input tnft ot) in Hf.
    exact (prog_expr_facts_domain p k f Hf).
  - intros r occ Hin. rewrite (phase_expr_facts_eq_spec input tnft ot).
    exact (prog_expr_facts_find p r occ Hin).
Defined.
Lemma build_expr_fact_table_map {p} (input : CompilationInput p) (tnft : TypeNameFactTable p)
    (ot : ExprOutcomeTable input tnft) :
  eft_map (build_expr_fact_table input tnft ot) = phase_expr_facts input tnft ot.
Proof. reflexivity. Qed.


(* ---- the EXPRESSION DECISION: every println argument resolves IFF the program is [ProgramTyped] ---- *)

Lemma forallb_flat_map {A B} (f : B -> bool) (g : A -> list B) (l : list A) :
  forallb f (flat_map g l) = forallb (fun x => forallb f (g x)) l.
Proof. induction l as [|a l IH]; simpl; [reflexivity | rewrite forallb_app, IH; reflexivity]. Qed.

(* (moved from GoTypes) — THE PER-OCCURRENCE TYPING PREDICATE.  GoCompile is the SOLE meeting point of
   GoIndex identity and GoTypes semantics, so this occurrence/traversal bridge (which needs BOTH [SourceOccurrence]
   / [occs_file] from GoIndex and [expr_typedb] / [source_file_typedb] from GoTypes) lives HERE — GoTypes owns
   the type/constant relation only and imports no GoIndex.  [occ_arg_typedb] is the leaf typing decision over ONE
   source occurrence: a println-argument occurrence is typed iff its expression resolves (through the SAME
   [GoTypes.expr_typedb] resolver — no semantic judgment duplicated); every other occurrence is vacuously typed.
   [occs_file_typedb_eq] proves that folding it over the canonical occurrence stream ([occs_file]) equals the
   existing [source_file_typedb].  [elaborate] CONSUMES this over its retained visit stream. *)

(* the per-occurrence typing decision on the ORIGINAL syntax the traversal delivers: only a println-argument
   expression occurrence carries a semantic obligation (delegated to [expr_typedb UsePrintlnArg]); every other
   occurrence (file root, package clause, declaration, statement, conversion operand) is vacuously typed. *)
Definition occ_arg_typedb (o : GoIndex.SourceOccurrence) : bool :=
  match GoIndex.occurrence_role o with
  | GoIndex.RPrintlnArg _ => match GoIndex.view_expr o with Some e => expr_typedb GoTypes.UsePrintlnArg e | None => true end
  | _ => true
  end.

(* a conversion's TYPE-NAME occurrence (kind KTypeName, no expression view) is vacuously typed. *)
Lemma occ_arg_typedb_typename : forall ts par sub,
  occ_arg_typedb (GoIndex.mkOcc GoIndex.KTypeName (GoIndex.ViewTypeName ts) (Some par) GoIndex.RConversionTarget sub) = true.
Proof. reflexivity. Qed.

Lemma occ_arg_typedb_operand : forall e par sub,
  occ_arg_typedb (GoIndex.mkOcc GoIndex.KExpression (GoIndex.ViewExpression e) (Some par) GoIndex.RConversionOperand sub) = true.
Proof. reflexivity. Qed.

Lemma occ_arg_typedb_printlnarg : forall e par aidx sub,
  occ_arg_typedb (GoIndex.mkOcc GoIndex.KExpression (GoIndex.ViewExpression e) (Some par) (GoIndex.RPrintlnArg aidx) sub)
  = expr_typedb GoTypes.UsePrintlnArg e.
Proof. reflexivity. Qed.

(* every occurrence inside a conversion operand carries role [RConversionOperand], hence is vacuously typed. *)
Lemma occs_expr_operand_true : forall e parent me,
  forallb (fun x => occ_arg_typedb (snd x)) (GoIndex.occs_expr parent GoIndex.RConversionOperand me e) = true.
Proof.
  induction e as [ b|n1|n2|s| df | dcx | ts x IHx ];
    intros parent me; cbn [GoIndex.occs_expr forallb snd].
  1,2,3,4,5,6: rewrite occ_arg_typedb_operand; reflexivity.
  rewrite occ_arg_typedb_operand, occ_arg_typedb_typename, !Bool.andb_true_l; apply IHx.
Qed.

(* one println argument's occurrence stream types exactly as the existing [expr_typedb UsePrintlnArg]. *)
Lemma occs_arg_typedb_eq : forall e parent aidx me,
  forallb (fun x => occ_arg_typedb (snd x)) (GoIndex.occs_arg parent aidx me e) = expr_typedb GoTypes.UsePrintlnArg e.
Proof.
  intros e parent aidx me. unfold GoIndex.occs_arg.
  destruct e as [ b|n1|n2|s| df | dcx | ts x ];
    cbn [GoIndex.occs_expr forallb snd]; rewrite occ_arg_typedb_printlnarg.
  1,2,3,4,5,6: apply Bool.andb_true_r.
  rewrite occ_arg_typedb_typename, occs_expr_operand_true, ?Bool.andb_true_r, ?Bool.andb_true_l; reflexivity.
Qed.

Lemma occs_args_typedb_eq : forall es parent aidx me,
  forallb (fun x => occ_arg_typedb (snd x)) (GoIndex.occs_args parent aidx me es)
  = forallb (expr_typedb GoTypes.UsePrintlnArg) es.
Proof.
  induction es as [|e rest IH]; intros parent aidx me.
  - reflexivity.
  - cbn [GoIndex.occs_args]. rewrite forallb_app, occs_arg_typedb_eq, IH. reflexivity.
Qed.

Lemma occs_stmt_typedb_eq : forall s parent sidx me,
  forallb (fun x => occ_arg_typedb (snd x)) (GoIndex.occs_stmt parent sidx me s) = stmt_typedb s.
Proof.
  intros [args] parent sidx me.
  cbn [GoIndex.occs_stmt forallb snd occ_arg_typedb GoIndex.occurrence_role].
  rewrite occs_args_typedb_eq. reflexivity.
Qed.

Lemma occs_stmts_typedb_eq : forall ss parent sidx me,
  forallb (fun x => occ_arg_typedb (snd x)) (GoIndex.occs_stmts parent sidx me ss) = forallb stmt_typedb ss.
Proof.
  induction ss as [|s rest IH]; intros parent sidx me.
  - reflexivity.
  - cbn [GoIndex.occs_stmts]. rewrite forallb_app, occs_stmt_typedb_eq, IH. reflexivity.
Qed.

Lemma occs_decl_typedb_eq : forall d parent didx me,
  forallb (fun x => occ_arg_typedb (snd x)) (GoIndex.occs_decl parent didx me d) = decl_typedb d.
Proof.
  intros [body] parent didx me.
  cbn [GoIndex.occs_decl forallb snd occ_arg_typedb GoIndex.occurrence_role].
  rewrite occs_stmts_typedb_eq. reflexivity.
Qed.

Lemma occs_decls_typedb_eq : forall ds parent didx me,
  forallb (fun x => occ_arg_typedb (snd x)) (GoIndex.occs_decls parent didx me ds) = forallb decl_typedb ds.
Proof.
  induction ds as [|d rest IH]; intros parent didx me.
  - reflexivity.
  - cbn [GoIndex.occs_decls]. rewrite forallb_app, occs_decl_typedb_eq, IH. reflexivity.
Qed.

(* the WHOLE file's occurrence stream types exactly as the existing [source_file_typedb] (the file-root and
   package-clause occurrences are vacuously typed; the body delegates to [occs_decls_typedb_eq]). *)
Lemma occs_file_typedb_eq : forall f,
  forallb (fun x => occ_arg_typedb (snd x)) (GoIndex.occs_file f) = source_file_typedb f.
Proof.
  intros f. unfold GoIndex.occs_file. destruct (source_imports f) as [|i tl] eqn:E.
  - cbn [forallb snd occ_arg_typedb GoIndex.occurrence_role].
    rewrite occs_decls_typedb_eq. unfold GoTypes.source_file_typedb, GoTypes.file_typedb. reflexivity.
  - destruct i.
Qed.

(** one file's argument occurrences resolve iff the file types (the traversal projects [occs_file], reusing
    the [occ_arg_typedb] = [source_file_typedb] bridge). *)
Lemma visit_file_arg_typedb {p} (fr : GoIndex.Snap.FileRef p) :
  forallb (fun x => occ_arg_typedb (snd x)) (GoIndex.Snap.visit_file fr)
  = source_file_typedb (GoIndex.Snap.file_ref_source fr).
Proof.
  rewrite GoTypes.forallb_map_snd, GoIndex.Snap.visit_file_snd, <- GoTypes.forallb_map_snd.
  apply occs_file_typedb_eq.
Qed.

(** the per-occurrence "argument resolves" check folded over the whole program. *)
Definition expr_all_ok (p : GoProgram) : bool :=
  forallb (fun x => occ_arg_typedb (snd x)) (prog_visit p).

(** DECISION EXACTNESS: [expr_all_ok] is EXACTLY [program_typedb] (hence [ProgramTyped]).  This is the
    expression half of [ElaborationOK <-> GoCompile]: no expression diagnostic <-> every argument resolves. *)
Lemma expr_all_ok_program_typedb (p : GoProgram) : expr_all_ok p = program_typedb p.
Proof.
  unfold expr_all_ok. rewrite prog_visit_flat_map, forallb_flat_map. unfold GoTypes.program_typedb.
  apply GoTypes.forallb_ext_in. intros b Hb. unfold binding_visit.
  pose proof (GoAST.file_bindings_find (prog_files p) b Hb) as Hfind.
  destruct (GoIndex.Snap.file_of_path_source p (fst b) (snd b) Hfind) as [fr [Hfop [Hpath Hsrc]]].
  rewrite Hfop, visit_file_arg_typedb, Hsrc. reflexivity.
Qed.

Lemma expr_all_ok_ProgramTyped (p : GoProgram) : expr_all_ok p = true <-> ProgramTyped p.
Proof. rewrite expr_all_ok_program_typedb. apply GoTypes.program_typedb_iff. Qed.

(* ---- the PACKAGE DECISION: [pkg_decls_unique_b] + [main_pkgs_have_entry_b] + [source_spec_package_rules_b], the factored
   roots [PackageDeclsUnique] / [MainPackagesHaveEntry] / [PackageRulesValid], and their DIRECT reflections
   ([pkg_decls_unique_b_iff] / [main_pkgs_have_entry_b_iff] / [source_spec_package_rules_b_PackageRulesValid]) are all
   defined early, above [source_spec_valid_b] (which reuses [source_spec_package_rules_b] as its package half), so the
   retained-bucket production decision ([pkg_diags_empty_iff_rules]) can root DIRECTLY in the two factored roots.  The
   exactly-one property is only the downstream CONSEQUENCE [current_package_rules_exactly_one]. ---- *)

(* ---- the COMBINED DECIDABLE decision [semantic_ok_b]: the readable SOURCE-specification decision, proved
   EXACTLY = [SourceProgramValid] (the SOURCE-semantic half of [GoCompile]; [GoCompile] additionally requires
   the separate fresh-build preflight).  Production elaboration decides the SAME source semantics from its
   RETAINED diagnostics; [source_spec_valid_b] is the readable-spec reflection. ---- *)

Definition semantic_ok_b (p : GoProgram) : bool := expr_all_ok p && source_spec_package_rules_b p.

Lemma semantic_ok_b_source_spec_valid_b (p : GoProgram) : semantic_ok_b p = source_spec_valid_b p.
Proof. unfold semantic_ok_b, source_spec_valid_b. rewrite expr_all_ok_program_typedb. reflexivity. Qed.

(* [GoCompile p] is defined below as the fresh-build preflight on top of [SourceProgramValid] (the factored
   package rules); this elaboration decision is exactly the SOURCE half, reflected DIRECTLY against
   [SourceProgramValid] by [semantic_ok_b_SourceProgramValid] below (no [prog_ok]/[ProgValid] intermediary). *)
Lemma semantic_ok_b_split (p : GoProgram) :
  semantic_ok_b p = true <-> expr_all_ok p = true /\ source_spec_package_rules_b p = true.
Proof. unfold semantic_ok_b. rewrite Bool.andb_true_iff. reflexivity. Qed.

(* the EXPRESSION diagnostic construction, per occurrence, with anchors.

   The key move (no descent, no ref minting): the primary is the OCCURRENCE'S OWN reference.
   - a LOCALLY-failing conversion (its operand's [const_info] succeeds but its own [convert_const] fails) IS the
     innermost failing conversion — anchor [DRInvalidConversion] at its own ExprRef;
   - a println-argument occurrence whose [const_info] is an UNTYPED constant that does not default — anchor
     [DRDefaultNotRepresentable] at its own ExprRef.
   ([outer_context] is [] here — sound vacuously; the annotation pass supplies the enclosing conversions.) *)

Definition default_target_of (c : GoConst) : GoType :=
  match c with
  | CBool _    => TBool
  | CInt _     => TInteger IInt
  | CFloat _   => TFloat F64
  | CComplex _ => TComplex C128
  | CString _  => TString
  end.

(** the explicit-conversion SYNTAX projection: an expression is a conversion whose target NAME resolves (in the
    predeclared context) to the semantic type [t], of operand [x]. *)
Definition conv_targets (e : GoExpr) : option (GoType * GoExpr) :=
  match e with
  | EConvert ts x => Some (predeclared_type ts, x)
  | _             => None
  end.

(** a local conversion failure denotes EXACTLY: the expression is the explicit conversion to
    the reported target [t] of some operand [x] ([conv_targets]), [x]'s exact successful status is the reported
    [ci] ([const_info x = Some ci]), and the shared [convert_const] rejects it.  So the DRInvalidConversion
    primary/target/operand-status faithfully denote the reported explicit conversion. *)
Lemma local_conv_failure_char (e : GoExpr) (t : GoType) (ci : ConstInfo) :
  local_conv_failure e = Some (t, ci) ->
  exists x, conv_targets e = Some (t, x) /\ const_info x = Some ci /\ convert_const t ci = None.
Proof.
  intro H. destruct e as [ b|n1|n2|s| df | dcx | ts x ]; try discriminate H; cbn [local_conv_failure] in H;
    (destruct (const_info x) as [ci'|] eqn:Ex; [| discriminate H];
     destruct (convert_const _ ci') as [c'|] eqn:Ec; [ discriminate H | injection H as Ht Hc; subst ];
     exists x; cbn [conv_targets]; rewrite Ex; split; [reflexivity | split; [reflexivity | exact Ec]]).
Qed.

(** ═══ §7 THE DIRECT CONVERSION-FAILURE CAUSE ═══ a stored [EOConvFail] does NOT reduce to a re-run of the
    source-spec [local_conv_failure]/[const_info]: its cause is read DIRECTLY off the retained phase.  For any
    visited conversion occurrence whose TOTAL outcome is [EOConvFail], the reported refs ARE the occurrence's
    OWN retained conversion target/operand refs; the reported target type IS the SEALED [TypeNameFactTable]'s
    stored fact at that target ref (never a fresh resolver call); the operand's OWN total outcome is a SUCCESS
    [EOOk opf] whose [ef_const_status] IS the reported [ci] (never a fresh [const_info] scan); and
    [convert_const] genuinely REJECTS that status at that resolved target.  The whole causal chain is a query
    of the ONE retained phase. *)
Lemma phase_convfail_cause {p} {input : CompilationInput p} {tnft} (ot : ExprOutcomeTable input tnft)
    (r : GoIndex.Snap.NodeRef p) occ (er : GoIndex.ExprRef p) e
    (er2 : GoIndex.ExprRef p) (tr2 : GoIndex.TypeNameRef p) (opr2 : GoIndex.ExprRef p) t ci :
  In (r, occ) (prog_visit p) -> GoIndex.view_expr occ = Some e ->
  GoIndex.as_expr (ci_idx input) r = Some er -> GoIndex.erase_ref er = r ->
  total_outcome_at ot er = EOConvFail er2 tr2 opr2 t ci ->
     er2 = er
  /\ conversion_target_ref (ci_idx input) er = Some tr2
  /\ conversion_operand_ref (ci_idx input) er = Some opr2
  /\ t = tnf_type (type_name_fact_at_table tnft tr2)
  /\ (exists opf, total_outcome_at ot opr2 = EOOk opf /\ ci = ef_const_status opf)
  /\ convert_const t ci = None.
Proof.
  intros Hin Hv Hae Her Hcf.
  pose proof (total_outcome_at_matches ot r occ er e Hin Hv Hae Her) as Hm.
  rewrite Hcf in Hm. cbn [outcome_matches] in Hm.
  destruct Hm as [_ Hev]. unfold outcome_convfail_ev in Hev.
  destruct Hev as [Ha2 [[e' [Hve' Hlc]] [Htr2 Hopr2]]].
  (* er2 = er: both are [as_expr (ci_idx input) r] *)
  rewrite Hae in Ha2. injection Ha2 as He2. subst er2.
  (* e' = e (same view) *)
  rewrite Hv in Hve'. injection Hve' as He'e. subst e'.
  (* characterise the local failure and expose the source syntax [ts] *)
  destruct (local_conv_failure_char e t ci Hlc) as [x0 [Hct [Hcix Hcv]]].
  destruct e as [ b|n1|n2|s| df | dcx | ts x1 ]; cbn [conv_targets] in Hct; try discriminate Hct.
  injection Hct as Ht Hx. subst t. subst x1.
  (* target ref + [type_name_ref_syntax tr2 = Some ts] via [conversion_target_ref_conv] *)
  destruct (conversion_target_ref_conv (ci_idx input) r occ er ts x0 Hin Hv Hae)
    as [tr [Htrc [_ [_ Htsyn]]]].
  rewrite Htr2 in Htrc. injection Htrc as Htreq. subst tr.
  (* operand ref + operand-occurrence view via [conversion_operand_ref_conv] *)
  destruct (conversion_operand_ref_conv (ci_idx input) r occ er ts x0 Hin Hv Hae)
    as [opr [Hoprc [_ [_ Hoprv]]]].
  rewrite Hopr2 in Hoprc. injection Hoprc as Hopreq. subst opr.
  split; [ reflexivity | ].
  split; [ exact Htr2 | ].
  split; [ exact Hopr2 | ].
  split.
  { (* t = tnf_type of the SEALED table's stored fact at tr2 *)
    rewrite (type_name_fact_at_table_resolves tnft tr2 ts Htsyn). reflexivity. }
  split.
  { (* the operand's OWN total outcome is EOOk opf with ef_const_status opf = ci *)
    pose proof (total_outcome_at_matches ot (GoIndex.erase_ref opr2)
                  (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref opr2)) opr2 x0
                  (noderef_in_prog_visit p (GoIndex.erase_ref opr2)) Hoprv
                  (as_expr_erase (ci_idx input) opr2) eq_refl) as Hmop.
    destruct (total_outcome_at ot opr2) as [opf| ? ? ? ? ? | ] eqn:Hoo;
      cbn [outcome_matches] in Hmop.
    - exists opf. split; [ reflexivity | ].
      unfold occ_expr_fact in Hmop. rewrite Hoprv, Hcix in Hmop.
      injection Hmop as Hopf. rewrite <- Hopf. reflexivity.
    - exfalso. destruct Hmop as [Hnone _]. unfold occ_expr_fact in Hnone.
      rewrite Hoprv, Hcix in Hnone. discriminate Hnone.
    - exfalso. destruct Hmop as [Hnone _]. unfold occ_expr_fact in Hnone.
      rewrite Hoprv, Hcix in Hnone. discriminate Hnone. }
  (* convert_const genuinely rejects at the resolved target *)
  exact Hcv.
Qed.

(** a println-argument occurrence whose exact untyped constant does not default — returns (constant, default). *)
Definition arg_default_failure (occ : GoIndex.SourceOccurrence) (e : GoExpr) : option (GoConst * GoType) :=
  match GoIndex.occurrence_role occ with
  | GoIndex.RPrintlnArg _ =>
      match const_info e with
      | Some (CIUntyped c) => match default_const c with None => Some (c, default_target_of c) | Some _ => None end
      | _ => None
      end
  | _ => None
  end.

(** the explicit-conversion SYNTAX test on a DELIVERED occurrence (consumed by the
    one-pass [annotate_encl]): a node is a conversion iff its occurrence's OWN syntax is one of the three
    explicit conversions.  Reads only the delivered [SourceOccurrence] — no [node_at] recovery, no
    [visit_file] re-traversal — so it is snapshot-independent (source-determined). *)
Definition is_conversion_occ (occ : GoIndex.SourceOccurrence) : bool :=
  match GoIndex.view_expr occ with
  | Some (EConvert _ _) => true
  | _ => false
  end.

(** the ONE-PASS enclosing-conversion context.  A single FORWARD pass over the RETAINED
    preorder file stream carries the open-conversion stack (nearest-first, push-front); each occurrence is
    annotated with its enclosing-conversion refs = [map fst] of the currently-open stack (its strict
    conversion ancestors).  Entries whose subtree has closed ([node_subtree_end < node_ref_local]) are popped;
    a conversion occurrence pushes its own [ExprRef] + subtree end AFTER recording.  No per-diagnostic
    [visit_file] re-traversal and no [node_at] recovery — only retained refs, index subtree metadata, and the
    delivered occurrence's own syntax ([is_conversion_occ]).  This IS the enclosing-context authority (the
    [outer_context] delivered to the diagnostic emitters); its erased form is a source function of the keyed
    stream ([annotate_encl_erased]), the basis for cross-snapshot report determinism. *)
Fixpoint annotate_encl {p} (idx : GoIndex.Snap.SyntaxIndex p)
    (stack : list (GoIndex.ExprRef p * positive))
    (stream : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence))
    : list ((GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) * list (GoIndex.ExprRef p)) :=
  match stream with
  | [] => []
  | ro :: rest =>
      let open := filter (fun e => Pos.leb (GoIndex.Snap.node_ref_local (fst ro)) (snd e)) stack in
      let stack' := match GoIndex.as_expr idx (fst ro) with
                    | Some er => if is_conversion_occ (snd ro)
                                 then (er, GoIndex.Snap.node_subtree_end idx (fst ro)) :: open
                                 else open
                    | None => open
                    end in
      (ro, map fst open) :: annotate_encl idx stack' rest
  end.

Lemma flat_map_map {A B C} (f : B -> list C) (g : A -> B) (l : list A) :
  flat_map f (map g l) = flat_map (fun x => f (g x)) l.
Proof. induction l as [|a l IH]; [reflexivity|]. cbn [map flat_map]. rewrite IH. reflexivity. Qed.

(** the annotation preserves the underlying occurrence stream (it only attaches context). *)
Lemma annotate_encl_fst {p} (idx : GoIndex.Snap.SyntaxIndex p) stack stream :
  map fst (annotate_encl idx stack stream) = stream.
Proof.
  revert stack; induction stream as [|ro rest IH]; intro stack; [reflexivity|].
  cbn [annotate_encl map]. rewrite IH. reflexivity.
Qed.

(* the annotation-STACK invariant: every open entry [(er, se)] is a genuine CONVERSION
   [ExprRef] (erasing to a node whose occurrence's syntax is a conversion) whose subtree end is [se]. *)
Definition estack_ok {p} (idx : GoIndex.Snap.SyntaxIndex p) (stack : list (GoIndex.ExprRef p * positive)) : Prop :=
  forall er se, In (er, se) stack ->
    GoIndex.as_expr idx (GoIndex.erase_ref er) = Some er
    /\ is_conversion_occ (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) = true
    /\ GoIndex.Snap.node_subtree_end idx (GoIndex.erase_ref er) = se.

(* filtering preserves the stack invariant. *)
Lemma estack_ok_filter {p} (idx : GoIndex.Snap.SyntaxIndex p) P stack :
  estack_ok idx stack -> estack_ok idx (filter P stack).
Proof. intros H er se Hin. apply filter_In in Hin. exact (H er se (proj1 Hin)). Qed.

(** the NESTED SCAR soundness: every enclosing-conversion ref delivered to occurrence [ro] is a genuine
    CONVERSION whose subtree STRICTLY contains [ro] (a strict-ancestor conversion — [node_ref_local < ro <=
    node_subtree_end]).  Requires the stream sorted by local (preorder) with the stack's entries all below the
    stream's locals — exactly the per-file [visit_file] block. *)
Lemma annotate_encl_ctx_sound {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall stream stack,
  StronglySorted (fun x y => Pos.lt (GoIndex.Snap.node_ref_local (fst x)) (GoIndex.Snap.node_ref_local (fst y))) stream ->
  (forall ro, In ro stream -> snd ro = GoIndex.Snap.source_occurrence_of_ref (fst ro)) ->
  estack_ok idx stack ->
  (forall ro er se, In ro stream -> In (er, se) stack -> Pos.lt (GoIndex.Snap.node_ref_local (GoIndex.erase_ref er)) (GoIndex.Snap.node_ref_local (fst ro))) ->
  forall ro ctx, In (ro, ctx) (annotate_encl idx stack stream) ->
  forall er, In er ctx ->
    is_conversion_occ (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) = true
    /\ Pos.lt (GoIndex.Snap.node_ref_local (GoIndex.erase_ref er)) (GoIndex.Snap.node_ref_local (fst ro))
    /\ Pos.le (GoIndex.Snap.node_ref_local (fst ro)) (GoIndex.Snap.node_subtree_end idx (GoIndex.erase_ref er)).
Proof.
  induction stream as [|ro0 rest IH]; intros stack Hsort Hval Hstk Hbnd roc ctx Hin er Her; [destruct Hin|].
  cbn [annotate_encl] in Hin.
  set (open := filter (fun e => Pos.leb (GoIndex.Snap.node_ref_local (fst ro0)) (snd e)) stack) in *.
  apply StronglySorted_inv in Hsort. destruct Hsort as [Hsort0 Hhd].
  destruct Hin as [Heq | Hin].
  - injection Heq as Hro Hctx. subst roc ctx.
    apply in_map_iff in Her. destruct Her as [[er2 se] [Her2 Hin2]]. cbn [fst] in Her2. subst er2.
    pose proof Hin2 as Hin2'. apply filter_In in Hin2'. destruct Hin2' as [Hstack Hle]. apply Pos.leb_le in Hle.
    destruct (Hstk er se Hstack) as [_ [Hconv Hse]].
    split; [ exact Hconv | split ].
    + exact (Hbnd ro0 er se (or_introl eq_refl) Hstack).
    + rewrite Hse. exact Hle.
  - refine (IH _ Hsort0 (fun ro' Hr => Hval ro' (or_intror Hr)) _ _ roc ctx Hin er Her).
    + (* estack_ok idx stack' *)
      destruct (GoIndex.as_expr idx (fst ro0)) as [er0|] eqn:Ea.
      * destruct (is_conversion_occ (snd ro0)) eqn:Hc0.
        -- intros e s [Hh | Ht].
           ++ injection Hh as He Hs. subst e s.
              rewrite (GoIndex.erase_as_kind idx (fst ro0) GoIndex.KExpression er0 Ea).
              split; [exact Ea | split; [ rewrite <- (Hval ro0 (or_introl eq_refl)); exact Hc0 | reflexivity ]].
           ++ exact (estack_ok_filter idx _ stack Hstk e s Ht).
        -- exact (estack_ok_filter idx _ stack Hstk).
      * exact (estack_ok_filter idx _ stack Hstk).
    + (* the bound for rest: stack' entries below rest's locals *)
      intros ro' e s Hr' Hes.
      assert (Hlt0 : Pos.lt (GoIndex.Snap.node_ref_local (fst ro0)) (GoIndex.Snap.node_ref_local (fst ro'))).
      { rewrite Forall_forall in Hhd. exact (Hhd ro' Hr'). }
      destruct (GoIndex.as_expr idx (fst ro0)) as [er0|] eqn:Ea.
      * destruct (is_conversion_occ (snd ro0)) eqn:Hc0.
        -- destruct Hes as [Hh | Ht].
           ++ injection Hh as He Hs. subst e.
              rewrite (GoIndex.erase_as_kind idx (fst ro0) GoIndex.KExpression er0 Ea). exact Hlt0.
           ++ pose proof Ht as Ht'. apply filter_In in Ht'.
              exact (Pos.lt_trans _ _ _ (Hbnd ro0 e s (or_introl eq_refl) (proj1 Ht')) Hlt0).
        -- pose proof Hes as Ht'. apply filter_In in Ht'.
           exact (Pos.lt_trans _ _ _ (Hbnd ro0 e s (or_introl eq_refl) (proj1 Ht')) Hlt0).
      * pose proof Hes as Ht'. apply filter_In in Ht'.
        exact (Pos.lt_trans _ _ _ (Hbnd ro0 e s (or_introl eq_refl) (proj1 Ht')) Hlt0).
Qed.

Lemma StronglySorted_filter {A} (R : A -> A -> Prop) (P : A -> bool) l :
  StronglySorted R l -> StronglySorted R (filter P l).
Proof.
  induction l as [|a l IH]; intro H; [constructor|].
  apply StronglySorted_inv in H. destruct H as [Hs Hhd]. cbn [filter].
  destruct (P a); [| apply IH; exact Hs].
  constructor; [apply IH; exact Hs|]. rewrite Forall_forall in Hhd |- *.
  intros x Hx. apply filter_In in Hx. apply Hhd. exact (proj1 Hx).
Qed.

Lemma StronglySorted_map {A B} (R : B -> B -> Prop) (f : A -> B) l :
  StronglySorted (fun x y => R (f x) (f y)) l -> StronglySorted R (map f l).
Proof.
  induction l as [|a l IH]; intro H; [constructor|].
  cbn [map]. apply StronglySorted_inv in H. destruct H as [Hs Hhd].
  constructor; [apply IH; exact Hs|].
  rewrite Forall_forall in Hhd |- *. intros y Hy. apply in_map_iff in Hy.
  destruct Hy as [x [Hxy Hx]]. subst y. exact (Hhd x Hx).
Qed.

Lemma StronglySorted_NoDup {A} (R : A -> A -> Prop) l :
  (forall a, ~ R a a) -> StronglySorted R l -> NoDup l.
Proof.
  intro Hirr. induction l as [|a l IH]; intro H; [constructor|].
  apply StronglySorted_inv in H. destruct H as [Hs Hhd].
  constructor; [| apply IH; exact Hs].
  intro Hina. rewrite Forall_forall in Hhd. exact (Hirr a (Hhd a Hina)).
Qed.

Lemma StronglySorted_impl_in {A} (R R' : A -> A -> Prop) l :
  (forall x y, In x l -> In y l -> R x y -> R' x y) -> StronglySorted R l -> StronglySorted R' l.
Proof.
  intros Himp H. induction l as [|a l IH]; [constructor|].
  apply StronglySorted_inv in H. destruct H as [Hs Hhd].
  constructor.
  - apply IH; [| exact Hs]. intros x y Hx Hy. apply Himp; right; assumption.
  - rewrite Forall_forall in Hhd |- *. intros x Hx. apply Himp; [left; reflexivity | right; exact Hx | exact (Hhd x Hx)].
Qed.

Lemma StronglySorted_app {A} (R : A -> A -> Prop) l1 l2 :
  StronglySorted R l1 -> StronglySorted R l2 -> (forall a b, In a l1 -> In b l2 -> R a b) ->
  StronglySorted R (l1 ++ l2).
Proof.
  intros H1 H2 Hcross. induction l1 as [|a l1 IH]; [exact H2|].
  apply StronglySorted_inv in H1. destruct H1 as [Hs Hhd]. cbn [app]. constructor.
  - apply IH; [exact Hs | intros b c Hb Hc; apply Hcross; [right; exact Hb | exact Hc]].
  - rewrite Forall_forall. intros x Hx. apply in_app_iff in Hx. destruct Hx as [Hx | Hx].
    + rewrite Forall_forall in Hhd. exact (Hhd x Hx).
    + apply Hcross; [left; reflexivity | exact Hx].
Qed.

(* the annotation-STACK is same-file and STRICTLY DESCENDING by local (front = last pushed = deepest =
   NEAREST); its projection to the [ExprRef] context is thus same-file, nearest-first, and duplicate-free. *)
Definition estack_wf {p} (idx : GoIndex.Snap.SyntaxIndex p) (fr : GoIndex.Snap.FileRef p)
    (stack : list (GoIndex.ExprRef p * positive)) : Prop :=
  Forall (fun e => GoIndex.Snap.node_ref_file (GoIndex.erase_ref (fst e)) = fr) stack
  /\ StronglySorted (fun x y => Pos.lt (GoIndex.Snap.node_ref_local (GoIndex.erase_ref (fst y)))
                                       (GoIndex.Snap.node_ref_local (GoIndex.erase_ref (fst x)))) stack.

Lemma estack_wf_filter {p} (idx : GoIndex.Snap.SyntaxIndex p) fr P stack :
  estack_wf idx fr stack -> estack_wf idx fr (filter P stack).
Proof.
  intros [Hf Hs]. split.
  - apply Forall_forall. intros e He. apply filter_In in He. rewrite Forall_forall in Hf. exact (Hf e (proj1 He)).
  - apply StronglySorted_filter; assumption.
Qed.

(** the nested scar is SAME-FILE, NEAREST-FIRST, and DUPLICATE-FREE: over a per-file
    [visit_file] block the delivered [outer_context] is all in that file, and strictly descending by local
    (deepest/nearest enclosing conversion first) — whence [NoDup]. *)
Lemma annotate_encl_ctx_wf {p} (idx : GoIndex.Snap.SyntaxIndex p) (fr : GoIndex.Snap.FileRef p) :
  forall stream stack,
  StronglySorted (fun x y => Pos.lt (GoIndex.Snap.node_ref_local (fst x)) (GoIndex.Snap.node_ref_local (fst y))) stream ->
  (forall ro, In ro stream -> snd ro = GoIndex.Snap.source_occurrence_of_ref (fst ro) /\ GoIndex.Snap.node_ref_file (fst ro) = fr) ->
  estack_wf idx fr stack ->
  (forall ro er se, In ro stream -> In (er, se) stack -> Pos.lt (GoIndex.Snap.node_ref_local (GoIndex.erase_ref er)) (GoIndex.Snap.node_ref_local (fst ro))) ->
  forall ro ctx, In (ro, ctx) (annotate_encl idx stack stream) ->
    Forall (fun er => GoIndex.Snap.node_ref_file (GoIndex.erase_ref er) = fr) ctx
    /\ StronglySorted (fun a b => Pos.lt (GoIndex.Snap.node_ref_local (GoIndex.erase_ref b)) (GoIndex.Snap.node_ref_local (GoIndex.erase_ref a))) ctx.
Proof.
  induction stream as [|ro0 rest IH]; intros stack Hsort Hval Hwf Hbnd roc ctx Hin; [destruct Hin|].
  cbn [annotate_encl] in Hin.
  set (open := filter (fun e => Pos.leb (GoIndex.Snap.node_ref_local (fst ro0)) (snd e)) stack) in *.
  apply StronglySorted_inv in Hsort. destruct Hsort as [Hsort0 Hhd].
  assert (Hwfopen : estack_wf idx fr open) by (apply estack_wf_filter; exact Hwf).
  destruct Hin as [Heq | Hin].
  - injection Heq as Hro Hctx. subst roc ctx. destruct Hwfopen as [Hf Hs].
    split.
    + rewrite Forall_forall. intros er Herin. apply in_map_iff in Herin.
      destruct Herin as [[e s] [Hes Hin']]. cbn [fst] in Hes. subst er.
      rewrite Forall_forall in Hf. exact (Hf (e, s) Hin').
    + apply (StronglySorted_map (fun a b => Pos.lt (GoIndex.Snap.node_ref_local (GoIndex.erase_ref b))
                                                   (GoIndex.Snap.node_ref_local (GoIndex.erase_ref a)))
              fst open). exact Hs.
  - refine (IH _ Hsort0 (fun ro' Hr => Hval ro' (or_intror Hr)) _ _ roc ctx Hin).
    + destruct (GoIndex.as_expr idx (fst ro0)) as [er0|] eqn:Ea;
        [ destruct (is_conversion_occ (snd ro0)) eqn:Hc0 | ]; try (exact Hwfopen).
      destruct Hwfopen as [Hf Hs]. split.
      * constructor; [| exact Hf]. cbn [fst].
        rewrite (GoIndex.erase_as_kind idx (fst ro0) GoIndex.KExpression er0 Ea).
        exact (proj2 (Hval ro0 (or_introl eq_refl))).
      * constructor; [exact Hs|]. apply Forall_forall. intros [e s] He. cbn [fst].
        rewrite (GoIndex.erase_as_kind idx (fst ro0) GoIndex.KExpression er0 Ea).
        pose proof He as He'. apply filter_In in He'.
        exact (Hbnd ro0 e s (or_introl eq_refl) (proj1 He')).
    + intros ro' e s Hr' Hes.
      assert (Hlt0 : Pos.lt (GoIndex.Snap.node_ref_local (fst ro0)) (GoIndex.Snap.node_ref_local (fst ro'))).
      { rewrite Forall_forall in Hhd. exact (Hhd ro' Hr'). }
      destruct (GoIndex.as_expr idx (fst ro0)) as [er0|] eqn:Ea;
        [ destruct (is_conversion_occ (snd ro0)) eqn:Hc0 | ].
      * destruct Hes as [Hh | Ht].
        -- injection Hh as He Hs. subst e.
           rewrite (GoIndex.erase_as_kind idx (fst ro0) GoIndex.KExpression er0 Ea). exact Hlt0.
        -- pose proof Ht as Ht'. apply filter_In in Ht'.
           exact (Pos.lt_trans _ _ _ (Hbnd ro0 e s (or_introl eq_refl) (proj1 Ht')) Hlt0).
      * pose proof Hes as Ht'. apply filter_In in Ht'.
        exact (Pos.lt_trans _ _ _ (Hbnd ro0 e s (or_introl eq_refl) (proj1 Ht')) Hlt0).
      * pose proof Hes as Ht'. apply filter_In in Ht'.
        exact (Pos.lt_trans _ _ _ (Hbnd ro0 e s (or_introl eq_refl) (proj1 Ht')) Hlt0).
Qed.

Lemma StronglySorted_map_inv {A B} (R : B -> B -> Prop) (f : A -> B) (l : list A) :
  StronglySorted R (map f l) -> StronglySorted (fun x y => R (f x) (f y)) l.
Proof.
  induction l as [|a l IH]; intro H; [constructor|].
  cbn [map] in H. apply StronglySorted_inv in H. destruct H as [Hs Hhd].
  constructor; [apply IH; exact Hs|].
  rewrite Forall_forall in Hhd |- *. intros x Hx. apply Hhd. exact (in_map f l x Hx).
Qed.

Definition annotate_program {p} (idx : GoIndex.Snap.SyntaxIndex p)
  : list ((GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) * list (GoIndex.ExprRef p)) :=
  flat_map (annotate_encl idx []) (prog_blocks p).

(** lift the nested-scar soundness to the whole program: every enclosing-conversion ref delivered to any
    annotated occurrence is a strict-ancestor conversion (its subtree strictly contains the occurrence). *)
Lemma annotate_program_ctx_sound {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall ro ctx er,
  In (ro, ctx) (annotate_program idx) -> In er ctx ->
  is_conversion_occ (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) = true
  /\ Pos.lt (GoIndex.Snap.node_ref_local (GoIndex.erase_ref er)) (GoIndex.Snap.node_ref_local (fst ro))
  /\ Pos.le (GoIndex.Snap.node_ref_local (fst ro)) (GoIndex.Snap.node_subtree_end idx (GoIndex.erase_ref er)).
Proof.
  intros ro ctx er Hin Her. unfold annotate_program in Hin. apply in_flat_map in Hin.
  destruct Hin as [block [Hblock Hin]]. unfold prog_blocks in Hblock.
  apply in_map_iff in Hblock. destruct Hblock as [b [Hbv Hb]]. subst block. unfold binding_visit in Hin.
  destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|] eqn:Efr; [| destruct Hin].
  refine (annotate_encl_ctx_sound idx (GoIndex.Snap.visit_file fr) [] _ _ _ _ ro ctx Hin er Her).
  - apply StronglySorted_map_inv. exact (GoIndex.Snap.visit_file_order p fr).
  - intros [r occ] Hro. destruct (GoIndex.Snap.visit_file_view p fr r occ Hro) as [Ho _]. exact Ho.
  - intros er0 se [].
  - intros ro0 er0 se _ [].
Qed.

(** the whole-program nested scar is SAME-FILE (as the primary), NEAREST-FIRST, and DUPLICATE-FREE. *)
Lemma annotate_program_ctx_wf {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall ro ctx,
  In (ro, ctx) (annotate_program idx) ->
  Forall (fun er => GoIndex.Snap.node_ref_file (GoIndex.erase_ref er) = GoIndex.Snap.node_ref_file (fst ro)) ctx
  /\ StronglySorted (fun a b => Pos.lt (GoIndex.Snap.node_ref_local (GoIndex.erase_ref b)) (GoIndex.Snap.node_ref_local (GoIndex.erase_ref a))) ctx
  /\ NoDup ctx.
Proof.
  intros ro ctx Hin. unfold annotate_program in Hin. apply in_flat_map in Hin.
  destruct Hin as [block [Hblock Hin]]. unfold prog_blocks in Hblock.
  apply in_map_iff in Hblock. destruct Hblock as [b [Hbv Hb]]. subst block. unfold binding_visit in Hin.
  destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|] eqn:Efr; [| destruct Hin].
  assert (Hroin : In ro (GoIndex.Snap.visit_file fr))
    by (rewrite <- (annotate_encl_fst idx [] (GoIndex.Snap.visit_file fr)); exact (in_map fst _ _ Hin)).
  assert (Hrf : GoIndex.Snap.node_ref_file (fst ro) = fr).
  { destruct ro as [r occ]. destruct (GoIndex.Snap.visit_file_view p fr r occ Hroin) as [_ Hf]. exact Hf. }
  assert (Hprops : Forall (fun er => GoIndex.Snap.node_ref_file (GoIndex.erase_ref er) = fr) ctx
                 /\ StronglySorted (fun a b => Pos.lt (GoIndex.Snap.node_ref_local (GoIndex.erase_ref b))
                                                      (GoIndex.Snap.node_ref_local (GoIndex.erase_ref a))) ctx).
  { refine (annotate_encl_ctx_wf idx fr (GoIndex.Snap.visit_file fr) [] _ _ _ _ ro ctx Hin).
    - apply StronglySorted_map_inv. exact (GoIndex.Snap.visit_file_order p fr).
    - intros [r occ] Hro. destruct (GoIndex.Snap.visit_file_view p fr r occ Hro) as [Ho Hf]. split; assumption.
    - split; constructor.
    - intros ro0 er0 se _ []. }
  destruct Hprops as [Hfile Hss].
  rewrite Hrf. split; [exact Hfile | split; [exact Hss |]].
  exact (StronglySorted_NoDup _ ctx (fun a => Pos.lt_irrefl _) Hss).
Qed.

Lemma annotate_program_fst {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  map fst (annotate_program idx) = prog_visit p.
Proof.
  unfold annotate_program, prog_visit.
  induction (prog_blocks p) as [|b L IH]; [reflexivity|].
  cbn [flat_map concat]. rewrite map_app, annotate_encl_fst, IH. reflexivity.
Qed.

(** the diagnostic(s) an occurrence emits (a singleton or nothing), anchored at its OWN validated ExprRef.
    The [outer] enclosing-conversion context is DELIVERED by the one-pass [annotate_program] annotation,
    never recomputed here — so no [visit_file]/[node_at] per diagnostic. *)
Definition occ_expr_diags {p} (idx : GoIndex.Snap.SyntaxIndex p) (outer : list (GoIndex.ExprRef p))
    (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) : list (DiagnosticReason p) :=
  match GoIndex.as_expr idx (fst ro) with
  | None => []
  | Some er =>
      match GoIndex.view_expr (snd ro) with
      | None => []
      | Some e =>
          match local_conv_failure e with
          | Some (t, ci) =>
              match conversion_target_ref idx er with
              | Some tr =>
                  match conversion_operand_ref idx er with
                  | Some opr => [ DRInvalidConversion er tr opr outer t ci ]
                  | None => []   (* provably dead: a live conversion always mints its operand ref *)
                  end
              | None => []   (* provably dead: a live conversion always mints its target ref *)
              end
          | None =>
              match arg_default_failure (snd ro) e with
              | Some (c, dt) => [ DRDefaultNotRepresentable er c dt ]
              | None => []
              end
          end
      end
  end.

(** code-specific EXPRESSION-diagnostic soundness.  A local conversion failure genuinely
    FAILS the shared [convert_const] for the reported target. *)
Lemma local_conv_failure_sound : forall e t ci,
  local_conv_failure e = Some (t, ci) -> convert_const t ci = None.
Proof.
  intros e t ci H. unfold local_conv_failure in H.
  destruct e as [b|n|n0|s|df|dcx| ts x ]; try discriminate H;
    (destruct (const_info x) as [ci'|]; [| discriminate H];
     destruct (convert_const _ ci') eqn:Ec; [ discriminate H | injection H as <- <-; exact Ec ]).
Qed.

(** a [DRInvalidConversion] diagnostic DENOTES its reported code end-to-end: the [outer_context]
    is EXACTLY the delivered enclosing context; the primary [er] is the occurrence's OWN [ExprRef]; the
    occurrence's syntax IS the explicit conversion to the reported target [t] of operand [x] ([conv_targets]);
    the reported operand status [ci] is [x]'s exact successful [const_info]; and the shared [convert_const]
    genuinely REJECTS it.  So target/operand-status/primary faithfully denote the reported conversion. *)
Lemma occ_expr_diags_conv_sound {p} (idx : GoIndex.Snap.SyntaxIndex p) ro outer er tr opr outer' t ci :
  In (DRInvalidConversion er tr opr outer' t ci) (occ_expr_diags idx outer ro) ->
  outer' = outer
  /\ GoIndex.as_expr idx (fst ro) = Some er
  /\ conversion_target_ref idx er = Some tr
  /\ conversion_operand_ref idx er = Some opr
  /\ convert_const t ci = None
  /\ exists e x, GoIndex.view_expr (snd ro) = Some e /\ conv_targets e = Some (t, x) /\ const_info x = Some ci.
Proof.
  intro Hin. unfold occ_expr_diags in Hin.
  destruct (GoIndex.as_expr idx (fst ro)) as [er2|] eqn:Ea; [| destruct Hin].
  destruct (GoIndex.view_expr (snd ro)) as [e|] eqn:Ev; [| destruct Hin].
  destruct (local_conv_failure e) as [[t' ci']|] eqn:Elc.
  - destruct (conversion_target_ref idx er2) as [tr2|] eqn:Ectr; [| destruct Hin].
    destruct (conversion_operand_ref idx er2) as [opr2|] eqn:Ecor; [| destruct Hin].
    destruct Hin as [Heq|[]]. injection Heq as He Htr Hopr Ho Ht Hc. subst er2 tr2 opr2 t' ci'.
    destruct (local_conv_failure_char e t ci Elc) as [x [Hct [Hci Hcv]]].
    split; [ symmetry; exact Ho
           | split; [ reflexivity
                    | split; [ exact Ectr
                             | split; [ exact Ecor
                                      | split; [ exact Hcv
                                               | exists e, x; split; [reflexivity | split; [exact Hct | exact Hci]]]]]]].
  - destruct (arg_default_failure (snd ro) e) as [[c dt]|];
      [ destruct Hin as [Heq|[]]; discriminate Heq | destruct Hin ].
Qed.

(** a [DRDefaultNotRepresentable] diagnostic DENOTES its reported code end-to-end: the primary
    [er] is the occurrence's OWN [ExprRef]; the occurrence is genuinely a PRINTLN ARGUMENT ([RPrintlnArg]) —
    the only use context that can default-fail; its syntax's exact status is the reported untyped constant
    [CIUntyped c]; that [c] does NOT default ([default_const c = None]); and the reported default target is
    EXACTLY [c]'s Go default ([default_target_of] — integer->int, float->float64, complex->complex128). *)
Lemma occ_expr_diags_default_sound {p} (idx : GoIndex.Snap.SyntaxIndex p) ro outer er c dt :
  In (DRDefaultNotRepresentable er c dt) (occ_expr_diags idx outer ro) ->
  GoIndex.as_expr idx (fst ro) = Some er
  /\ (exists aidx, GoIndex.occurrence_role (snd ro) = GoIndex.RPrintlnArg aidx)
  /\ (exists e, GoIndex.view_expr (snd ro) = Some e /\ const_info e = Some (CIUntyped c))
  /\ default_const c = None
  /\ dt = default_target_of c.
Proof.
  intro Hin. unfold occ_expr_diags in Hin.
  destruct (GoIndex.as_expr idx (fst ro)) as [er'|] eqn:Ea; [| destruct Hin].
  destruct (GoIndex.view_expr (snd ro)) as [e|] eqn:Ev; [| destruct Hin].
  destruct (local_conv_failure e) as [[t' ci']|] eqn:Elc;
    [ destruct (conversion_target_ref idx er') as [tr'|];
      [ destruct (conversion_operand_ref idx er') as [opr'|];
        [ destruct Hin as [Heq|[]]; discriminate Heq | destruct Hin ]
      | destruct Hin ] |].
  destruct (arg_default_failure (snd ro) e) as [[c' dt']|] eqn:Ead; [| destruct Hin].
  destruct Hin as [Heq|[]]. injection Heq as He Hc Hd. subst er' c' dt'.
  unfold arg_default_failure in Ead.
  destruct (GoIndex.occurrence_role (snd ro)) as [ | | ai | si | ain | | ] eqn:Erole; try discriminate Ead.
  destruct (const_info e) as [cinf|] eqn:Eci; try discriminate Ead.
  destruct cinf as [cc | ct tc]; [| discriminate Ead].
  destruct (default_const cc) eqn:Edc; [ discriminate Ead | injection Ead as Hcc Hdtc ]. subst c dt.
  split; [ reflexivity
         | split; [ exists ain; reflexivity
                  | split; [ exists e; split; [reflexivity | exact Eci]
                           | split; [ exact Edc | reflexivity ]]]].
Qed.

(* ---- the diagnostic step ([occ_work_diags], below): PROJECTS each occurrence's stored outcome from the ONE
   retained [ExprOutcomeTable] via the TOTAL [total_outcome_at] query.  A local invalid conversion reads its
   own [EOConvFail], emitting the diagnostic from the STORED conversion/target refs + resolved target + operand
   status ALREADY computed by the outcome fold — NEVER re-minting the target ref, never a second [convert_const]
   or resolver call.  A default failure reads its own [EOOk] fact's status.  Proved to agree with the
   [occ_expr_diags] specification. ---- *)

Lemma local_conv_failure_const_none e t ci : local_conv_failure e = Some (t, ci) -> const_info e = None.
Proof.
  intro H. destruct e as [ b|n1|n2|s| df | dcx | ts x ]; cbn [local_conv_failure] in H; try discriminate H.
  destruct (const_info x) as [cix|] eqn:Ex; [| discriminate H].
  destruct (convert_const (predeclared_type ts) cix) as [tc|] eqn:Ecv; [ discriminate H |].
  injection H as <- <-. rewrite const_info_conv_eq, Ex, Ecv. reflexivity.
Qed.

Lemma flat_map_ext_in {A B} (f g : A -> list B) (l : list A) :
  (forall a, In a l -> f a = g a) -> flat_map f l = flat_map g l.
Proof.
  induction l as [|a l IH]; intro H; [reflexivity|].
  cbn [flat_map]. rewrite (H a (or_introl eq_refl)), IH by (intros a' Ha'; apply H; right; exact Ha'). reflexivity.
Qed.

(* the production expression diagnostics: the TOTAL outcome projection over the ONE-PASS annotated stream —
   each occurrence's enclosing-conversion context [snd roc] is DELIVERED by [annotate_program], its outcome is
   read from the ONE retained [ExprOutcomeTable] (via [total_outcome_at]); a local invalid conversion emits its
   STORED refs (no re-mint), no per-diagnostic [visit_file]/[node_at], no second [convert_const]. *)
(* the SPECIFICATION expression-diagnostic report: the declarative per-occurrence [occ_expr_diags] over the
   one-pass annotated stream.  The PRODUCTION report is [phase_expr_diags] (the TOTAL projection of the retained
   [ExprOutcomeTable]), proved equal to THIS ([phase_expr_diags_eq_spec] / [ep_diags_eq_expr_diags]). *)
Definition expr_diags {p} (idx : GoIndex.Snap.SyntaxIndex p) : list (DiagnosticReason p) :=
  flat_map (fun roc => occ_expr_diags idx (snd roc) (fst roc)) (annotate_program idx).

Lemma expr_diags_eq_spec {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  expr_diags idx = flat_map (fun roc => occ_expr_diags idx (snd roc) (fst roc)) (annotate_program idx).
Proof. reflexivity. Qed.

(** ═══ §9.2 THE TOTAL DIAGNOSTIC PROJECTION ═══ for each annotated occurrence the ref is minted inline and its
    stored outcome queried TOTALLY: an [EOConvFail] emits [DRInvalidConversion] from its STORED refs + evidence;
    an [EOOk] at a println use performs default reporting from its STORED fact; an [EOChildFail] emits no local
    reason; every other [EOOk] none.  No optional [conv_failure]/[arg_default] map lookup, no fail-open. *)
Definition work_default_failure (occ : GoIndex.SourceOccurrence) (f : ExprFact) : option (GoConst * GoType) :=
  match GoIndex.occurrence_role occ with
  | GoIndex.RPrintlnArg _ =>
      match ef_const_status f with
      | CIUntyped c => match default_const c with None => Some (c, default_target_of c) | Some _ => None end
      | _ => None end
  | _ => None
  end.
Lemma work_default_failure_eq (occ : GoIndex.SourceOccurrence) e f :
  const_info e = Some (ef_const_status f) -> work_default_failure occ f = arg_default_failure occ e.
Proof.
  intro Hci. unfold work_default_failure, arg_default_failure.
  destruct (GoIndex.occurrence_role occ); try reflexivity. rewrite Hci. reflexivity.
Qed.
Lemma local_conv_failure_none_of_const e ci : const_info e = Some ci -> local_conv_failure e = None.
Proof.
  intro Hci. destruct (local_conv_failure e) as [[t' ci']|] eqn:Elc; [| reflexivity].
  exfalso. pose proof (local_conv_failure_const_none e t' ci' Elc) as Hcn. rewrite Hci in Hcn. discriminate Hcn.
Qed.

Definition occ_work_diags {p} (input : CompilationInput p) (tnft : TypeNameFactTable p)
    (ot : ExprOutcomeTable input tnft)
    (roc : (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) * list (GoIndex.ExprRef p))
  : list (DiagnosticReason p) :=
  match GoIndex.as_expr (ci_idx input) (fst (fst roc)) with
  | None => []
  | Some er =>
      match total_outcome_at ot er with
      | EOConvFail er2 tr2 opr2 t ci => [ DRInvalidConversion er2 tr2 opr2 (snd roc) t ci ]
      | EOOk f =>
          match work_default_failure (snd (fst roc)) f with
          | Some (c, dt) => [ DRDefaultNotRepresentable er c dt ]
          | None => []
          end
      | EOChildFail => []
      end
  end.

Lemma occ_work_diags_eq_spec {p} (input : CompilationInput p) (tnft : TypeNameFactTable p)
    (ot : ExprOutcomeTable input tnft) roc :
  In (fst roc) (prog_visit p) ->
  occ_work_diags input tnft ot roc = occ_expr_diags (ci_idx input) (snd roc) (fst roc).
Proof.
  intro Hin. destruct roc as [[r occ] ctx]. cbn [fst snd] in Hin |- *.
  unfold occ_work_diags, occ_expr_diags. cbn [fst snd].
  destruct (GoIndex.as_expr (ci_idx input) r) as [er|] eqn:Hae; [| reflexivity].
  assert (Her : GoIndex.erase_ref er = r) by exact (GoIndex.erase_as_kind (ci_idx input) r GoIndex.KExpression er Hae).
  assert (Hv : GoIndex.view_expr occ = Some (expr_ref_view er))
    by (rewrite (prog_visit_occ_is_source p r occ Hin), <- Her; exact (expr_ref_view_eq er)).
  rewrite Hv.
  pose proof (total_outcome_at_matches ot r occ er (expr_ref_view er) Hin Hv Hae Her) as Hm.
  destruct (total_outcome_at ot er) as [f|er2 tr2 opr2 t ci| ]; cbn [outcome_matches] in Hm.
  - (* EOOk f : has a fact => not a local failure; default from the stored fact = the source default failure *)
    assert (Hcf : const_info (expr_ref_view er) = Some (ef_const_status f)).
    { unfold occ_expr_fact in Hm. rewrite Hv in Hm.
      destruct (const_info (expr_ref_view er)) as [ce|] eqn:Ece; [| discriminate Hm]. injection Hm as Hf0. rewrite <- Hf0. reflexivity. }
    rewrite (local_conv_failure_none_of_const (expr_ref_view er) (ef_const_status f) Hcf).
    rewrite (work_default_failure_eq occ (expr_ref_view er) f Hcf). reflexivity.
  - (* EOConvFail : the stored evidence IS the spec diagnostic *)
    destruct Hm as [_ [Hae2 [[e' [Hv' Hlcf]] [Htr2 Hopr2]]]].
    rewrite Hae in Hae2. injection Hae2 as He2. subst er2.
    rewrite Hv in Hv'. injection Hv' as He'. subst e'.
    rewrite Hlcf, Htr2, Hopr2. reflexivity.
  - (* EOChildFail : no local failure and no fact => no reason *)
    destruct Hm as [Hnf [e' [Hv' Hlcf]]]. rewrite Hv in Hv'. injection Hv' as He'. subst e'.
    rewrite Hlcf. unfold arg_default_failure.
    assert (Hcn : const_info (expr_ref_view er) = None).
    { unfold occ_expr_fact in Hnf. rewrite Hv in Hnf.
      destruct (const_info (expr_ref_view er)) as [ce|] eqn:Ece; [discriminate Hnf | reflexivity]. }
    destruct (GoIndex.occurrence_role occ); try reflexivity. rewrite Hcn. reflexivity.
Qed.

Definition phase_expr_diags {p} (input : CompilationInput p) (tnft : TypeNameFactTable p)
    (ot : ExprOutcomeTable input tnft) : list (DiagnosticReason p) :=
  flat_map (occ_work_diags input tnft ot) (flat_map (annotate_encl (ci_idx input) []) (ci_blocks input)).

Lemma phase_expr_diags_eq_spec {p} (input : CompilationInput p) (tnft : TypeNameFactTable p)
    (ot : ExprOutcomeTable input tnft) :
  phase_expr_diags input tnft ot
  = flat_map (fun roc => occ_expr_diags (ci_idx input) (snd roc) (fst roc)) (annotate_program (ci_idx input)).
Proof.
  unfold phase_expr_diags. rewrite (ci_blocks_ok input).
  change (flat_map (annotate_encl (ci_idx input) []) (prog_blocks p)) with (annotate_program (ci_idx input)).
  apply flat_map_ext_in. intros roc Hin. apply occ_work_diags_eq_spec.
  rewrite <- (annotate_program_fst (ci_idx input)). exact (in_map fst _ _ Hin).
Qed.

(** ═══ §8 THE ONE EXPRESSION PHASE ═══ a transient object bundling the retained [TypeNameFactTable] and the
    proof-carrying [ExprOutcomeTable] (built from the SAME [CompilationInput]).  [elaborate] builds ONE of these;
    its table is queried, its outcomes are queried TOTALLY, its FACTS and its DIAGNOSTICS both project the SAME
    [ep_ot] object — NOT two extensional equalities to a global map. *)
Record ExpressionPhase {p} (input : CompilationInput p) : Type := mkExpressionPhase {
  ep_tnft : TypeNameFactTable p ;
  ep_ot   : ExprOutcomeTable input ep_tnft ;
  ep_eft  : ExprFactTable p (ci_ip input) ;      (* §9/§2.8 the RETAINED proof-backed fact object, sealed by identity *)
  ep_tnft_prov : ep_tnft = build_type_name_fact_table input
    (* §5/§2.9 RETAINED-INPUT PROVENANCE: the phase's type-name table is not an arbitrary [TypeNameFactTable p] —
       it IS the exact object built from THIS phase's [CompilationInput] (whose map is the fold over [ci_visit
       input], [build_tnft_map]).  No ExpressionPhase can be constructed with a foreign table. *)
}.
Arguments mkExpressionPhase {p input} _ _ _ _.
Arguments ep_tnft {p input} _.  Arguments ep_ot {p input} _.  Arguments ep_eft {p input} _.
Arguments ep_tnft_prov {p input} _.

Definition build_expression_phase {p} (input : CompilationInput p) : ExpressionPhase input :=
  let tnft := build_type_name_fact_table input in
  let ot   := build_outcome_table input tnft in
  mkExpressionPhase tnft ot (build_expr_fact_table input tnft ot) eq_refl.

(* the phase's fact projection (= the retained [ep_eft] object's map for the built phase, definitionally). *)
Definition ep_facts {p} {input : CompilationInput p} (ph : ExpressionPhase input)
  : GoIndex.NodeKeyMapBase.t ExprFact := phase_expr_facts input (ep_tnft ph) (ep_ot ph).
Definition ep_diags {p} {input : CompilationInput p} (ph : ExpressionPhase input)
  : list (DiagnosticReason p) := phase_expr_diags input (ep_tnft ph) (ep_ot ph).

(** ★§8/§10.6 THE ONE PHASE DRIVES BOTH PROJECTIONS: the sealed FACTS and the DIAGNOSTICS are BOTH projections
    of the SAME retained [ep_ot ph] outcome table inside ONE [ExpressionPhase] — each proved equal to its
    declarative specification, but SOURCED from the one object (not a conjunction over a global raw map). *)
Theorem facts_and_diags_share_phase {p} (input : CompilationInput p) (ph : ExpressionPhase input) :
  ep_facts ph = prog_expr_facts p
  /\ ep_diags ph = flat_map (fun roc => occ_expr_diags (ci_idx input) (snd roc) (fst roc)) (annotate_program (ci_idx input)).
Proof.
  split; [ exact (phase_expr_facts_eq_spec input (ep_tnft ph) (ep_ot ph))
         | exact (phase_expr_diags_eq_spec input (ep_tnft ph) (ep_ot ph)) ].
Qed.

(* the phase diagnostics EQUAL the spec [expr_diags] (for the decision infrastructure). *)
Lemma ep_diags_eq_expr_diags {p} (input : CompilationInput p) (ph : ExpressionPhase input) :
  ep_diags ph = expr_diags (ci_idx input).
Proof. rewrite (proj2 (facts_and_diags_share_phase input ph)), (expr_diags_eq_spec (ci_idx input)). reflexivity. Qed.

(** THE NESTED SCAR: every [outer_context] ref of an invalid-conversion diagnostic in the
    whole expression report is a genuine CONVERSION whose subtree STRICTLY contains the primary — a real
    strict-ancestor conversion, never fabricated or copied syntax.  (Delivered by the ONE-PASS annotation,
    proved sound by [annotate_program_ctx_sound].) *)
Lemma expr_diags_conv_scar_sound {p} (idx : GoIndex.Snap.SyntaxIndex p) er tr opr outer t ci :
  In (DRInvalidConversion er tr opr outer t ci) (expr_diags idx) ->
  forall a, In a outer ->
    is_conversion_occ (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref a)) = true
    /\ Pos.lt (GoIndex.Snap.node_ref_local (GoIndex.erase_ref a)) (GoIndex.Snap.node_ref_local (GoIndex.erase_ref er))
    /\ Pos.le (GoIndex.Snap.node_ref_local (GoIndex.erase_ref er)) (GoIndex.Snap.node_subtree_end idx (GoIndex.erase_ref a)).
Proof.
  intros Hin a Ha. rewrite expr_diags_eq_spec in Hin. apply in_flat_map in Hin.
  destruct Hin as [roc [Hroc Hd]].
  destruct (occ_expr_diags_conv_sound idx (fst roc) (snd roc) er tr opr outer t ci Hd) as [Hoeq [Hae _]].
  subst outer.
  pose proof Hroc as Hroc2. rewrite (surjective_pairing roc) in Hroc2.
  destruct (annotate_program_ctx_sound idx (fst roc) (snd roc) a Hroc2 Ha) as [Hconv [Hlt Hle]].
  assert (Her : GoIndex.erase_ref er = fst (fst roc))
    by exact (GoIndex.erase_as_kind idx (fst (fst roc)) GoIndex.KExpression er Hae).
  rewrite Her. split; [exact Hconv | split; [exact Hlt | exact Hle]].
Qed.

(** the nested scar is SAME-FILE (as the primary), NEAREST-FIRST (deepest enclosing
    conversion first), and DUPLICATE-FREE for every invalid-conversion diagnostic in the whole report. *)
Lemma expr_diags_conv_scar_wf {p} (idx : GoIndex.Snap.SyntaxIndex p) er tr opr outer t ci :
  In (DRInvalidConversion er tr opr outer t ci) (expr_diags idx) ->
  Forall (fun a => GoIndex.Snap.node_ref_file (GoIndex.erase_ref a) = GoIndex.Snap.node_ref_file (GoIndex.erase_ref er)) outer
  /\ StronglySorted (fun a b => Pos.lt (GoIndex.Snap.node_ref_local (GoIndex.erase_ref b)) (GoIndex.Snap.node_ref_local (GoIndex.erase_ref a))) outer
  /\ NoDup outer.
Proof.
  intro Hin. rewrite expr_diags_eq_spec in Hin. apply in_flat_map in Hin.
  destruct Hin as [roc [Hroc Hd]].
  destruct (occ_expr_diags_conv_sound idx (fst roc) (snd roc) er tr opr outer t ci Hd) as [Hoeq [Hae _]].
  subst outer.
  pose proof Hroc as Hroc2. rewrite (surjective_pairing roc) in Hroc2.
  destruct (annotate_program_ctx_wf idx (fst roc) (snd roc) Hroc2) as [Hfile [Hss Hnd]].
  assert (Her : GoIndex.erase_ref er = fst (fst roc))
    by exact (GoIndex.erase_as_kind idx (fst (fst roc)) GoIndex.KExpression er Hae).
  rewrite Her. split; [exact Hfile | split; [exact Hss | exact Hnd]].
Qed.

(* ---- COMPLETENESS: [expr_diags] is empty IFF every argument resolves (= [program_typedb]) ---- *)

(** the PURE (index-free) per-occurrence "emits nothing" predicate: no locally-failing conversion here, and no
    defaulting-argument failure here. *)
Definition occ_local_ok (occ : GoIndex.SourceOccurrence) : bool :=
  match GoIndex.view_expr occ with
  | Some e => match local_conv_failure e with Some _ => false | None => true end
  | None => true
  end.
Definition occ_default_ok (occ : GoIndex.SourceOccurrence) : bool :=
  match GoIndex.view_expr occ with
  | Some e => match arg_default_failure occ e with Some _ => false | None => true end
  | None => true
  end.
Definition occ_emits_none_pure (occ : GoIndex.SourceOccurrence) : bool :=
  occ_local_ok occ && occ_default_ok occ.

(* a conversion's TYPE-NAME occurrence (no expression view) is vacuously local-OK / default-OK / emit-none. *)
Lemma occ_local_ok_typename : forall ts par sub,
  occ_local_ok (GoIndex.mkOcc GoIndex.KTypeName (GoIndex.ViewTypeName ts) (Some par) GoIndex.RConversionTarget sub) = true.
Proof. reflexivity. Qed.
Lemma occ_default_ok_typename : forall ts par sub,
  occ_default_ok (GoIndex.mkOcc GoIndex.KTypeName (GoIndex.ViewTypeName ts) (Some par) GoIndex.RConversionTarget sub) = true.
Proof. reflexivity. Qed.
Lemma occ_emits_none_pure_typename : forall ts par sub,
  occ_emits_none_pure (GoIndex.mkOcc GoIndex.KTypeName (GoIndex.ViewTypeName ts) (Some par) GoIndex.RConversionTarget sub) = true.
Proof. reflexivity. Qed.

(** every use-context type is allowed for a println argument (the type universe is exactly the allowed set). *)
Lemma use_allowsb_println_true : forall t, use_allowsb UsePrintlnArg t = true.
Proof. intro t; destruct t; reflexivity. Qed.

(** KEY: no conversion in a subtree locally fails IFF the subtree's [const_info] succeeds. *)
Lemma conv_ok_fold : forall e parent role me,
  forallb (fun x => occ_local_ok (snd x)) (GoIndex.occs_expr parent role me e)
  = match const_info e with Some _ => true | None => false end.
Proof.
  induction e as [ b|n1|n2|s| df | dcx | ts x IHx ]; intros parent role me.
  1,2,3,4,5,6: reflexivity.
  cbn [GoIndex.occs_expr forallb snd].
  rewrite occ_local_ok_typename.
  unfold occ_local_ok at 1; cbn [GoIndex.view_expr GoIndex.occurrence_view];
  cbn [local_conv_failure]; cbn [GoTypes.const_info];
  specialize (IHx me GoIndex.RConversionOperand (Pos.succ (Pos.succ me)));
  destruct (const_info x) as [ci|] eqn:Ex;
  [ destruct (convert_const _ ci) as [ci'|] eqn:Ec;
    [ cbn [andb]; rewrite IHx; reflexivity
    | cbn [andb option_map]; reflexivity ]
  | cbn [andb option_map]; rewrite IHx; reflexivity ].
Qed.

Lemma forallb_andb {A} (f g : A -> bool) (l : list A) :
  forallb (fun x => f x && g x) l = forallb f l && forallb g l.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity|]. rewrite IH.
  destruct (f a), (g a), (forallb f l), (forallb g l); reflexivity.
Qed.

(** a conversion-operand occurrence is always default-OK (only a println-arg root can default-fail). *)
Lemma occ_default_ok_operand : forall e par sub,
  occ_default_ok (GoIndex.mkOcc GoIndex.KExpression (GoIndex.ViewExpression e) (Some par) GoIndex.RConversionOperand sub) = true.
Proof. reflexivity. Qed.

Lemma occ_default_ok_operand_true : forall e parent me,
  forallb (fun x => occ_default_ok (snd x)) (GoIndex.occs_expr parent GoIndex.RConversionOperand me e) = true.
Proof.
  induction e as [ b|n1|n2|s| df | dcx | ts x IHx ];
    intros parent me; cbn [GoIndex.occs_expr forallb snd].
  1,2,3,4,5,6: rewrite occ_default_ok_operand; reflexivity.
  rewrite occ_default_ok_operand, occ_default_ok_typename, !Bool.andb_true_l; apply IHx.
Qed.

(** a println-argument root occurrence is default-OK IFF its untyped constant defaults (typed / failed = OK). *)
Lemma occ_default_ok_printlnarg : forall e par aidx sub,
  occ_default_ok (GoIndex.mkOcc GoIndex.KExpression (GoIndex.ViewExpression e) (Some par) (GoIndex.RPrintlnArg aidx) sub)
  = match const_info e with Some (CIUntyped c) => match default_const c with Some _ => true | None => false end | _ => true end.
Proof.
  intros e par aidx sub. unfold occ_default_ok.
  cbn [GoIndex.view_expr GoIndex.occurrence_view arg_default_failure GoIndex.occurrence_role].
  destruct (const_info e) as [[c|t tc]|]; [ destruct (default_const c) | | ]; reflexivity.
Qed.

Lemma occ_default_fold_arg : forall e parent aidx me,
  forallb (fun x => occ_default_ok (snd x)) (GoIndex.occs_expr parent (GoIndex.RPrintlnArg aidx) me e)
  = match const_info e with Some (CIUntyped c) => match default_const c with Some _ => true | None => false end | _ => true end.
Proof.
  intros e parent aidx me. destruct e as [ b|n1|n2|s| df | dcx | ts x ];
    cbn [GoIndex.occs_expr forallb snd].
  1,2,3,4,5,6: rewrite Bool.andb_true_r; apply occ_default_ok_printlnarg.
  rewrite occ_default_ok_typename, occ_default_ok_operand_true, ?Bool.andb_true_r, ?Bool.andb_true_l;
    apply occ_default_ok_printlnarg.
Qed.

(** ONE println argument's occurrence stream emits nothing IFF the argument resolves ([expr_typedb]). *)
Lemma occ_emits_arg : forall e parent aidx me,
  forallb (fun x => occ_emits_none_pure (snd x)) (GoIndex.occs_arg parent aidx me e) = expr_typedb UsePrintlnArg e.
Proof.
  intros e parent aidx me. unfold GoIndex.occs_arg, occ_emits_none_pure.
  rewrite forallb_andb, conv_ok_fold, occ_default_fold_arg.
  unfold GoTypes.expr_typedb, GoTypes.resolve_expr, GoTypes.resolve_expr_const.
  destruct (const_info e) as [[c|t tc]|]; cbn [resolve_const_info].
  - destruct (default_const c) as [rc|]; cbn [option_map]; [ rewrite use_allowsb_println_true |]; reflexivity.
  - cbn [option_map]. rewrite use_allowsb_println_true. reflexivity.
  - cbn [option_map]. reflexivity.
Qed.

Lemma occ_emits_args : forall es parent aidx me,
  forallb (fun x => occ_emits_none_pure (snd x)) (GoIndex.occs_args parent aidx me es)
  = forallb (expr_typedb UsePrintlnArg) es.
Proof.
  induction es as [|e rest IH]; intros parent aidx me; [reflexivity|].
  cbn [GoIndex.occs_args]. rewrite forallb_app, occ_emits_arg, IH. reflexivity.
Qed.

Lemma occ_emits_stmt : forall s parent sidx me,
  forallb (fun x => occ_emits_none_pure (snd x)) (GoIndex.occs_stmt parent sidx me s) = stmt_typedb s.
Proof.
  intros [args] parent sidx me.
  cbn [GoIndex.occs_stmt forallb occ_emits_none_pure occ_local_ok occ_default_ok snd
       GoIndex.view_expr GoIndex.occurrence_view].
  rewrite occ_emits_args. reflexivity.
Qed.

Lemma occ_emits_stmts : forall ss parent sidx me,
  forallb (fun x => occ_emits_none_pure (snd x)) (GoIndex.occs_stmts parent sidx me ss) = forallb stmt_typedb ss.
Proof.
  induction ss as [|s rest IH]; intros parent sidx me; [reflexivity|].
  cbn [GoIndex.occs_stmts]. rewrite forallb_app, occ_emits_stmt, IH. reflexivity.
Qed.

Lemma occ_emits_decl : forall d parent didx me,
  forallb (fun x => occ_emits_none_pure (snd x)) (GoIndex.occs_decl parent didx me d) = decl_typedb d.
Proof.
  intros [body] parent didx me.
  cbn [GoIndex.occs_decl forallb occ_emits_none_pure occ_local_ok occ_default_ok snd
       GoIndex.view_expr GoIndex.occurrence_view].
  rewrite occ_emits_stmts. reflexivity.
Qed.

Lemma occ_emits_decls : forall ds parent didx me,
  forallb (fun x => occ_emits_none_pure (snd x)) (GoIndex.occs_decls parent didx me ds) = forallb decl_typedb ds.
Proof.
  induction ds as [|d rest IH]; intros parent didx me; [reflexivity|].
  cbn [GoIndex.occs_decls]. rewrite forallb_app, occ_emits_decl, IH. reflexivity.
Qed.

Lemma occ_emits_file : forall f,
  forallb (fun x => occ_emits_none_pure (snd x)) (GoIndex.occs_file f) = source_file_typedb f.
Proof.
  intros f. unfold GoIndex.occs_file. destruct (source_imports f) as [|i tl]; [| destruct i].
  cbn [forallb occ_emits_none_pure occ_local_ok occ_default_ok snd GoIndex.view_expr GoIndex.occurrence_view].
  rewrite occ_emits_decls. unfold GoTypes.source_file_typedb, GoTypes.file_typedb. reflexivity.
Qed.

(** lift the file-level emit fold to the whole program (via the traversal projection). *)
Lemma visit_file_emits {p} (fr : GoIndex.Snap.FileRef p) :
  forallb (fun x => occ_emits_none_pure (snd x)) (GoIndex.Snap.visit_file fr)
  = source_file_typedb (GoIndex.Snap.file_ref_source fr).
Proof.
  rewrite GoTypes.forallb_map_snd, GoIndex.Snap.visit_file_snd, <- GoTypes.forallb_map_snd.
  apply occ_emits_file.
Qed.

Lemma emits_none_program_typedb (p : GoProgram) :
  forallb (fun x => occ_emits_none_pure (snd x)) (prog_visit p) = program_typedb p.
Proof.
  rewrite prog_visit_flat_map, forallb_flat_map. unfold GoTypes.program_typedb.
  apply GoTypes.forallb_ext_in. intros b Hb. unfold binding_visit.
  pose proof (GoAST.file_bindings_find (prog_files p) b Hb) as Hfind.
  destruct (GoIndex.Snap.file_of_path_source p (fst b) (snd b) Hfind) as [fr [Hfop [Hpath Hsrc]]].
  rewrite Hfop, visit_file_emits, Hsrc. reflexivity.
Qed.

(** every program-visited occurrence IS its reference's exact source occurrence. *)
Lemma prog_visit_view (p : GoProgram) (r : GoIndex.Snap.NodeRef p) occ :
  In (r, occ) (prog_visit p) -> occ = GoIndex.Snap.source_occurrence_of_ref r.
Proof.
  rewrite prog_visit_flat_map. intro Hin. apply in_flat_map in Hin. destruct Hin as [b [Hb Hin]].
  unfold binding_visit in Hin. destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|]; [| destruct Hin].
  destruct (GoIndex.Snap.visit_file_view p fr r occ Hin) as [Hocc _]. exact Hocc.
Qed.

(** per-occurrence: the emitted diagnostics are empty IFF the occurrence emits nothing (pure). *)
Lemma occ_expr_diags_empty {p} (idx : GoIndex.Snap.SyntaxIndex p) (outer : list (GoIndex.ExprRef p))
    (r : GoIndex.Snap.NodeRef p) occ :
  In (r, occ) (prog_visit p) ->
  (occ_expr_diags idx outer (r, occ) = nil <-> occ_emits_none_pure occ = true).
Proof.
  intro Hin. pose proof (prog_visit_view p r occ Hin) as Hocc.
  unfold occ_emits_none_pure, occ_local_ok, occ_default_ok. cbn [fst snd].
  unfold occ_expr_diags. cbn [fst snd].
  destruct (GoIndex.as_expr idx r) as [er|] eqn:Ea.
  - assert (Hke : GoIndex.occurrence_kind occ = GoIndex.KExpression).
    { rewrite Hocc, <- (GoIndex.Snap.node_kind_matches_source p idx r).
      unfold GoIndex.as_expr, GoIndex.as_kind in Ea.
      destruct (GoIndex.syntaxkind_eq_dec (GoIndex.Snap.node_kind idx r) GoIndex.KExpression) as [Hk|]; [exact Hk|discriminate Ea]. }
    destruct (GoIndex.kind_view_expr occ Hke) as [e Hve]. rewrite Hve.
    destruct (local_conv_failure e) as [[t ci]|] eqn:Elc; cbn [andb].
    + (* a real conversion mints its target ref, so the emitted list is a nonempty singleton *)
      destruct e as [ b|n1|n2|s| df | dcx | ts x ]; try discriminate Elc.
      destruct (conversion_target_ref_conv idx r occ er ts x Hin Hve Ea) as [tr [Hctr _]].
      destruct (conversion_operand_ref_conv idx r occ er ts x Hin Hve Ea) as [opr [Hcor _]].
      rewrite Hctr, Hcor. split; intro H; discriminate H.
    + destruct (arg_default_failure occ e) as [[c dt]|]; cbn [andb];
        split; intro H; try discriminate H; reflexivity.
  - assert (Hve : GoIndex.view_expr occ = None).
    { destruct (GoIndex.view_expr occ) as [e|] eqn:E; [| reflexivity].
      exfalso. unfold GoIndex.as_expr, GoIndex.as_kind in Ea.
      destruct (GoIndex.syntaxkind_eq_dec (GoIndex.Snap.node_kind idx r) GoIndex.KExpression) as [|Hk]; [discriminate Ea|].
      apply Hk. rewrite (GoIndex.Snap.node_kind_matches_source p idx r), <- Hocc. exact (GoIndex.view_expr_kind occ e E). }
    rewrite Hve. split; intro H; try discriminate H; reflexivity.
Qed.

Lemma flat_map_nil_forallb {A B} (g : A -> list B) (l : list A) :
  flat_map g l = nil <-> forallb (fun x => match g x with nil => true | _ => false end) l = true.
Proof.
  induction l as [|a l IH]; [split; reflexivity|].
  simpl. destruct (g a) as [|b gb] eqn:Ega; simpl.
  - exact IH.
  - split; intro H; discriminate H.
Qed.

(** THE EXPRESSION COMPLETENESS: [expr_diags] is empty IFF the program types ([ProgramTyped]). *)
Lemma expr_diags_empty_iff {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  expr_diags idx = nil <-> program_typedb p = true.
Proof.
  rewrite expr_diags_eq_spec. rewrite flat_map_nil_forallb, <- emits_none_program_typedb.
  rewrite !forallb_forall. split; intro H.
  - intros [r occ] Hin.
    assert (Hroc : exists ctx, In ((r, occ), ctx) (annotate_program idx)).
    { rewrite <- (annotate_program_fst idx) in Hin. apply in_map_iff in Hin. destruct Hin as [[ro ctx] [Hf Hi]].
      cbn [fst] in Hf. subst ro. exists ctx. exact Hi. }
    destruct Hroc as [ctx Hroc]. specialize (H _ Hroc). cbn [fst snd] in H.
    apply (occ_expr_diags_empty idx ctx r occ Hin).
    destruct (occ_expr_diags idx ctx (r, occ)); [reflexivity | discriminate H].
  - intros roc Hin. destruct roc as [[r occ] ctx]. cbn [fst snd].
    assert (Hin' : In (r, occ) (prog_visit p)).
    { rewrite <- (annotate_program_fst idx). exact (in_map fst _ _ Hin). }
    specialize (H (r, occ) Hin'). cbn [snd] in H.
    apply (occ_expr_diags_empty idx ctx r occ Hin') in H. rewrite H. reflexivity.
Qed.

(* ---- PACKAGE main-count relation: # of top-level-decl occurrences per file = [file_main_count] ---- *)

Definition occ_main_count (occ : GoIndex.SourceOccurrence) : nat :=
  match GoIndex.occurrence_role occ with GoIndex.RFileDecl _ => 1 | _ => 0 end.
Definition sum_main {A} (l : list (A * GoIndex.SourceOccurrence)) : nat :=
  fold_right (fun (ro : A * GoIndex.SourceOccurrence) (acc : nat) => (occ_main_count (snd ro) + acc)%nat) 0%nat l.

Lemma sum_main_cons {A} (x : A * GoIndex.SourceOccurrence) (l : list (A * GoIndex.SourceOccurrence)) :
  sum_main (x :: l) = (occ_main_count (snd x) + sum_main l)%nat.
Proof. reflexivity. Qed.

Lemma sum_main_app {A} (a b : list (A * GoIndex.SourceOccurrence)) :
  sum_main (a ++ b) = (sum_main a + sum_main b)%nat.
Proof.
  induction a as [|x a IH]; [reflexivity|].
  rewrite <- app_comm_cons, (sum_main_cons x (a ++ b)), (sum_main_cons x a), IH. lia.
Qed.

Lemma sum_main_operand : forall e parent me,
  sum_main (GoIndex.occs_expr parent GoIndex.RConversionOperand me e) = 0%nat.
Proof.
  induction e as [ b|n1|n2|s| df | dcx | ts x IHx ]; intros parent me;
    cbn [GoIndex.occs_expr]; rewrite sum_main_cons; cbn [occ_main_count GoIndex.occurrence_role snd].
  1,2,3,4,5,6: reflexivity.
  rewrite Nat.add_0_l, sum_main_cons; cbn [occ_main_count GoIndex.occurrence_role snd];
    rewrite Nat.add_0_l; apply IHx.
Qed.

Lemma sum_main_arg : forall e parent aidx me, sum_main (GoIndex.occs_arg parent aidx me e) = 0%nat.
Proof.
  intros e parent aidx me. unfold GoIndex.occs_arg.
  destruct e as [ b|n1|n2|s| df | dcx | ts x ];
    cbn [GoIndex.occs_expr]; rewrite sum_main_cons; cbn [occ_main_count GoIndex.occurrence_role snd].
  1,2,3,4,5,6: reflexivity.
  rewrite Nat.add_0_l, sum_main_cons; cbn [occ_main_count GoIndex.occurrence_role snd];
    rewrite Nat.add_0_l; apply sum_main_operand.
Qed.

Lemma sum_main_args : forall es parent aidx me, sum_main (GoIndex.occs_args parent aidx me es) = 0%nat.
Proof.
  induction es as [|e rest IH]; intros parent aidx me; [reflexivity|].
  cbn [GoIndex.occs_args]. rewrite sum_main_app, sum_main_arg, IH. reflexivity.
Qed.

Lemma sum_main_stmt : forall s parent sidx me, sum_main (GoIndex.occs_stmt parent sidx me s) = 0%nat.
Proof.
  intros [args] parent sidx me. cbn [GoIndex.occs_stmt].
  rewrite sum_main_cons; cbn [occ_main_count GoIndex.occurrence_role snd].
  rewrite Nat.add_0_l. apply sum_main_args.
Qed.

Lemma sum_main_stmts : forall ss parent sidx me, sum_main (GoIndex.occs_stmts parent sidx me ss) = 0%nat.
Proof.
  induction ss as [|s rest IH]; intros parent sidx me; [reflexivity|].
  cbn [GoIndex.occs_stmts]. rewrite sum_main_app, sum_main_stmt, IH. reflexivity.
Qed.

Lemma sum_main_decl : forall d parent didx me, sum_main (GoIndex.occs_decl parent didx me d) = 1%nat.
Proof.
  intros [body] parent didx me. cbn [GoIndex.occs_decl].
  rewrite sum_main_cons; cbn [occ_main_count GoIndex.occurrence_role snd].
  rewrite sum_main_stmts. reflexivity.
Qed.

Lemma sum_main_decls : forall ds parent didx me, sum_main (GoIndex.occs_decls parent didx me ds) = length ds.
Proof.
  induction ds as [|d rest IH]; intros parent didx me; [reflexivity|].
  cbn [GoIndex.occs_decls length]. rewrite sum_main_app, sum_main_decl, IH. reflexivity.
Qed.

Lemma file_main_count_length : forall decls, file_main_count decls = length decls.
Proof.
  intro decls. unfold file_main_count.
  induction decls as [|[body] rest IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma sum_main_file : forall f, sum_main (GoIndex.occs_file f) = file_main_count (source_decls f).
Proof.
  intros f. unfold GoIndex.occs_file. destruct (source_imports f) as [|i tl]; [| destruct i].
  rewrite sum_main_cons; cbn [occ_main_count GoIndex.occurrence_role snd].
  rewrite sum_main_cons; cbn [occ_main_count GoIndex.occurrence_role snd].
  rewrite sum_main_decls, file_main_count_length. reflexivity.
Qed.

(* PACKAGE MAIN-REF BUCKETS.  The per-file/per-package collection of the top-level-decl (main)
   occurrences as validated [DeclRef]s, in canonical order.  Its length is the declarative [file_main_count]
   (hence, aggregated, [ps_main_count]) — so the reference collection AGREES with the package count judgment,
   without a second production package decision.

   [decl_kind_count] counts an occurrence by its KIND (KTopLevelDecl); [occ_main_count] counts by its ROLE
   (RFileDecl).  Over a real occurrence stream ([occs_file]) the two coincide (a decl head is the ONLY
   KTopLevelDecl and the ONLY RFileDecl), so a DeclRef minted on kind counts exactly the main declarations. *)

Definition decl_kind_count (o : GoIndex.SourceOccurrence) : nat :=
  match GoIndex.occurrence_kind o with GoIndex.KTopLevelDecl => 1%nat | _ => 0%nat end.

Definition decl_count_list {A} (l : list (A * GoIndex.SourceOccurrence)) : nat :=
  fold_right (fun (ro : A * GoIndex.SourceOccurrence) (acc : nat) => (decl_kind_count (snd ro) + acc)%nat) 0%nat l.

Lemma decl_count_list_cons {A} (x : A * GoIndex.SourceOccurrence) (l : list (A * GoIndex.SourceOccurrence)) :
  decl_count_list (x :: l) = (decl_kind_count (snd x) + decl_count_list l)%nat.
Proof. reflexivity. Qed.

Lemma decl_count_list_app {A} (a b : list (A * GoIndex.SourceOccurrence)) :
  decl_count_list (a ++ b) = (decl_count_list a + decl_count_list b)%nat.
Proof.
  induction a as [|x a IH]; [reflexivity|].
  rewrite <- app_comm_cons, (decl_count_list_cons x (a ++ b)), (decl_count_list_cons x a), IH. lia.
Qed.

(** [decl_count_list] depends only on the OCCURRENCE component (the [snd]-projection). *)
Lemma decl_count_list_snd {A B} (l1 : list (A * GoIndex.SourceOccurrence)) (l2 : list (B * GoIndex.SourceOccurrence)) :
  map snd l1 = map snd l2 -> decl_count_list l1 = decl_count_list l2.
Proof.
  revert l2. induction l1 as [|x l1 IH]; intros [|y l2] Hm; cbn [map] in Hm; try discriminate; [reflexivity|].
  injection Hm as Hsnd Hrest.
  rewrite (decl_count_list_cons x l1), (decl_count_list_cons y l2), Hsnd, (IH l2 Hrest). reflexivity.
Qed.

(* ---- kind/role COHERENCE over a real occurrence stream: [decl_kind_count o = occ_main_count o]. ---- *)

Definition coh (o : GoIndex.SourceOccurrence) : Prop := decl_kind_count o = occ_main_count o.

Lemma coh_operand : forall e parent me,
  Forall (fun ro => coh (snd ro)) (GoIndex.occs_expr parent GoIndex.RConversionOperand me e).
Proof.
  induction e as [ b|n1|n2|s| df | dcx | ts x IHx ]; intros parent me; cbn [GoIndex.occs_expr].
  1,2,3,4,5,6: constructor; [ reflexivity | constructor ].
  constructor; [ reflexivity | constructor; [ reflexivity | apply IHx ] ].
Qed.

Lemma coh_arg : forall e parent aidx me,
  Forall (fun ro => coh (snd ro)) (GoIndex.occs_arg parent aidx me e).
Proof.
  intros e parent aidx me. unfold GoIndex.occs_arg.
  destruct e as [ b|n1|n2|s| df | dcx | ts x ]; cbn [GoIndex.occs_expr].
  1,2,3,4,5,6: constructor; [ reflexivity | constructor ].
  constructor; [ reflexivity | constructor; [ reflexivity | apply coh_operand ] ].
Qed.

Lemma coh_args : forall es parent aidx me,
  Forall (fun ro => coh (snd ro)) (GoIndex.occs_args parent aidx me es).
Proof.
  induction es as [|e rest IH]; intros parent aidx me; [constructor|].
  cbn [GoIndex.occs_args]. apply Forall_app. split; [ apply coh_arg | apply IH ].
Qed.

Lemma coh_stmt : forall s parent sidx me,
  Forall (fun ro => coh (snd ro)) (GoIndex.occs_stmt parent sidx me s).
Proof.
  intros [args] parent sidx me. cbn [GoIndex.occs_stmt].
  constructor; [ reflexivity | apply coh_args ].
Qed.

Lemma coh_stmts : forall ss parent sidx me,
  Forall (fun ro => coh (snd ro)) (GoIndex.occs_stmts parent sidx me ss).
Proof.
  induction ss as [|s rest IH]; intros parent sidx me; [constructor|].
  cbn [GoIndex.occs_stmts]. apply Forall_app. split; [ apply coh_stmt | apply IH ].
Qed.

Lemma coh_decl : forall d parent didx me,
  Forall (fun ro => coh (snd ro)) (GoIndex.occs_decl parent didx me d).
Proof.
  intros [body] parent didx me. cbn [GoIndex.occs_decl].
  constructor; [ reflexivity | apply coh_stmts ].
Qed.

Lemma coh_decls : forall ds parent didx me,
  Forall (fun ro => coh (snd ro)) (GoIndex.occs_decls parent didx me ds).
Proof.
  induction ds as [|d rest IH]; intros parent didx me; [constructor|].
  cbn [GoIndex.occs_decls]. apply Forall_app. split; [ apply coh_decl | apply IH ].
Qed.

Lemma coh_file : forall f, Forall (fun ro => coh (snd ro)) (GoIndex.occs_file f).
Proof.
  intro f. unfold GoIndex.occs_file. destruct (source_imports f) as [|i tl]; [| destruct i].
  constructor; [ reflexivity | ]. constructor; [ reflexivity | apply coh_decls ].
Qed.

(** the COHERENCE, transported to the [snd]-count identity: [decl_count_list = sum_main] over a file's occurrences. *)
Lemma decl_count_sum_main_file : forall f, decl_count_list (GoIndex.occs_file f) = sum_main (GoIndex.occs_file f).
Proof.
  intro f. pose proof (coh_file f) as Hcoh.
  induction (GoIndex.occs_file f) as [|x l IH]; [reflexivity|].
  inversion Hcoh as [|? ? Hx Hl]; subst.
  rewrite (decl_count_list_cons x l), (sum_main_cons x l), (IH Hl). unfold coh in Hx. rewrite Hx. reflexivity.
Qed.

(* the optional-bucket length, and its rewrite past the [Some l => l | None => []] read shape — the shared
   arithmetic helpers the package-bucket fold characterization below reasons through. *)
Definition olen {A} (o : option (list A)) : nat := match o with Some l => length l | None => 0%nat end.

Lemma olen_match {A} (o : option (list A)) :
  length (match o with Some l => l | None => [] end) = olen o.
Proof. destruct o; reflexivity. Qed.

(* the PACKAGE main-ref buckets built as ONE fold over the DELIVERED visit stream (NOT a second
   per-file [Snap.visit_file]).  Each occurrence contributes to its file's package ([occ_pkg] = the file's
   parent directory): a [DMain] declaration prepends its [DeclRef]; a FILE ROOT ([KFile]) INITIALIZES the
   package entry (so a package with zero mains is still represented) without disturbing existing mains.  Since
   [prog_visit] visits each file's root then its decls in preorder, and [fold_right] processes the stream
   right-to-left, a package's bucket ends up its files' mains in canonical stream order. *)

Definition occ_pkg {p} (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) : string :=
  fp_parent (GoIndex.Snap.file_ref_path (GoIndex.Snap.node_ref_file (fst ro))).

Definition ppkg_step {p} (idx : GoIndex.Snap.SyntaxIndex p)
    (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) (acc : PM.t (list (GoIndex.DeclRef p)))
  : PM.t (list (GoIndex.DeclRef p)) :=
  match GoIndex.as_decl idx (fst ro) with
  | Some dr => PM.add (occ_pkg ro) (dr :: match PM.find (occ_pkg ro) acc with Some l => l | None => [] end) acc
  | None =>
      match GoIndex.as_kind idx (fst ro) GoIndex.KFile with
      | Some _ => match PM.find (occ_pkg ro) acc with Some _ => acc | None => PM.add (occ_pkg ro) [] acc end
      | None => acc
      end
  end.

(* the package buckets over an EXPLICIT visit stream — the ONE shared builder: production elaboration
   folds it over its RETAINED [visit] value (no second [prog_visit]/[prog_blocks]/[visit_file]); the canonical
   convenience form below applies it to [prog_visit p]. *)
Definition prog_package_refs_from_visit {p} (idx : GoIndex.Snap.SyntaxIndex p)
    (visit : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) : PM.t (list (GoIndex.DeclRef p)) :=
  fold_right (ppkg_step idx) (PM.empty (list (GoIndex.DeclRef p))) visit.

Definition prog_package_refs {p} (idx : GoIndex.Snap.SyntaxIndex p) : PM.t (list (GoIndex.DeclRef p)) :=
  prog_package_refs_from_visit idx (prog_visit p).

(* the per-package DMain count over an occurrence list (an occurrence contributes 1 exactly when its file's
   package is [dir] AND it mints a DeclRef). *)
Fixpoint pkg_declcount {p} (idx : GoIndex.Snap.SyntaxIndex p) (dir : string)
    (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) : nat :=
  match l with
  | [] => 0%nat
  | ro :: rest =>
      ((if String.eqb (occ_pkg ro) dir
        then match GoIndex.as_decl idx (fst ro) with Some _ => 1%nat | None => 0%nat end else 0%nat)
       + pkg_declcount idx dir rest)%nat
  end.

(* the per-step bucket-length contribution: exactly the DMain-count contribution (a file-root init adds an
   empty bucket — presence, not length). *)
Lemma ppkg_step_olen {p} (idx : GoIndex.Snap.SyntaxIndex p) (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)
  (acc : PM.t (list (GoIndex.DeclRef p))) (dir : string) :
  olen (PM.find dir (ppkg_step idx ro acc))
  = ((if String.eqb (occ_pkg ro) dir then match GoIndex.as_decl idx (fst ro) with Some _ => 1%nat | None => 0%nat end else 0%nat)
     + olen (PM.find dir acc))%nat.
Proof.
  unfold ppkg_step. destruct (GoIndex.as_decl idx (fst ro)) as [dr|] eqn:Ed.
  - destruct (String.eqb (occ_pkg ro) dir) eqn:Edir.
    + apply String.eqb_eq in Edir. rewrite Edir, PMF.add_eq_o by reflexivity. cbn [olen length]. rewrite <- Edir, olen_match. reflexivity.
    + apply String.eqb_neq in Edir. rewrite PMF.add_neq_o by exact Edir. reflexivity.
  - destruct (GoIndex.as_kind idx (fst ro) GoIndex.KFile) as [fnr|] eqn:Ef.
    + destruct (PM.find (occ_pkg ro) acc) as [l|] eqn:Efind.
      * destruct (String.eqb (occ_pkg ro) dir) eqn:Edir; [ apply String.eqb_eq in Edir; rewrite Edir in Efind; rewrite Efind | ]; reflexivity.
      * destruct (String.eqb (occ_pkg ro) dir) eqn:Edir.
        -- apply String.eqb_eq in Edir. rewrite Edir, PMF.add_eq_o by reflexivity. cbn [olen length].
           rewrite <- Edir, Efind. reflexivity.
        -- apply String.eqb_neq in Edir. rewrite PMF.add_neq_o by exact Edir. reflexivity.
    + destruct (String.eqb (occ_pkg ro) dir) eqn:Edir; reflexivity.
Qed.

Lemma ppkg_olen_char {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall l acc dir,
  olen (PM.find dir (fold_right (ppkg_step idx) acc l)) = (pkg_declcount idx dir l + olen (PM.find dir acc))%nat.
Proof.
  induction l as [|ro rest IH]; intros acc dir; [reflexivity|].
  cbn [fold_right pkg_declcount]. rewrite (ppkg_step_olen idx ro (fold_right (ppkg_step idx) acc rest) dir).
  rewrite (IH acc dir). lia.
Qed.

(* on a VISITED occurrence the DeclRef-mint contribution equals its [decl_kind_count]. *)
Lemma ppkg_as_decl_kind_count {p} (idx : GoIndex.Snap.SyntaxIndex p) (fr : GoIndex.Snap.FileRef p)
  (r : GoIndex.Snap.NodeRef p) (occ : GoIndex.SourceOccurrence) :
  In (r, occ) (GoIndex.Snap.visit_file fr) ->
  (match GoIndex.as_decl idx r with Some _ => 1%nat | None => 0%nat end) = decl_kind_count occ.
Proof.
  intro Hin. pose proof (GoIndex.Snap.visit_file_view p fr r occ Hin) as [Hocc _].
  assert (Hk : GoIndex.Snap.node_kind idx r = GoIndex.occurrence_kind occ)
    by (rewrite (GoIndex.Snap.node_kind_matches_source p idx r), Hocc; reflexivity).
  unfold GoIndex.as_decl, GoIndex.as_kind, decl_kind_count.
  destruct (GoIndex.syntaxkind_eq_dec (GoIndex.Snap.node_kind idx r) GoIndex.KTopLevelDecl) as [He|Hne].
  - rewrite Hk in He; rewrite He; reflexivity.
  - rewrite Hk in Hne. destruct (GoIndex.occurrence_kind occ); try reflexivity. exfalso; apply Hne; reflexivity.
Qed.

(* over a list all of whose occurrences share package [D] and mint DeclRefs by kind, the DMain-count is the
   whole [decl_count_list] when [D = dir], else 0. *)
Lemma pkg_declcount_uniform {p} (idx : GoIndex.Snap.SyntaxIndex p) (dir D : string)
  (L : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) :
  (forall ro, In ro L -> occ_pkg ro = D) ->
  (forall ro, In ro L -> match GoIndex.as_decl idx (fst ro) with Some _ => 1%nat | None => 0%nat end = decl_kind_count (snd ro)) ->
  pkg_declcount idx dir L = (if String.eqb D dir then decl_count_list L else 0%nat).
Proof.
  induction L as [|ro rest IH]; intros Hpkg Hkind.
  - cbn [pkg_declcount decl_count_list]. destruct (String.eqb D dir); reflexivity.
  - cbn [pkg_declcount]. rewrite decl_count_list_cons.
    rewrite (Hpkg ro (or_introl eq_refl)), (Hkind ro (or_introl eq_refl)).
    rewrite (IH (fun ro' Hr => Hpkg ro' (or_intror Hr)) (fun ro' Hr => Hkind ro' (or_intror Hr))).
    destruct (String.eqb D dir); lia.
Qed.

(* within a file block every occurrence has the same package ([fp_parent] of the file path); the block's
   DMain-count is the file's [file_main_count] when the package matches, else 0. *)
Lemma pkg_declcount_binding {p} (idx : GoIndex.Snap.SyntaxIndex p) (b : FilePath * GoSourceFile) (dir : string) :
  In b (GoAST.file_bindings (prog_files p)) ->
  pkg_declcount idx dir (binding_visit p b)
  = (if String.eqb (fp_parent (fst b)) dir then file_main_count (source_decls (snd b)) else 0%nat).
Proof.
  intro Hb. unfold binding_visit.
  pose proof (GoAST.file_bindings_find (prog_files p) b Hb) as Hfind.
  destruct (GoIndex.Snap.file_of_path_source p (fst b) (snd b) Hfind) as [fr [Hfop [Hpath Hsrc]]].
  rewrite Hfop.
  rewrite (pkg_declcount_uniform idx dir (fp_parent (GoIndex.Snap.file_ref_path fr)) (GoIndex.Snap.visit_file fr)).
  - rewrite Hpath. destruct (String.eqb (fp_parent (fst b)) dir) eqn:E; [| reflexivity].
    rewrite (decl_count_list_snd (GoIndex.Snap.visit_file fr) (GoIndex.occs_file (GoIndex.Snap.file_ref_source fr))
               (GoIndex.Snap.visit_file_snd p fr)).
    rewrite decl_count_sum_main_file, sum_main_file, Hsrc. reflexivity.
  - intros [r occ] Hin. unfold occ_pkg; cbn [fst].
    destruct (GoIndex.Snap.visit_file_view p fr r occ Hin) as [_ Hf]. rewrite Hf. reflexivity.
  - intros [r occ] Hin. cbn [fst snd]. exact (ppkg_as_decl_kind_count idx fr r occ Hin).
Qed.

Lemma pkg_declcount_app {p} (idx : GoIndex.Snap.SyntaxIndex p) (dir : string)
  (l1 l2 : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) :
  pkg_declcount idx dir (l1 ++ l2) = (pkg_declcount idx dir l1 + pkg_declcount idx dir l2)%nat.
Proof. induction l1 as [|ro l1 IH]; cbn [pkg_declcount app]; [reflexivity | rewrite IH; lia]. Qed.

(* the WHOLE-PROGRAM DMain count per package, over the retained visit stream, IS the declarative
   [pkg_main_count] (= [list_dir_count] over the file bindings). *)
Lemma pkg_declcount_prog_visit {p} (idx : GoIndex.Snap.SyntaxIndex p) (dir : string) :
  pkg_declcount idx dir (prog_visit p) = pkg_main_count dir (prog_files p).
Proof.
  rewrite prog_visit_flat_map. unfold pkg_main_count.
  assert (H : forall L, (forall b, In b L -> In b (GoAST.file_bindings (prog_files p))) ->
             pkg_declcount idx dir (flat_map (binding_visit p) L) = list_dir_count dir L).
  { induction L as [|b rest IHL]; intro Hsub; [reflexivity|].
    cbn [flat_map list_dir_count]. rewrite pkg_declcount_app.
    rewrite (pkg_declcount_binding idx b dir (Hsub b (or_introl eq_refl))).
    rewrite (IHL (fun b' Hb' => Hsub b' (or_intror Hb'))). reflexivity. }
  apply H; intros b Hb; exact Hb.
Qed.

(** BUCKET LENGTH EXACTNESS (from the ONE visit-stream fold): a present bucket's length is the package's
    declarative main count [pkg_main_count]. *)
Lemma prog_package_refs_bucket_len {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall dir l,
  PM.find dir (prog_package_refs idx) = Some l -> length l = pkg_main_count dir (prog_files p).
Proof.
  intros dir l Hfind.
  assert (Holen : olen (PM.find dir (prog_package_refs idx)) = pkg_main_count dir (prog_files p)).
  { unfold prog_package_refs, prog_package_refs_from_visit. rewrite (ppkg_olen_char idx (prog_visit p) (PM.empty _) dir).
    rewrite PMF.empty_o. cbn [olen]. rewrite Nat.add_0_r. exact (pkg_declcount_prog_visit idx dir). }
  rewrite Hfind in Holen. cbn [olen] in Holen. exact Holen.
Qed.

(* an occurrence CONTRIBUTES its package to the bucket map iff it mints a DeclRef OR is a file root. *)
Definition ppkg_contributes {p} (idx : GoIndex.Snap.SyntaxIndex p) (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) : Prop :=
  GoIndex.as_decl idx (fst ro) <> None \/ GoIndex.as_kind idx (fst ro) GoIndex.KFile <> None.

Lemma ppkg_step_some {p} (idx : GoIndex.Snap.SyntaxIndex p) (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)
  (acc : PM.t (list (GoIndex.DeclRef p))) (dir : string) :
  PM.find dir (ppkg_step idx ro acc) <> None
  <-> ((occ_pkg ro = dir /\ ppkg_contributes idx ro) \/ PM.find dir acc <> None).
Proof.
  unfold ppkg_step, ppkg_contributes.
  destruct (GoIndex.as_decl idx (fst ro)) as [dr|] eqn:Ed.
  - destruct (string_dec (occ_pkg ro) dir) as [He|Hne].
    + rewrite He, PMF.add_eq_o by reflexivity. split; [ intros _; left; split; [reflexivity | left; discriminate] | intros _; discriminate ].
    + rewrite PMF.add_neq_o by exact Hne. split.
      * intro H; right; exact H.
      * intros [[He _]|H]; [ exfalso; apply Hne; exact He | exact H ].
  - destruct (GoIndex.as_kind idx (fst ro) GoIndex.KFile) as [fnr|] eqn:Ef.
    + destruct (PM.find (occ_pkg ro) acc) as [l|] eqn:Efind.
      * split.
        -- intro H; right; exact H.
        -- intros [[He _]|H]; [ rewrite He in Efind; rewrite Efind; discriminate | exact H ].
      * destruct (string_dec (occ_pkg ro) dir) as [He|Hne].
        -- rewrite He, PMF.add_eq_o by reflexivity. split; [ intros _; left; split; [reflexivity | right; discriminate] | intros _; discriminate ].
        -- rewrite PMF.add_neq_o by exact Hne. split.
           ++ intro H; right; exact H.
           ++ intros [[He _]|H]; [ exfalso; apply Hne; exact He | exact H ].
    + split.
      * intro H; right; exact H.
      * intros [[_ [Hd|Hf]]|H]; [ exfalso; apply Hd; reflexivity | exfalso; apply Hf; reflexivity | exact H ].
Qed.

Lemma ppkg_find_some_iff {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall l acc dir,
  PM.find dir (fold_right (ppkg_step idx) acc l) <> None
  <-> ((exists ro, In ro l /\ occ_pkg ro = dir /\ ppkg_contributes idx ro) \/ PM.find dir acc <> None).
Proof.
  induction l as [|ro rest IH]; intros acc dir.
  - cbn [fold_right]. split; [ intro H; right; exact H | intros [[ro' [[] _]]|H]; exact H ].
  - cbn [fold_right]. rewrite (ppkg_step_some idx ro (fold_right (ppkg_step idx) acc rest) dir), (IH acc dir). split.
    + intros [Hstep|[[ro' [Hin' Hc']]|Hacc]].
      * left; exists ro; split; [left; reflexivity | exact Hstep].
      * left; exists ro'; split; [right; exact Hin' | exact Hc'].
      * right; exact Hacc.
    + intros [[ro' [[<-|Hin'] Hc']]|Hacc].
      * left; exact Hc'.
      * right; left; exists ro'; split; [exact Hin' | exact Hc'].
      * right; right; exact Hacc.
Qed.

(* the file ROOT is a [KFile] occurrence (so a file always contributes its package's presence). *)
Lemma root_node_kind {p} (idx : GoIndex.Snap.SyntaxIndex p) (fr : GoIndex.Snap.FileRef p) :
  GoIndex.Snap.node_kind idx (GoIndex.Snap.file_root_ref fr) = GoIndex.KFile.
Proof.
  rewrite (GoIndex.Snap.node_kind_matches_source p idx (GoIndex.Snap.file_root_ref fr)).
  pose proof (GoIndex.Snap.source_occ_of_ref_eq (GoIndex.Snap.file_root_ref fr)) as Hso.
  rewrite (GoIndex.Snap.file_root_ref_file p fr), (GoIndex.Snap.file_root_ref_local p fr) in Hso.
  assert (Hroot : In (GoIndex.root_id, GoIndex.mkOcc GoIndex.KFile (GoIndex.ViewFile (GoIndex.Snap.file_ref_source fr))
                        None GoIndex.RFileRoot (GoIndex.count_file (GoIndex.Snap.file_ref_source fr)))
                     (GoIndex.occs_file (GoIndex.Snap.file_ref_source fr))).
  { unfold GoIndex.occs_file. destruct (source_imports (GoIndex.Snap.file_ref_source fr)) as [|i tl]; [| destruct i].
    left; reflexivity. }
  apply GoIndex.occs_file_exact in Hroot. rewrite Hso in Hroot. injection Hroot as Heq. rewrite Heq. reflexivity.
Qed.

Lemma root_ref_contributes {p} (idx : GoIndex.Snap.SyntaxIndex p) (fr : GoIndex.Snap.FileRef p) :
  ppkg_contributes idx (GoIndex.Snap.file_root_ref fr, GoIndex.Snap.source_occurrence_of_ref (GoIndex.Snap.file_root_ref fr)).
Proof.
  right. cbn [fst]. unfold GoIndex.as_kind.
  destruct (GoIndex.syntaxkind_eq_dec (GoIndex.Snap.node_kind idx (GoIndex.Snap.file_root_ref fr)) GoIndex.KFile) as [He|Hne];
    [ discriminate | exfalso; apply Hne; apply root_node_kind ].
Qed.

(** DOMAIN EXACTNESS (from the ONE visit-stream fold): a bucket is present iff a file has that parent directory. *)
Lemma prog_package_refs_present {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall dir,
  PM.In dir (prog_package_refs idx) <-> list_dir_mem dir (GoAST.file_bindings (prog_files p)) = true.
Proof.
  intro dir. rewrite PMF.in_find_iff. unfold prog_package_refs, prog_package_refs_from_visit.
  rewrite (ppkg_find_some_iff idx (prog_visit p) (PM.empty _) dir). rewrite PMF.empty_o. split.
  - intros [[[r occ] [Hin [Hpkg _]]]|Hne]; [| exfalso; apply Hne; reflexivity].
    (* the occurrence's file is in prog_files with parent dir *)
    rewrite prog_visit_flat_map in Hin. apply in_flat_map in Hin. destruct Hin as [b [Hb Hrb]].
    unfold binding_visit in Hrb. destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|] eqn:Ef; [|destruct Hrb].
    destruct (GoIndex.Snap.visit_file_view p fr r occ Hrb) as [_ Hfile].
    unfold occ_pkg in Hpkg. cbn [fst] in Hpkg. rewrite Hfile, (GoIndex.Snap.file_of_path_sound p (fst b) fr Ef) in Hpkg.
    unfold list_dir_mem. apply existsb_exists. exists b. split; [exact Hb | apply String.eqb_eq; exact Hpkg].
  - intro Hmem. unfold list_dir_mem in Hmem. apply existsb_exists in Hmem. destruct Hmem as [b [Hb He]].
    apply String.eqb_eq in He.
    left. pose proof (GoAST.file_bindings_find (prog_files p) b Hb) as Hfind.
    destruct (GoIndex.Snap.file_of_path_source p (fst b) (snd b) Hfind) as [fr [Hfop [Hpath _]]].
    exists (GoIndex.Snap.file_root_ref fr, GoIndex.Snap.source_occurrence_of_ref (GoIndex.Snap.file_root_ref fr)).
    split; [ | split; [ | apply root_ref_contributes ] ].
    + apply noderef_in_prog_visit.
    + unfold occ_pkg. cbn [fst]. rewrite (GoIndex.Snap.file_root_ref_file p fr), Hpath. exact He.
Qed.

(** BELONGS: a main DeclRef in a package's bucket belongs to THAT package (its file's parent = the key). *)
Lemma ppkg_mem {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall l acc dir d,
  In d (match PM.find dir (fold_right (ppkg_step idx) acc l) with Some x => x | None => [] end) ->
  (exists ro, In ro l /\ occ_pkg ro = dir /\ GoIndex.as_decl idx (fst ro) = Some d)
  \/ In d (match PM.find dir acc with Some x => x | None => [] end).
Proof.
  induction l as [|ro rest IH]; intros acc dir d Hin; [right; exact Hin|].
  cbn [fold_right] in Hin. unfold ppkg_step at 1 in Hin.
  destruct (GoIndex.as_decl idx (fst ro)) as [dr|] eqn:Ed.
  - destruct (string_dec (occ_pkg ro) dir) as [He|Hne].
    + rewrite He, PMF.add_eq_o in Hin by reflexivity. destruct Hin as [<-|Hin].
      * left; exists ro; split; [left; reflexivity | split; [exact He | exact Ed]].
      * destruct (IH acc dir d Hin) as [[ro' [Hin' [Hp' Hd']]]|Hrest];
          [ left; exists ro'; split; [right; exact Hin' | split; [exact Hp'|exact Hd']] | right; exact Hrest ].
    + rewrite PMF.add_neq_o in Hin by exact Hne.
      destruct (IH acc dir d Hin) as [[ro' [Hin' [Hp' Hd']]]|Hrest];
        [ left; exists ro'; split; [right; exact Hin' | split; [exact Hp'|exact Hd']] | right; exact Hrest ].
  - assert (Hin' : In d (match PM.find dir (fold_right (ppkg_step idx) acc rest) with Some x => x | None => [] end)).
    { destruct (GoIndex.as_kind idx (fst ro) GoIndex.KFile) as [fnr|];
      [ destruct (PM.find (occ_pkg ro) (fold_right (ppkg_step idx) acc rest)) eqn:Efind;
        [ exact Hin | destruct (string_dec (occ_pkg ro) dir) as [He|Hne];
          [ rewrite He, PMF.add_eq_o in Hin by reflexivity; rewrite <- He, Efind; exact Hin
          | rewrite PMF.add_neq_o in Hin by exact Hne; exact Hin ] ]
      | exact Hin ]. }
    destruct (IH acc dir d Hin') as [[ro' [Hin2 [Hp' Hd']]]|Hrest];
      [ left; exists ro'; split; [right; exact Hin2 | split; [exact Hp'|exact Hd']] | right; exact Hrest ].
Qed.

Lemma prog_package_refs_belongs {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall dir l,
  PM.find dir (prog_package_refs idx) = Some l ->
  forall d, In d l ->
  fp_parent (GoIndex.Snap.file_ref_path (GoIndex.Snap.node_ref_file (GoIndex.erase_ref d))) = dir.
Proof.
  intros dir l Hfind d Hin.
  assert (Hb : In d (match PM.find dir (prog_package_refs idx) with Some x => x | None => [] end))
    by (rewrite Hfind; exact Hin).
  unfold prog_package_refs, prog_package_refs_from_visit in Hb.
  destruct (ppkg_mem idx (prog_visit p) (PM.empty _) dir d Hb) as [[ro [_ [Hp Hd]]]|Hempty];
    [ | rewrite PMF.empty_o in Hempty; destruct Hempty ].
  rewrite (GoIndex.erase_as_kind idx (fst ro) GoIndex.KTopLevelDecl d Hd). exact Hp.
Qed.

Lemma prog_package_refs_singleton_on_success {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  current_grammar_one_main p -> forall dir l,
  PM.find dir (prog_package_refs idx) = Some l -> exists d, l = [d].
Proof.
  intros Hall dir l Hfind.
  pose proof (prog_package_refs_bucket_len idx dir l Hfind) as Hlen.
  assert (Hmem : list_dir_mem dir (GoAST.file_bindings (prog_files p)) = true).
  { apply (prog_package_refs_present idx dir). apply PMF.in_find_iff. rewrite Hfind. discriminate. }
  assert (Hmt : PM.MapsTo dir (mkPkgSummary (pkg_main_count dir (prog_files p))) (package_summaries (prog_files p))).
  { apply PMF.find_mapsto_iff. rewrite package_summaries_find, Hmem. reflexivity. }
  pose proof (Hall dir _ Hmt) as Hone. cbn [ps_main_count] in Hone.
  rewrite Hone in Hlen. destruct l as [|d [|d2 rest]]; cbn [length] in Hlen; try discriminate. exists d; reflexivity.
Qed.

(* the PACKAGE diagnostics.  Every package with a main count other than one is a failure; the anchor
   is a validated [PackageRef] (each package in [package_summaries] is represented, so the reference is real).
   Emptiness is tied DIRECTLY to [source_spec_package_rules_b] (the package half of the decision).
   A package with zero mains is diagnosed [DRMissingMainEntry]; a package with more than one is diagnosed
   [DRMainRedeclared] over the collected main [DeclRef]s. *)

(* A non-conforming package is diagnosed with STRUCTURED reasons anchored in the exact snapshot:
   - n >= 2 mains -> n-1 [DRMainRedeclared], one per TAIL main [d2, d3, ...] each related to the FIRST canonical
     main [d1] ([later_primary] = the redundant tail main; [earlier_related] = the first main);
   - zero mains -> [DRMissingMainEntry] anchored at the validated [PackageRef].
   The canonical bucket order (FileMap-path then local NodeKey) makes the anchors deterministic; evidence is
   never overwritten (the bucket preserves every main, and every redundant main after the first is reported). *)
(** the RETAINED-bucket package classifier: decides a package PURELY from its bucket in the retained
    [prog_package_refs] map — a bucket [d1 :: rest] emits [map (DRMainRedeclared _ d1) rest] (n-1 diagnostics,
    each redundant tail main related to the first; empty for the conforming length-1 bucket); a length-0 bucket
    emits [DRMissingMainEntry] with the [PackageRef] built from the bucket's OWN domain membership
    ([bucket_key_present], NO [package_summaries] / [package_present_b] rescan).  [package_summaries] (the legacy
    FM.fold counter) is used ONLY to bridge the bucket lengths to [current_grammar_one_main]
    ([pkg_diags_empty_iff]), NEVER in the decision. *)
Lemma elements_all_mapsto {p} (m : PM.t (list (GoIndex.DeclRef p))) : forall kv,
  In kv (PM.elements m) -> PM.MapsTo (fst kv) (snd kv) m.
Proof.
  intros [dir l] Hin. apply PMF.elements_mapsto_iff, InA_alt.
  exists (dir, l). split; [ split; reflexivity | exact Hin ].
Qed.

Lemma mapsto_in_elements {p} (m : PM.t (list (GoIndex.DeclRef p))) : forall dir l,
  PM.MapsTo dir l m -> In (dir, l) (PM.elements m).
Proof.
  intros dir l Hmt. apply PMF.elements_mapsto_iff in Hmt. apply InA_alt in Hmt.
  destruct Hmt as [[dir' l'] [[Hk Hl] Hin]]. cbn in Hk, Hl. subst. exact Hin.
Qed.

Lemma bucket_key_present {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall dir l,
  PM.MapsTo dir l (prog_package_refs idx) -> package_present_b p dir = true.
Proof.
  intros dir l Hmt. unfold package_present_b.
  apply (proj1 (prog_package_refs_present idx dir)). exists l. exact Hmt.
Qed.

Definition pkg_diag_of_bucket {p} (m : PM.t (list (GoIndex.DeclRef p)))
    (Hpres : forall dir l, PM.MapsTo dir l m -> package_present_b p dir = true)
    (dir : string) (l : list (GoIndex.DeclRef p)) (Hmt : PM.MapsTo dir l m)
    : list (DiagnosticReason p) :=
  match l with
  | nil        => [ DRMissingMainEntry (mkPackageRef p dir (Hpres dir l Hmt)) ]
  | d1 :: rest => map (fun dk => DRMainRedeclared dk d1) rest
  end.

Lemma pkg_diag_of_bucket_nil_iff {p} (m : PM.t (list (GoIndex.DeclRef p))) Hpres dir l Hmt :
  @pkg_diag_of_bucket p m Hpres dir l Hmt = nil <-> length l = 1%nat.
Proof.
  unfold pkg_diag_of_bucket; destruct l as [|d1 [|d2 rest]]; cbn [map length];
    split; intro H; solve [ reflexivity | discriminate H ].
Qed.

Fixpoint bucket_diags_elems {p} (m : PM.t (list (GoIndex.DeclRef p)))
    (Hpres : forall dir l, PM.MapsTo dir l m -> package_present_b p dir = true)
    (es : list (string * list (GoIndex.DeclRef p)))
    (Hall : forall kv, In kv es -> PM.MapsTo (fst kv) (snd kv) m)
    : list (DiagnosticReason p) :=
  match es return (forall kv, In kv es -> PM.MapsTo (fst kv) (snd kv) m) -> list (DiagnosticReason p) with
  | [] => fun _ => []
  | kv :: rest => fun H =>
      pkg_diag_of_bucket m Hpres (fst kv) (snd kv) (H kv (or_introl eq_refl))
      ++ bucket_diags_elems m Hpres rest (fun kv' Hin => H kv' (or_intror Hin))
  end Hall.

Lemma bucket_diags_elems_nil_iff {p} (m : PM.t (list (GoIndex.DeclRef p))) Hpres es Hall :
  @bucket_diags_elems p m Hpres es Hall = nil <-> (forall kv, In kv es -> length (snd kv) = 1%nat).
Proof.
  revert Hall. induction es as [|kv rest IH]; intro Hall; cbn [bucket_diags_elems].
  - split; [ intros _ kv0 [] | reflexivity ].
  - split.
    + intro Hn. apply app_eq_nil in Hn. destruct Hn as [H1 H2]. intros kv0 [Heq | Hin].
      * subst kv0. exact (proj1 (pkg_diag_of_bucket_nil_iff m Hpres (fst kv) (snd kv) (Hall kv (or_introl eq_refl))) H1).
      * exact (proj1 (IH (fun kv' Hin' => Hall kv' (or_intror Hin'))) H2 kv0 Hin).
    + intro Hlen.
      assert (H1 : pkg_diag_of_bucket m Hpres (fst kv) (snd kv) (Hall kv (or_introl eq_refl)) = nil)
        by exact (proj2 (pkg_diag_of_bucket_nil_iff m Hpres (fst kv) (snd kv) (Hall kv (or_introl eq_refl))) (Hlen kv (or_introl eq_refl))).
      assert (H2 : bucket_diags_elems m Hpres rest (fun kv' Hin' => Hall kv' (or_intror Hin')) = nil)
        by exact (proj2 (IH (fun kv' Hin' => Hall kv' (or_intror Hin'))) (fun kv0 Hin0 => Hlen kv0 (or_intror Hin0))).
      rewrite H1, H2. reflexivity.
Qed.

Definition pkg_diags {p} (idx : GoIndex.Snap.SyntaxIndex p) : list (DiagnosticReason p) :=
  bucket_diags_elems (prog_package_refs idx) (bucket_key_present idx)
    (PM.elements (prog_package_refs idx)) (elements_all_mapsto (prog_package_refs idx)).

(** THE PACKAGE COMPLETENESS: no package diagnostic IFF every package has exactly one main.  The DECISION
    reads only the retained buckets (each bucket's LENGTH); [package_summaries] appears ONLY here, bridging
    the bucket lengths to the TWO FACTORED ROOTS [PackageDeclsUnique] / [MainPackagesHaveEntry]. *)

(** the PRODUCTION (retained-bucket) package decision reflects the two FACTORED roots DIRECTLY: a
    bucket of length ≤ 1 is exactly package-block uniqueness, a bucket of length ≥ 1 is exactly main-package
    entry; the diagnostic pass is empty iff BOTH hold, i.e. [PackageRulesValid].  This roots the elaborator's
    package acceptance in [PackageDeclsUnique] AND [MainPackagesHaveEntry] — NOT in the exactly-one consequence
    the exactly-one consequence [current_package_rules_exactly_one], which stays a downstream grammar coincidence. *)
Lemma pkg_diags_empty_iff_rules {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  pkg_diags idx = nil <-> PackageRulesValid p.
Proof.
  unfold pkg_diags. rewrite bucket_diags_elems_nil_iff.
  unfold PackageRulesValid, PackageDeclsUnique, MainPackagesHaveEntry. split.
  - intros Hbuck; split; intros dir s Hmt;
      (assert (Hpres : list_dir_mem dir (GoAST.file_bindings (prog_files p)) = true) by
         (pose proof (PM.find_1 Hmt) as Hf; rewrite package_summaries_find in Hf;
          destruct (list_dir_mem dir (GoAST.file_bindings (prog_files p))) eqn:E; [ reflexivity | discriminate Hf ]));
      destruct (proj2 (prog_package_refs_present idx dir) Hpres) as [l Hbmt];
      assert (Hlen : length l = 1%nat) by (apply (Hbuck (dir, l)); apply mapsto_in_elements; exact Hbmt);
      rewrite (package_summary_main_count (prog_files p) dir s Hmt);
      rewrite <- (prog_package_refs_bucket_len idx dir l (PM.find_1 Hbmt)); lia.
  - intros [Hle Hge] kv Hin.
    pose proof (elements_all_mapsto (prog_package_refs idx) kv Hin) as Hbmt.
    pose proof (bucket_key_present idx (fst kv) (snd kv) Hbmt) as Hpres.
    assert (Hms : PM.MapsTo (fst kv) (mkPkgSummary (pkg_main_count (fst kv) (prog_files p))) (package_summaries (prog_files p))).
    { apply PM.find_2. rewrite package_summaries_find. unfold package_present_b in Hpres. rewrite Hpres. reflexivity. }
    pose proof (Hle (fst kv) _ Hms) as Hle1. pose proof (Hge (fst kv) _ Hms) as Hge1.
    cbn [ps_main_count] in Hle1, Hge1.
    rewrite (prog_package_refs_bucket_len idx (fst kv) (snd kv) (PM.find_1 Hbmt)). lia.
Qed.

(** the same production decision, expressed against the SHARED package half [source_spec_package_rules_b] — the two are ONE
    judgment ([PackageRulesValid]), one retained-bucket view (production) and one [package_summaries] view
    (fixtures), each rooted DIRECTLY in the factored roots ([pkg_diags_empty_iff_rules] /
    [source_spec_package_rules_b_PackageRulesValid]); neither routes through the exactly-one consequence. *)
Lemma pkg_diags_empty_iff {p} (idx : GoIndex.Snap.SyntaxIndex p) : pkg_diags idx = nil <-> source_spec_package_rules_b p = true.
Proof. rewrite pkg_diags_empty_iff_rules, source_spec_package_rules_b_PackageRulesValid. reflexivity. Qed.

(** the PRODUCTION diagnostics capture EACH factored rule EXACTLY.  The retained bucket pass emits a
    [DRMainRedeclared] per redundant main (a bucket of length ≥ 2) and a [DRMissingMainEntry] per empty package
    (length 0).  So the REDECLARATION diagnostics are empty IFF [PackageDeclsUnique] and the MISSING-ENTRY
    diagnostics are empty IFF [MainPackagesHaveEntry] — each factored root reflected DIRECTLY by production. *)
Definition diag_is_redeclared {p} (d : DiagnosticReason p) : bool :=
  match d with DRMainRedeclared _ _ => true | _ => false end.
Definition diag_is_missing_entry {p} (d : DiagnosticReason p) : bool :=
  match d with DRMissingMainEntry _ => true | _ => false end.

Lemma filter_redecl_map {p} (d1 : GoIndex.DeclRef p) rest :
  filter diag_is_redeclared (map (fun dk => DRMainRedeclared dk d1) rest) = map (fun dk => DRMainRedeclared dk d1) rest.
Proof. induction rest as [|d2 rest' IH]; cbn [map filter diag_is_redeclared]; [ reflexivity | rewrite IH; reflexivity ]. Qed.

Lemma filter_missing_map {p} (d1 : GoIndex.DeclRef p) rest :
  filter diag_is_missing_entry (map (fun dk => DRMainRedeclared dk d1) rest) = nil.
Proof. induction rest as [|d2 rest' IH]; cbn [map filter diag_is_missing_entry]; [ reflexivity | exact IH ]. Qed.

Lemma redecl_of_bucket_nil_iff {p} m Hpres dir l Hmt :
  filter diag_is_redeclared (@pkg_diag_of_bucket p m Hpres dir l Hmt) = nil <-> (length l <= 1)%nat.
Proof.
  unfold pkg_diag_of_bucket. destruct l as [|d1 rest].
  - cbn [length filter diag_is_redeclared]. split; intros _; [ lia | reflexivity ].
  - rewrite filter_redecl_map. cbn [length]. destruct rest as [|d2 rest'].
    + cbn [map length]. split; intros _; [ lia | reflexivity ].
    + cbn [map length]. split; intro H; [ discriminate H | exfalso; lia ].
Qed.

Lemma missing_of_bucket_nil_iff {p} m Hpres dir l Hmt :
  filter diag_is_missing_entry (@pkg_diag_of_bucket p m Hpres dir l Hmt) = nil <-> (1 <= length l)%nat.
Proof.
  unfold pkg_diag_of_bucket. destruct l as [|d1 rest].
  - cbn [length filter diag_is_missing_entry]. split; intro H; [ discriminate H | exfalso; lia ].
  - rewrite filter_missing_map. cbn [length]. split; intros _; [ lia | reflexivity ].
Qed.

Lemma redecl_diags_elems_nil_iff {p} m Hpres es Hall :
  filter diag_is_redeclared (@bucket_diags_elems p m Hpres es Hall) = nil
    <-> (forall kv, In kv es -> (length (snd kv) <= 1)%nat).
Proof.
  revert Hall. induction es as [|kv rest IH]; intro Hall; cbn [bucket_diags_elems].
  - split; [ intros _ kv0 [] | reflexivity ].
  - rewrite filter_app. split.
    + intro Hn. apply app_eq_nil in Hn. destruct Hn as [H1 H2]. intros kv0 [Heq | Hin].
      * subst kv0. exact (proj1 (redecl_of_bucket_nil_iff m Hpres (fst kv) (snd kv) (Hall kv (or_introl eq_refl))) H1).
      * exact (proj1 (IH (fun kv' Hin' => Hall kv' (or_intror Hin'))) H2 kv0 Hin).
    + intro Hlen.
      assert (H1 : filter diag_is_redeclared (pkg_diag_of_bucket m Hpres (fst kv) (snd kv) (Hall kv (or_introl eq_refl))) = nil)
        by exact (proj2 (redecl_of_bucket_nil_iff m Hpres (fst kv) (snd kv) (Hall kv (or_introl eq_refl))) (Hlen kv (or_introl eq_refl))).
      assert (H2 : filter diag_is_redeclared (bucket_diags_elems m Hpres rest (fun kv' Hin' => Hall kv' (or_intror Hin'))) = nil)
        by exact (proj2 (IH (fun kv' Hin' => Hall kv' (or_intror Hin'))) (fun kv0 Hin0 => Hlen kv0 (or_intror Hin0))).
      rewrite H1, H2. reflexivity.
Qed.

Lemma missing_diags_elems_nil_iff {p} m Hpres es Hall :
  filter diag_is_missing_entry (@bucket_diags_elems p m Hpres es Hall) = nil
    <-> (forall kv, In kv es -> (1 <= length (snd kv))%nat).
Proof.
  revert Hall. induction es as [|kv rest IH]; intro Hall; cbn [bucket_diags_elems].
  - split; [ intros _ kv0 [] | reflexivity ].
  - rewrite filter_app. split.
    + intro Hn. apply app_eq_nil in Hn. destruct Hn as [H1 H2]. intros kv0 [Heq | Hin].
      * subst kv0. exact (proj1 (missing_of_bucket_nil_iff m Hpres (fst kv) (snd kv) (Hall kv (or_introl eq_refl))) H1).
      * exact (proj1 (IH (fun kv' Hin' => Hall kv' (or_intror Hin'))) H2 kv0 Hin).
    + intro Hlen.
      assert (H1 : filter diag_is_missing_entry (pkg_diag_of_bucket m Hpres (fst kv) (snd kv) (Hall kv (or_introl eq_refl))) = nil)
        by exact (proj2 (missing_of_bucket_nil_iff m Hpres (fst kv) (snd kv) (Hall kv (or_introl eq_refl))) (Hlen kv (or_introl eq_refl))).
      assert (H2 : filter diag_is_missing_entry (bucket_diags_elems m Hpres rest (fun kv' Hin' => Hall kv' (or_intror Hin'))) = nil)
        by exact (proj2 (IH (fun kv' Hin' => Hall kv' (or_intror Hin'))) (fun kv0 Hin0 => Hlen kv0 (or_intror Hin0))).
      rewrite H1, H2. reflexivity.
Qed.

(** redeclaration diagnostics empty IFF [PackageDeclsUnique] (every package has AT MOST one main). *)
Lemma redecl_diags_empty_iff_rules {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  filter diag_is_redeclared (pkg_diags idx) = nil <-> PackageDeclsUnique p.
Proof.
  unfold pkg_diags. rewrite redecl_diags_elems_nil_iff. unfold PackageDeclsUnique. split.
  - intros Hbuck dir s Hmt.
    assert (Hpres : list_dir_mem dir (GoAST.file_bindings (prog_files p)) = true) by
      (pose proof (PM.find_1 Hmt) as Hf; rewrite package_summaries_find in Hf;
       destruct (list_dir_mem dir (GoAST.file_bindings (prog_files p))) eqn:E; [ reflexivity | discriminate Hf ]).
    destruct (proj2 (prog_package_refs_present idx dir) Hpres) as [l Hbmt].
    assert (Hlen : (length l <= 1)%nat) by (apply (Hbuck (dir, l)); apply mapsto_in_elements; exact Hbmt).
    rewrite (package_summary_main_count (prog_files p) dir s Hmt).
    rewrite <- (prog_package_refs_bucket_len idx dir l (PM.find_1 Hbmt)); lia.
  - intros Hle kv Hin.
    pose proof (elements_all_mapsto (prog_package_refs idx) kv Hin) as Hbmt.
    pose proof (bucket_key_present idx (fst kv) (snd kv) Hbmt) as Hpres.
    assert (Hms : PM.MapsTo (fst kv) (mkPkgSummary (pkg_main_count (fst kv) (prog_files p))) (package_summaries (prog_files p))).
    { apply PM.find_2. rewrite package_summaries_find. unfold package_present_b in Hpres. rewrite Hpres. reflexivity. }
    pose proof (Hle (fst kv) _ Hms) as Hle1. cbn [ps_main_count] in Hle1.
    rewrite (prog_package_refs_bucket_len idx (fst kv) (snd kv) (PM.find_1 Hbmt)). lia.
Qed.

(** missing-entry diagnostics empty IFF [MainPackagesHaveEntry] (every package has AT LEAST one main). *)
Lemma missing_diags_empty_iff_rules {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  filter diag_is_missing_entry (pkg_diags idx) = nil <-> MainPackagesHaveEntry p.
Proof.
  unfold pkg_diags. rewrite missing_diags_elems_nil_iff. unfold MainPackagesHaveEntry. split.
  - intros Hbuck dir s Hmt.
    assert (Hpres : list_dir_mem dir (GoAST.file_bindings (prog_files p)) = true) by
      (pose proof (PM.find_1 Hmt) as Hf; rewrite package_summaries_find in Hf;
       destruct (list_dir_mem dir (GoAST.file_bindings (prog_files p))) eqn:E; [ reflexivity | discriminate Hf ]).
    destruct (proj2 (prog_package_refs_present idx dir) Hpres) as [l Hbmt].
    assert (Hlen : (1 <= length l)%nat) by (apply (Hbuck (dir, l)); apply mapsto_in_elements; exact Hbmt).
    rewrite (package_summary_main_count (prog_files p) dir s Hmt).
    rewrite <- (prog_package_refs_bucket_len idx dir l (PM.find_1 Hbmt)); lia.
  - intros Hge kv Hin.
    pose proof (elements_all_mapsto (prog_package_refs idx) kv Hin) as Hbmt.
    pose proof (bucket_key_present idx (fst kv) (snd kv) Hbmt) as Hpres.
    assert (Hms : PM.MapsTo (fst kv) (mkPkgSummary (pkg_main_count (fst kv) (prog_files p))) (package_summaries (prog_files p))).
    { apply PM.find_2. rewrite package_summaries_find. unfold package_present_b in Hpres. rewrite Hpres. reflexivity. }
    pose proof (Hge (fst kv) _ Hms) as Hge1. cbn [ps_main_count] in Hge1.
    rewrite (prog_package_refs_bucket_len idx (fst kv) (snd kv) (PM.find_1 Hbmt)). lia.
Qed.

(* the ONE retained indexed-elaboration root.  [elaborate] builds ONE [IndexedProgram] and returns
   either exact facts (on success) or a NONEMPTY structured diagnostic list (on failure).  Production
   elaboration DECIDES from those RETAINED diagnostics; their emptiness coincides (proved) with the decidable
   SPECIFICATION predicate [semantic_ok_b] (= [SourceProgramValid], the SOURCE-semantic half of GoCompile
   acceptance; the fresh-build preflight is a separate condition [GoCompile] adds on top).
   [semantic_diagnostics] gives the structured failure payload, nonempty exactly when the decision fails. *)

Lemma app_nil_iff {A} (l1 l2 : list A) : l1 ++ l2 = nil <-> l1 = nil /\ l2 = nil.
Proof. split; [ apply app_eq_nil | intros [-> ->]; reflexivity ]. Qed.

(* DIAGNOSTIC STORAGE AND CANONICAL ORDER.  Node-primary diagnostics (invalid-conversion, defaulting,
   duplicate-main — each anchored at an occurrence NodeKey) are accumulated into a STANDARD [NodeKeyMapBase]
   whose bucket value is a code-ordered list (normally a singleton, but a bucket prevents a future map overwrite
   from erasing multiple diagnostics at one occurrence).  The final report flattens the map's CANONICAL elements
   (path then local id) with code-ordered bucket values, THEN appends the package-primary (missing-main)
   diagnostics in PackageMap key order.  So a duplicate-main at `a/q.go:3` correctly precedes an
   invalid-conversion at `z/main.go:5` even though the latter is discovered first. *)

(* NO project-authored sorting algorithm: a node-primary diagnostic is prepended to its occurrence's
   bucket.  Every occurrence emits AT MOST ONE node-primary diagnostic, so the bucket is a singleton and no
   within-bucket ordering is required (`bucket_singleton` below proves it); the canonical order is entirely the
   NodeKeyMap's key-sorted `elements` ([bucket_flatten_key_sorted]). *)
Definition nkm_find {X} (k : GoIndex.NodeKey) (m : GoIndex.NodeKeyMapBase.t (list X)) : list X :=
  match GoIndex.NodeKeyMapBase.find k m with Some l => l | None => [] end.

Definition bucket_add {X} (kx : GoIndex.NodeKey * X)
    (m : GoIndex.NodeKeyMapBase.t (list X)) : GoIndex.NodeKeyMapBase.t (list X) :=
  GoIndex.NodeKeyMapBase.add (fst kx) (snd kx :: nkm_find (fst kx) m) m.

(* flatten node-keyed values into the NodeKeyMap-canonical order (path/local id). *)
Definition bucket_flatten {X} (kxs : list (GoIndex.NodeKey * X)) : list X :=
  flat_map snd (GoIndex.NodeKeyMapBase.elements
    (fold_right bucket_add (GoIndex.NodeKeyMapBase.empty (list X)) kxs)).

(* if some key maps to a nonempty bucket, the whole flatten is nonempty (that bucket's elements are included). *)
Lemma nkm_find_flat_nonempty {X} (m : GoIndex.NodeKeyMapBase.t (list X)) (k : GoIndex.NodeKey) (b : list X) :
  GoIndex.NodeKeyMapBase.find k m = Some b -> b <> nil ->
  flat_map snd (GoIndex.NodeKeyMapBase.elements m) <> nil.
Proof.
  intros Hf Hb.
  apply GoIndex.NodeKeyMapFacts.find_mapsto_iff, GoIndex.NodeKeyMapFacts.elements_mapsto_iff, InA_alt in Hf.
  destruct Hf as [[k' b'] [[Hk Hb'] Hin]]. cbn in Hk, Hb'.
  intro Hnil. apply Hb. rewrite Hb'.
  assert (Hin2 : In b' (map snd (GoIndex.NodeKeyMapBase.elements m)))
    by (apply in_map_iff; exists (k', b'); split; [reflexivity | exact Hin]).
  clear -Hnil Hin2. revert Hnil Hin2. generalize (GoIndex.NodeKeyMapBase.elements m) as els.
  induction els as [|e els IH]; cbn [flat_map map]; [intros _ []|].
  intros Hnil Hin2. apply app_eq_nil in Hnil. destruct Hnil as [He Htl].
  destruct Hin2 as [<-|Hin2]; [exact He | apply IH; assumption].
Qed.

(* a nonempty keyed list flattens to a nonempty report: its first key holds a nonempty bucket. *)
Lemma bucket_flatten_cons_nonempty {X} (kx : GoIndex.NodeKey * X) (rest : list (GoIndex.NodeKey * X)) :
  bucket_flatten (kx :: rest) <> nil.
Proof.
  unfold bucket_flatten. cbn [fold_right]. unfold bucket_add at 1.
  set (m := fold_right bucket_add (GoIndex.NodeKeyMapBase.empty (list X)) rest).
  apply (nkm_find_flat_nonempty _ (fst kx) (snd kx :: nkm_find (fst kx) m)).
  - apply nodekeymap_add_eq.
  - discriminate.
Qed.

Lemma bucket_flatten_nil_iff {X} (kxs : list (GoIndex.NodeKey * X)) :
  bucket_flatten kxs = nil <-> kxs = nil.
Proof.
  split; [ | intros ->; reflexivity ].
  destruct kxs as [|kx rest]; [reflexivity|].
  intro H. exfalso. exact (bucket_flatten_cons_nonempty kx rest H).
Qed.

(* the node-primary key of a diagnostic (Some for the three node-anchored reasons; None for missing-main). *)
Definition diag_node_key {p} (d : DiagnosticReason p) : option GoIndex.NodeKey :=
  match diagnostic_primary d with AtNode r => Some (GoIndex.Snap.node_ref_key r) | _ => None end.
Definition node_keyed {p} (l : list (DiagnosticReason p)) : list (GoIndex.NodeKey * DiagnosticReason p) :=
  flat_map (fun d => match diag_node_key d with Some k => [(k, d)] | None => [] end) l.
Definition pkg_primary {p} (l : list (DiagnosticReason p)) : list (DiagnosticReason p) :=
  flat_map (fun d => match diag_node_key d with Some _ => [] | None => [d] end) l.

Definition semantic_diagnostics (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p) : list (DiagnosticReason p) :=
  bucket_flatten (node_keyed (expr_diags idx ++ pkg_diags idx))
  ++ pkg_primary (expr_diags idx ++ pkg_diags idx).

(* node_keyed and pkg_primary partition the diagnostics, so both empty iff the whole list is empty. *)
Lemma node_pkg_partition_nil {p} (l : list (DiagnosticReason p)) :
  node_keyed l = nil /\ pkg_primary l = nil <-> l = nil.
Proof.
  split; [ | intros ->; split; reflexivity ].
  destruct l as [|d rest]; [reflexivity|]. unfold node_keyed, pkg_primary; cbn [flat_map].
  destruct (diag_node_key d) as [k|]; cbn [app]; intros [H1 H2]; discriminate.
Qed.

Lemma semantic_diagnostics_empty_iff (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p) :
  semantic_diagnostics p idx = nil <-> semantic_ok_b p = true.
Proof.
  unfold semantic_diagnostics. rewrite app_nil_iff, bucket_flatten_nil_iff, node_pkg_partition_nil, app_nil_iff.
  rewrite expr_diags_empty_iff, pkg_diags_empty_iff.
  unfold semantic_ok_b. rewrite Bool.andb_true_iff, expr_all_ok_program_typedb. reflexivity.
Qed.

Lemma semantic_diagnostics_nonempty (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p) :
  semantic_ok_b p = false -> semantic_diagnostics p idx <> nil.
Proof.
  intros H Hc. apply (semantic_diagnostics_empty_iff p idx) in Hc. rewrite Hc in H. discriminate H.
Qed.

(* ---- the node-bucketing COMMUTES WITH a value transform, so the ERASED report is the erased source
   diagnostics run through the SAME bucketing.  This makes the erased report a source function (deterministic,
   vm-computable), and it is the bridge for the exact fixtures. ---- *)

Lemma nodekey_sorted_map_fst {A B} (f : A -> B) : forall l,
  Sorted (@GoIndex.NodeKeyMapBase.lt_key A) l ->
  Sorted (@GoIndex.NodeKeyMapBase.lt_key B) (map (fun kv => (fst kv, f (snd kv))) l).
Proof.
  induction l as [|a l IH]; intro Hs; cbn [map]; [constructor|].
  apply Sorted_inv in Hs. destruct Hs as [Hs Hhd]. constructor; [apply IH; exact Hs|].
  destruct l as [|b l']; cbn [map]; [constructor|]. apply HdRel_inv in Hhd. constructor. exact Hhd.
Qed.

Lemma nodekeymap_map_elements {A B} (f : A -> B) (m : GoIndex.NodeKeyMapBase.t A) :
  GoIndex.NodeKeyMapBase.elements (GoIndex.NodeKeyMapBase.map f m)
  = map (fun kv => (fst kv, f (snd kv))) (GoIndex.NodeKeyMapBase.elements m).
Proof.
  apply GoIndex.nodekey_eqlistA_eqke_eq.
  apply GoIndex.NodeKeyMapOrd.sort_equivlistA_eqlistA;
    [ apply GoIndex.NodeKeyMapBase.elements_3
    | apply nodekey_sorted_map_fst, GoIndex.NodeKeyMapBase.elements_3 | ].
  intros [k e].
  rewrite <- GoIndex.NodeKeyMapFacts.elements_mapsto_iff, GoIndex.NodeKeyMapFacts.map_mapsto_iff, InA_alt.
  split.
  - intros [a [He Hmt]]. subst e.
    apply GoIndex.NodeKeyMapFacts.elements_mapsto_iff in Hmt. rewrite InA_alt in Hmt.
    destruct Hmt as [[k' a'] [[Hk Ha] Hin]]. cbn in Hk, Ha. unfold GoIndex.NodeKey_OT.eq in Hk. subst k' a'.
    exists (k, f a). split; [ split; reflexivity | ].
    apply in_map_iff. exists (k, a). split; [reflexivity | exact Hin].
  - intros [[k' e'] [[Hk He] Hin]]. cbn in Hk, He. unfold GoIndex.NodeKey_OT.eq in Hk. subst k' e'.
    apply in_map_iff in Hin. destruct Hin as [[k'' a] [Heq Hin]]. injection Heq as Hk2 He2. subst k'' e.
    exists a. split; [reflexivity | ].
    apply GoIndex.NodeKeyMapFacts.elements_mapsto_iff. rewrite InA_alt. exists (k, a).
    split; [ split; reflexivity | exact Hin ].
Qed.

Lemma nkmap_map_add {A B} (h : A -> B) (k : GoIndex.NodeKey) (v : A) (m : GoIndex.NodeKeyMapBase.t A) :
  GoIndex.NodeKeyMapBase.Equal (GoIndex.NodeKeyMapBase.map h (GoIndex.NodeKeyMapBase.add k v m))
                               (GoIndex.NodeKeyMapBase.add k (h v) (GoIndex.NodeKeyMapBase.map h m)).
Proof.
  intro k'. rewrite GoIndex.NodeKeyMapFacts.map_o.
  destruct (GoIndex.NodeKey_OT.eq_dec k k') as [Heq|Hne].
  - rewrite !GoIndex.NodeKeyMapFacts.add_eq_o by exact Heq. reflexivity.
  - rewrite !GoIndex.NodeKeyMapFacts.add_neq_o by exact Hne. rewrite GoIndex.NodeKeyMapFacts.map_o. reflexivity.
Qed.

Lemma bucket_fold_map {X Y} (g : X -> Y) (kxs : list (GoIndex.NodeKey * X)) :
  GoIndex.NodeKeyMapBase.Equal
    (GoIndex.NodeKeyMapBase.map (map g) (fold_right bucket_add (GoIndex.NodeKeyMapBase.empty (list X)) kxs))
    (fold_right bucket_add (GoIndex.NodeKeyMapBase.empty (list Y)) (map (fun kx => (fst kx, g (snd kx))) kxs)).
Proof.
  induction kxs as [|kx rest IH]; cbn [fold_right map].
  - intro k. rewrite GoIndex.NodeKeyMapFacts.map_o, !GoIndex.NodeKeyMapFacts.empty_o. reflexivity.
  - unfold bucket_add at 1 3. cbn [fst snd].
    set (M := fold_right bucket_add (GoIndex.NodeKeyMapBase.empty (list X)) rest) in *.
    set (M' := fold_right bucket_add (GoIndex.NodeKeyMapBase.empty (list Y))
                          (map (fun kx0 => (fst kx0, g (snd kx0))) rest)) in *.
    assert (Hfind : nkm_find (fst kx) M' = map g (nkm_find (fst kx) M)).
    { unfold nkm_find. rewrite <- (IH (fst kx)), GoIndex.NodeKeyMapFacts.map_o.
      destruct (GoIndex.NodeKeyMapBase.find (fst kx) M); reflexivity. }
    rewrite Hfind.
    transitivity (GoIndex.NodeKeyMapBase.add (fst kx)
                    (map g (snd kx :: nkm_find (fst kx) M)) (GoIndex.NodeKeyMapBase.map (map g) M)).
    + apply nkmap_map_add.
    + apply GoIndex.NodeKeyMapFacts.add_m; [reflexivity | reflexivity | exact IH].
Qed.

Lemma bucket_flatten_map {X Y} (g : X -> Y) (kxs : list (GoIndex.NodeKey * X)) :
  map g (bucket_flatten kxs) = bucket_flatten (map (fun kx => (fst kx, g (snd kx))) kxs).
Proof.
  unfold bucket_flatten.
  rewrite <- (GoIndex.nodekeymap_elements_Equal _ _ (bucket_fold_map g kxs)).
  rewrite nodekeymap_map_elements.
  generalize (GoIndex.NodeKeyMapBase.elements (fold_right bucket_add (GoIndex.NodeKeyMapBase.empty (list X)) kxs)) as l.
  induction l as [|[k b] l IH]; cbn [flat_map map]; [reflexivity|].
  rewrite map_app, IH. reflexivity.
Qed.

(* ---- MEMBERSHIP: the bucketing preserves the multiset of values (a reordering), so the report has EXACTLY the
   diagnostics of [expr_diags ++ pkg_diags] (needed for the order-independent legacy-class projection). ---- *)

Lemma flat_map_snd_mapsto {X} (m : GoIndex.NodeKeyMapBase.t (list X)) (d : X) :
  In d (flat_map snd (GoIndex.NodeKeyMapBase.elements m)) <->
  exists k b, GoIndex.NodeKeyMapBase.MapsTo k b m /\ In d b.
Proof.
  rewrite in_flat_map. split.
  - intros [[k b] [Hin Hd]]. cbn in Hd. exists k, b. split; [|exact Hd].
    apply GoIndex.NodeKeyMapFacts.elements_mapsto_iff, InA_alt. exists (k, b). split; [split; reflexivity | exact Hin].
  - intros [k [b [Hmt Hd]]].
    apply GoIndex.NodeKeyMapFacts.elements_mapsto_iff, InA_alt in Hmt.
    destruct Hmt as [[k' b'] [[Hk Hb] Hin]]. cbn in Hk, Hb.
    exists (k', b'). split; [exact Hin | cbn; rewrite <- Hb; exact Hd].
Qed.

Lemma flat_map_snd_add {X} (m : GoIndex.NodeKeyMapBase.t (list X)) (k : GoIndex.NodeKey) (v : list X) (d : X) :
  In d (flat_map snd (GoIndex.NodeKeyMapBase.elements (GoIndex.NodeKeyMapBase.add k v m))) <->
  In d v \/ In d (flat_map snd (GoIndex.NodeKeyMapBase.elements (GoIndex.NodeKeyMapBase.remove k m))).
Proof.
  rewrite !flat_map_snd_mapsto. split.
  - intros [k' [b [Hmt Hd]]]. apply GoIndex.NodeKeyMapFacts.add_mapsto_iff in Hmt.
    destruct Hmt as [[Hk Hb]|[Hk Hmt]].
    + subst b. left; exact Hd.
    + right. exists k', b. split; [ apply GoIndex.NodeKeyMapFacts.remove_mapsto_iff; split; [exact Hk|exact Hmt] | exact Hd ].
  - intros [Hd | [k' [b [Hmt Hd]]]].
    + exists k, v. split; [ apply GoIndex.NodeKeyMapFacts.add_mapsto_iff; left; split; reflexivity | exact Hd ].
    + apply GoIndex.NodeKeyMapFacts.remove_mapsto_iff in Hmt. destruct Hmt as [Hk Hmt].
      exists k', b. split; [ apply GoIndex.NodeKeyMapFacts.add_mapsto_iff; right; split; [exact Hk | exact Hmt] | exact Hd ].
Qed.

Lemma flat_map_snd_find {X} (m : GoIndex.NodeKeyMapBase.t (list X)) (k : GoIndex.NodeKey) (d : X) :
  In d (flat_map snd (GoIndex.NodeKeyMapBase.elements m)) <->
  In d (nkm_find k m) \/ In d (flat_map snd (GoIndex.NodeKeyMapBase.elements (GoIndex.NodeKeyMapBase.remove k m))).
Proof.
  rewrite !flat_map_snd_mapsto. unfold nkm_find. split.
  - intros [k' [b [Hmt Hd]]]. destruct (GoIndex.NodeKey_OT.eq_dec k k') as [Hk|Hk].
    + left. apply GoIndex.NodeKeyMapFacts.find_mapsto_iff in Hmt.
      rewrite (GoIndex.NodeKeyMapFacts.find_o m Hk), Hmt. exact Hd.
    + right. exists k', b. split; [ apply GoIndex.NodeKeyMapFacts.remove_mapsto_iff; split; [exact Hk | exact Hmt] | exact Hd ].
  - intros [Hd | [k' [b [Hmt Hd]]]].
    + destruct (GoIndex.NodeKeyMapBase.find k m) as [b0|] eqn:Ef; [ | destruct Hd ].
      exists k, b0. split; [ apply GoIndex.NodeKeyMapFacts.find_mapsto_iff; exact Ef | exact Hd ].
    + apply GoIndex.NodeKeyMapFacts.remove_mapsto_iff in Hmt. destruct Hmt as [Hk Hmt].
      exists k', b. split; [exact Hmt | exact Hd].
Qed.

Lemma bucket_flatten_In {X} (kxs : list (GoIndex.NodeKey * X)) (d : X) :
  In d (bucket_flatten kxs) <-> In d (map snd kxs).
Proof.
  unfold bucket_flatten. induction kxs as [|kx rest IH]; cbn [fold_right map].
  - rewrite flat_map_snd_mapsto. split; [ intros [k [b [Hmt _]]]; revert Hmt; apply GoIndex.NodeKeyMapFacts.empty_mapsto_iff | intros [] ].
  - unfold bucket_add at 1.
    set (M := fold_right bucket_add (GoIndex.NodeKeyMapBase.empty (list X)) rest) in *.
    rewrite flat_map_snd_add. cbn [In].
    rewrite or_assoc, <- (flat_map_snd_find M (fst kx) d), IH. tauto.
Qed.

Lemma existsb_In_eq {A} (f : A -> bool) (l1 l2 : list A) :
  (forall x, In x l1 <-> In x l2) -> existsb f l1 = existsb f l2.
Proof.
  intro H. destruct (existsb f l1) eqn:E1; destruct (existsb f l2) eqn:E2; try reflexivity.
  - apply existsb_exists in E1. destruct E1 as [x [Hin Hf]].
    assert (Hc : existsb f l2 = true) by (apply existsb_exists; exists x; split; [apply H; exact Hin | exact Hf]).
    rewrite Hc in E2; discriminate.
  - apply existsb_exists in E2. destruct E2 as [x [Hin Hf]].
    assert (Hc : existsb f l1 = true) by (apply existsb_exists; exists x; split; [apply H; exact Hin | exact Hf]).
    rewrite Hc in E1; discriminate.
Qed.

Lemma node_pkg_In {p} (l : list (DiagnosticReason p)) (d : DiagnosticReason p) :
  In d (map snd (node_keyed l)) \/ In d (pkg_primary l) <-> In d l.
Proof.
  induction l as [|d0 rest IH]; [cbn; tauto|].
  replace (node_keyed (d0 :: rest))
    with ((match diag_node_key d0 with Some k => [(k, d0)] | None => nil end) ++ node_keyed rest) by reflexivity.
  replace (pkg_primary (d0 :: rest))
    with ((match diag_node_key d0 with Some _ => nil | None => [d0] end) ++ pkg_primary rest) by reflexivity.
  rewrite map_app, !in_app_iff. cbn [In]. destruct (diag_node_key d0) as [k|]; cbn [map In]; rewrite <- IH; tauto.
Qed.

Lemma collect_diagnostics_In {p} (idx : GoIndex.Snap.SyntaxIndex p) (d : DiagnosticReason p) :
  In d (semantic_diagnostics p idx) <-> In d (expr_diags idx ++ pkg_diags idx).
Proof.
  unfold semantic_diagnostics. rewrite in_app_iff, bucket_flatten_In. apply node_pkg_In.
Qed.

(** the UNIVERSAL STRICT CANONICAL-ORDER theorem (below, [semantic_diagnostics_node_strict]): the
   node-primary diagnostics appear in STRICTLY ascending NodeKey order (path then local id).  The input keys
   are UNIQUE ([collect_node_input_nodup]) so every bucket is a SINGLETON ([collect_node_buckets_singleton]);
   there are no within-bucket ties, and the order is entirely the NodeKeyMap's key-sorted [elements]. *)
Lemma node_keyed_self {p} (l : list (DiagnosticReason p)) :
  forall kd, In kd (node_keyed l) -> diag_node_key (snd kd) = Some (fst kd).
Proof.
  intros kd Hin. unfold node_keyed in Hin. apply in_flat_map in Hin. destruct Hin as [d [_ Hin]].
  destruct (diag_node_key d) as [k|] eqn:E; cbn [In] in Hin.
  - destruct Hin as [Heq|[]]. subst kd. cbn [fst snd]. exact E.
  - destruct Hin.
Qed.

(* the KEY list of a diagnostic list (the node-primary keys, in order). *)
Definition node_keys {p} (l : list (DiagnosticReason p)) : list GoIndex.NodeKey :=
  flat_map (fun d => match diag_node_key d with Some k => [k] | None => [] end) l.

Lemma node_keys_eq {p} (l : list (DiagnosticReason p)) : map fst (node_keyed l) = node_keys l.
Proof.
  induction l as [|d l IH]; [reflexivity|].
  replace (node_keyed (d :: l))
    with ((match diag_node_key d with Some k => [(k, d)] | None => nil end) ++ node_keyed l) by reflexivity.
  replace (node_keys (d :: l))
    with ((match diag_node_key d with Some k => [k] | None => nil end) ++ node_keys l) by reflexivity.
  rewrite map_app, IH. f_equal. destruct (diag_node_key d); reflexivity.
Qed.

Lemma node_keys_app {p} (l1 l2 : list (DiagnosticReason p)) : node_keys (l1 ++ l2) = node_keys l1 ++ node_keys l2.
Proof. unfold node_keys. rewrite flat_map_app. reflexivity. Qed.

(* GENERIC: if each source element produces at most one keyed value all carrying that element's (distinct) key,
   the produced key list is NoDup. *)
Lemma flat_map_le1_key_nodup {A} (key : A -> GoIndex.NodeKey) (f : A -> list GoIndex.NodeKey) (L : list A) :
  NoDup (map key L) ->
  (forall a, (length (f a) <= 1)%nat) ->
  (forall a b, In b (f a) -> b = key a) ->
  NoDup (flat_map f L).
Proof.
  intros Hnd Hf1 Hkey. induction L as [|a L IH]; [constructor|].
  cbn [map] in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd].
  cbn [flat_map]. destruct (f a) as [|b [|b' rest]] eqn:Ef.
  - cbn [app]. apply IH; assumption.
  - cbn [app]. constructor.
    + rewrite (Hkey a b) by (rewrite Ef; left; reflexivity). intro Hin. apply Hnotin.
      apply in_flat_map in Hin. destruct Hin as [a0 [Ha0 Hb0]].
      rewrite (Hkey a0 _ Hb0). apply in_map. exact Ha0.
    + apply IH; assumption.
  - exfalso. pose proof (Hf1 a) as Hle. rewrite Ef in Hle. cbn [length] in Hle. lia.
Qed.

Lemma occ_expr_diags_le1 {p} (idx : GoIndex.Snap.SyntaxIndex p) outer ro :
  (length (occ_expr_diags idx outer ro) <= 1)%nat.
Proof.
  unfold occ_expr_diags. destruct (GoIndex.as_expr idx (fst ro)) as [er|]; [|cbn; lia].
  destruct (GoIndex.view_expr (snd ro)); [|cbn; lia].
  destruct (local_conv_failure g) as [[t ci]|];
    [ destruct (conversion_target_ref idx er); [destruct (conversion_operand_ref idx er)|]; cbn; lia |].
  destruct (arg_default_failure (snd ro) g) as [[c dt]|]; cbn; lia.
Qed.

Lemma occ_expr_diags_key {p} (idx : GoIndex.Snap.SyntaxIndex p) outer ro :
  forall d, In d (occ_expr_diags idx outer ro) -> diag_node_key d = Some (GoIndex.Snap.node_ref_key (fst ro)).
Proof.
  intros d Hin. unfold occ_expr_diags in Hin.
  destruct (GoIndex.as_expr idx (fst ro)) as [er|] eqn:Ea; [|destruct Hin].
  assert (Her : GoIndex.erase_ref er = fst ro) by exact (GoIndex.erase_as_kind idx (fst ro) GoIndex.KExpression er Ea).
  destruct (GoIndex.view_expr (snd ro)) as [e|]; [|destruct Hin].
  destruct (local_conv_failure e) as [[t ci]|].
  - destruct (conversion_target_ref idx er) as [tr|]; [|destruct Hin].
    destruct (conversion_operand_ref idx er) as [opr|]; [|destruct Hin].
    cbn [In] in Hin. destruct Hin as [<-|[]]. cbn [diag_node_key diagnostic_primary]. rewrite Her. reflexivity.
  - destruct (arg_default_failure (snd ro) e) as [[c dt]|]; [|destruct Hin].
    cbn [In] in Hin. destruct Hin as [<-|[]]. cbn [diag_node_key diagnostic_primary]. rewrite Her. reflexivity.
Qed.

Lemma flat_map_flat_map {A B C} (g : B -> list C) (h : A -> list B) (L : list A) :
  flat_map g (flat_map h L) = flat_map (fun x => flat_map g (h x)) L.
Proof. induction L as [|a L IH]; [reflexivity|]. cbn [flat_map]. rewrite flat_map_app, IH. reflexivity. Qed.

(* the per-occurrence keys of one occurrence's diagnostics: at most one, and it is the occurrence's key. *)
Lemma occ_node_keys_le1 {p} (idx : GoIndex.Snap.SyntaxIndex p) outer ro :
  (length (node_keys (occ_expr_diags idx outer ro)) <= 1)%nat.
Proof.
  unfold node_keys.
  pose proof (occ_expr_diags_le1 idx outer ro) as Hle.
  destruct (occ_expr_diags idx outer ro) as [|d [|d' r]]; cbn [length flat_map app] in Hle |- *; [ lia | | lia ].
  destruct (diag_node_key d); cbn [length app]; lia.
Qed.

Lemma occ_node_keys_val {p} (idx : GoIndex.Snap.SyntaxIndex p) outer ro :
  forall k, In k (node_keys (occ_expr_diags idx outer ro)) -> k = GoIndex.Snap.node_ref_key (fst ro).
Proof.
  intros k Hin. unfold node_keys in Hin. apply in_flat_map in Hin. destruct Hin as [d [Hd Hk]].
  rewrite (occ_expr_diags_key idx outer ro d Hd) in Hk. cbn [In] in Hk. destruct Hk as [<-|[]]. reflexivity.
Qed.

Lemma expr_node_keys_nodup {p} (idx : GoIndex.Snap.SyntaxIndex p) : NoDup (node_keys (expr_diags idx)).
Proof.
  unfold node_keys. rewrite expr_diags_eq_spec, flat_map_flat_map.
  apply (flat_map_le1_key_nodup (fun roc => GoIndex.Snap.node_ref_key (fst (fst roc)))).
  - assert (H : map (fun roc => GoIndex.Snap.node_ref_key (fst (fst roc))) (annotate_program idx)
                = map (fun ro => GoIndex.Snap.node_ref_key (fst ro)) (prog_visit p)).
    { rewrite <- (annotate_program_fst idx), map_map. reflexivity. }
    rewrite H. apply prog_visit_key_nodup.
  - intro roc. exact (occ_node_keys_le1 idx (snd roc) (fst roc)).
  - intros roc k Hin. exact (occ_node_keys_val idx (snd roc) (fst roc) k Hin).
Qed.

(* the duplicate-main keys of one package bucket: the TAIL mains' occurrence keys. *)
Definition bucket_dup_keys {p} (l : list (GoIndex.DeclRef p)) : list GoIndex.NodeKey :=
  match l with nil => nil | _ :: rest => map (fun dk => GoIndex.Snap.node_ref_key (GoIndex.erase_ref dk)) rest end.

Lemma node_keys_map_dup {p} (d1 : GoIndex.DeclRef p) (rest : list (GoIndex.DeclRef p)) :
  node_keys (map (fun dk => DRMainRedeclared dk d1) rest)
  = map (fun dk => GoIndex.Snap.node_ref_key (GoIndex.erase_ref dk)) rest.
Proof.
  induction rest as [|dk rest IH]; [reflexivity|].
  replace (node_keys (map (fun dk => DRMainRedeclared dk d1) (dk :: rest)))
    with ((match diag_node_key (DRMainRedeclared dk d1) with Some k => [k] | None => nil end)
          ++ node_keys (map (fun dk => DRMainRedeclared dk d1) rest)) by reflexivity.
  cbn [diag_node_key diagnostic_primary]. rewrite IH. reflexivity.
Qed.

Lemma pkg_diag_of_bucket_node_keys {p} (m : PM.t (list (GoIndex.DeclRef p))) Hpres dir l Hmt :
  node_keys (@pkg_diag_of_bucket p m Hpres dir l Hmt) = bucket_dup_keys l.
Proof.
  unfold pkg_diag_of_bucket, bucket_dup_keys. destruct l as [|d1 rest]; [reflexivity | apply node_keys_map_dup].
Qed.

Lemma bucket_diags_elems_node_keys {p} (m : PM.t (list (GoIndex.DeclRef p))) Hpres es Hall :
  node_keys (@bucket_diags_elems p m Hpres es Hall) = flat_map (fun kv => bucket_dup_keys (snd kv)) es.
Proof.
  revert Hall. induction es as [|kv rest IH]; intro Hall; cbn [bucket_diags_elems flat_map]; [reflexivity|].
  rewrite node_keys_app, (pkg_diag_of_bucket_node_keys m Hpres (fst kv) (snd kv)), IH. reflexivity.
Qed.

Lemma pkg_node_keys_spec {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  node_keys (pkg_diags idx) = flat_map (fun kv => bucket_dup_keys (snd kv)) (PM.elements (prog_package_refs idx)).
Proof. unfold pkg_diags. apply bucket_diags_elems_node_keys. Qed.

Lemma in_nkm_find_mapsto {X} (k : GoIndex.NodeKey) (m : GoIndex.NodeKeyMapBase.t (list X)) (d : X) :
  In d (nkm_find k m) -> exists b, GoIndex.NodeKeyMapBase.MapsTo k b m /\ In d b.
Proof.
  unfold nkm_find. intro Hd. destruct (GoIndex.NodeKeyMapBase.find k m) as [b|] eqn:E.
  - exists b. split; [ apply GoIndex.NodeKeyMapFacts.find_mapsto_iff; exact E | exact Hd ].
  - exfalso; exact Hd.
Qed.

Lemma bucket_value_key {X} (key : X -> option GoIndex.NodeKey)
    (kxs : list (GoIndex.NodeKey * X)) (Hself : forall kd, In kd kxs -> key (snd kd) = Some (fst kd)) :
  forall k b, GoIndex.NodeKeyMapBase.MapsTo k b (fold_right bucket_add (GoIndex.NodeKeyMapBase.empty (list X)) kxs) ->
  forall d, In d b -> key d = Some k.
Proof.
  induction kxs as [|kx rest IH]; intros k b Hmt d Hd.
  - apply GoIndex.NodeKeyMapFacts.empty_mapsto_iff in Hmt. destruct Hmt.
  - cbn [fold_right] in Hmt. unfold bucket_add in Hmt.
    apply GoIndex.NodeKeyMapFacts.add_mapsto_iff in Hmt. destruct Hmt as [[Hk Hb]|[Hk Hmt]].
    + subst b. unfold GoIndex.NodeKey_OT.eq in Hk. subst k. cbn [In] in Hd. destruct Hd as [<-|Hd].
      * exact (Hself kx (or_introl eq_refl)).
      * apply in_nkm_find_mapsto in Hd. destruct Hd as [b0 [Hm0 Hd]].
        exact (IH (fun kd Hin => Hself kd (or_intror Hin)) (fst kx) b0 Hm0 d Hd).
    + exact (IH (fun kd Hin => Hself kd (or_intror Hin)) k b Hmt d Hd).
Qed.

Lemma nkmap_lt_key_trans {A} : forall (a b c : GoIndex.NodeKey * A),
  GoIndex.NodeKeyMapBase.lt_key a b -> GoIndex.NodeKeyMapBase.lt_key b c -> GoIndex.NodeKeyMapBase.lt_key a c.
Proof. intros [k1 ?] [k2 ?] [k3 ?]; unfold GoIndex.NodeKeyMapBase.lt_key; cbn; apply GoIndex.NodeKey_OT.lt_trans. Qed.

(** the ERASED SOURCE-SEMANTIC report: the canonical SOURCE diagnostic list ([semantic_diagnostics]) projected
    through [erase_diagnostic], so it is a snapshot-INDEPENDENT [list ErasedDiagnostic] comparable by [=].  It is
    empty exactly when the SOURCE semantics accept ([semantic_ok_b]).  This is NOT the whole command-facing
    result: [erased_elaboration_report] (below) is the full elaboration report, which additionally carries the
    separate fresh-build-preflight diagnostics. *)
Definition erased_report (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p) : list ErasedDiagnostic :=
  map erase_diagnostic (semantic_diagnostics p idx).

Lemma erased_report_empty_iff (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p) :
  erased_report p idx = nil <-> semantic_ok_b p = true.
Proof.
  unfold erased_report. rewrite <- semantic_diagnostics_empty_iff.
  split; [ apply map_eq_nil | intro H; rewrite H; reflexivity ].
Qed.

(* the KEYED visit stream is SOURCE-DETERMINED.  Erasing a visited reference to its
   NodeKey (path + local id) and pairing it with its source occurrence yields a stream that depends ONLY on the
   file map's canonical [file_bindings] and each file's [occs_file] — NO snapshot [p] survives.  This is the
   foundation for cross-snapshot report/fact determinism: [FilesEqual] programs have IDENTICAL keyed streams. *)
Lemma keyed_visit_file {p} (fr : GoIndex.Snap.FileRef p) :
  map (fun rc => (GoIndex.Snap.node_ref_key (fst rc), snd rc)) (GoIndex.Snap.visit_file fr)
  = map (fun idocc => (GoIndex.mkKey (GoIndex.Snap.file_ref_path fr) (fst idocc), snd idocc))
        (GoIndex.occs_file (GoIndex.Snap.file_ref_source fr)).
Proof.
  rewrite <- (GoIndex.Snap.visit_file_idocc p fr), map_map.
  apply map_ext_in. intros [r occ] Hin. cbn [fst snd].
  rewrite GoIndex.Snap.node_ref_key_eq.
  destruct (GoIndex.Snap.visit_file_view p fr r occ Hin) as [_ Hf]. rewrite Hf. reflexivity.
Qed.

Lemma keyed_binding_visit (p : GoProgram) (b : FilePath * GoSourceFile) :
  In b (GoAST.file_bindings (prog_files p)) ->
  map (fun rc => (GoIndex.Snap.node_ref_key (fst rc), snd rc)) (binding_visit p b)
  = map (fun idocc => (GoIndex.mkKey (fst b) (fst idocc), snd idocc)) (GoIndex.occs_file (snd b)).
Proof.
  intro Hin. unfold binding_visit.
  pose proof (GoAST.file_bindings_find (prog_files p) b Hin) as Hfind.
  destruct (GoIndex.Snap.file_of_path_source p (fst b) (snd b) Hfind) as [fr [Hfop [Hpath Hsrc]]].
  rewrite Hfop, keyed_visit_file, Hpath, Hsrc. reflexivity.
Qed.

Definition keyed_visit (p : GoProgram) : list (GoIndex.NodeKey * GoIndex.SourceOccurrence) :=
  map (fun rc => (GoIndex.Snap.node_ref_key (fst rc), snd rc)) (prog_visit p).

Definition source_keyed_visit (fm : GoAST.GoFileMap) : list (GoIndex.NodeKey * GoIndex.SourceOccurrence) :=
  flat_map (fun b => map (fun idocc => (GoIndex.mkKey (fst b) (fst idocc), snd idocc)) (GoIndex.occs_file (snd b)))
           (GoAST.file_bindings fm).

Lemma keyed_visit_source (p : GoProgram) : keyed_visit p = source_keyed_visit (prog_files p).
Proof.
  unfold keyed_visit, source_keyed_visit. rewrite prog_visit_flat_map, map_flat_map.
  apply flat_map_ext_in. intros b Hin. exact (keyed_binding_visit p b Hin).
Qed.

(** the KEYED visit stream depends ONLY on the file map: [FilesEqual] programs have IDENTICAL keyed
    streams (their canonical [file_bindings] are the same list, and each file's [occs_file] is source-only). *)
Lemma keyed_visit_FilesEqual (p1 p2 : GoProgram) :
  GoAST.FilesEqual (prog_files p1) (prog_files p2) -> keyed_visit p1 = keyed_visit p2.
Proof.
  intro Heq. rewrite !keyed_visit_source. unfold source_keyed_visit.
  assert (Hb : GoAST.file_bindings (prog_files p1) = GoAST.file_bindings (prog_files p2)).
  { unfold GoAST.file_bindings. apply Collections.filemap_elements_Equal. exact Heq. }
  rewrite Hb. reflexivity.
Qed.

(** the ONE-PASS enclosing context erases to a SOURCE function of the keyed stream.  [annotate_keyed]
   runs the SAME stack discipline over keyed entries (NodeKeys + occurrences), and the erased ref-annotation
   [annotate_encl] equals it.  So the erased [outer_context] depends only on the file map. *)

(* the erasure of one annotated occurrence: its NodeKey, its occurrence, and its enclosing-context KEYS. *)
Definition erase_annot {p}
    (roc : (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) * list (GoIndex.ExprRef p))
  : (GoIndex.NodeKey * GoIndex.SourceOccurrence) * list GoIndex.NodeKey :=
  ((GoIndex.Snap.node_ref_key (fst (fst roc)), snd (fst roc)),
   map (fun er => GoIndex.Snap.node_ref_key (GoIndex.erase_ref er)) (snd roc)).

Definition erase_estack {p} (stack : list (GoIndex.ExprRef p * positive)) : list (GoIndex.NodeKey * positive) :=
  map (fun e => (GoIndex.Snap.node_ref_key (GoIndex.erase_ref (fst e)), snd e)) stack.

Fixpoint annotate_keyed (stack : list (GoIndex.NodeKey * positive))
    (stream : list (GoIndex.NodeKey * GoIndex.SourceOccurrence))
    : list ((GoIndex.NodeKey * GoIndex.SourceOccurrence) * list GoIndex.NodeKey) :=
  match stream with
  | [] => []
  | ke :: rest =>
      let open := filter (fun e => Pos.leb (GoIndex.nk_local (fst ke)) (snd e)) stack in
      let stack' := if is_conversion_occ (snd ke)
                    then (fst ke, GoIndex.occurrence_subtree_end (snd ke)) :: open else open in
      (ke, map fst open) :: annotate_keyed stack' rest
  end.

(* a conversion occurrence (on a VALID reference whose occurrence is its source) HAS an [ExprRef] erasing to it. *)
Lemma is_conversion_occ_as_expr {p} (idx : GoIndex.Snap.SyntaxIndex p) (r : GoIndex.Snap.NodeRef p) :
  is_conversion_occ (GoIndex.Snap.source_occurrence_of_ref r) = true ->
  exists er, GoIndex.as_expr idx r = Some er /\ GoIndex.erase_ref er = r.
Proof.
  intro Hconv.
  assert (Hk : GoIndex.Snap.node_kind idx r = GoIndex.KExpression).
  { rewrite (GoIndex.Snap.node_kind_matches_source p idx r). unfold is_conversion_occ in Hconv.
    destruct (GoIndex.view_expr (GoIndex.Snap.source_occurrence_of_ref r)) as [e|] eqn:Ev;
      [ exact (GoIndex.view_expr_kind _ e Ev) | discriminate Hconv ]. }
  unfold GoIndex.as_expr. destruct (GoIndex.as_kind_complete idx r GoIndex.KExpression Hk) as [tr [Has Her]].
  exists tr; split; [exact Has | exact Her].
Qed.

Lemma map_filter_comm {A B} (f : A -> B) (g : B -> bool) (h : A -> bool) (l : list A) :
  (forall a, g (f a) = h a) -> map f (filter h l) = filter g (map f l).
Proof.
  intro Hgh. induction l as [|a l IH]; [reflexivity|]. cbn [filter map].
  rewrite <- Hgh. destruct (g (f a)); cbn [map]; rewrite IH; reflexivity.
Qed.

Lemma erase_estack_filter {p} (l : positive) (stack : list (GoIndex.ExprRef p * positive)) :
  erase_estack (filter (fun e => Pos.leb l (snd e)) stack)
  = filter (fun e => Pos.leb l (snd e)) (erase_estack stack).
Proof. unfold erase_estack. apply map_filter_comm. intro a. reflexivity. Qed.

(* THE SIMULATION: over a stream of VALID occurrences, the erased ref-annotation equals the keyed annotation. *)
Lemma annotate_encl_erased {p} (idx : GoIndex.Snap.SyntaxIndex p) stack stream :
  (forall ro, In ro stream -> snd ro = GoIndex.Snap.source_occurrence_of_ref (fst ro)) ->
  map erase_annot (annotate_encl idx stack stream)
  = annotate_keyed (erase_estack stack) (map (fun ro => (GoIndex.Snap.node_ref_key (fst ro), snd ro)) stream).
Proof.
  revert stack. induction stream as [|ro rest IH]; intro stack; intro Hval; [reflexivity|].
  pose proof (Hval ro (or_introl eq_refl)) as Hsrc.
  cbn [annotate_encl map annotate_keyed fst snd].
  assert (Hok : filter (fun e => Pos.leb (GoIndex.nk_local (GoIndex.Snap.node_ref_key (fst ro))) (snd e))
                       (erase_estack stack)
              = erase_estack (filter (fun e => Pos.leb (GoIndex.Snap.node_ref_local (fst ro)) (snd e)) stack)).
  { rewrite erase_estack_filter, GoIndex.Snap.node_ref_key_eq. reflexivity. }
  f_equal.
  - unfold erase_annot. cbn [fst snd]. rewrite Hok. unfold erase_estack. rewrite !map_map. reflexivity.
  - rewrite (IH _ (fun ro' Hin => Hval ro' (or_intror Hin))), Hok. f_equal.
    destruct (is_conversion_occ (snd ro)) eqn:Hc.
    + assert (Hc' : is_conversion_occ (GoIndex.Snap.source_occurrence_of_ref (fst ro)) = true)
        by (rewrite <- Hsrc; exact Hc).
      destruct (is_conversion_occ_as_expr idx (fst ro) Hc') as [er [Ha He]].
      rewrite Ha. cbn [erase_estack map fst snd]. rewrite He.
      rewrite (GoIndex.Snap.node_subtree_end_matches_source p idx (fst ro)), <- Hsrc. reflexivity.
    + destruct (GoIndex.as_expr idx (fst ro)) as [er|]; reflexivity.
Qed.

(* each per-file visited occurrence IS its reference's exact source occurrence (the validity the simulation needs). *)
Lemma binding_visit_valid (p : GoProgram) (b : FilePath * GoSourceFile) :
  forall ro, In ro (binding_visit p b) -> snd ro = GoIndex.Snap.source_occurrence_of_ref (fst ro).
Proof.
  intros [r occ] Hin. unfold binding_visit in Hin.
  destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|]; [| destruct Hin].
  destruct (GoIndex.Snap.visit_file_view p fr r occ Hin) as [Ho _]. exact Ho.
Qed.

(* the SOURCE enclosing-context annotation: per file, the keyed one-pass annotation over that file's source
   occurrence stream (keyed by the file's path).  A pure function of the file map. *)
Definition annotate_source (fm : GoAST.GoFileMap)
  : list ((GoIndex.NodeKey * GoIndex.SourceOccurrence) * list GoIndex.NodeKey) :=
  flat_map (fun b => annotate_keyed []
              (map (fun idocc => (GoIndex.mkKey (fst b) (fst idocc), snd idocc)) (GoIndex.occs_file (snd b))))
           (GoAST.file_bindings fm).

Lemma annotate_program_erased {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  map erase_annot (annotate_program idx) = annotate_source (prog_files p).
Proof.
  unfold annotate_program, prog_blocks. rewrite flat_map_map.
  unfold annotate_source. rewrite map_flat_map.
  apply flat_map_ext_in. intros b Hin.
  rewrite (annotate_encl_erased idx [] (binding_visit p b) (binding_visit_valid p b)).
  cbn [erase_estack]. f_equal. exact (keyed_binding_visit p b Hin).
Qed.

Lemma annotate_source_FilesEqual (fm1 fm2 : GoAST.GoFileMap) :
  GoAST.FilesEqual fm1 fm2 -> annotate_source fm1 = annotate_source fm2.
Proof.
  intro Heq. unfold annotate_source.
  assert (Hb : GoAST.file_bindings fm1 = GoAST.file_bindings fm2)
    by (unfold GoAST.file_bindings; apply Collections.filemap_elements_Equal; exact Heq).
  rewrite Hb. reflexivity.
Qed.


(* the ERASED expression diagnostic an annotated KEYED occurrence emits — the same decision as [occ_expr_diags]
   but over erased data (its NodeKey + occurrence + enclosing-context KEYS); a pure source function. *)
Definition erase_occ_diags (kroc : (GoIndex.NodeKey * GoIndex.SourceOccurrence) * list GoIndex.NodeKey)
  : list ErasedDiagnostic :=
  match GoIndex.view_expr (snd (fst kroc)) with
  | None => []
  | Some e =>
      match local_conv_failure e with
      | Some (t, _) => [ mkErasedDiagnostic DCInvalidConversion (EANode (fst (fst kroc)))
                                            (map EANode (snd kroc)) (Some t) None (expr_conv_target e) ]
      | None =>
          match arg_default_failure (snd (fst kroc)) e with
          | Some (_, dt) => [ mkErasedDiagnostic DCDefaultNotRepresentable (EANode (fst (fst kroc))) [] (Some dt) None None ]
          | None => []
          end
      end
  end.

(* erasing the two expression diagnostics, computed explicitly (isolating the anchor/target projection). *)
Lemma erase_diagnostic_invalid {p} (er : GoIndex.ExprRef p) tr opr outer t ci :
  erase_diagnostic (DRInvalidConversion er tr opr outer t ci)
  = mkErasedDiagnostic DCInvalidConversion (EANode (GoIndex.Snap.node_ref_key (GoIndex.erase_ref er)))
      (map (fun r => EANode (GoIndex.Snap.node_ref_key (GoIndex.erase_ref r))) outer) (Some t) None
      (GoIndex.type_name_ref_syntax tr).
Proof.
  unfold erase_diagnostic.
  cbn [diagnostic_code diagnostic_primary diagnostic_related erased_target erased_output erased_source_target erase_anchor].
  rewrite map_map. reflexivity.
Qed.

Lemma erase_diagnostic_default {p} (er : GoIndex.ExprRef p) c dt :
  erase_diagnostic (DRDefaultNotRepresentable er c dt)
  = mkErasedDiagnostic DCDefaultNotRepresentable (EANode (GoIndex.Snap.node_ref_key (GoIndex.erase_ref er))) [] (Some dt) None None.
Proof. reflexivity. Qed.

(* per VISITED occurrence: erasing the ref-emitted diagnostics equals the keyed emitter on the erased
   annotation.  Membership is needed so a LOCAL conversion failure mints its exact target ref
   ([conversion_target_ref_conv]) — ruling out the (dead) [None] branch — AND so the ref-side source-target
   payload [type_name_ref_syntax tr] equals the source-side [expr_conv_target e] (both the exact source name). *)
Lemma erase_occ_diags_eq {p} (idx : GoIndex.Snap.SyntaxIndex p) (r : GoIndex.Snap.NodeRef p) occ ctx :
  In (r, occ) (prog_visit p) ->
  map erase_diagnostic (occ_expr_diags idx ctx (r, occ)) = erase_occ_diags (erase_annot ((r, occ), ctx)).
Proof.
  intro Hin.
  assert (Hval : occ = GoIndex.Snap.source_occurrence_of_ref r) by exact (prog_visit_view p r occ Hin).
  unfold occ_expr_diags, erase_occ_diags, erase_annot. cbn [fst snd].
  destruct (GoIndex.as_expr idx r) as [er|] eqn:Ea.
  - assert (Hk : GoIndex.Snap.node_kind idx r = GoIndex.KExpression).
    { unfold GoIndex.as_expr, GoIndex.as_kind in Ea.
      destruct (GoIndex.syntaxkind_eq_dec (GoIndex.Snap.node_kind idx r) GoIndex.KExpression) as [He|]; [exact He|discriminate Ea]. }
    assert (Hke : GoIndex.occurrence_kind occ = GoIndex.KExpression)
      by (rewrite Hval, <- (GoIndex.Snap.node_kind_matches_source p idx r); exact Hk).
    destruct (GoIndex.kind_view_expr occ Hke) as [e Hv]. rewrite Hv.
    assert (Her : GoIndex.erase_ref er = r) by exact (GoIndex.erase_as_kind idx r GoIndex.KExpression er Ea).
    destruct (local_conv_failure e) as [[t ci]|] eqn:Elc.
    + destruct e as [ b|n1|n2|s| df | dcx | ts x ]; try discriminate Elc.
      destruct (conversion_target_ref_conv idx r occ er ts x Hin Hv Ea) as [tr [Hctr [_ [_ Hsyn]]]].
      destruct (conversion_operand_ref_conv idx r occ er ts x Hin Hv Ea) as [opr [Hcor _]].
      rewrite Hctr, Hcor. cbn [map]. rewrite erase_diagnostic_invalid, Her, map_map, Hsyn.
      cbn [expr_conv_target]. reflexivity.
    + destruct (arg_default_failure occ e) as [[c dt]|].
      * cbn [map]. rewrite erase_diagnostic_default, Her. reflexivity.
      * reflexivity.
  - assert (Hkne : GoIndex.Snap.node_kind idx r <> GoIndex.KExpression).
    { unfold GoIndex.as_expr, GoIndex.as_kind in Ea.
      destruct (GoIndex.syntaxkind_eq_dec (GoIndex.Snap.node_kind idx r) GoIndex.KExpression); [discriminate Ea|assumption]. }
    assert (Hvne : GoIndex.view_expr occ = None).
    { destruct (GoIndex.view_expr occ) as [e|] eqn:E; [|reflexivity]. exfalso. apply Hkne.
      rewrite (GoIndex.Snap.node_kind_matches_source p idx r), <- Hval. exact (GoIndex.view_expr_kind occ e E). }
    rewrite Hvne. reflexivity.
Qed.

(* the erased expression report over the annotated program = the keyed emitter over each occurrence. *)
Lemma erased_expr_diags_annot {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  map erase_diagnostic (expr_diags idx)
  = flat_map (fun roc => erase_occ_diags (erase_annot roc)) (annotate_program idx).
Proof.
  rewrite expr_diags_eq_spec, map_flat_map. apply flat_map_ext_in.
  intros roc Hin. destruct roc as [[r occ] ctx]. cbn [fst snd].
  apply erase_occ_diags_eq.
  pose proof (in_map fst _ _ Hin) as Hin'. rewrite annotate_program_fst in Hin'. cbn [fst] in Hin'.
  exact Hin'.
Qed.

(** the erased EXPRESSION report is a SOURCE function of the file map (via [annotate_source]). *)
Lemma erased_expr_diags_source {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  map erase_diagnostic (expr_diags idx) = flat_map erase_occ_diags (annotate_source (prog_files p)).
Proof.
  rewrite erased_expr_diags_annot, <- (annotate_program_erased idx), flat_map_map. reflexivity.
Qed.

(** the PACKAGE buckets erase to a SOURCE function of the keyed stream.  [keyed_ppkg_step] runs the
   SAME package-grouping over keyed entries (NodeKeys), and the erased ([node_ref_key . erase_ref]) buckets
   equal it (find-wise, hence PM.Equal).  So the erased package diagnostics depend only on the file map. *)

Definition erase_dkey {p} (dr : GoIndex.DeclRef p) : GoIndex.NodeKey := GoIndex.Snap.node_ref_key (GoIndex.erase_ref dr).
Definition occ_pkg_key (ke : GoIndex.NodeKey * GoIndex.SourceOccurrence) : string :=
  fp_parent (GoIndex.nk_file (fst ke)).

Definition keyed_ppkg_step (ke : GoIndex.NodeKey * GoIndex.SourceOccurrence) (acc : PM.t (list GoIndex.NodeKey))
  : PM.t (list GoIndex.NodeKey) :=
  match GoIndex.occurrence_kind (snd ke) with
  | GoIndex.KTopLevelDecl =>
      PM.add (occ_pkg_key ke) (fst ke :: match PM.find (occ_pkg_key ke) acc with Some l => l | None => [] end) acc
  | GoIndex.KFile =>
      match PM.find (occ_pkg_key ke) acc with Some _ => acc | None => PM.add (occ_pkg_key ke) [] acc end
  | _ => acc
  end.

Definition keyed_buckets (l : list (GoIndex.NodeKey * GoIndex.SourceOccurrence)) : PM.t (list GoIndex.NodeKey) :=
  fold_right keyed_ppkg_step (PM.empty (list GoIndex.NodeKey)) l.

(* the keyed package of an occurrence equals its source parent directory (via [node_ref_key_eq]). *)
Lemma occ_pkg_key_eq {p} (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) :
  occ_pkg_key (GoIndex.Snap.node_ref_key (fst ro), snd ro) = occ_pkg ro.
Proof.
  unfold occ_pkg_key, occ_pkg. cbn [fst]. rewrite GoIndex.Snap.node_ref_key_eq. reflexivity.
Qed.

Lemma ppkg_erased_find {p} (idx : GoIndex.Snap.SyntaxIndex p) (L : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) :
  (forall ro, In ro L -> snd ro = GoIndex.Snap.source_occurrence_of_ref (fst ro)) ->
  forall k, PM.find k (PM.map (map erase_dkey) (fold_right (ppkg_step idx) (PM.empty _) L))
          = PM.find k (keyed_buckets (map (fun ro => (GoIndex.Snap.node_ref_key (fst ro), snd ro)) L)).
Proof.
  induction L as [|ro L IH]; intro Hval.
  - intro k. rewrite PMF.map_o. cbn [fold_right map keyed_buckets]. rewrite !PMF.empty_o. reflexivity.
  - pose proof (IH (fun ro' Hin => Hval ro' (or_intror Hin))) as IHk.
    unfold keyed_buckets in IHk.
    pose proof (Hval ro (or_introl eq_refl)) as Hsrc.
    assert (Hk : GoIndex.Snap.node_kind idx (fst ro) = GoIndex.occurrence_kind (snd ro))
      by (rewrite (GoIndex.Snap.node_kind_matches_source p idx (fst ro)), <- Hsrc; reflexivity).
    intro k. cbn [fold_right map keyed_buckets].
    set (acc := fold_right (ppkg_step idx) (PM.empty (list (GoIndex.DeclRef p))) L) in *.
    set (kacc := fold_right keyed_ppkg_step (PM.empty (list GoIndex.NodeKey))
                   (map (fun ro => (GoIndex.Snap.node_ref_key (fst ro), snd ro)) L)) in *.
    unfold ppkg_step at 1, keyed_ppkg_step at 1. cbn [fst snd]. rewrite occ_pkg_key_eq.
    destruct (GoIndex.occurrence_kind (snd ro)) eqn:Hok.
    + (* KFile: as_decl = None, as_kind KFile = Some — file-root init (presence, not length) *)
      assert (Hd : GoIndex.as_decl idx (fst ro) = None)
        by (apply GoIndex.as_kind_mismatch; rewrite Hk; discriminate).
      destruct (GoIndex.as_kind_complete idx (fst ro) GoIndex.KFile) as [fr [Hf _]]; [rewrite Hk; reflexivity|].
      rewrite Hd, Hf.
      pose proof (IHk (occ_pkg ro)) as IHo. rewrite PMF.map_o in IHo. rewrite <- IHo.
      destruct (PM.find (occ_pkg ro) acc) as [la|] eqn:Ea; cbn [option_map].
      * exact (IHk k).
      * destruct (String.eqb (occ_pkg ro) k) eqn:Ek.
        -- apply String.eqb_eq in Ek. rewrite PMF.map_o, PMF.add_eq_o, PMF.add_eq_o by exact Ek. reflexivity.
        -- apply String.eqb_neq in Ek. rewrite PMF.map_o, PMF.add_neq_o, PMF.add_neq_o by exact Ek.
           rewrite <- PMF.map_o. exact (IHk k).
    + (* KPackageClause: neither *)
      assert (Hd : GoIndex.as_decl idx (fst ro) = None)
        by (apply GoIndex.as_kind_mismatch; rewrite Hk; discriminate).
      assert (Hf : GoIndex.as_kind idx (fst ro) GoIndex.KFile = None)
        by (apply GoIndex.as_kind_mismatch; rewrite Hk; discriminate).
      rewrite Hd, Hf. exact (IHk k).
    + (* KTopLevelDecl: as_decl = Some dr — a main is prepended; its erased key IS the occurrence's key *)
      destruct (GoIndex.as_kind_complete idx (fst ro) GoIndex.KTopLevelDecl) as [dr [Hdr Her]];
        [ rewrite Hk; reflexivity | ].
      unfold GoIndex.as_decl. rewrite Hdr.
      pose proof (IHk (occ_pkg ro)) as IHo. rewrite PMF.map_o in IHo.
      destruct (String.eqb (occ_pkg ro) k) eqn:Ek.
      * apply String.eqb_eq in Ek. rewrite PMF.map_o, PMF.add_eq_o, PMF.add_eq_o by exact Ek.
        cbn [option_map map]. unfold erase_dkey. rewrite Her. f_equal. f_equal.
        rewrite <- IHo. destruct (PM.find (occ_pkg ro) acc) as [la|]; reflexivity.
      * apply String.eqb_neq in Ek. rewrite PMF.map_o, PMF.add_neq_o, PMF.add_neq_o by exact Ek.
        rewrite <- PMF.map_o. exact (IHk k).
    + (* KStatement: neither *)
      assert (Hd : GoIndex.as_decl idx (fst ro) = None)
        by (apply GoIndex.as_kind_mismatch; rewrite Hk; discriminate).
      assert (Hf : GoIndex.as_kind idx (fst ro) GoIndex.KFile = None)
        by (apply GoIndex.as_kind_mismatch; rewrite Hk; discriminate).
      rewrite Hd, Hf. exact (IHk k).
    + (* KExpression: neither *)
      assert (Hd : GoIndex.as_decl idx (fst ro) = None)
        by (apply GoIndex.as_kind_mismatch; rewrite Hk; discriminate).
      assert (Hf : GoIndex.as_kind idx (fst ro) GoIndex.KFile = None)
        by (apply GoIndex.as_kind_mismatch; rewrite Hk; discriminate).
      rewrite Hd, Hf. exact (IHk k).
    + (* KTypeName: neither (a conversion's source type name is not a decl or file) *)
      assert (Hd : GoIndex.as_decl idx (fst ro) = None)
        by (apply GoIndex.as_kind_mismatch; rewrite Hk; discriminate).
      assert (Hf : GoIndex.as_kind idx (fst ro) GoIndex.KFile = None)
        by (apply GoIndex.as_kind_mismatch; rewrite Hk; discriminate).
      rewrite Hd, Hf. exact (IHk k).
Qed.

(* the erased buckets of the retained elaboration EQUAL (find-wise, hence [PM.Equal]) the keyed source buckets. *)
Lemma prog_package_refs_erased {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  PM.Equal (PM.map (map erase_dkey) (prog_package_refs idx)) (keyed_buckets (keyed_visit p)).
Proof.
  intro k. unfold prog_package_refs, prog_package_refs_from_visit, keyed_visit.
  apply (ppkg_erased_find idx (prog_visit p)).
  intros [r occ] Hin. exact (prog_visit_view p r occ Hin).
Qed.

(* the ERASED package diagnostics of one bucket, over its erased (NodeKey) keys — a pure source function. *)
Definition erase_bucket_diag (kv : string * list GoIndex.NodeKey) : list ErasedDiagnostic :=
  match snd kv with
  | nil        => [ mkErasedDiagnostic DCMissingMainEntry (EAPackage (fst kv)) [] None None None ]
  | e1 :: erest => map (fun ek => mkErasedDiagnostic DCMainRedeclared (EANode ek) [EANode e1] None None None) erest
  end.

Lemma pkg_diag_of_bucket_erased {p} (m : PM.t (list (GoIndex.DeclRef p))) Hpres dir l Hmt :
  map erase_diagnostic (@pkg_diag_of_bucket p m Hpres dir l Hmt)
  = erase_bucket_diag (dir, map erase_dkey l).
Proof.
  unfold pkg_diag_of_bucket, erase_bucket_diag. cbn [snd]. destruct l as [|d1 rest]; cbn [map].
  - unfold erase_diagnostic. cbn [diagnostic_code diagnostic_primary diagnostic_related erased_target erased_output erase_anchor].
    reflexivity.
  - rewrite !map_map. unfold erase_diagnostic, erase_dkey.
    cbn [diagnostic_code diagnostic_primary diagnostic_related erased_target erased_output erase_anchor map]. reflexivity.
Qed.

Lemma bucket_diags_elems_erased {p} (m : PM.t (list (GoIndex.DeclRef p))) Hpres es Hall :
  map erase_diagnostic (@bucket_diags_elems p m Hpres es Hall)
  = flat_map erase_bucket_diag (map (fun kv => (fst kv, map erase_dkey (snd kv))) es).
Proof.
  revert Hall. induction es as [|kv rest IH]; intro Hall; cbn [bucket_diags_elems map flat_map]; [reflexivity|].
  rewrite map_app, IH. f_equal. apply pkg_diag_of_bucket_erased.
Qed.

(** the erased PACKAGE report is a SOURCE function of the file map (via the keyed source buckets). *)
Lemma erased_pkg_diags_source {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  map erase_diagnostic (pkg_diags idx)
  = flat_map erase_bucket_diag (PM.elements (keyed_buckets (keyed_visit p))).
Proof.
  unfold pkg_diags. rewrite bucket_diags_elems_erased.
  rewrite <- Collections.packagemap_map_elements.
  rewrite (Collections.packagemap_elements_Equal _ _ (prog_package_refs_erased idx)). reflexivity.
Qed.

Lemma erased_pkg_diags_FilesEqual (p1 p2 : GoProgram)
    (idx1 : GoIndex.Snap.SyntaxIndex p1) (idx2 : GoIndex.Snap.SyntaxIndex p2) :
  GoAST.FilesEqual (prog_files p1) (prog_files p2) ->
  map erase_diagnostic (pkg_diags idx1) = map erase_diagnostic (pkg_diags idx2).
Proof.
  intro Heq. rewrite !erased_pkg_diags_source, (keyed_visit_FilesEqual p1 p2 Heq). reflexivity.
Qed.

(** the WHOLE erased report as a PURE SOURCE function of the file map — expression diagnostics via
    [annotate_source] (occurrence keys + open-conversion context) then package diagnostics via the keyed source
    buckets.  Since it mentions no [Snap] projection it [vm_compute]s to the exact [ErasedDiagnostic] list (code
    + NodeKey/package anchors + target payload) for any concrete program — the basis of the EXACT fixtures. *)
(* the ERASED node-diagnostic key/partition (mirroring the dependent ones, over snapshot-free anchors). *)
Definition enode_key (e : ErasedDiagnostic) : option GoIndex.NodeKey :=
  match ed_primary e with EANode k => Some k | _ => None end.
Definition enode_keyed (l : list ErasedDiagnostic) : list (GoIndex.NodeKey * ErasedDiagnostic) :=
  flat_map (fun e => match enode_key e with Some k => [(k, e)] | None => [] end) l.
Definition epkg_primary (l : list ErasedDiagnostic) : list ErasedDiagnostic :=
  flat_map (fun e => match enode_key e with Some _ => [] | None => [e] end) l.

(* the raw (unordered) erased source diagnostics — expression scars over [annotate_source], then the keyed
   source package buckets. *)
Definition erased_src_diags (fm : GoAST.GoFileMap) : list ErasedDiagnostic :=
  flat_map erase_occ_diags (annotate_source fm)
  ++ flat_map erase_bucket_diag (PM.elements (keyed_buckets (source_keyed_visit fm))).

(** the WHOLE erased report as a PURE SOURCE function of the file map, in canonical order: node-primary
    diagnostics bucketed by NodeKey and flattened in path/local order (each occurrence emits at most one node
    diagnostic, so no within-bucket sort is needed), THEN the package-primary (missing-main) diagnostics.  It
    mentions no [Snap] projection, so it [vm_compute]s to the exact ordered [ErasedDiagnostic] list. *)
Definition erased_report_src (fm : GoAST.GoFileMap) : list ErasedDiagnostic :=
  bucket_flatten (enode_keyed (erased_src_diags fm)) ++ epkg_primary (erased_src_diags fm).

Lemma enode_key_erase {p} (d : DiagnosticReason p) : enode_key (erase_diagnostic d) = diag_node_key d.
Proof. destruct d; reflexivity. Qed.

Lemma node_keyed_erase {p} (l : list (DiagnosticReason p)) :
  map (fun kd => (fst kd, erase_diagnostic (snd kd))) (node_keyed l) = enode_keyed (map erase_diagnostic l).
Proof.
  induction l as [|d rest IH]; [reflexivity|].
  replace (node_keyed (d :: rest))
    with ((match diag_node_key d with Some k => [(k, d)] | None => nil end) ++ node_keyed rest) by reflexivity.
  replace (enode_keyed (map erase_diagnostic (d :: rest)))
    with ((match enode_key (erase_diagnostic d) with Some k => [(k, erase_diagnostic d)] | None => nil end)
          ++ enode_keyed (map erase_diagnostic rest)) by reflexivity.
  rewrite map_app, IH, enode_key_erase. destruct (diag_node_key d) as [k|]; reflexivity.
Qed.

Lemma pkg_primary_erase {p} (l : list (DiagnosticReason p)) :
  map erase_diagnostic (pkg_primary l) = epkg_primary (map erase_diagnostic l).
Proof.
  induction l as [|d rest IH]; [reflexivity|].
  replace (pkg_primary (d :: rest))
    with ((match diag_node_key d with Some _ => nil | None => [d] end) ++ pkg_primary rest) by reflexivity.
  replace (epkg_primary (map erase_diagnostic (d :: rest)))
    with ((match enode_key (erase_diagnostic d) with Some _ => nil | None => [erase_diagnostic d] end)
          ++ epkg_primary (map erase_diagnostic rest)) by reflexivity.
  rewrite map_app, IH, enode_key_erase. destruct (diag_node_key d) as [k|]; reflexivity.
Qed.

Lemma erased_src_diags_eq {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  map erase_diagnostic (expr_diags idx ++ pkg_diags idx) = erased_src_diags (prog_files p).
Proof.
  unfold erased_src_diags. rewrite map_app, erased_expr_diags_source, erased_pkg_diags_source, keyed_visit_source.
  reflexivity.
Qed.

Lemma erased_report_src_eq {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  erased_report p idx = erased_report_src (prog_files p).
Proof.
  unfold erased_report, erased_report_src, semantic_diagnostics. rewrite map_app. f_equal.
  - rewrite (bucket_flatten_map erase_diagnostic (node_keyed (expr_diags idx ++ pkg_diags idx))).
    rewrite node_keyed_erase, erased_src_diags_eq. reflexivity.
  - rewrite pkg_primary_erase, erased_src_diags_eq. reflexivity.
Qed.

Lemma erased_src_diags_FilesEqual (fm1 fm2 : GoAST.GoFileMap) :
  GoAST.FilesEqual fm1 fm2 -> erased_src_diags fm1 = erased_src_diags fm2.
Proof.
  intro Heq. unfold erased_src_diags. rewrite (annotate_source_FilesEqual _ _ Heq). f_equal.
  assert (Hb : GoAST.file_bindings fm1 = GoAST.file_bindings fm2)
    by (unfold GoAST.file_bindings; apply Collections.filemap_elements_Equal; exact Heq).
  unfold source_keyed_visit. rewrite Hb. reflexivity.
Qed.

(** THE cross-snapshot determinism theorem: two programs with the SAME file map (their
    diagnostics live in DIFFERENT dependent snapshot types) produce the IDENTICAL erased report — it depends
    ONLY on the file map (the erased report is [erased_report_src (prog_files p)], a source function). *)
Theorem erased_report_FilesEqual (p1 p2 : GoProgram)
    (idx1 : GoIndex.Snap.SyntaxIndex p1) (idx2 : GoIndex.Snap.SyntaxIndex p2) :
  GoAST.FilesEqual (prog_files p1) (prog_files p2) ->
  erased_report p1 idx1 = erased_report p2 idx2.
Proof.
  intro Heq. rewrite !erased_report_src_eq. unfold erased_report_src.
  rewrite (erased_src_diags_FilesEqual _ _ Heq). reflexivity.
Qed.

(** CONSTRUCTION-list permutation corollary: building the SAME module from a PERMUTED file-node
    list yields the IDENTICAL erased report (permuted nodes build the same [FilesEqual] map — the standard
    duplicate-rejecting [filemap_of_nodes] is order-independent — so the report, a function of the map, is
    unchanged).  The report is invariant to the order in which the proposer supplies the files. *)
Theorem erased_report_build_permutation : forall ms nodes1 nodes2 p1 p2
    (idx1 : GoIndex.Snap.SyntaxIndex p1) (idx2 : GoIndex.Snap.SyntaxIndex p2),
  Permutation nodes1 nodes2 ->
  build_program ms nodes1 = Some p1 -> build_program ms nodes2 = Some p2 ->
  erased_report p1 idx1 = erased_report p2 idx2.
Proof.
  intros ms nodes1 nodes2 p1 p2 idx1 idx2 Hperm Hb1 Hb2.
  apply erased_report_FilesEqual. unfold build_program in *.
  destruct (filemap_of_nodes nodes1) as [fm1|] eqn:F1; [ | discriminate ].
  destruct (filemap_of_nodes nodes2) as [fm2|] eqn:F2; [ | discriminate ].
  injection Hb1 as <-. injection Hb2 as <-. cbn [prog_files].
  exact (filemap_of_nodes_permutation nodes1 nodes2 fm1 fm2 Hperm F1 F2).
Qed.

(* ---- SUCCESSFUL-fact enumeration determinism.  The expression fact table's keys are SOURCE
   NodeKeys and its values source-derived, so it is a fold-map fusion over the keyed stream — a pure source
   function of the file map, needing no erasure. ---- *)
Definition keyed_add (ke : GoIndex.NodeKey * GoIndex.SourceOccurrence)
    (m : GoIndex.NodeKeyMapBase.t ExprFact) : GoIndex.NodeKeyMapBase.t ExprFact :=
  match occ_expr_fact (snd ke) with
  | Some f => GoIndex.NodeKeyMapBase.add (fst ke) f m
  | None => m
  end.

Definition keyed_facts (l : list (GoIndex.NodeKey * GoIndex.SourceOccurrence)) : GoIndex.NodeKeyMapBase.t ExprFact :=
  fold_right keyed_add (GoIndex.NodeKeyMapBase.empty ExprFact) l.

Lemma prog_expr_facts_source (p : GoProgram) : prog_expr_facts p = keyed_facts (keyed_visit p).
Proof.
  rewrite prog_expr_facts_eq_spec. unfold keyed_facts, keyed_visit.
  induction (prog_visit p) as [|ro L IH]; [reflexivity|].
  cbn [map fold_right]. rewrite IH. unfold add_occ_fact, keyed_add. cbn [fst snd]. reflexivity.
Qed.

(** SUCCESSFUL-fact enumeration determinism: the expression fact table (each visited
    occurrence's key -> its exact ConstInfo + println-use fact) depends ONLY on the file map — its keys are
    source NodeKeys and its values source-derived (a fold-map fusion over the keyed stream) — so FilesEqual
    programs have the IDENTICAL fact table, hence the IDENTICAL canonical fact enumeration. *)
Lemma prog_expr_facts_FilesEqual (p1 p2 : GoProgram) :
  GoAST.FilesEqual (prog_files p1) (prog_files p2) -> prog_expr_facts p1 = prog_expr_facts p2.
Proof.
  intro Heq. rewrite !prog_expr_facts_source, (keyed_visit_FilesEqual p1 p2 Heq). reflexivity.
Qed.

Theorem prog_expr_facts_enum_FilesEqual (p1 p2 : GoProgram) :
  GoAST.FilesEqual (prog_files p1) (prog_files p2) ->
  GoIndex.NodeKeyMapBase.elements (prog_expr_facts p1) = GoIndex.NodeKeyMapBase.elements (prog_expr_facts p2).
Proof. intro Heq. rewrite (prog_expr_facts_FilesEqual p1 p2 Heq). reflexivity. Qed.

(* ---- the TWO disjoint diagnostic families (typing / package), used to PROJECT a legacy compile class from
   the diagnostics (never a second check).  Expression diagnostics are typing-class; package diagnostics are
   package-class; the two are disjoint. ---- *)

Definition diag_is_typing {p} (d : DiagnosticReason p) : bool :=
  match diagnostic_code d with DCInvalidConversion | DCDefaultNotRepresentable => true | _ => false end.
Definition diag_is_package {p} (d : DiagnosticReason p) : bool :=
  match diagnostic_code d with DCMainRedeclared | DCMissingMainEntry => true | _ => false end.
Definition diag_is_build_output {p} (d : DiagnosticReason p) : bool :=
  match diagnostic_code d with DCBuildOutputIsDirectory => true | _ => false end.
Lemma diag_typing_not_build {p} (d : DiagnosticReason p) : diag_is_typing d = true -> diag_is_build_output d = false.
Proof. unfold diag_is_typing, diag_is_build_output; destruct (diagnostic_code d); (reflexivity || discriminate). Qed.
Lemma diag_package_not_build {p} (d : DiagnosticReason p) : diag_is_package d = true -> diag_is_build_output d = false.
Proof. unfold diag_is_package, diag_is_build_output; destruct (diagnostic_code d); (reflexivity || discriminate). Qed.

Lemma existsb_all_true {A} (f : A -> bool) (l : list A) :
  (forall x, In x l -> f x = true) -> existsb f l = match l with [] => false | _ => true end.
Proof. destruct l as [|x xs]; [reflexivity|]. intro H. cbn [existsb]. rewrite (H x (or_introl eq_refl)). reflexivity. Qed.

Lemma existsb_all_false {A} (f : A -> bool) (l : list A) :
  (forall x, In x l -> f x = false) -> existsb f l = false.
Proof.
  induction l as [|x xs IH]; [reflexivity|]. intro H. cbn [existsb].
  rewrite (H x (or_introl eq_refl)), IH by (intros y Hy; apply H; right; exact Hy). reflexivity.
Qed.

Lemma occ_expr_diags_family {p} (idx : GoIndex.Snap.SyntaxIndex p) outer ro : forall d,
  In d (occ_expr_diags idx outer ro) -> diag_is_typing d = true /\ diag_is_package d = false.
Proof.
  intros d Hin. unfold occ_expr_diags in Hin.
  destruct (GoIndex.as_expr idx (fst ro)) as [er|]; [| destruct Hin].
  destruct (GoIndex.view_expr (snd ro)) as [e|]; [| destruct Hin].
  destruct (local_conv_failure e) as [[t ci]|].
  - destruct (conversion_target_ref idx er) as [tr|]; [| destruct Hin].
    destruct (conversion_operand_ref idx er) as [opr|]; [| destruct Hin].
    destruct Hin as [<-|[]]. split; reflexivity.
  - destruct (arg_default_failure (snd ro) e) as [[c dt]|]; [ destruct Hin as [<-|[]]; split; reflexivity | destruct Hin ].
Qed.

Lemma expr_diags_typing {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall d, In d (expr_diags idx) -> diag_is_typing d = true.
Proof.
  intros d Hin. rewrite expr_diags_eq_spec in Hin. apply in_flat_map in Hin. destruct Hin as [roc [_ Hd]].
  apply (occ_expr_diags_family idx (snd roc) (fst roc) d Hd).
Qed.
Lemma expr_diags_not_package {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall d, In d (expr_diags idx) -> diag_is_package d = false.
Proof.
  intros d Hin. rewrite expr_diags_eq_spec in Hin. apply in_flat_map in Hin. destruct Hin as [roc [_ Hd]].
  apply (occ_expr_diags_family idx (snd roc) (fst roc) d Hd).
Qed.

Lemma pkg_diag_of_bucket_family {p} (m : PM.t (list (GoIndex.DeclRef p))) Hpres dir l Hmt : forall d,
  In d (@pkg_diag_of_bucket p m Hpres dir l Hmt) -> diag_is_package d = true /\ diag_is_typing d = false.
Proof.
  intros d Hin. unfold pkg_diag_of_bucket in Hin. destruct l as [|d1 rest].
  - destruct Hin as [<-|[]]; split; reflexivity.
  - apply in_map_iff in Hin. destruct Hin as [dk [<- _]]. split; reflexivity.
Qed.

Lemma bucket_diags_elems_family {p} (m : PM.t (list (GoIndex.DeclRef p))) Hpres es Hall : forall d,
  In d (@bucket_diags_elems p m Hpres es Hall) -> diag_is_package d = true /\ diag_is_typing d = false.
Proof.
  revert Hall. induction es as [|kv rest IH]; intro Hall; cbn [bucket_diags_elems]; intros d Hin.
  - destruct Hin.
  - apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
    + exact (pkg_diag_of_bucket_family m Hpres (fst kv) (snd kv) (Hall kv (or_introl eq_refl)) d Hin).
    + exact (IH (fun kv' Hin' => Hall kv' (or_intror Hin')) d Hin).
Qed.

Lemma pkg_diags_family {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall d,
  In d (pkg_diags idx) -> diag_is_package d = true /\ diag_is_typing d = false.
Proof.
  intros d Hin. unfold pkg_diags in Hin. exact (bucket_diags_elems_family _ _ _ _ d Hin).
Qed.

(** code-specific PACKAGE-diagnostic soundness.  A [DRMissingMainEntry] comes from an EMPTY bucket
    and anchors at THAT package key (the [PackageRef] carries its own presence proof — [package_ref_ok] — so
    the package is represented in [p]); an empty bucket length is the package's zero [main] count
    ([prog_package_refs_bucket_len]), i.e. there is genuinely no [DMain]. *)
Lemma pkg_diag_of_bucket_missing_sound {p} (m : PM.t (list (GoIndex.DeclRef p))) Hpres dir l Hmt pk :
  In (DRMissingMainEntry pk) (@pkg_diag_of_bucket p m Hpres dir l Hmt) ->
  l = nil /\ package_ref_key pk = dir.
Proof.
  intro Hin. unfold pkg_diag_of_bucket in Hin. destruct l as [|d1 rest].
  - destruct Hin as [Heq|[]]. injection Heq as Hpk. subst pk. split; reflexivity.
  - apply in_map_iff in Hin. destruct Hin as [dk [Heq _]]. discriminate Heq.
Qed.

(** A [DRMainRedeclared later earlier] comes from a bucket [earlier :: rest] with [later] in the TAIL: the
    related [earlier] is the FIRST canonical main and the primary [later] is a strictly-later main in the same
    bucket (hence same package — [prog_package_refs_belongs] — and in canonical bucket order). *)
Lemma pkg_diag_of_bucket_dup_sound {p} (m : PM.t (list (GoIndex.DeclRef p))) Hpres dir l Hmt later earlier :
  In (DRMainRedeclared later earlier) (@pkg_diag_of_bucket p m Hpres dir l Hmt) ->
  exists rest, l = earlier :: rest /\ In later rest.
Proof.
  intro Hin. unfold pkg_diag_of_bucket in Hin. destruct l as [|d1 rest].
  - destruct Hin as [Heq|[]]. discriminate Heq.
  - apply in_map_iff in Hin. destruct Hin as [dk [Heq Hdk]]. injection Heq as Hl He.
    exists rest. split; [ rewrite <- He; reflexivity | rewrite <- Hl; exact Hdk ].
Qed.

(* a diagnostic in the flattened bucket enumeration comes from SOME mapped bucket of [m]. *)
Lemma bucket_diags_elems_in {p} (m : PM.t (list (GoIndex.DeclRef p))) Hpres es Hall : forall d,
  In d (@bucket_diags_elems p m Hpres es Hall) ->
  exists dir l (Hmt : PM.MapsTo dir l m), In d (@pkg_diag_of_bucket p m Hpres dir l Hmt).
Proof.
  revert Hall. induction es as [|kv rest IH]; intro Hall; cbn [bucket_diags_elems]; intros d Hin.
  - destruct Hin.
  - apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
    + exists (fst kv), (snd kv), (Hall kv (or_introl eq_refl)). exact Hin.
    + destruct (IH (fun kv' Hin' => Hall kv' (or_intror Hin')) d Hin) as [dir [l [Hmt Hd]]].
      exists dir, l, Hmt. exact Hd.
Qed.

(** the WHOLE-program [DRMainRedeclared] soundness DENOTES its code: the primary [later] and the
    related [earlier] both anchor genuine TOP-LEVEL declarations (the only [GoDecl] is [DMain] — `func main`),
    they lie in the SAME package (equal parent directory — [prog_package_refs_belongs]), and [earlier] is the
    FIRST canonical main of that package's bucket with [later] a strictly-later one. *)
Lemma pkg_diags_dup_sound {p} (idx : GoIndex.Snap.SyntaxIndex p) later earlier :
  In (DRMainRedeclared later earlier) (pkg_diags idx) ->
  fp_parent (GoIndex.Snap.file_ref_path (GoIndex.Snap.node_ref_file (GoIndex.erase_ref later)))
    = fp_parent (GoIndex.Snap.file_ref_path (GoIndex.Snap.node_ref_file (GoIndex.erase_ref earlier)))
  /\ GoIndex.occurrence_kind (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref later)) = GoIndex.KTopLevelDecl
  /\ GoIndex.occurrence_kind (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref earlier)) = GoIndex.KTopLevelDecl.
Proof.
  intro Hin. unfold pkg_diags in Hin.
  destruct (bucket_diags_elems_in _ _ _ _ _ Hin) as [dir [l [Hmt Hd]]].
  destruct (pkg_diag_of_bucket_dup_sound _ _ dir l Hmt later earlier Hd) as [rest [Hl Hlater]].
  assert (Hfind : PM.find dir (prog_package_refs idx) = Some l) by (apply PM.find_1; exact Hmt).
  assert (HinE : In earlier l) by (rewrite Hl; left; reflexivity).
  assert (HinL : In later l)  by (rewrite Hl; right; exact Hlater).
  split; [ | split ].
  - rewrite (prog_package_refs_belongs idx dir l Hfind later HinL),
            (prog_package_refs_belongs idx dir l Hfind earlier HinE); reflexivity.
  - exact (GoIndex.noderefof_kind later).
  - exact (GoIndex.noderefof_kind earlier).
Qed.

(** the WHOLE-program [DRMissingMainEntry] soundness: a missing-main diagnostic anchors a package
    that IS represented in the program ([package_ref_ok]) and genuinely contains ZERO [DMain] declarations (its
    exact [pkg_main_count] is 0 — the empty bucket's length). *)
Lemma pkg_diags_missing_sound {p} (idx : GoIndex.Snap.SyntaxIndex p) pk :
  In (DRMissingMainEntry pk) (pkg_diags idx) ->
  package_present_b p (package_ref_key pk) = true
  /\ pkg_main_count (package_ref_key pk) (prog_files p) = 0%nat.
Proof.
  intro Hin. unfold pkg_diags in Hin.
  destruct (bucket_diags_elems_in _ _ _ _ _ Hin) as [dir [l [Hmt Hd]]].
  destruct (pkg_diag_of_bucket_missing_sound _ _ dir l Hmt pk Hd) as [Hl Hkey]. subst l.
  split.
  - exact (package_ref_ok pk).
  - rewrite Hkey. symmetry. exact (prog_package_refs_bucket_len idx dir nil (PM.find_1 Hmt)).
Qed.

(** the package buckets are NodeKey-SORTED and DUPLICATE-FREE, hence duplicate-main diagnostics carry
   strict canonical precedence + distinctness.  Foundation: the whole visit stream is NodeKey-sorted. *)

(* one file's block is NodeKey-sorted: same file (path constant), local strictly ascending. *)
Lemma visit_file_key_sorted {p} (fr : GoIndex.Snap.FileRef p) :
  StronglySorted (fun x y => GoIndex.NodeKey_OT.lt (GoIndex.Snap.node_ref_key (fst x)) (GoIndex.Snap.node_ref_key (fst y)))
                 (GoIndex.Snap.visit_file fr).
Proof.
  apply (StronglySorted_impl_in (fun x y => Pos.lt (GoIndex.Snap.node_ref_local (fst x)) (GoIndex.Snap.node_ref_local (fst y)))).
  - intros [rx ox] [ry oy] Hx Hy Hlt.
    destruct (GoIndex.Snap.visit_file_view p fr rx ox Hx) as [_ Hfx].
    destruct (GoIndex.Snap.visit_file_view p fr ry oy Hy) as [_ Hfy].
    cbn [fst] in *. rewrite (GoIndex.Snap.node_ref_key_eq rx), (GoIndex.Snap.node_ref_key_eq ry).
    right. cbn [GoIndex.nk_file GoIndex.nk_local]. split; [ rewrite Hfx, Hfy; reflexivity | exact Hlt ].
  - apply StronglySorted_map_inv. exact (GoIndex.Snap.visit_file_order p fr).
Qed.

(* every node visited in binding [b]'s block has that binding's path as its key's file component. *)
Lemma binding_block_key_file (p : GoProgram) (b : FilePath * GoSourceFile) :
  forall ro, In ro (binding_visit p b) -> GoIndex.nk_file (GoIndex.Snap.node_ref_key (fst ro)) = fst b.
Proof.
  intros [r occ] Hin. unfold binding_visit in Hin.
  destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|] eqn:Efr; [| destruct Hin].
  destruct (GoIndex.Snap.visit_file_view p fr r occ Hin) as [_ Hf].
  cbn [fst]. rewrite (GoIndex.Snap.node_ref_key_eq r). cbn [GoIndex.nk_file]. rewrite Hf.
  exact (GoIndex.Snap.file_of_path_sound p (fst b) fr Efr).
Qed.

Lemma prog_visit_key_sorted_aux (p : GoProgram) (L : list (FilePath * GoSourceFile)) :
  StronglySorted (fun a b => Collections.FilePath_OT.lt (fst a) (fst b)) L ->
  StronglySorted (fun x y => GoIndex.NodeKey_OT.lt (GoIndex.Snap.node_ref_key (fst x)) (GoIndex.Snap.node_ref_key (fst y)))
                 (concat (map (binding_visit p) L)).
Proof.
  induction L as [|b L IH]; intro Hbsort; [constructor|].
  apply StronglySorted_inv in Hbsort. destruct Hbsort as [Hbs Hbhd].
  cbn [map concat]. apply StronglySorted_app.
  { unfold binding_visit. destruct (GoIndex.Snap.file_of_path p (fst b)) as [fr|]; [apply visit_file_key_sorted | constructor]. }
  { apply IH; exact Hbs. }
  intros x y Hx Hy. apply in_concat in Hy. destruct Hy as [block [Hblock Hyb]].
  apply in_map_iff in Hblock. destruct Hblock as [b' [Hb'v Hb'L]]. subst block.
  assert (Hxf : GoIndex.nk_file (GoIndex.Snap.node_ref_key (fst x)) = fst b) by (apply binding_block_key_file; exact Hx).
  assert (Hyf : GoIndex.nk_file (GoIndex.Snap.node_ref_key (fst y)) = fst b') by (apply binding_block_key_file; exact Hyb).
  rewrite Forall_forall in Hbhd. pose proof (Hbhd b' Hb'L) as Hlt.
  unfold GoIndex.NodeKey_OT.lt. left. rewrite Hxf, Hyf. exact Hlt.
Qed.

Lemma prog_visit_key_sorted (p : GoProgram) :
  StronglySorted (fun x y => GoIndex.NodeKey_OT.lt (GoIndex.Snap.node_ref_key (fst x)) (GoIndex.Snap.node_ref_key (fst y)))
                 (prog_visit p).
Proof.
  unfold prog_visit, prog_blocks. apply prog_visit_key_sorted_aux.
  apply Sorted_StronglySorted; [ intros x y z; apply Collections.FilePath_OT.lt_trans | ].
  unfold GoAST.file_bindings. apply Collections.FileMapBase.elements_3.
Qed.

(* one [ppkg_step]'s effect on ONE package bucket, as an actual list: it prepends this occurrence's DeclRef
   (when it mints one for THIS package), else leaves the bucket unchanged.  (A file-root init adds an empty
   bucket — presence, not a list element.)  Mirrors [ppkg_step_olen] at the list level. *)
Lemma ppkg_step_bucket {p} (idx : GoIndex.Snap.SyntaxIndex p)
    (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence) (acc : PM.t (list (GoIndex.DeclRef p))) (dir : string) :
  (match PM.find dir (ppkg_step idx ro acc) with Some bk => bk | None => nil end)
  = (if String.eqb (occ_pkg ro) dir
     then match GoIndex.as_decl idx (fst ro) with
          | Some dr => dr :: (match PM.find dir acc with Some bk => bk | None => nil end)
          | None => (match PM.find dir acc with Some bk => bk | None => nil end)
          end
     else (match PM.find dir acc with Some bk => bk | None => nil end)).
Proof.
  unfold ppkg_step. destruct (GoIndex.as_decl idx (fst ro)) as [dr|] eqn:Ed.
  - destruct (String.eqb (occ_pkg ro) dir) eqn:Edir.
    + apply String.eqb_eq in Edir. rewrite Edir, PMF.add_eq_o by reflexivity. reflexivity.
    + apply String.eqb_neq in Edir. rewrite PMF.add_neq_o by exact Edir. reflexivity.
  - destruct (GoIndex.as_kind idx (fst ro) GoIndex.KFile) as [fnr|] eqn:Ef.
    + destruct (PM.find (occ_pkg ro) acc) as [l0|] eqn:Efind.
      * destruct (String.eqb (occ_pkg ro) dir) eqn:Edir; [ apply String.eqb_eq in Edir; subst dir | ]; reflexivity.
      * destruct (String.eqb (occ_pkg ro) dir) eqn:Edir.
        -- apply String.eqb_eq in Edir. rewrite Edir, PMF.add_eq_o by reflexivity.
           rewrite <- Edir, Efind. reflexivity.
        -- apply String.eqb_neq in Edir. rewrite PMF.add_neq_o by exact Edir. reflexivity.
    + destruct (String.eqb (occ_pkg ro) dir) eqn:Edir; reflexivity.
Qed.

Definition bucket_of {p} (idx : GoIndex.Snap.SyntaxIndex p)
    (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) (dir : string) : list (GoIndex.DeclRef p) :=
  match PM.find dir (fold_right (ppkg_step idx) (PM.empty _) l) with Some bk => bk | None => nil end.

(* the fold's action on the head occurrence, stated over [bucket_of] (a real head symbol, so [rewrite]'s keyed
   unification finds it — a bare [match] LHS has no head to key on). *)
Lemma ppkg_fold_bucket_cons {p} (idx : GoIndex.Snap.SyntaxIndex p)
    (ro : GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)
    (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) (dir : string) :
  bucket_of idx (ro :: l) dir
  = (if String.eqb (occ_pkg ro) dir
     then match GoIndex.as_decl idx (fst ro) with
          | Some dr => dr :: bucket_of idx l dir
          | None => bucket_of idx l dir
          end
     else bucket_of idx l dir).
Proof. unfold bucket_of. cbn [fold_right]. apply (ppkg_step_bucket idx ro (fold_right (ppkg_step idx) (PM.empty _) l) dir). Qed.

(* over a NodeKey-sorted stream, every package bucket is NodeKey-sorted, and each ref erases to an occurrence
   in the stream (so its key is one of the stream's keys — used to establish the strict prepend order). *)
Lemma ppkg_dir_sorted {p} (idx : GoIndex.Snap.SyntaxIndex p) (l : list (GoIndex.Snap.NodeRef p * GoIndex.SourceOccurrence)) :
  StronglySorted (fun x y => GoIndex.NodeKey_OT.lt (GoIndex.Snap.node_ref_key (fst x)) (GoIndex.Snap.node_ref_key (fst y))) l ->
  forall dir,
    StronglySorted (fun a b => GoIndex.NodeKey_OT.lt (GoIndex.Snap.node_ref_key (GoIndex.erase_ref a))
                                                     (GoIndex.Snap.node_ref_key (GoIndex.erase_ref b))) (bucket_of idx l dir)
    /\ (forall a, In a (bucket_of idx l dir) -> exists ro, In ro l /\ GoIndex.erase_ref a = fst ro).
Proof.
  induction l as [|ro l IH]; intro Hsort; intro dir.
  - unfold bucket_of. rewrite PMF.empty_o. split; [constructor | intros a []].
  - apply StronglySorted_inv in Hsort. destruct Hsort as [Hsort0 Hhd].
    specialize (IH Hsort0). destruct (IH dir) as [IHsort IHref]. split.
    + (* the bucket stays NodeKey-sorted *)
      rewrite (ppkg_fold_bucket_cons idx ro l dir).
      destruct (String.eqb (occ_pkg ro) dir) eqn:Ek; [ destruct (GoIndex.as_decl idx (fst ro)) as [dr|] eqn:Ed | ]; try exact IHsort.
      (* prepend this file's main ref — smaller key than every later main (stream sorted) *)
      assert (Her : GoIndex.erase_ref dr = fst ro) by exact (GoIndex.erase_as_kind idx (fst ro) GoIndex.KTopLevelDecl dr Ed).
      constructor; [ exact IHsort |].
      rewrite Forall_forall. intros a Ha. destruct (IHref a Ha) as [ro' [Hro' Hae]].
      rewrite Forall_forall in Hhd. rewrite Her, Hae. exact (Hhd ro' Hro').
    + (* every bucket ref erases to a stream occurrence *)
      rewrite (ppkg_fold_bucket_cons idx ro l dir).
      destruct (String.eqb (occ_pkg ro) dir) eqn:Ek; [ destruct (GoIndex.as_decl idx (fst ro)) as [dr|] eqn:Ed | ].
      * assert (Her : GoIndex.erase_ref dr = fst ro) by exact (GoIndex.erase_as_kind idx (fst ro) GoIndex.KTopLevelDecl dr Ed).
        intros a [Hah | Hat].
        -- subst a. exists ro. split; [left; reflexivity | exact Her].
        -- destruct (IHref a Hat) as [ro' [Hro' Hae]]. exists ro'. split; [right; exact Hro' | exact Hae].
      * intros a Ha. destruct (IHref a Ha) as [ro' [Hro' Hae]]. exists ro'. split; [right; exact Hro' | exact Hae].
      * intros a Ha. destruct (IHref a Ha) as [ro' [Hro' Hae]]. exists ro'. split; [right; exact Hro' | exact Hae].
Qed.
(** the WHOLE-program [DRMainRedeclared] PRECEDENCE + DISTINCTNESS: because every package bucket
    is the strictly-NodeKey-ascending subselection of the sorted visit stream ([ppkg_dir_sorted] over
    [prog_visit_key_sorted]), the related [earlier] main is strictly BEFORE the primary [later] in canonical
    occurrence order, and the two are DISTINCT.  So the canonical main a package keeps is unambiguous — the
    unique smallest-key one — and every duplicate diagnostic names a genuinely different, strictly-later main. *)
Lemma pkg_diags_dup_precedence {p} (idx : GoIndex.Snap.SyntaxIndex p) later earlier :
  In (DRMainRedeclared later earlier) (pkg_diags idx) ->
  GoIndex.NodeKey_OT.lt (GoIndex.Snap.node_ref_key (GoIndex.erase_ref earlier))
                        (GoIndex.Snap.node_ref_key (GoIndex.erase_ref later))
  /\ earlier <> later.
Proof.
  intro Hin. unfold pkg_diags in Hin.
  destruct (bucket_diags_elems_in _ _ _ _ _ Hin) as [dir [l [Hmt Hd]]].
  destruct (pkg_diag_of_bucket_dup_sound _ _ dir l Hmt later earlier Hd) as [rest [Hl Hlater]].
  assert (Hfind : PM.find dir (prog_package_refs idx) = Some l) by (apply PM.find_1; exact Hmt).
  assert (Hbeq : bucket_of idx (prog_visit p) dir = l).
  { unfold bucket_of. unfold prog_package_refs, prog_package_refs_from_visit in Hfind. rewrite Hfind. reflexivity. }
  destruct (ppkg_dir_sorted idx (prog_visit p) (prog_visit_key_sorted p) dir) as [Hsort _].
  rewrite Hbeq, Hl in Hsort. apply StronglySorted_inv in Hsort. destruct Hsort as [_ Hhd].
  rewrite Forall_forall in Hhd. pose proof (Hhd later Hlater) as Hlt.
  split; [ exact Hlt |].
  intro Heq. subst later.
  assert (Hne : ~ GoIndex.NodeKey_OT.eq (GoIndex.Snap.node_ref_key (GoIndex.erase_ref earlier))
                                        (GoIndex.Snap.node_ref_key (GoIndex.erase_ref earlier)))
    by (apply GoIndex.NodeKey_OT.lt_not_eq; exact Hlt).
  apply Hne. apply (proj2 (GoIndex.nodekey_compare_eq _ _)). reflexivity.
Qed.

(** the node-primary diagnostic report is in STRICTLY ascending NodeKey order.
    The chain: (1) the node-keyed INPUT keys are UNIQUE ([collect_node_input_nodup]) — proved from the expr
    keys' NoDup, the pkg keys' NoDup, and their DISJOINTNESS (an occurrence is an expression OR a decl, never
    both, by [node_ref_key_inj] + the kind refinement); (2) so every resulting bucket is a SINGLETON
    ([collect_node_buckets_singleton]); (3) hence the NodeKeyMap flattening is strictly key-ascending with no
    within-bucket ties ([semantic_diagnostics_node_strict]).  No project-authored sort. *)

(* nodekey strict-order lift over [option]: both anchored, strictly ascending (no ties). *)
Definition nk_lt_opt (oa ob : option GoIndex.NodeKey) : Prop :=
  match oa, ob with Some ka, Some kb => GoIndex.NodeKey_OT.lt ka kb | _, _ => False end.

Lemma nodekey_lt_irrefl : forall a, ~ GoIndex.NodeKey_OT.lt a a.
Proof.
  intros a H. assert (Hne : ~ GoIndex.NodeKey_OT.eq a a) by (apply GoIndex.NodeKey_OT.lt_not_eq; exact H).
  apply Hne. apply (proj2 (GoIndex.nodekey_compare_eq a a)). reflexivity.
Qed.

Lemma pm_elements_nodup_fst {A} (m : PM.t A) : NoDup (map fst (PM.elements m)).
Proof.
  pose proof (PM.elements_3w m) as H. generalize dependent (PM.elements m). intro l.
  induction l as [|[k e] l IH]; simpl; intro H; [constructor|].
  inversion H as [|x xs Hni Hnd Heq]; subst. constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as [[k' e'] [Hk Hin']]. cbn in Hk; subst k'.
    apply Hni, SetoidList.InA_alt. exists (k, e'). split; [ reflexivity | exact Hin' ].
  - apply IH; exact Hnd.
Qed.

(* NoDup of a disjoint append (stdlib has no direct form). *)
Lemma NoDup_app_disjoint {A} (l1 l2 : list A) :
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> In x l2 -> False) -> NoDup (l1 ++ l2).
Proof.
  intros H1 H2 Hd. induction l1 as [|a l1 IH]; [exact H2|].
  cbn [app]. apply NoDup_cons_iff in H1. destruct H1 as [Hni H1].
  apply NoDup_cons_iff. split.
  - intro Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
    + exact (Hni Hin).
    + exact (Hd a (or_introl eq_refl) Hin).
  - apply IH; [exact H1 | intros x Hx1 Hx2; exact (Hd x (or_intror Hx1) Hx2)].
Qed.

(* every key of the folded bucket map is one of the input keys. *)
Lemma bucket_find_in_keys {X} (kxs : list (GoIndex.NodeKey * X)) (k : GoIndex.NodeKey) (b : list X) :
  GoIndex.NodeKeyMapBase.MapsTo k b (fold_right bucket_add (GoIndex.NodeKeyMapBase.empty (list X)) kxs) ->
  In k (map fst kxs).
Proof.
  induction kxs as [|kx rest IH]; cbn [fold_right map].
  - intro Hmt. apply GoIndex.NodeKeyMapFacts.empty_mapsto_iff in Hmt. destruct Hmt.
  - unfold bucket_add. intro Hmt. apply GoIndex.NodeKeyMapFacts.add_mapsto_iff in Hmt.
    destruct Hmt as [[Hk _]|[_ Hmt]].
    + unfold GoIndex.NodeKey_OT.eq in Hk. subst k. left; reflexivity.
    + right. exact (IH Hmt).
Qed.

(* unique input keys => every bucket is a singleton. *)
Lemma nodup_keys_buckets_singleton {X} (kxs : list (GoIndex.NodeKey * X)) :
  NoDup (map fst kxs) ->
  forall k b, GoIndex.NodeKeyMapBase.MapsTo k b (fold_right bucket_add (GoIndex.NodeKeyMapBase.empty (list X)) kxs) ->
  length b = 1%nat.
Proof.
  induction kxs as [|kx rest IH]; intros Hnd k b Hmt.
  - cbn [fold_right] in Hmt. apply GoIndex.NodeKeyMapFacts.empty_mapsto_iff in Hmt. destruct Hmt.
  - cbn [map] in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hni Hnd].
    cbn [fold_right] in Hmt.
    set (M := fold_right bucket_add (GoIndex.NodeKeyMapBase.empty (list X)) rest) in *.
    unfold bucket_add in Hmt.
    apply GoIndex.NodeKeyMapFacts.add_mapsto_iff in Hmt. destruct Hmt as [[Hk Hb]|[_ Hmt]].
    + subst b. unfold GoIndex.NodeKey_OT.eq in Hk. subst k.
      assert (Hnf : nkm_find (fst kx) M = []).
      { unfold nkm_find. destruct (GoIndex.NodeKeyMapBase.find (fst kx) M) as [b'|] eqn:Ef; [|reflexivity].
        exfalso. apply Hni. apply GoIndex.NodeKeyMapFacts.find_mapsto_iff in Ef.
        exact (bucket_find_in_keys rest (fst kx) b' Ef). }
      rewrite Hnf. reflexivity.
    + exact (IH Hnd k b Hmt).
Qed.

(* singleton buckets, key-sorted elements => the flattening is STRICTLY key-ascending. *)
Lemma flat_map_snd_bucket_singleton_strict {X} (key : X -> option GoIndex.NodeKey)
    (els : list (GoIndex.NodeKey * list X)) :
  Sorted (@GoIndex.NodeKeyMapBase.lt_key (list X)) els ->
  (forall k b, In (k, b) els -> forall d, In d b -> key d = Some k) ->
  (forall k b, In (k, b) els -> length b = 1%nat) ->
  StronglySorted (fun a b => nk_lt_opt (key a) (key b)) (flat_map snd els).
Proof.
  induction els as [|[k b] rest IH]; intro Hs; intros Hkey Hlen; cbn [flat_map snd]; [constructor|].
  pose proof (Sorted_StronglySorted nkmap_lt_key_trans Hs) as Hss.
  apply StronglySorted_inv in Hss. destruct Hss as [_ Hhd]. apply Sorted_inv in Hs. destruct Hs as [Hs _].
  assert (Hb1 : length b = 1%nat) by exact (Hlen k b (or_introl eq_refl)).
  destruct b as [|d [|d' b']]; cbn [length] in Hb1; try discriminate Hb1.
  cbn [app]. constructor.
  - apply IH; [ exact Hs
    | intros k' b0 Hin' d0 Hd0; exact (Hkey k' b0 (or_intror Hin') d0 Hd0)
    | intros k' b0 Hin'; exact (Hlen k' b0 (or_intror Hin')) ].
  - rewrite Forall_forall. intros a'' Ha''.
    assert (Hkd : key d = Some k) by exact (Hkey k [d] (or_introl eq_refl) d (or_introl eq_refl)).
    apply in_flat_map in Ha''. destruct Ha'' as [[k'' b''] [Hin'' Ha'']]. cbn [snd] in Ha''.
    assert (Hkd'' : key a'' = Some k'') by exact (Hkey k'' b'' (or_intror Hin'') a'' Ha'').
    unfold nk_lt_opt. rewrite Hkd, Hkd''.
    rewrite Forall_forall in Hhd. exact (Hhd (k'', b'') Hin'').
Qed.

Lemma bucket_flatten_singleton_strict {X} (key : X -> option GoIndex.NodeKey) (kxs : list (GoIndex.NodeKey * X))
    (Hself : forall kd, In kd kxs -> key (snd kd) = Some (fst kd))
    (Hsingle : forall k b, GoIndex.NodeKeyMapBase.MapsTo k b
                 (fold_right bucket_add (GoIndex.NodeKeyMapBase.empty (list X)) kxs) -> length b = 1%nat) :
  StronglySorted (fun a b => nk_lt_opt (key a) (key b)) (bucket_flatten kxs).
Proof.
  unfold bucket_flatten. apply flat_map_snd_bucket_singleton_strict.
  - apply GoIndex.NodeKeyMapBase.elements_3.
  - intros k b Hin d Hd. apply (bucket_value_key key kxs Hself k b); [
      apply GoIndex.NodeKeyMapFacts.elements_mapsto_iff, InA_alt; exists (k, b);
        split; [split; reflexivity | exact Hin] | exact Hd ].
  - intros k b Hin. apply (Hsingle k b).
    apply GoIndex.NodeKeyMapFacts.elements_mapsto_iff, InA_alt. exists (k, b);
      split; [split; reflexivity | exact Hin].
Qed.

(* the tail duplicate-main keys of one package bucket are NoDup (the bucket is a strictly-sorted visit stream). *)
Lemma bucket_dup_keys_nodup {p} (idx : GoIndex.Snap.SyntaxIndex p) (kv : string * list (GoIndex.DeclRef p)) :
  PM.find (fst kv) (prog_package_refs idx) = Some (snd kv) -> NoDup (bucket_dup_keys (snd kv)).
Proof.
  intro Hfind.
  destruct (ppkg_dir_sorted idx (prog_visit p) (prog_visit_key_sorted p) (fst kv)) as [Hsort _].
  assert (Hb : bucket_of idx (prog_visit p) (fst kv) = snd kv)
    by (unfold bucket_of; unfold prog_package_refs, prog_package_refs_from_visit in Hfind; rewrite Hfind; reflexivity).
  rewrite Hb in Hsort. destruct (snd kv) as [|d1 rest]; cbn [bucket_dup_keys]; [constructor|].
  apply StronglySorted_inv in Hsort. destruct Hsort as [Hsort _].
  apply (StronglySorted_NoDup GoIndex.NodeKey_OT.lt); [ exact nodekey_lt_irrefl |].
  apply (StronglySorted_map GoIndex.NodeKey_OT.lt (fun dk => GoIndex.Snap.node_ref_key (GoIndex.erase_ref dk))).
  exact Hsort.
Qed.

Lemma pkg_node_keys_nodup {p} (idx : GoIndex.Snap.SyntaxIndex p) : NoDup (node_keys (pkg_diags idx)).
Proof.
  rewrite pkg_node_keys_spec.
  apply (nodup_flat_map_tag (fun kv => bucket_dup_keys (snd kv))
           (fun k => fp_parent (GoIndex.nk_file k)) (fun kv => fst kv)).
  - intros kv Hin. apply (bucket_dup_keys_nodup idx kv).
    apply PM.find_1, PMF.elements_mapsto_iff, InA_alt. exists kv. split; [split; reflexivity | exact Hin].
  - intros kv k Hin Hk.
    assert (Hfind : PM.find (fst kv) (prog_package_refs idx) = Some (snd kv))
      by (apply PM.find_1, PMF.elements_mapsto_iff, InA_alt; exists kv; split; [split; reflexivity | exact Hin]).
    unfold bucket_dup_keys in Hk. destruct (snd kv) as [|d1 rest] eqn:Esnd; [destruct Hk|].
    apply in_map_iff in Hk. destruct Hk as [dk [Hdk Hdkin]].
    rewrite <- Hdk, GoIndex.Snap.node_ref_key_eq. cbn [GoIndex.nk_file].
    apply (prog_package_refs_belongs idx (fst kv) (d1 :: rest)); [ exact Hfind | right; exact Hdkin ].
  - apply pm_elements_nodup_fst.
Qed.

(* each expression-diagnostic key belongs to an EXPRESSION occurrence; each pkg-diagnostic key to a DECL
   occurrence — so the two key sets are disjoint (no occurrence is both). *)
Lemma occ_expr_diags_key_kind {p} (idx : GoIndex.Snap.SyntaxIndex p) outer ro :
  forall d, In d (occ_expr_diags idx outer ro) ->
  diag_node_key d = Some (GoIndex.Snap.node_ref_key (fst ro)) /\
  GoIndex.occurrence_kind (GoIndex.Snap.source_occurrence_of_ref (fst ro)) = GoIndex.KExpression.
Proof.
  intros d Hin. unfold occ_expr_diags in Hin.
  destruct (GoIndex.as_expr idx (fst ro)) as [er|] eqn:Ea; [|destruct Hin].
  assert (Her : GoIndex.erase_ref er = fst ro) by exact (GoIndex.erase_as_kind idx (fst ro) GoIndex.KExpression er Ea).
  assert (Hk : GoIndex.occurrence_kind (GoIndex.Snap.source_occurrence_of_ref (fst ro)) = GoIndex.KExpression)
    by (rewrite <- Her; exact (GoIndex.noderefof_kind er)).
  destruct (GoIndex.view_expr (snd ro)) as [e|]; [|destruct Hin].
  destruct (local_conv_failure e) as [[t ci]|].
  - destruct (conversion_target_ref idx er) as [tr|]; [|destruct Hin].
    destruct (conversion_operand_ref idx er) as [opr|]; [|destruct Hin].
    cbn [In] in Hin. destruct Hin as [<-|[]].
    split; [ cbn [diag_node_key diagnostic_primary]; rewrite Her; reflexivity | exact Hk ].
  - destruct (arg_default_failure (snd ro) e) as [[c dt]|]; [|destruct Hin].
    cbn [In] in Hin. destruct Hin as [<-|[]].
    split; [ cbn [diag_node_key diagnostic_primary]; rewrite Her; reflexivity | exact Hk ].
Qed.

Lemma expr_node_key_has_kind {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  forall k, In k (node_keys (expr_diags idx)) ->
  exists r : GoIndex.Snap.NodeRef p,
    GoIndex.Snap.node_ref_key r = k /\
    GoIndex.occurrence_kind (GoIndex.Snap.source_occurrence_of_ref r) = GoIndex.KExpression.
Proof.
  intros k Hin. unfold node_keys in Hin. apply in_flat_map in Hin. destruct Hin as [d [Hd Hk]].
  destruct (diag_node_key d) as [k0|] eqn:Edk; cbn [In] in Hk; [|destruct Hk].
  destruct Hk as [Heq|[]]. subst k0.
  rewrite expr_diags_eq_spec in Hd. apply in_flat_map in Hd. destruct Hd as [roc [_ Hd]].
  destruct (occ_expr_diags_key_kind idx (snd roc) (fst roc) d Hd) as [Hdk2 Hkind].
  rewrite Edk in Hdk2. injection Hdk2 as Hkk.
  exists (fst (fst roc)). split; [ exact (eq_sym Hkk) | exact Hkind ].
Qed.

Lemma pkg_node_key_has_kind {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  forall k, In k (node_keys (pkg_diags idx)) ->
  exists r : GoIndex.Snap.NodeRef p,
    GoIndex.Snap.node_ref_key r = k /\
    GoIndex.occurrence_kind (GoIndex.Snap.source_occurrence_of_ref r) = GoIndex.KTopLevelDecl.
Proof.
  intros k Hin. rewrite pkg_node_keys_spec in Hin.
  apply in_flat_map in Hin. destruct Hin as [kv [_ Hin]].
  unfold bucket_dup_keys in Hin. destruct (snd kv) as [|d1 rest]; [destruct Hin|].
  apply in_map_iff in Hin. destruct Hin as [dk [Hdk _]].
  exists (GoIndex.erase_ref dk). split; [ exact Hdk | exact (GoIndex.noderefof_kind dk) ].
Qed.

Lemma expr_pkg_node_keys_disjoint {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  forall k, In k (node_keys (expr_diags idx)) -> In k (node_keys (pkg_diags idx)) -> False.
Proof.
  intros k He Hp.
  destruct (expr_node_key_has_kind idx k He) as [re [Hre Hke]].
  destruct (pkg_node_key_has_kind idx k Hp) as [rd [Hrd Hkd]].
  assert (Hreq : re = rd) by (apply GoIndex.Snap.node_ref_key_inj; rewrite Hre, Hrd; reflexivity).
  subst rd. rewrite Hke in Hkd. discriminate Hkd.
Qed.

(** the node-keyed diagnostic INPUT has UNIQUE keys (expr NoDup + pkg NoDup + disjoint). *)
Theorem collect_node_input_nodup {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  NoDup (node_keys (expr_diags idx ++ pkg_diags idx)).
Proof.
  rewrite node_keys_app. apply NoDup_app_disjoint;
    [ apply expr_node_keys_nodup | apply pkg_node_keys_nodup | apply expr_pkg_node_keys_disjoint ].
Qed.

(** every node-keyed diagnostic BUCKET is a SINGLETON (from the unique input keys). *)
Theorem collect_node_buckets_singleton {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  forall k b, GoIndex.NodeKeyMapBase.MapsTo k b
    (fold_right bucket_add (GoIndex.NodeKeyMapBase.empty (list (DiagnosticReason p)))
       (node_keyed (expr_diags idx ++ pkg_diags idx))) -> length b = 1%nat.
Proof.
  apply nodup_keys_buckets_singleton. rewrite node_keys_eq. apply collect_node_input_nodup.
Qed.

(** the WHOLE report's node-primary diagnostics are in STRICTLY ascending NodeKey order (path
    then local id): the NodeKeyMap flattening IS the canonical enumeration; with unique keys / singleton buckets
    there are NO ties.  No project-authored sort. *)
Theorem semantic_diagnostics_node_strict {p} (idx : GoIndex.Snap.SyntaxIndex p) :
  StronglySorted (fun a b => nk_lt_opt (diag_node_key a) (diag_node_key b))
                 (bucket_flatten (node_keyed (expr_diags idx ++ pkg_diags idx))).
Proof.
  apply bucket_flatten_singleton_strict; [ apply node_keyed_self | apply collect_node_buckets_singleton ].
Qed.

Lemma pkg_diags_package {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall d, In d (pkg_diags idx) -> diag_is_package d = true.
Proof. intros d Hin; apply (pkg_diags_family idx d Hin). Qed.
Lemma pkg_diags_not_typing {p} (idx : GoIndex.Snap.SyntaxIndex p) : forall d, In d (pkg_diags idx) -> diag_is_typing d = false.
Proof. intros d Hin; apply (pkg_diags_family idx d Hin). Qed.

(** the diagnostic-derived TYPING flag is exactly "not program-typed"; the PACKAGE flag (when typed) is exactly
    "not one-main-per-package".  So the legacy class is a PROJECTION of the diagnostics, matching the decision. *)
Lemma existsb_typing_semantic (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p) :
  existsb diag_is_typing (semantic_diagnostics p idx) = negb (program_typedb p).
Proof.
  rewrite (existsb_In_eq _ _ _ (collect_diagnostics_In idx)), existsb_app.
  rewrite (existsb_all_false diag_is_typing (pkg_diags idx) (pkg_diags_not_typing idx)), Bool.orb_false_r.
  rewrite (existsb_all_true diag_is_typing (expr_diags idx) (expr_diags_typing idx)).
  destruct (expr_diags idx) as [|d ds] eqn:E.
  - rewrite (proj1 (expr_diags_empty_iff idx) E). reflexivity.
  - destruct (program_typedb p) eqn:Ht; [ | reflexivity ].
    exfalso. pose proof (proj2 (expr_diags_empty_iff idx) Ht) as Hc. rewrite Hc in E; discriminate E.
Qed.
Lemma existsb_package_semantic (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p) :
  existsb diag_is_package (semantic_diagnostics p idx) = negb (source_spec_package_rules_b p).
Proof.
  rewrite (existsb_In_eq _ _ _ (collect_diagnostics_In idx)), existsb_app.
  rewrite (existsb_all_false diag_is_package (expr_diags idx) (expr_diags_not_package idx)), Bool.orb_false_l.
  rewrite (existsb_all_true diag_is_package (pkg_diags idx) (pkg_diags_package idx)).
  destruct (pkg_diags idx) as [|d ds] eqn:E.
  - rewrite (proj1 (pkg_diags_empty_iff idx) E). reflexivity.
  - destruct (source_spec_package_rules_b p) eqn:Ht; [ | reflexivity ].
    exfalso. pose proof (proj2 (pkg_diags_empty_iff idx) Ht) as Hc. rewrite Hc in E; discriminate E.
Qed.
(* the SEMANTIC report never contains a build-output diagnostic (only expression / package reasons) — so the
   build-output class fires ONLY through the command-ordered preflight branch, never the semantic branch. *)
Lemma existsb_build_output_semantic (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p) :
  existsb diag_is_build_output (semantic_diagnostics p idx) = false.
Proof.
  rewrite (existsb_In_eq _ _ _ (collect_diagnostics_In idx)), existsb_app.
  rewrite (existsb_all_false diag_is_build_output (expr_diags idx)
             (fun d Hin => diag_typing_not_build d (expr_diags_typing idx d Hin))),
          (existsb_all_false diag_is_build_output (pkg_diags idx)
             (fun d Hin => diag_package_not_build d (pkg_diags_package idx d Hin))).
  reflexivity.
Qed.

(** the pinned cmd/go DEFAULT-OUTPUT-NAME string layer.  Faithful to pinned Go 1.23.12
    ([go env GOVERSION] = go1.23.12) [cmd/go/internal/load/pkg.go]: [isVersionElement] (1288-1298) and
    [exeFromImportPath] (1675-1685) — the [DefaultExecName] path taken by a `go build ./...` (non-CmdlineFiles)
    build.  Pure functions over the import-path STRING; NO filesystem path cleaning (inputs are canonical
    import paths, per the contract).  Empirically confirmed against the pinned image (see SOURCE_FOREST_STATUS). *)

Local Open Scope string_scope.

Definition ascii_is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in andb (Nat.leb 48 n) (Nat.leb n 57).

(* every byte of [s] is a decimal digit. *)
Fixpoint str_all_digits (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => andb (ascii_is_digit c) (str_all_digits s')
  end.

(* [isVersionElement] (pkg.go:1288-1298): [len>=2], [s[0]='v'], [s[1]<>'0'], not ([s[1]='1' /\ len=2]), and
   every byte [s[1..]] is a decimal digit.  A single [andb] chain (no [if]) for a clean reflection. *)
Definition is_version_element (s : string) : bool :=
  match s with
  | String c0 (String c1 rest) =>
      andb (Ascii.eqb c0 "v"%char)
        (andb (negb (Ascii.eqb c1 "0"%char))
          (andb (negb (andb (Ascii.eqb c1 "1"%char)
                            (match rest with EmptyString => true | _ => false end)))
                (str_all_digits (String c1 rest))))
  | _ => false
  end.

(* [exeFromImportPath] (pkg.go:1675-1685) over the import-path COMPONENT LIST: the LAST component, dropped to
   the PREVIOUS component exactly when the last is a version element AND there is an earlier component. *)
Definition default_exec_name_c (comps : list string) : string :=
  match comps with
  | _ :: _ :: _ =>
      let final := List.last comps ""%string in
      if is_version_element final then List.last (List.removelast comps) ""%string else final
  | _ => List.last comps ""%string
  end.

(** reflection — [is_version_element] agrees with the pinned structural predicate. *)
Lemma is_version_element_spec : forall s,
  is_version_element s = true <->
  (exists c1 rest, s = String "v"%char (String c1 rest)
                   /\ c1 <> "0"%char
                   /\ ~ (c1 = "1"%char /\ rest = EmptyString)
                   /\ str_all_digits (String c1 rest) = true).
Proof.
  intros s. split.
  - destruct s as [|c0 [|c1 rest]]; cbn [is_version_element]; try discriminate.
    intro H.
    apply andb_true_iff in H; destruct H as [Hv H].
    apply andb_true_iff in H; destruct H as [H0 H].
    apply andb_true_iff in H; destruct H as [H1 Hd].
    apply Ascii.eqb_eq in Hv; subst c0.
    exists c1, rest. split; [reflexivity | split; [ | split ] ].
    + apply negb_true_iff, Ascii.eqb_neq in H0. exact H0.
    + apply negb_true_iff, andb_false_iff in H1. intros [Hc1 Hre]. destruct H1 as [H1|H1].
      * apply Ascii.eqb_neq in H1. exact (H1 Hc1).
      * subst rest. cbn in H1. discriminate H1.
    + exact Hd.
  - intros [c1 [rest [Hs [H0 [H1 Hd]]]]]. subst s. cbn [is_version_element].
    apply andb_true_iff; split; [ apply Ascii.eqb_refl |].
    apply andb_true_iff; split.
    + apply negb_true_iff. apply Ascii.eqb_neq. exact H0.
    + apply andb_true_iff; split; [ | exact Hd ].
      apply negb_true_iff, andb_false_iff.
      destruct (Ascii.eqb c1 "1"%char) eqn:E1; [ | left; reflexivity ].
      apply Ascii.eqb_eq in E1. subst c1. right. destruct rest as [|rc rr].
      * exfalso. apply H1. split; reflexivity.
      * reflexivity.
Qed.

(** is_version_element reflection FIXTURES (pinned Go 1.23.12, SOURCE_FOREST_STATUS-confirmed). *)
Example ive_v0   : is_version_element "v0"   = false. Proof. reflexivity. Qed.
Example ive_v00  : is_version_element "v00"  = false. Proof. reflexivity. Qed.
Example ive_v01  : is_version_element "v01"  = false. Proof. reflexivity. Qed.
Example ive_v05  : is_version_element "v05"  = false. Proof. reflexivity. Qed.
Example ive_v1   : is_version_element "v1"   = false. Proof. reflexivity. Qed.
Example ive_v2   : is_version_element "v2"   = true.  Proof. reflexivity. Qed.
Example ive_v3   : is_version_element "v3"   = true.  Proof. reflexivity. Qed.
Example ive_v10  : is_version_element "v10"  = true.  Proof. reflexivity. Qed.
Example ive_v100 : is_version_element "v100" = true.  Proof. reflexivity. Qed.
Example ive_v1x  : is_version_element "v1x"  = false. Proof. reflexivity. Qed.
Example ive_v2x  : is_version_element "v2x"  = false. Proof. reflexivity. Qed.
Example ive_V2   : is_version_element "V2"   = false. Proof. reflexivity. Qed.
Example ive_v    : is_version_element "v"    = false. Proof. reflexivity. Qed.

(** default_exec_name_c FIXTURES — the exact pinned import-path COMPONENTS -> exe-name rule. *)
Example den_root    : default_exec_name_c ["example.com"; "m"]               = "m".       Proof. reflexivity. Qed.
Example den_sub     : default_exec_name_c ["example.com"; "m"; "sub"]        = "sub".     Proof. reflexivity. Qed.
Example den_ab      : default_exec_name_c ["example.com"; "m"; "a"; "b"]     = "b".       Proof. reflexivity. Qed.
Example den_av2     : default_exec_name_c ["example.com"; "m"; "a"; "v2"]    = "a".       Proof. reflexivity. Qed.
Example den_v2      : default_exec_name_c ["example.com"; "m"; "v2"]         = "m".       Proof. reflexivity. Qed.
Example den_maingo  : default_exec_name_c ["example.com"; "main.go"]         = "main.go". Proof. reflexivity. Qed.
Example den_gomod   : default_exec_name_c ["example.com"; "go.mod"]          = "go.mod".  Proof. reflexivity. Qed.
Example den_sub_v10 : default_exec_name_c ["example.com"; "m"; "sub"; "v10"] = "sub".     Proof. reflexivity. Qed.

(** the exact cmd/go IMPORT PATH and default EXECUTABLE NAME of a selected package, built
    COMPOSITIONALLY from the lower-layer component authorities: the [ModulePath] segments
    ([ModulePath.mp_segments]) then the package directory components ([FilePath.dir_components]).  The exec
    name is cmd/go's component rule applied DIRECTLY to those components (NO string reparse); the import-path
    STRING is their "/"-join (the ONE string bridge/view).  Each component is nonempty, so the exec name is a
    nonempty component ([default_exec_name_nonempty]).  This replaces the deleted character-level slash/scan
    forest — the nonempty/slash-free facts now live in [ModulePath]/[FilePath] and are merely composed here. *)

(* the import-path COMPONENTS: the module segments then the package directory components. *)
Definition package_import_components (ms : ModuleSpec) (dir : string) : list string :=
  ModulePath.mp_segments (module_path ms) ++ FilePath.dir_components dir.

(* the default executable name: cmd/go's rule DIRECTLY over the import-path components (no reparse). *)
Definition default_exec_name (ms : ModuleSpec) (dir : string) : string :=
  default_exec_name_c (package_import_components ms dir).

(* the exact cmd/go import-path STRING: the "/"-join of the components (the ONE string bridge/view). *)
Definition package_import_path (ms : ModuleSpec) (dir : string) : string :=
  String.concat "/" (package_import_components ms dir).

(* generic "/"-join shape helpers (list-of-string; no character scan). *)
Lemma sapp_assoc : forall a b c, ((a ++ b) ++ c)%string = (a ++ (b ++ c))%string.
Proof. intros a b c. induction a as [|x a' IH]; [ reflexivity | cbn [append]; rewrite IH; reflexivity ]. Qed.

Lemma concat_cons2 : forall sep x y rest,
  String.concat sep (x :: y :: rest) = (x ++ sep ++ String.concat sep (y :: rest))%string.
Proof. intros sep x y rest. reflexivity. Qed.

(* the "/"-join of the concatenation of two NONEMPTY component lists splits at the join. *)
Lemma concat_app_join : forall (A B : list string), A <> [] -> B <> [] ->
  String.concat "/" (A ++ B) = (String.concat "/" A ++ "/" ++ String.concat "/" B)%string.
Proof.
  intros A. induction A as [|a A' IH]; intros B HA HB; [ contradiction |].
  destruct A' as [|a2 A''].
  - cbn [app]. destruct B as [|b B']; [ contradiction | reflexivity ].
  - cbn [app].
    rewrite (concat_cons2 "/"%string a a2 (A'' ++ B)).
    rewrite app_comm_cons.
    rewrite (IH B ltac:(discriminate) HB).
    rewrite (concat_cons2 "/"%string a a2 A'').
    rewrite <- !sapp_assoc. reflexivity.
Qed.

(* the ONE string bridge: the root key "" imports as the module path; a nested key appends "/" then the dir. *)
Lemma package_import_path_root : forall ms, package_import_path ms "" = mp_string (module_path ms).
Proof.
  intro ms. unfold package_import_path, package_import_components.
  cbn [FilePath.dir_components String.eqb]. rewrite app_nil_r, ModulePath.mp_string_concat. reflexivity.
Qed.

Lemma package_import_path_nested : forall ms dir, dir <> ""%string ->
  package_import_path ms dir = (mp_string (module_path ms) ++ "/" ++ dir)%string.
Proof.
  intros ms dir Hd. unfold package_import_path, package_import_components, FilePath.dir_components.
  destruct (String.eqb dir ""%string) eqn:E; [ apply String.eqb_eq in E; contradiction |].
  rewrite (concat_app_join _ _ (ModulePath.mp_segments_nonempty (module_path ms))
                               (FilePath.split_slash_nonempty dir)).
  rewrite ModulePath.mp_string_concat, FilePath.split_slash_concat. reflexivity.
Qed.

(* the component list is nonempty (the module always has >= 1 segment). *)
Lemma package_import_components_nonempty : forall ms dir, package_import_components ms dir <> [].
Proof.
  intros ms dir. unfold package_import_components. intro Hc.
  apply (ModulePath.mp_segments_nonempty (module_path ms)).
  destruct (ModulePath.mp_segments (module_path ms)); [ reflexivity | discriminate Hc ].
Qed.

Lemma last_In : forall (l : list string), l <> [] -> In (List.last l ""%string) l.
Proof.
  induction l as [|x l IH]; intro H; [ contradiction |].
  destruct l as [|y l']; [ left; reflexivity |].
  right. apply IH. discriminate.
Qed.

Lemma removelast_In : forall (l : list string) x, In x (List.removelast l) -> In x l.
Proof.
  induction l as [|a l IH]; intros x Hin.
  - cbn [List.removelast] in Hin. exact Hin.
  - destruct l as [|b l'].
    + cbn [List.removelast] in Hin. destruct Hin.
    + cbn [List.removelast] in Hin. destruct Hin as [->|Hin]; [ left; reflexivity | right; apply IH; exact Hin ].
Qed.

(* the exec name IS one of the components (the last, or the previous when the last is a version element). *)
Lemma default_exec_name_c_in : forall comps, comps <> [] -> In (default_exec_name_c comps) comps.
Proof.
  intros comps Hne. unfold default_exec_name_c. destruct comps as [|a [|b rest]]; [ contradiction | |].
  - cbn [List.last]. left; reflexivity.
  - destruct (is_version_element (List.last (a :: b :: rest) ""%string)).
    + apply removelast_In, last_In. cbn [List.removelast]. discriminate.
    + apply last_In. discriminate.
Qed.

(** the DEFAULT EXECUTABLE NAME is NEVER empty: it is one of the import path's components, and every
    component — a [ModulePath] segment or a package DIRECTORY component of some represented file — is
    nonempty (from the composed lower-layer authorities), so cmd/go always writes a nonempty default output. *)
Lemma default_exec_name_nonempty : forall ms dir,
  (dir = ""%string \/ exists fp, fp_parent fp = dir) ->
  default_exec_name ms dir <> ""%string.
Proof.
  intros ms dir Hdir. unfold default_exec_name.
  assert (Hall : forall s, In s (package_import_components ms dir) -> s <> ""%string).
  { intros s Hs. unfold package_import_components in Hs. apply in_app_or in Hs. destruct Hs as [Hs|Hs].
    - exact (ModulePath.mp_segments_nonempty_elt (module_path ms) s Hs).
    - destruct Hdir as [Hd0 | [fp Hfp]].
      + subst dir. unfold FilePath.dir_components in Hs. cbn [String.eqb] in Hs. destruct Hs.
      + apply (FilePath.parent_dir_components_nonempty fp s). rewrite Hfp. exact Hs. }
  apply Hall. apply default_exec_name_c_in. apply package_import_components_nonempty.
Qed.

(* split the joined import-path string at the module boundary: it recovers the package DIRECTORY components as
   the suffix after the (fixed) module-string components — the reusable exactness lemma the injectivity proof
   below rests on.  The module prefix is left as the opaque [FilePath.split_slash] of the module string, so the
   cancellation needs no cross-module segment identity. *)
Lemma split_import_path_dir_components : forall ms dir,
  FilePath.split_slash (package_import_path ms dir)
    = (FilePath.split_slash (mp_string (module_path ms)) ++ FilePath.dir_components dir)%list.
Proof.
  intros ms dir. destruct (String.eqb dir ""%string) eqn:E.
  - apply String.eqb_eq in E; subst dir.
    rewrite package_import_path_root. unfold FilePath.dir_components.
    cbn [String.eqb]. rewrite app_nil_r. reflexivity.
  - assert (Hne : dir <> ""%string) by (apply String.eqb_neq; exact E).
    rewrite (package_import_path_nested ms dir Hne). unfold FilePath.dir_components. rewrite E.
    change ((mp_string (module_path ms) ++ "/" ++ dir)%string)
      with ((mp_string (module_path ms) ++ String "/"%char dir)%string).
    apply FilePath.split_slash_app.
Qed.

(* a short list-app left cancellation over string components (a leaf fact; not a collection algorithm). *)
Lemma slist_app_inv_head : forall (l l1 l2 : list string), (l ++ l1)%list = (l ++ l2)%list -> l1 = l2.
Proof.
  induction l as [|x l IH]; intros l1 l2 H; [ exact H |].
  cbn [app] in H. injection H as H. apply IH. exact H.
Qed.

(** the cmd/go import PATH is INJECTIVE in the package directory under a fixed module: two directory keys that
    produce the same import-path string are equal.  Proved THROUGH the component authority — split the joined
    string, cancel the common module-string prefix to obtain equal [FilePath.dir_components], then recover the
    directory key with [FilePath.dir_components_concat].  No basename/dirname reparse re-enters here. *)
Theorem package_import_path_inj : forall ms dir1 dir2,
  package_import_path ms dir1 = package_import_path ms dir2 -> dir1 = dir2.
Proof.
  intros ms dir1 dir2 H.
  assert (Hd : FilePath.dir_components dir1 = FilePath.dir_components dir2).
  { pose proof (split_import_path_dir_components ms dir1) as S1.
    pose proof (split_import_path_dir_components ms dir2) as S2.
    rewrite H in S1. rewrite S1 in S2. apply slist_app_inv_head in S2. exact S2. }
  pose proof (FilePath.dir_components_concat dir1) as C1.
  rewrite Hd, (FilePath.dir_components_concat dir2) in C1. exact (eq_sym C1).
Qed.

(** import-path DETERMINISM: an equal module spec and equal package directory key give the SAME import path —
    the direct API companion to [package_import_path_inj].  The whole-program [package_import_path_InputEqual]
    below is a CONSEQUENCE of this (equal program inputs give an equal module path), not a substitute for it. *)
Theorem package_import_path_deterministic : forall ms1 ms2 dir1 dir2,
  ms1 = ms2 -> dir1 = dir2 -> package_import_path ms1 dir1 = package_import_path ms2 dir2.
Proof. intros ms1 ms2 dir1 dir2 Hm Hd; subst; reflexivity. Qed.

(** the package set the literal `./...` pattern SELECTS: exactly the domain of the
    one-pass [package_summaries] PackageMap (= the distinct parent directories of the represented FilePaths).
    The canonical enumeration is the standard map's [elements] (a DERIVED list, not a second authority); NO
    list-backed set. *)

Definition selected_packages (p : GoProgram) : PM.t PackageSummary := package_summaries (prog_files p).
Definition selected_package_keys (p : GoProgram) : list string := map fst (PM.elements (selected_packages p)).
Definition selected_package_count (p : GoProgram) : nat := length (selected_package_keys p).

(** domain exactness: a directory is a selected package IFF some represented file has that parent dir. *)
Lemma selected_iff_file : forall p dir,
  PM.In dir (selected_packages p) <->
  (exists b, In b (GoAST.file_bindings (prog_files p)) /\ fp_parent (fst b) = dir).
Proof.
  intros p dir. unfold selected_packages. split.
  - apply package_no_empty.
  - intros [b [Hin Heq]].
    assert (Hmem : list_dir_mem dir (GoAST.file_bindings (prog_files p)) = true).
    { unfold list_dir_mem. apply existsb_exists. exists b. split; [ exact Hin | rewrite Heq; apply String.eqb_refl ]. }
    exists (mkPkgSummary (pkg_main_count dir (prog_files p))).
    apply PMF.find_mapsto_iff. rewrite package_summaries_find, Hmem. reflexivity.
Qed.

(** the empty program selects ZERO packages. *)
Lemma selected_count_empty : forall ms, selected_package_count (empty_program ms) = 0%nat.
Proof.
  intro ms. unfold selected_package_count, selected_package_keys, selected_packages.
  assert (He : PM.Empty (package_summaries (prog_files (empty_program ms)))).
  { intros k e Hmt. apply PMF.find_mapsto_iff in Hmt.
    cbn [prog_files empty_program] in Hmt. rewrite (package_summaries_empty k) in Hmt. discriminate. }
  rewrite (proj1 (PMP.elements_Empty _) He). reflexivity.
Qed.

(** one directory coalesces to ONE selected package: two files sharing a parent directory land on the
    SAME (unique) map key.  (Distinct parents land on distinct keys — intrinsic to the map's key identity.) *)
Lemma selected_one_dir : forall p b1 b2,
  In b1 (GoAST.file_bindings (prog_files p)) -> In b2 (GoAST.file_bindings (prog_files p)) ->
  fp_parent (fst b1) = fp_parent (fst b2) ->
  PM.In (fp_parent (fst b1)) (selected_packages p).
Proof.
  intros p b1 b2 Hin1 _ _. apply selected_iff_file. exists b1. split; [ exact Hin1 | reflexivity ].
Qed.

(** the FRESH ROOT LAYOUT foundation + the conflict AUDIT.  A fresh materialization of the
    DirectoryImage has, at its ROOT: the one [go.mod], each root-level source file, and one directory per
    distinct first path-component of a nested source file.  [FreshRootEntryKind] tags a root entry.

    THE AUDIT: can one root key be BOTH a regular file and a directory?  NO — by the intrinsic FilePath
    grammar.  A directory component is [component_ok] = [a-z][a-z0-9]* (DOT-FREE); a root source basename is
    [filename_ok] (ends ".go", DOTTED) and the module file is "go.mod" (DOTTED).  So a directory key can never
    equal a source-file key or "go.mod": the layout is conflict-free by construction — no rejecting validation
    is needed (the impossibility is PROVED below, [dir_component_neq_gomod] and the dot lemmas). *)

Inductive FreshRootEntryKind : Type :=
| FREGoMod
| FRESourceFile (path : FilePath)
| FREDirectory.

(* the FIRST path component of a path string (before the first '/'); the whole name for a root-level file. *)
Fixpoint first_component (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => if Ascii.eqb c "/"%char then EmptyString else String c (first_component s')
  end.

Fixpoint contains_dot (s : string) : bool :=
  match s with EmptyString => false | String c s' => orb (Ascii.eqb c "."%char) (contains_dot s') end.

Lemma contains_dot_app : forall a b, contains_dot (a ++ b) = orb (contains_dot a) (contains_dot b).
Proof. induction a as [|c a IH]; intro b; simpl; [reflexivity | rewrite IH; apply Bool.orb_assoc]. Qed.

(* a lowercase-or-digit byte is never '.'; a lowercase byte is never '.'. *)
Lemma is_lower_digit_no_dot : forall c, FilePath.is_lower_digit c = true -> Ascii.eqb c "."%char = false.
Proof.
  intros c H. apply Bool.not_true_iff_false. intro E. apply Ascii.eqb_eq in E. subst c. vm_compute in H. discriminate H.
Qed.

Lemma tail_ok_no_dot : forall s, FilePath.tail_ok s = true -> contains_dot s = false.
Proof.
  induction s as [|c s' IH]; intro H; [reflexivity|].
  cbn [FilePath.tail_ok] in H. apply andb_true_iff in H. destruct H as [Hc Hs].
  cbn [contains_dot]. rewrite (is_lower_digit_no_dot c Hc); cbn [orb]. exact (IH Hs).
Qed.

Lemma component_ok_no_dot : forall s, FilePath.component_ok s = true -> contains_dot s = false.
Proof.
  intros [|c s'] H; [discriminate H|].
  cbn [FilePath.component_ok] in H. apply andb_true_iff in H. destruct H as [Hc Hs].
  cbn [contains_dot].
  assert (Hne : Ascii.eqb c "."%char = false).
  { apply Bool.not_true_iff_false. intro E. apply Ascii.eqb_eq in E. subst c. vm_compute in Hc. discriminate Hc. }
  rewrite Hne; cbn [orb]. exact (tail_ok_no_dot s' Hs).
Qed.

(* a dot-free directory key can never equal the DOTTED module file name "go.mod". *)
Lemma dir_component_neq_gomod : forall d, FilePath.dir_component_ok d = true -> d <> "go.mod".
Proof.
  intros d Hd Heq. subst d. unfold FilePath.dir_component_ok in Hd. apply andb_true_iff in Hd. destruct Hd as [Hc _].
  pose proof (component_ok_no_dot _ Hc) as Hnd. vm_compute in Hnd. discriminate Hnd.
Qed.

(** file-vs-directory key disjointness: a root source basename is [filename_ok] (ends
    ".go", hence DOTTED), so it can never equal a dot-free directory component key.  Completes the audit. *)

Lemma substring_full : forall s, String.substring 0 (String.length s) s = s.
Proof. induction s as [|c s IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma substring_split : forall k s, (k <= String.length s)%nat ->
  s = (String.substring 0 k s ++ String.substring k (String.length s - k) s)%string.
Proof.
  intros k s; revert k; induction s as [|c s IH]; intros [|k'] Hk.
  - reflexivity.
  - simpl in Hk; lia.
  - change (String.substring 0 0 (String c s)) with EmptyString.
    rewrite Nat.sub_0_r, substring_full. reflexivity.
  - cbn [String.substring String.length Nat.sub String.append]. f_equal. apply IH. simpl in Hk; lia.
Qed.

Lemma ends_go_recon : forall s, FilePath.ends_go s = true -> s = (FilePath.strip_go s ++ ".go")%string.
Proof.
  intros s H. unfold FilePath.ends_go in H. apply andb_true_iff in H. destruct H as [Hn Heq].
  apply Nat.leb_le in Hn. apply String.eqb_eq in Heq. unfold FilePath.strip_go.
  pose proof (substring_split (String.length s - 3) s ltac:(lia)) as Hsp.
  replace (String.length s - (String.length s - 3))%nat with 3%nat in Hsp by lia.
  rewrite Heq in Hsp. exact Hsp.
Qed.

Lemma filename_ok_has_dot : forall s, FilePath.filename_ok s = true -> contains_dot s = true.
Proof.
  intros s H. unfold FilePath.filename_ok in H. apply andb_true_iff in H. destruct H as [Hends _].
  rewrite (ends_go_recon s Hends), contains_dot_app.
  replace (contains_dot ".go") with true by reflexivity. apply Bool.orb_true_r.
Qed.

Lemma dir_component_neq_filename : forall d f,
  FilePath.dir_component_ok d = true -> FilePath.filename_ok f = true -> d <> f.
Proof.
  intros d f Hd Hf Heq. subst f.
  unfold FilePath.dir_component_ok in Hd. apply andb_true_iff in Hd. destruct Hd as [Hc _].
  pose proof (component_ok_no_dot d Hc) as Hnd. pose proof (filename_ok_has_dot d Hf) as Hyd.
  rewrite Hnd in Hyd. discriminate Hyd.
Qed.

(** the THIRD disjointness pair (completing "pairwise disjoint"): a root source basename [filename_ok] is
    never "go.mod" — "go.mod" ends ".mod", not ".go", so [ends_go "go.mod" = false].  So FRESourceFile keys
    and the FREGoMod key are disjoint. *)
Lemma filename_ok_neq_gomod : forall f, FilePath.filename_ok f = true -> f <> "go.mod".
Proof. intros f Hf Heq. subst f. vm_compute in Hf. discriminate Hf. Qed.

(** the first path component of a NESTED file (one with a nonempty parent directory) is
    a valid [dir_component_ok] key: it is the first '/'-separated segment, which [path_ok] requires to be an
    admissible directory component.  So every FREDirectory key is dot-free (feeds the disjointness above). *)

Lemma first_component_hd : forall s, first_component s = List.hd EmptyString (FilePath.split_slash s).
Proof.
  induction s as [|c s IH]; [reflexivity|].
  cbn [first_component FilePath.split_slash].
  destruct (Ascii.eqb c "/"%char); [reflexivity|].
  rewrite IH. destruct (FilePath.split_slash s) as [|h t]; reflexivity.
Qed.

Lemma hd_app_l {A} (d : A) (l1 l2 : list A) : l1 <> [] -> List.hd d (l1 ++ l2) = List.hd d l1.
Proof. destruct l1; [contradiction | reflexivity]. Qed.

Lemma first_component_dir_ok : forall s,
  FilePath.path_ok s = true -> FilePath.parent_of s <> EmptyString ->
  FilePath.dir_component_ok (first_component s) = true.
Proof.
  intros s Hp Hpar. rewrite first_component_hd.
  unfold FilePath.path_ok in Hp.
  destruct (rev (FilePath.split_slash s)) as [|last rdirs] eqn:Erev; [discriminate Hp|].
  apply andb_true_iff in Hp. destruct Hp as [Hdirs _].
  assert (Hrd : rdirs <> []).
  { intro Hc. subst rdirs. apply Hpar. unfold FilePath.parent_of. rewrite Erev. reflexivity. }
  assert (Hss : FilePath.split_slash s = (rev rdirs ++ [last])%list).
  { rewrite <- (rev_involutive (FilePath.split_slash s)), Erev. reflexivity. }
  rewrite Hss.
  assert (Hrr : rev rdirs <> []).
  { intro Hc. apply (f_equal (@rev _)) in Hc. rewrite rev_involutive in Hc. exact (Hrd Hc). }
  rewrite (hd_app_l EmptyString (rev rdirs) [last] Hrr).
  rewrite forallb_forall in Hdirs. apply Hdirs. apply in_rev.
  destruct (rev rdirs) as [|h t] eqn:Er; [contradiction | left; reflexivity].
Qed.

(** every [path_ok] path CONTAINS a dot (its last segment is a `.go` filename): splitting on '/' preserves
    dots (a separator has none), and the last segment is [filename_ok] hence dotted.  Used for the RootEntryMap
    disjointness (a root source-file key is dotted, a directory key is not). *)
Lemma contains_dot_split_slash : forall s, contains_dot s = existsb contains_dot (FilePath.split_slash s).
Proof.
  induction s as [|c s' IH]; [reflexivity|].
  cbn [FilePath.split_slash contains_dot].
  destruct (Ascii.eqb c "/"%char) eqn:E.
  - apply Ascii.eqb_eq in E. subst c. cbn [existsb contains_dot]. rewrite IH. reflexivity.
  - cbn [existsb].
    destruct (FilePath.split_slash s') as [|h t].
    + rewrite IH. cbn [existsb contains_dot]. rewrite !Bool.orb_false_r. reflexivity.
    + rewrite IH. cbn [existsb contains_dot]. rewrite Bool.orb_assoc. reflexivity.
Qed.

Lemma path_ok_has_dot : forall s, FilePath.path_ok s = true -> contains_dot s = true.
Proof.
  intros s Hp. rewrite contains_dot_split_slash. apply existsb_exists.
  unfold FilePath.path_ok in Hp.
  destruct (rev (FilePath.split_slash s)) as [|last rdirs] eqn:Erev; [discriminate Hp|].
  apply andb_true_iff in Hp. destruct Hp as [_ Hfn].
  exists last. split.
  - assert (Hin : In last (rev (FilePath.split_slash s))) by (rewrite Erev; left; reflexivity).
    rewrite <- in_rev in Hin. exact Hin.
  - apply filename_ok_has_dot. exact Hfn.
Qed.

(** the fresh ROOT LAYOUT as a standard string-keyed [PackageMap]: "go.mod" -> FREGoMod,
    each root-level file -> its FRESourceFile, each nested file's first component -> FREDirectory.  Built by one
    fold over the file bindings; conflict-free by the disjointness above (proved via [root_entry_hval]). *)

Definition root_entry_of_file (b : FilePath * GoSourceFile) : string * FreshRootEntryKind :=
  if String.eqb (fp_parent (fst b)) ""
  then (fp_string (fst b), FRESourceFile (fst b))
  else (first_component (fp_string (fst b)), FREDirectory).

(** the KEY-ONLY root entry: [root_entry_of_file] depends ONLY on the binding's FilePath (never its source
    value), so it factors through this.  Used by the DirectoryImage bridge — the rendered image keeps the
    same FilePath keys but different (rendered-bytes) values, and the root layout is the SAME. *)
Definition root_entry_of_path (fp : FilePath) : string * FreshRootEntryKind :=
  if String.eqb (fp_parent fp) ""
  then (fp_string fp, FRESourceFile fp)
  else (first_component (fp_string fp), FREDirectory).

Lemma root_entry_of_file_eq_path : forall b, root_entry_of_file b = root_entry_of_path (fst b).
Proof. intro b. reflexivity. Qed.

Definition root_layout (p : GoProgram) : PM.t FreshRootEntryKind :=
  fold_right (fun b acc => PM.add (fst (root_entry_of_file b)) (snd (root_entry_of_file b)) acc)
             (PM.add "go.mod" FREGoMod (PM.empty _))
             (GoAST.file_bindings (prog_files p)).

(** the fresh root layout over a bare FilePath KEY list — [root_layout] factored through the keys (the source
    values are irrelevant to the layout).  The image bridge recomputes this from the image's own keys. *)
Definition root_layout_of_keys (ks : list FilePath) : PM.t FreshRootEntryKind :=
  fold_right (fun fp acc => PM.add (fst (root_entry_of_path fp)) (snd (root_entry_of_path fp)) acc)
             (PM.add "go.mod" FREGoMod (PM.empty _)) ks.

Lemma root_layout_eq_of_keys : forall p,
  root_layout p = root_layout_of_keys (map fst (GoAST.file_bindings (prog_files p))).
Proof.
  intro p. unfold root_layout, root_layout_of_keys.
  induction (GoAST.file_bindings (prog_files p)) as [|b bs IH]; [reflexivity|].
  cbn [map fold_right]. rewrite IH, root_entry_of_file_eq_path. reflexivity.
Qed.

(* GENERIC fold-of-adds find: an absent key falls through to [init]; a present key gets its (unique) value. *)
Lemma fold_add_find_notin {A} (kv : (FilePath * GoSourceFile) -> string * A) (init : PM.t A)
    (l : list (FilePath * GoSourceFile)) (e : string) :
  (forall b, In b l -> fst (kv b) <> e) ->
  PM.find e (fold_right (fun b acc => PM.add (fst (kv b)) (snd (kv b)) acc) init l) = PM.find e init.
Proof.
  induction l as [|b l IH]; intro Hni; [reflexivity|].
  cbn [fold_right]. destruct (String.eqb (fst (kv b)) e) eqn:Eb.
  - apply String.eqb_eq in Eb. exfalso. exact (Hni b (or_introl eq_refl) Eb).
  - apply String.eqb_neq in Eb. rewrite PMF.add_neq_o by exact Eb. apply IH. intros b' Hb'. apply Hni; right; exact Hb'.
Qed.

Lemma fold_add_find_in {A} (kv : (FilePath * GoSourceFile) -> string * A) (init : PM.t A)
    (l : list (FilePath * GoSourceFile)) (e : string) (b0 : FilePath * GoSourceFile) :
  In b0 l -> fst (kv b0) = e ->
  (forall b1 b2, In b1 l -> In b2 l -> fst (kv b1) = fst (kv b2) -> snd (kv b1) = snd (kv b2)) ->
  PM.find e (fold_right (fun b acc => PM.add (fst (kv b)) (snd (kv b)) acc) init l) = Some (snd (kv b0)).
Proof.
  induction l as [|b l IH]; intros Hin Hk Hval; [destruct Hin|].
  cbn [fold_right]. destruct (String.eqb (fst (kv b)) e) eqn:Eb.
  - apply String.eqb_eq in Eb. rewrite PMF.add_eq_o by exact Eb. f_equal.
    apply (Hval b b0); [ left; reflexivity | exact Hin | rewrite Eb; symmetry; exact Hk ].
  - apply String.eqb_neq in Eb. rewrite PMF.add_neq_o by exact Eb.
    destruct Hin as [Hb0|Hin]; [ subst b0; exfalso; exact (Eb Hk) |].
    apply IH; [ exact Hin | exact Hk | intros b1 b2 H1 H2; apply Hval; right; assumption ].
Qed.

(* the root-entry key uniquely determines its value: same key => same kind (the conflict audit, mapped). *)
Lemma root_entry_hval : forall b1 b2 : FilePath * GoSourceFile,
  fst (root_entry_of_file b1) = fst (root_entry_of_file b2) ->
  snd (root_entry_of_file b1) = snd (root_entry_of_file b2).
Proof.
  intros b1 b2 Hk. unfold root_entry_of_file in *.
  destruct (String.eqb (fp_parent (fst b1)) "") eqn:E1;
    destruct (String.eqb (fp_parent (fst b2)) "") eqn:E2; cbn [fst snd] in *.
  - assert (Hp : fst b1 = fst b2) by (apply fp_eq; exact Hk). rewrite Hp. reflexivity.
  - exfalso. apply String.eqb_neq in E2.
    pose proof (path_ok_has_dot (fp_string (fst b1)) (fp_ok (fst b1))) as Hd1.
    pose proof (first_component_dir_ok (fp_string (fst b2)) (fp_ok (fst b2)) E2) as Hdc2.
    unfold FilePath.dir_component_ok in Hdc2. apply andb_true_iff in Hdc2. destruct Hdc2 as [Hc2 _].
    rewrite Hk, (component_ok_no_dot _ Hc2) in Hd1. discriminate Hd1.
  - exfalso. apply String.eqb_neq in E1.
    pose proof (path_ok_has_dot (fp_string (fst b2)) (fp_ok (fst b2))) as Hd2.
    pose proof (first_component_dir_ok (fp_string (fst b1)) (fp_ok (fst b1)) E1) as Hdc1.
    unfold FilePath.dir_component_ok in Hdc1. apply andb_true_iff in Hdc1. destruct Hdc1 as [Hc1 _].
    rewrite <- Hk, (component_ok_no_dot _ Hc1) in Hd2. discriminate Hd2.
  - reflexivity.
Qed.

(** the ROOT-DIRECTORY characterization: a key maps to FREDirectory in the layout
    IFF some NESTED represented file has that key as its first path component.  (This is what the fresh-build
    preflight consults: an existing root DIRECTORY at the default exec name is the cmd/go collision.) *)
Lemma root_layout_dir_iff : forall p e,
  PM.find e (root_layout p) = Some FREDirectory <->
  (exists b, In b (GoAST.file_bindings (prog_files p))
             /\ fp_parent (fst b) <> "" /\ first_component (fp_string (fst b)) = e).
Proof.
  intros p e. unfold root_layout. split.
  - intro Hfind.
    destruct (existsb (fun b => String.eqb (fst (root_entry_of_file b)) e)
                (GoAST.file_bindings (prog_files p))) eqn:Eex.
    + apply existsb_exists in Eex. destruct Eex as [b [Hin Hkey]]. apply String.eqb_eq in Hkey.
      rewrite (fold_add_find_in root_entry_of_file (PM.add "go.mod" FREGoMod (PM.empty _))
                 (GoAST.file_bindings (prog_files p)) e b Hin Hkey
                 (fun b1 b2 _ _ => root_entry_hval b1 b2)) in Hfind.
      injection Hfind as Hval. exists b.
      unfold root_entry_of_file in Hkey, Hval.
      destruct (String.eqb (fp_parent (fst b)) "") eqn:E; cbn [fst snd] in Hkey, Hval.
      * discriminate Hval.
      * apply String.eqb_neq in E. split; [ exact Hin | split; [ exact E | exact Hkey ] ].
    + assert (Hni : forall b, In b (GoAST.file_bindings (prog_files p)) -> fst (root_entry_of_file b) <> e).
      { intros b Hin Hc. apply Bool.not_true_iff_false in Eex. apply Eex, existsb_exists.
        exists b. split; [ exact Hin | apply String.eqb_eq; exact Hc ]. }
      rewrite (fold_add_find_notin root_entry_of_file (PM.add "go.mod" FREGoMod (PM.empty _))
                 (GoAST.file_bindings (prog_files p)) e Hni) in Hfind.
      destruct (String.eqb "go.mod" e) eqn:Eg.
      * apply String.eqb_eq in Eg. rewrite <- Eg, PMF.add_eq_o in Hfind by reflexivity. discriminate Hfind.
      * apply String.eqb_neq in Eg. rewrite PMF.add_neq_o in Hfind by exact Eg.
        rewrite PMF.empty_o in Hfind. discriminate Hfind.
  - intros [b [Hin [Hpar Hfc]]].
    assert (Hkv : root_entry_of_file b = (e, FREDirectory)).
    { unfold root_entry_of_file. destruct (String.eqb (fp_parent (fst b)) "") eqn:E.
      - apply String.eqb_eq in E. exfalso. exact (Hpar E).
      - rewrite Hfc. reflexivity. }
    rewrite (fold_add_find_in root_entry_of_file (PM.add "go.mod" FREGoMod (PM.empty _))
               (GoAST.file_bindings (prog_files p)) e b Hin (f_equal fst Hkv)
               (fun b1 b2 _ _ => root_entry_hval b1 b2)).
    rewrite Hkv. reflexivity.
Qed.

(** a root-entry key is NEVER "go.mod": a root source key is the WHOLE
    [path_ok] file string, and [path_ok "go.mod" = false] (it ends ".mod", not ".go"); a nested directory key
    is [dir_component_ok] (dot-free), and "go.mod" has a dot.  So the base [FREGoMod] binding is never
    overwritten. *)
Lemma root_entry_key_neq_gomod : forall b, fst (root_entry_of_file b) <> "go.mod".
Proof.
  intro b. unfold root_entry_of_file.
  destruct (String.eqb (fp_parent (fst b)) "") eqn:E; cbn [fst]; intro Hc.
  - pose proof (fp_ok (fst b)) as Hok. unfold FilePath.fp_string in Hc. rewrite Hc in Hok.
    vm_compute in Hok. discriminate Hok.
  - apply String.eqb_neq in E.
    pose proof (first_component_dir_ok (fp_string (fst b)) (fp_ok (fst b)) E) as Hdc.
    rewrite Hc in Hdc. vm_compute in Hdc. discriminate Hdc.
Qed.

(** the GENERIC fold-of-adds MEMBERSHIP: a key is in the fold iff it is an added key OR is in [init]. *)
Lemma fold_add_in_iff {A} (kv : (FilePath * GoSourceFile) -> string * A) (init : PM.t A)
    (l : list (FilePath * GoSourceFile)) (e : string) :
  PM.In e (fold_right (fun b acc => PM.add (fst (kv b)) (snd (kv b)) acc) init l)
  <-> In e (map (fun b => fst (kv b)) l) \/ PM.In e init.
Proof.
  induction l as [|b bs IH]; cbn [fold_right map].
  - split; [ intro H; right; exact H | intros [[]|H]; exact H ].
  - rewrite PMF.add_in_iff, IH. split.
    + intros [He|[Hin|Hi]]; [ left; left; exact He | left; right; exact Hin | right; exact Hi ].
    + intros [[He|Hin]|Hi]; [ left; exact He | right; left; exact Hin | right; right; exact Hi ].
Qed.

(** the FREGoMod entry: "go.mod" ALWAYS maps to [FREGoMod], and it is the
    ONLY key that does (no file produces an [FREGoMod] value, and no file key equals "go.mod"). *)
Lemma root_layout_gomod : forall p, PM.find "go.mod" (root_layout p) = Some FREGoMod.
Proof.
  intro p. unfold root_layout.
  rewrite (fold_add_find_notin root_entry_of_file (PM.add "go.mod" FREGoMod (PM.empty _))
             (GoAST.file_bindings (prog_files p)) "go.mod" (fun b _ => root_entry_key_neq_gomod b)).
  apply PMF.add_eq_o. reflexivity.
Qed.

Lemma root_layout_gomod_iff : forall p e,
  PM.find e (root_layout p) = Some FREGoMod <-> e = "go.mod".
Proof.
  intros p e. split; [| intros ->; apply root_layout_gomod ].
  intro Hf. unfold root_layout in Hf.
  destruct (existsb (fun b => String.eqb (fst (root_entry_of_file b)) e)
              (GoAST.file_bindings (prog_files p))) eqn:Eex.
  - apply existsb_exists in Eex. destruct Eex as [b [Hin Hkey]]. apply String.eqb_eq in Hkey.
    rewrite (fold_add_find_in root_entry_of_file (PM.add "go.mod" FREGoMod (PM.empty _))
               (GoAST.file_bindings (prog_files p)) e b Hin Hkey
               (fun b1 b2 _ _ => root_entry_hval b1 b2)) in Hf.
    exfalso. injection Hf as Hval. unfold root_entry_of_file in Hval.
    destruct (String.eqb (fp_parent (fst b)) ""); cbn [snd] in Hval; discriminate Hval.
  - assert (Hni : forall b, In b (GoAST.file_bindings (prog_files p)) -> fst (root_entry_of_file b) <> e).
    { intros b Hin Hc. apply Bool.not_true_iff_false in Eex. apply Eex, existsb_exists.
      exists b. split; [ exact Hin | apply String.eqb_eq; exact Hc ]. }
    rewrite (fold_add_find_notin root_entry_of_file (PM.add "go.mod" FREGoMod (PM.empty _))
               (GoAST.file_bindings (prog_files p)) e Hni) in Hf.
    destruct (String.eqb "go.mod" e) eqn:Eg.
    + apply String.eqb_eq in Eg; symmetry; exact Eg.
    + apply String.eqb_neq in Eg. rewrite PMF.add_neq_o, PMF.empty_o in Hf by exact Eg. discriminate Hf.
Qed.

(** the [FRESourceFile] entries: a key maps to [FRESourceFile fp] IFF some
    root-level represented file (empty parent) has that key as its own path and IS [fp]. *)
Lemma root_layout_source_iff : forall p e fp,
  PM.find e (root_layout p) = Some (FRESourceFile fp) <->
  (exists b, In b (GoAST.file_bindings (prog_files p))
             /\ fp_parent (fst b) = "" /\ fp_string (fst b) = e /\ fst b = fp).
Proof.
  intros p e fp. unfold root_layout. split.
  - intro Hf.
    destruct (existsb (fun b => String.eqb (fst (root_entry_of_file b)) e)
                (GoAST.file_bindings (prog_files p))) eqn:Eex.
    + apply existsb_exists in Eex. destruct Eex as [b [Hin Hkey]]. apply String.eqb_eq in Hkey.
      rewrite (fold_add_find_in root_entry_of_file (PM.add "go.mod" FREGoMod (PM.empty _))
                 (GoAST.file_bindings (prog_files p)) e b Hin Hkey
                 (fun b1 b2 _ _ => root_entry_hval b1 b2)) in Hf.
      injection Hf as Hval. exists b.
      unfold root_entry_of_file in Hkey, Hval.
      destruct (String.eqb (fp_parent (fst b)) "") eqn:E; cbn [fst snd] in Hkey, Hval.
      * apply String.eqb_eq in E. injection Hval as Hfp.
        split; [ exact Hin | split; [ exact E | split; [ exact Hkey | exact Hfp ] ] ].
      * discriminate Hval.
    + exfalso.
      assert (Hni : forall b, In b (GoAST.file_bindings (prog_files p)) -> fst (root_entry_of_file b) <> e).
      { intros b Hin Hc. apply Bool.not_true_iff_false in Eex. apply Eex, existsb_exists.
        exists b. split; [ exact Hin | apply String.eqb_eq; exact Hc ]. }
      rewrite (fold_add_find_notin root_entry_of_file (PM.add "go.mod" FREGoMod (PM.empty _))
                 (GoAST.file_bindings (prog_files p)) e Hni) in Hf.
      destruct (String.eqb "go.mod" e) eqn:Eg.
      * apply String.eqb_eq in Eg. rewrite <- Eg, PMF.add_eq_o in Hf by reflexivity. discriminate Hf.
      * apply String.eqb_neq in Eg. rewrite PMF.add_neq_o, PMF.empty_o in Hf by exact Eg. discriminate Hf.
  - intros [b [Hin [Hpar [Hkey Hfp]]]].
    assert (Hkv : root_entry_of_file b = (e, FRESourceFile fp)).
    { unfold root_entry_of_file. destruct (String.eqb (fp_parent (fst b)) "") eqn:E.
      - rewrite Hkey, Hfp. reflexivity.
      - apply String.eqb_neq in E. exfalso. exact (E Hpar). }
    rewrite (fold_add_find_in root_entry_of_file (PM.add "go.mod" FREGoMod (PM.empty _))
               (GoAST.file_bindings (prog_files p)) e b Hin (f_equal fst Hkv)
               (fun b1 b2 _ _ => root_entry_hval b1 b2)).
    rewrite Hkv. reflexivity.
Qed.

(** the DOMAIN (no-extra-entry): the layout's keys are EXACTLY "go.mod"
    plus the root-entry key of every represented file — nothing else. *)
(* the base layout ([go.mod] only) membership, stated via find (robust to the empty-map facts spelling). *)
Lemma root_base_in_iff : forall e,
  PM.In e (PM.add "go.mod" FREGoMod (PM.empty FreshRootEntryKind)) <-> e = "go.mod".
Proof.
  intro e. rewrite PMF.add_in_iff, PMF.empty_in_iff. split.
  - intros [He|[]]; symmetry; exact He.
  - intros ->. left; reflexivity.
Qed.

Lemma root_layout_domain : forall p e,
  PM.In e (root_layout p) <->
  e = "go.mod" \/ In e (map (fun b => fst (root_entry_of_file b)) (GoAST.file_bindings (prog_files p))).
Proof.
  intros p e. unfold root_layout. rewrite fold_add_in_iff, root_base_in_iff.
  split; [ intros [Hin|He]; [ right; exact Hin | left; exact He ]
         | intros [He|Hin]; [ right; exact He | left; exact Hin ] ].
Qed.

(** the retained FRESH BUILD PLAN + its preflight.  After loading packages, cmd/go
    picks a default output ONLY for a sole selected MAIN package, then stats that name and FAILS (before
    compiling) if it is an existing DIRECTORY.  0 or >=2 selected packages write no default output (no
    preflight).  The current grammar makes every package `package main`, so a sole selected package is always
    a main package.  (A future single NON-main package would take an FBDDiscardSingleLibrary branch — omitted
    until that syntax exists.)  Derived purely from the retained PackageMap + ModuleSpec + root layout: no
    syntax revisit, no index rebuild, no rendering, no cmd/go call, no filesystem scan. *)

Inductive FreshBuildDisposition : Type :=
| FBDNoPackages
| FBDDiscardMultiple (count : nat)
| FBDWriteSingleMain (dir import_path output_name : string) (target : option FreshRootEntryKind).

(** the plan as a PURE FUNCTION of the ModuleSpec, a package-DIR key list, and the root layout — so the ONE
    retained package buckets (their keys) + the ONE retained root layout DERIVE the plan (retention),
    with no second [package_summaries] fold. *)
Definition fresh_build_plan_of (ms : ModuleSpec) (keys : list string)
    (rl : PM.t FreshRootEntryKind) : FreshBuildDisposition :=
  match keys with
  | [] => FBDNoPackages
  | dir :: nil =>
      let ip := package_import_path ms dir in
      let ex := default_exec_name ms dir in
      FBDWriteSingleMain dir ip ex (PM.find ex rl)
  | _ :: _ :: _ => FBDDiscardMultiple (length keys)
  end.

(** [fresh_build_plan] IS [fresh_build_plan_of] over the program's selected keys + root layout — ONE plan
    builder, so the retained buckets reproduce it once their keys are shown equal to [selected_package_keys]. *)
Definition fresh_build_plan (p : GoProgram) : FreshBuildDisposition :=
  fresh_build_plan_of (prog_module p) (selected_package_keys p) (root_layout p).

(* every selected package key is "" or the parent directory of a represented file. *)
Lemma selected_key_is_parent : forall p dir,
  In dir (selected_package_keys p) -> dir = ""%string \/ exists fp, fp_parent fp = dir.
Proof.
  intros p dir Hin. unfold selected_package_keys in Hin. apply in_map_iff in Hin.
  destruct Hin as [[k s] [Hfst Hinel]]. cbn in Hfst. subst k.
  assert (Hmt : PM.MapsTo dir s (selected_packages p))
    by (apply PMF.elements_mapsto_iff, InA_alt; exists (dir, s); split; [ split; reflexivity | exact Hinel ]).
  assert (Hex : exists b, In b (GoAST.file_bindings (prog_files p)) /\ fp_parent (fst b) = dir).
  { apply selected_iff_file. exists s. exact Hmt. }
  destruct Hex as [b [_ Hpar]]. right. exists (fst b). exact Hpar.
Qed.

(** the DEFAULT EXECUTABLE NAME of a sole selected package is NEVER empty: cmd/go
    always writes a nonempty default output name.  (Universal over every representable program's plan.) *)
Theorem fresh_build_plan_exec_nonempty : forall p dir ip ex t,
  fresh_build_plan p = FBDWriteSingleMain dir ip ex t -> ex <> ""%string.
Proof.
  intros p dir ip ex t Hplan.
  unfold fresh_build_plan, fresh_build_plan_of in Hplan.
  destruct (selected_package_keys p) as [|d0 [|d1 r]] eqn:Ek; try discriminate Hplan.
  injection Hplan as _ _ Hex _.
  assert (Hdir : d0 = ""%string \/ exists fp, fp_parent fp = d0)
    by (apply (selected_key_is_parent p); rewrite Ek; left; reflexivity).
  rewrite <- Hex. apply (default_exec_name_nonempty (prog_module p) d0 Hdir).
Qed.

(** the EXACT zero / single / multiple plan CLASSIFICATION by selected-package count. *)
Lemma fresh_build_plan_zero : forall p,
  selected_package_keys p = [] -> fresh_build_plan p = FBDNoPackages.
Proof. intros p H. unfold fresh_build_plan, fresh_build_plan_of. rewrite H. reflexivity. Qed.

Lemma fresh_build_plan_multiple : forall p d1 d2 rest,
  selected_package_keys p = d1 :: d2 :: rest ->
  fresh_build_plan p = FBDDiscardMultiple (selected_package_count p).
Proof. intros p d1 d2 rest H. unfold fresh_build_plan, fresh_build_plan_of, selected_package_count. rewrite H. reflexivity. Qed.

(** the sole-main plan's stored output TARGET is exactly the fresh root layout's classification at the default
    output name (feeds the image-side output-target bridge). *)
Lemma fresh_build_plan_single_target : forall p dir ip ex t,
  fresh_build_plan p = FBDWriteSingleMain dir ip ex t -> t = PM.find ex (root_layout p).
Proof.
  intros p dir ip ex t Hplan. unfold fresh_build_plan, fresh_build_plan_of in Hplan.
  destruct (selected_package_keys p) as [|d0 [|d1 r]] eqn:Ek; try discriminate Hplan.
  injection Hplan as _ _ Hex Ht. rewrite <- Hex. symmetry. exact Ht.
Qed.

(** the RETAINED package buckets' keys ARE [selected_package_keys] (same DIR domain — both are exactly the
    directories with a file), so the plan derives from the retained buckets rather than recomputing
    [package_summaries]. *)
Lemma bucket_keys_eq_selected : forall p (idx : GoIndex.Snap.SyntaxIndex p),
  map fst (PM.elements (prog_package_refs idx)) = selected_package_keys p.
Proof.
  intros p idx. unfold selected_package_keys, selected_packages.
  apply Collections.packagemap_same_domain_keys.
  intro dir. rewrite (prog_package_refs_present idx dir). split.
  - intro Hmem. apply PMF.in_find_iff. rewrite package_summaries_find, Hmem. discriminate.
  - intros [s Hmt]. apply PMF.find_mapsto_iff in Hmt. rewrite package_summaries_find in Hmt.
    destruct (list_dir_mem dir (GoAST.file_bindings (prog_files p))) eqn:E; [ reflexivity | discriminate Hmt ].
Qed.

(** the plan DERIVED from the retained buckets + root layout IS [fresh_build_plan p] (used to store the plan in
    [ElaborationFacts] with a real coherence proof, not a tautology). *)
Lemma fresh_build_plan_of_buckets : forall p (idx : GoIndex.Snap.SyntaxIndex p),
  fresh_build_plan_of (prog_module p) (map fst (PM.elements (prog_package_refs idx))) (root_layout p)
  = fresh_build_plan p.
Proof.
  intros p idx. rewrite (bucket_keys_eq_selected p idx). unfold fresh_build_plan. reflexivity.
Qed.

(* the preflight decision: reject ONLY a sole-main default output name that is an existing root directory. *)
Definition fresh_build_disposition_ok (d : FreshBuildDisposition) : bool :=
  match d with
  | FBDWriteSingleMain _ _ _ (Some FREDirectory) => false
  | _ => true
  end.

Definition fresh_build_preflight_ok (p : GoProgram) : Prop :=
  fresh_build_disposition_ok (fresh_build_plan p) = true.

(* the ONLY command-level preflight failure: a sole selected package whose default exec name is a root DIR. *)
Lemma preflight_fails_iff : forall p,
  fresh_build_disposition_ok (fresh_build_plan p) = false <->
  (exists dir, selected_package_keys p = [dir]
     /\ PM.find (default_exec_name (prog_module p) dir) (root_layout p) = Some FREDirectory).
Proof.
  intros p. unfold fresh_build_plan, fresh_build_plan_of, fresh_build_disposition_ok.
  destruct (selected_package_keys p) as [|dir [|d2 rest]] eqn:Ek.
  - split; [ discriminate | intros [d [Hd _]]; discriminate Hd ].
  - cbn.
    destruct (PM.find (default_exec_name (prog_module p) dir) (root_layout p))
      as [k|] eqn:Ef.
    + destruct k; cbn.
      * split; [ discriminate | intros [d [Hd Hf]]; injection Hd as ->; rewrite Ef in Hf; discriminate Hf ].
      * split; [ discriminate | intros [d [Hd Hf]]; injection Hd as ->; rewrite Ef in Hf; discriminate Hf ].
      * split; [ intros _; exists dir; split; [reflexivity | exact Ef] | reflexivity ].
    + split; [ discriminate | intros [d [Hd Hf]]; injection Hd as ->; rewrite Ef in Hf; discriminate Hf ].
  - cbn. split; [ discriminate | intros [d [Hd _]]; discriminate Hd ].
Qed.

(* the preflight failure, in cmd/go's terms (via root_layout_dir_iff): a sole package whose default exec name
   equals a NESTED represented file's first path component (so the fresh image has a directory at that name). *)
Corollary preflight_fails_dir : forall p,
  ~ fresh_build_preflight_ok p <->
  (exists dir b, selected_package_keys p = [dir]
     /\ In b (GoAST.file_bindings (prog_files p)) /\ fp_parent (fst b) <> ""
     /\ first_component (fp_string (fst b)) = default_exec_name (prog_module p) dir).
Proof.
  intros p. unfold fresh_build_preflight_ok. rewrite Bool.not_true_iff_false, preflight_fails_iff. split.
  - intros [dir [Hk Hf]]. apply (proj1 (root_layout_dir_iff p _)) in Hf.
    destruct Hf as [b [Hin [Hpar Hfc]]]. exists dir, b. repeat split; assumption.
  - intros [dir [b [Hk [Hin [Hpar Hfc]]]]]. exists dir. split; [ exact Hk |].
    apply (proj2 (root_layout_dir_iff p _)). exists b. repeat split; assumption.
Qed.

(** SOURCE-program validity, factored into the two INDEPENDENT Go rules the old combined
    "every package has exactly one DMain" conflated: package-block name UNIQUENESS (at most one `main`
    declaration per package) and main-package ENTRY validity (at least one).  For the current grammar (every
    package is `package main`; every DMain is intrinsically `func main()` with no params/results/type params)
    the two together are EQUIVALENT to the old rule — proved below — but this is the correct factoring for
    future non-main packages / methods / init.  SourceProgramValid is the SOURCE admission; GoCompile adds
    the fresh-build preflight on top. *)

(** [PackageDeclsUnique] / [MainPackagesHaveEntry] / [PackageRulesValid] and their executable reflections
    ([pkg_decls_unique_b_iff] / [main_pkgs_have_entry_b_iff] / [source_spec_package_rules_b_PackageRulesValid]) are defined
    early, beside [source_spec_package_rules_b], so BOTH the [package_summaries] view and the retained-bucket production
    decision root DIRECTLY in the two factored roots.  Here we package the SOURCE admission on top. *)
Definition SourceProgramValid (p : GoProgram) : Prop := ProgramTyped p /\ PackageRulesValid p.

(** the exactly-one property is retained ONLY as the universal CONSEQUENCE of today's two factored rules — a
    grammar coincidence, never the source authority. *)
Lemma current_package_rules_exactly_one : forall p, PackageRulesValid p <-> current_grammar_one_main p.
Proof.
  intro p. unfold PackageRulesValid, PackageDeclsUnique, MainPackagesHaveEntry, current_grammar_one_main. split.
  - intros [Hle Hge] dir s Hmt. pose proof (Hle dir s Hmt); pose proof (Hge dir s Hmt); lia.
  - intros H. split; intros dir s Hmt; pose proof (H dir s Hmt); lia.
Qed.

(** the decidable [source_spec_valid_b] reflects the LIVE factored root [SourceProgramValid] DIRECTLY:
    program typing ([program_typedb_iff]) AND the two factored package reflections ([source_spec_package_rules_b_PackageRulesValid]).
    No fragment/consequence bridge, no [ProgValid], no [prog_ok], no exactly-one intermediary. *)
Lemma source_spec_valid_b_iff : forall p, source_spec_valid_b p = true <-> SourceProgramValid p.
Proof.
  intro p. unfold source_spec_valid_b, SourceProgramValid.
  rewrite Bool.andb_true_iff, program_typedb_iff, source_spec_package_rules_b_PackageRulesValid. reflexivity.
Qed.

(** the decidable SPECIFICATION decision [semantic_ok_b] reflects the LIVE factored root [SourceProgramValid]
    DIRECTLY (via [semantic_ok_b_source_spec_valid_b] + [source_spec_valid_b_iff]; no [prog_ok] / [ProgValid]).
    It is the public source-validity reflection; production elaboration decides equivalently from its RETAINED
    diagnostics ([semantic_diagnostics_empty_iff]). *)
Lemma semantic_ok_b_SourceProgramValid (p : GoProgram) : semantic_ok_b p = true <-> SourceProgramValid p.
Proof. rewrite semantic_ok_b_source_spec_valid_b. apply source_spec_valid_b_iff. Qed.

(** the fresh-build COMMAND-level diagnostic list: when the preflight fails (a sole main
    package whose default exec name is an existing root directory), the ONE [DRBuildOutputIsDirectory] anchored
    at that sole package; otherwise empty.  Emptiness is exactly "the preflight passes". *)

Definition sole_package_ref (p : GoProgram) (dir : string) : option (PackageRef p) :=
  match Bool.bool_dec (package_present_b p dir) true with
  | left H  => Some (mkPackageRef p dir H)
  | right _ => None
  end.

Lemma sole_package_ref_some : forall p dir,
  package_present_b p dir = true -> exists pk, sole_package_ref p dir = Some pk.
Proof.
  intros p dir H. unfold sole_package_ref.
  destruct (Bool.bool_dec (package_present_b p dir) true) as [Ht|Hf]; [ eexists; reflexivity | destruct (Hf H) ].
Qed.

(* a sole selected package is present (it is a key of the package-summary map, so a file has that parent). *)
Lemma sole_package_present : forall p dir,
  selected_package_keys p = [dir] -> package_present_b p dir = true.
Proof.
  intros p dir Hk.
  assert (Hin : In dir (selected_package_keys p)) by (rewrite Hk; left; reflexivity).
  unfold selected_package_keys in Hin. apply in_map_iff in Hin.
  destruct Hin as [[k s] [Hfst Hinel]]. cbn in Hfst. subst k.
  assert (Hmt : PM.MapsTo dir s (selected_packages p))
    by (apply PMF.elements_mapsto_iff, InA_alt; exists (dir, s); split; [split; reflexivity | exact Hinel]).
  unfold package_present_b. unfold selected_packages in Hmt.
  apply PMF.find_mapsto_iff in Hmt. rewrite package_summaries_find in Hmt.
  destruct (list_dir_mem dir (GoAST.file_bindings (prog_files p))); [ reflexivity | discriminate Hmt ].
Qed.

(* the fresh-build command diagnostics as a function of a GIVEN plan — so the elaboration threads the ONE
   retained bucket-derived plan through the failure branch, never recomputing [fresh_build_plan p]. *)
Definition fresh_build_diagnostics_of (p : GoProgram) (plan : FreshBuildDisposition) : list (DiagnosticReason p) :=
  match plan with
  | FBDWriteSingleMain dir _ output_name (Some FREDirectory) =>
      match sole_package_ref p dir with
      | Some pk => [DRBuildOutputIsDirectory pk output_name]
      | None    => []
      end
  | _ => []
  end.

Definition fresh_build_diagnostics (p : GoProgram) : list (DiagnosticReason p) :=
  fresh_build_diagnostics_of p (fresh_build_plan p).

(** the ONE command-facing report builder over a plan + the semantic diagnostics: a FAILED fresh-build
    output preflight takes PRECEDENCE (the build-output-directory diagnostic), else the semantic diagnostics.
    Used by BOTH the readable [elaboration_diagnostics] and the production [elaborate_indexed] (over its retained
    plan), so their reports are the SAME builder on equal inputs — no second handwritten branch. *)
Definition command_diagnostics_of (p : GoProgram) (plan : FreshBuildDisposition)
    (semantic_ds : list (DiagnosticReason p)) : list (DiagnosticReason p) :=
  if fresh_build_disposition_ok plan then semantic_ds else fresh_build_diagnostics_of p plan.

Lemma fresh_build_diagnostics_nil_iff : forall p,
  fresh_build_diagnostics p = [] <-> fresh_build_preflight_ok p.
Proof.
  intros p. unfold fresh_build_diagnostics, fresh_build_diagnostics_of, fresh_build_preflight_ok, fresh_build_disposition_ok, fresh_build_plan.
  destruct (selected_package_keys p) as [|dir [|d2 rest]] eqn:Ek; cbn.
  - split; reflexivity.
  - destruct (PM.find (default_exec_name (prog_module p) dir) (root_layout p)) as [k|] eqn:Ef.
    + destruct k; cbn.
      * split; reflexivity.
      * split; reflexivity.
      * destruct (sole_package_ref p dir) as [pk|] eqn:Es.
        -- split; [ discriminate | discriminate ].
        -- exfalso. destruct (sole_package_ref_some p dir (sole_package_present p dir Ek)) as [pk Hpk].
           rewrite Hpk in Es. discriminate Es.
    + split; reflexivity.
  - split; reflexivity.
Qed.

(* every build-output diagnostic IS a build-output diagnostic; so when the preflight fails the report's
   build-output class fires. *)
Lemma fresh_build_diagnostics_is_build : forall p d, In d (fresh_build_diagnostics p) -> diag_is_build_output d = true.
Proof.
  intros p d Hin. unfold fresh_build_diagnostics, fresh_build_diagnostics_of in Hin.
  destruct (fresh_build_plan p) as [|count|dir ip name [ [ | | ] |]]; try destruct Hin.
  destruct (sole_package_ref p dir) as [pk|]; [| destruct Hin].
  cbn [In] in Hin. destruct Hin as [<-|[]]. reflexivity.
Qed.

Lemma existsb_build_output_fresh : forall p,
  fresh_build_disposition_ok (fresh_build_plan p) = false ->
  existsb diag_is_build_output (fresh_build_diagnostics p) = true.
Proof.
  intros p Hpf.
  assert (Hne : fresh_build_diagnostics p <> nil).
  { intro Hc. apply (proj1 (fresh_build_diagnostics_nil_iff p)) in Hc. unfold fresh_build_preflight_ok in Hc.
    rewrite Hc in Hpf; discriminate Hpf. }
  destruct (fresh_build_diagnostics p) as [|d ds] eqn:E; [ exfalso; apply Hne; reflexivity |].
  cbn [existsb]. rewrite (fresh_build_diagnostics_is_build p d) by (rewrite E; left; reflexivity). reflexivity.
Qed.

(** FULL program-input equality: the ModuleSpec AND the file map.  The full admission / plan / report /
    class depend on BOTH (the preflight's default exec name comes from the ModulePath), unlike the source
    facts which depend only on the file map. *)
Definition ProgramInputEqual (p1 p2 : GoProgram) : Prop :=
  prog_module p1 = prog_module p2 /\ GoAST.FilesEqual (prog_files p1) (prog_files p2).

(* the selected-package enumeration and the root layout depend only on the file map. *)
Lemma selected_package_keys_Equal : forall p1 p2,
  GoAST.FilesEqual (prog_files p1) (prog_files p2) -> selected_package_keys p1 = selected_package_keys p2.
Proof.
  intros p1 p2 Heq. unfold selected_package_keys, selected_packages.
  rewrite (Collections.packagemap_elements_Equal _ _ (package_summaries_Equal _ _ Heq)). reflexivity.
Qed.

Lemma root_layout_Equal : forall p1 p2,
  GoAST.FilesEqual (prog_files p1) (prog_files p2) -> root_layout p1 = root_layout p2.
Proof.
  intros p1 p2 Heq. unfold root_layout, GoAST.file_bindings.
  rewrite (Collections.filemap_elements_Equal _ _ Heq). reflexivity.
Qed.

Lemma fresh_build_plan_InputEqual : forall p1 p2,
  ProgramInputEqual p1 p2 -> fresh_build_plan p1 = fresh_build_plan p2.
Proof.
  intros p1 p2 [Hm Hf]. unfold fresh_build_plan.
  rewrite (selected_package_keys_Equal _ _ Hf), Hm, (root_layout_Equal _ _ Hf). reflexivity.
Qed.

Lemma fresh_build_disposition_InputEqual : forall p1 p2,
  ProgramInputEqual p1 p2 ->
  fresh_build_disposition_ok (fresh_build_plan p1) = fresh_build_disposition_ok (fresh_build_plan p2).
Proof. intros p1 p2 H. rewrite (fresh_build_plan_InputEqual _ _ H). reflexivity. Qed.

(** the COMMAND-ordered diagnostic list: if the fresh-build preflight FAILS, the report
    is EXACTLY the build-output-directory diagnostic (it takes PRECEDENCE, hiding the semantic diagnostics of
    the sole package); otherwise it is the semantic [semantic_diagnostics].  Emptiness is exactly GoCompile. *)
Definition elaboration_diagnostics (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p) : list (DiagnosticReason p) :=
  command_diagnostics_of p (fresh_build_plan p) (semantic_diagnostics p idx).

(** the RETAINED source validity is [SourceProgramValid] (the FACTORED rules
    [PackageDeclsUnique] + [MainPackagesHaveEntry], of which the old exactly-one-main rule is a proved
    consequence), NOT the old combined [ProgValid]. *)
Lemma elaboration_no_diags_source_valid : forall p idx, elaboration_diagnostics p idx = nil -> SourceProgramValid p.
Proof.
  intros p idx He.
  unfold elaboration_diagnostics, command_diagnostics_of in He. destruct (fresh_build_disposition_ok (fresh_build_plan p)) eqn:Ep.
  - exact (proj1 (semantic_ok_b_SourceProgramValid p) (proj1 (semantic_diagnostics_empty_iff p idx) He)).
  - apply (proj1 (fresh_build_diagnostics_nil_iff p)) in He. unfold fresh_build_preflight_ok in He.
    rewrite He in Ep. discriminate Ep.
Qed.

Lemma elaboration_no_diags_preflight : forall p idx, elaboration_diagnostics p idx = nil -> fresh_build_preflight_ok p.
Proof.
  intros p idx He. unfold elaboration_diagnostics, command_diagnostics_of in He. destruct (fresh_build_disposition_ok (fresh_build_plan p)) eqn:Ep.
  - unfold fresh_build_preflight_ok. exact Ep.
  - exact (proj1 (fresh_build_diagnostics_nil_iff p) He).
Qed.

Lemma elaboration_diagnostics_eq_semantic : forall p idx,
  fresh_build_disposition_ok (fresh_build_plan p) = true -> elaboration_diagnostics p idx = semantic_diagnostics p idx.
Proof. intros p idx H. unfold elaboration_diagnostics, command_diagnostics_of. rewrite H. reflexivity. Qed.

Lemma elaboration_diagnostics_eq_fresh : forall p idx,
  fresh_build_disposition_ok (fresh_build_plan p) = false -> elaboration_diagnostics p idx = fresh_build_diagnostics p.
Proof. intros p idx H. unfold elaboration_diagnostics, command_diagnostics_of. rewrite H. reflexivity. Qed.

(* end of the block — restore the default scope so the elaboration machinery's list [++] is list append. *)
Close Scope string_scope.

(** whole-program admissibility IS the exact fresh-build admission: the pinned one-shot
    `go build ./...` output PREFLIGHT passes AND the source is valid.  [SourceProgramValid] is the
    source/compiler/package part; [fresh_build_preflight_ok] is the cmd/go default-output part. *)
Definition GoCompile (p : GoProgram) : Prop := fresh_build_preflight_ok p /\ SourceProgramValid p.

(** the command-ordered report is empty EXACTLY on admissible programs.  ([elaboration_diagnostics] is definitionally the
    [diags] computed inside [elaborate_indexed], so the elaboration-exactness theorems below reduce to this.) *)
Lemma elaboration_diagnostics_nil_iff_GoCompile : forall p idx, elaboration_diagnostics p idx = nil <-> GoCompile p.
Proof.
  intros p idx. unfold GoCompile. split.
  - intro He. split; [ exact (elaboration_no_diags_preflight p idx He)
                     | exact (elaboration_no_diags_source_valid p idx He) ].
  - intros [Hpf Hsv]. unfold elaboration_diagnostics, command_diagnostics_of. unfold fresh_build_preflight_ok in Hpf. rewrite Hpf.
    apply (proj2 (semantic_diagnostics_empty_iff p idx)), (proj2 (semantic_ok_b_SourceProgramValid p)). exact Hsv.
Qed.

(** the command-ordered report computed on the RETAINED bucket-derived plan (the ONE plan
    [elaborate_indexed] threads through the disposition test AND the failure branch) IS the canonical
    [elaboration_diagnostics] (which is phrased over [fresh_build_plan p]).  The only gap is the plan
    presentation — [fresh_build_plan_of_buckets] closes it — so the elaboration's decision and its retained
    plan are literally the same object.  ([elaborate_indexed]'s local diagnostic term is definitionally this
    LHS: its `then` branch is the one-pass raw fold, convertible to [semantic_diagnostics p idx].) *)
Lemma command_plan_diags_eq (p : GoProgram) (ip : GoIndex.IndexedProgram p) :
  command_diagnostics_of p
    (fresh_build_plan_of (prog_module p)
       (map fst (PM.elements (prog_package_refs (GoIndex.indexed_syntax ip)))) (root_layout p))
    (semantic_diagnostics p (GoIndex.indexed_syntax ip))
  = elaboration_diagnostics p (GoIndex.indexed_syntax ip).
Proof.
  rewrite (fresh_build_plan_of_buckets p (GoIndex.indexed_syntax ip)).
  unfold elaboration_diagnostics. reflexivity.
Qed.

(** the SUCCESSFUL elaboration facts, retained over the SAME [IndexedProgram] the elaboration ran on:
    the occurrence-keyed [ExprFactTable] (standard NodeKey map) + the package main-ref buckets (standard
    PackageMap), each with its EXACTNESS proof, plus the compiled validity.  Facts are exposed ONLY on
    success. *)
Record ElaborationFacts (p : GoProgram) (ip : GoIndex.IndexedProgram p) : Type := mkElaborationFacts {
  (* the SEALED expression-fact table: no non-expression/foreign key, each visited occurrence's fact exact. *)
  ef_expr_facts      : ExprFactTable p ip ;
  (* the SEALED type-name-fact table (§8): a conversion's SOURCE type name resolved to its semantic [GoType],
     keyed by NodeKey; domain = exactly the visited type-name occurrences (no expression/foreign key). *)
  ef_type_name_facts : TypeNameFactTable p ;
  ef_package_refs    : PM.t (list (GoIndex.DeclRef p)) ;
  (* the bucket map's domain is exactly the represented package set... *)
  ef_package_present : forall dir, PM.In dir ef_package_refs <-> list_dir_mem dir (GoAST.file_bindings (prog_files p)) = true ;
  (* ...each present bucket's length is the package's declarative main count... *)
  ef_package_len     : forall dir l, PM.find dir ef_package_refs = Some l -> length l = pkg_main_count dir (prog_files p) ;
  (* ...and every main in a bucket BELONGS to that package (its file's parent = the key) — no swap between packages. *)
  ef_package_belongs : forall dir l, PM.find dir ef_package_refs = Some l ->
                         forall d, In d l ->
                         fp_parent (GoIndex.Snap.file_ref_path (GoIndex.Snap.node_ref_file (GoIndex.erase_ref d))) = dir ;
  ef_source_valid           : SourceProgramValid p ;
  (* the retained fresh-build PREFLIGHT evidence: the pinned one-shot `go build ./...` output
     preflight passes for this program.  Together with [ef_source_valid] it witnesses [GoCompile] (see [cp_ok]). *)
  ef_preflight       : fresh_build_preflight_ok p ;
  (* the RETAINED fresh ROOT LAYOUT and BUILD PLAN: computed ONCE (from the retained package
     buckets + the file bindings) and stored here with their coherence to [root_layout]/[fresh_build_plan], so a
     [CompilableProgram] PROJECTS the exact plan its elaboration used — never a recompute from the program. *)
  ef_root_layout     : PM.t FreshRootEntryKind ;
  ef_root_layout_ok  : ef_root_layout = root_layout p ;
  ef_build_plan      : FreshBuildDisposition ;
  ef_build_plan_ok   : ef_build_plan = fresh_build_plan p
}.
Arguments mkElaborationFacts {p ip} _ _ _ _ _ _ _ _ _ _ _ _.
Arguments ef_expr_facts {p ip} _.
Arguments ef_type_name_facts {p ip} _.
Arguments ef_package_refs {p ip} _.
Arguments ef_package_present {p ip} _.
Arguments ef_package_len {p ip} _.
Arguments ef_package_belongs {p ip} _.
Arguments ef_source_valid {p ip} _.
Arguments ef_preflight {p ip} _.
Arguments ef_root_layout {p ip} _.
Arguments ef_root_layout_ok {p ip} _.
Arguments ef_build_plan {p ip} _.
Arguments ef_build_plan_ok {p ip} _.

(** the public expression-fact query is TOTAL: on a valid [ElaborationFacts], EVERY typed [ExprRef]
    has an exact entry.  The ExprRef denotes a VISITED expression occurrence ([noderef_in_prog_visit] +
    [kind_view_expr]) whose [const_info] SUCCEEDS on a [ProgramTyped] program ([prog_visit_const_info_some],
    from [ef_source_valid]); [eft_complete] equates the map lookup to that occurrence's [occ_expr_fact], which is
    therefore [Some].  So the lookup is never [None] — the query returns an [ExprFact], not an option. *)
Lemma expr_ref_fact_some {p ip} (facts : ElaborationFacts p ip) (er : GoIndex.ExprRef p) :
  exists f, GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref er))
              (eft_map (ef_expr_facts facts)) = Some f.
Proof.
  assert (Hkind : GoIndex.occurrence_kind (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) = GoIndex.KExpression)
    by exact (proj2_sig er).
  destruct (GoIndex.kind_view_expr _ Hkind) as [e' Hv].
  pose proof (noderef_in_prog_visit p (GoIndex.erase_ref er)) as Hin.
  pose proof (proj2 (GoTypes.program_typedb_iff predeclared_type p) (proj1 (ef_source_valid facts))) as HPT.
  destruct (prog_visit_const_info_some p HPT (GoIndex.erase_ref er)
              (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) e' Hin Hv) as [ci Hci].
  pose proof (eft_complete (ef_expr_facts facts) (GoIndex.erase_ref er)
                (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) Hin) as Hfind.
  exists (mkExprFact ci (occ_use_resolved (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)))).
  rewrite Hfind. exact (occ_expr_fact_status _ e' ci Hv Hci).
Qed.

Lemma expr_fact_at_not_none {p ip} (facts : ElaborationFacts p ip) (er : GoIndex.ExprRef p) :
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref er)) (eft_map (ef_expr_facts facts)) = None -> False.
Proof. intro Hn. destruct (expr_ref_fact_some facts er) as [f Hf]. rewrite Hf in Hn; discriminate. Qed.

(* the option-free lookup: a genuine match on the (variable) lookup result, discharging [None] by the totality
   proof — so a defect-shipping [option] result is impossible. *)
Definition fact_of_find {p ip} (facts : ElaborationFacts p ip) (er : GoIndex.ExprRef p)
  (o : option ExprFact) :
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref er)) (eft_map (ef_expr_facts facts)) = o -> ExprFact :=
  match o with
  | Some f => fun _ => f
  | None   => fun Hn => False_rect ExprFact (expr_fact_at_not_none facts er Hn)
  end.

Definition expr_fact_at {p ip} (facts : ElaborationFacts p ip) (er : GoIndex.ExprRef p) : ExprFact :=
  fact_of_find facts er
    (GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref er)) (eft_map (ef_expr_facts facts)))
    eq_refl.

Lemma fact_of_find_some {p ip} (facts : ElaborationFacts p ip) (er : GoIndex.ExprRef p) o Ho f :
  o = Some f -> fact_of_find facts er o Ho = f.
Proof. intros ->. cbn. reflexivity. Qed.

(** the total query PROJECTS the underlying map: where the map holds a fact, [expr_fact_at] returns exactly it
    (so the total function is faithful to the sealed table, not a fresh value). *)
Lemma expr_fact_at_find {p ip} (facts : ElaborationFacts p ip) (er : GoIndex.ExprRef p) f :
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref er)) (eft_map (ef_expr_facts facts)) = Some f ->
  expr_fact_at facts er = f.
Proof.
  intro Hf. unfold expr_fact_at.
  exact (fact_of_find_some facts er
    (GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref er)) (eft_map (ef_expr_facts facts)))
    eq_refl f Hf).
Qed.

(** the public TYPE-NAME-fact query is TOTAL (§8): EVERY [TypeNameRef] has an exact stored entry.  Unlike the
    expression fact this needs NO validity hypothesis — a [TypeNameRef] denotes a VISITED KTypeName occurrence
    ([noderef_in_prog_visit] + [kind_view_typename]) whose source name resolves by construction (§7,
    [predeclared_type] total), so [occ_type_name_fact] is [Some] and [tnft_complete] equates the lookup to it. *)
Lemma type_name_ref_fact_some {p ip} (facts : ElaborationFacts p ip) (tr : GoIndex.TypeNameRef p) :
  exists f, GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref tr))
              (tnft_map (ef_type_name_facts facts)) = Some f.
Proof.
  assert (Hkind : GoIndex.occurrence_kind (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref tr)) = GoIndex.KTypeName)
    by exact (proj2_sig tr).
  destruct (GoIndex.kind_view_typename _ Hkind) as [ts Hv].
  pose proof (noderef_in_prog_visit p (GoIndex.erase_ref tr)) as Hin.
  pose proof (tnft_complete (ef_type_name_facts facts) (GoIndex.erase_ref tr)
                (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref tr)) Hin) as Hfind.
  exists (mkTypeNameFact (predeclared_type ts)).
  rewrite Hfind. exact (occ_type_name_fact_some _ ts Hv).
Qed.

Lemma type_name_fact_at_not_none {p ip} (facts : ElaborationFacts p ip) (tr : GoIndex.TypeNameRef p) :
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref tr)) (tnft_map (ef_type_name_facts facts)) = None -> False.
Proof. intro Hn. destruct (type_name_ref_fact_some facts tr) as [f Hf]. rewrite Hf in Hn; discriminate. Qed.

Definition tnfact_of_find {p ip} (facts : ElaborationFacts p ip) (tr : GoIndex.TypeNameRef p)
  (o : option TypeNameFact) :
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref tr)) (tnft_map (ef_type_name_facts facts)) = o -> TypeNameFact :=
  match o with
  | Some f => fun _ => f
  | None   => fun Hn => False_rect TypeNameFact (type_name_fact_at_not_none facts tr Hn)
  end.

Definition type_name_fact_at {p ip} (facts : ElaborationFacts p ip) (tr : GoIndex.TypeNameRef p) : TypeNameFact :=
  tnfact_of_find facts tr
    (GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref tr)) (tnft_map (ef_type_name_facts facts)))
    eq_refl.

Lemma tnfact_of_find_some {p ip} (facts : ElaborationFacts p ip) (tr : GoIndex.TypeNameRef p) o Ho f :
  o = Some f -> tnfact_of_find facts tr o Ho = f.
Proof. intros ->. cbn. reflexivity. Qed.

(** the total type-name query PROJECTS the sealed table — where the map holds a fact, [type_name_fact_at]
    returns EXACTLY it (it does not recompute resolution). *)
Lemma type_name_fact_at_find {p ip} (facts : ElaborationFacts p ip) (tr : GoIndex.TypeNameRef p) f :
  GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref tr)) (tnft_map (ef_type_name_facts facts)) = Some f ->
  type_name_fact_at facts tr = f.
Proof.
  intro Hf. unfold type_name_fact_at.
  exact (tnfact_of_find_some facts tr
    (GoIndex.NodeKeyMapBase.find (GoIndex.Snap.node_ref_key (GoIndex.erase_ref tr)) (tnft_map (ef_type_name_facts facts)))
    eq_refl f Hf).
Qed.

(** ★§8 EXACTNESS: the stored fact EQUALS [GoCompile] resolution of the SOURCE type name recovered THROUGH the
    reference ([type_name_ref_syntax]) — the resolved [GoType] is [predeclared_type] of that exact source name,
    not a recomputation and not a copy of the spelling. *)
Theorem type_name_fact_at_resolves {p ip} (facts : ElaborationFacts p ip) (tr : GoIndex.TypeNameRef p) ts :
  GoIndex.type_name_ref_syntax tr = Some ts ->
  type_name_fact_at facts tr = mkTypeNameFact (predeclared_type ts).
Proof.
  intro Hts. unfold GoIndex.type_name_ref_syntax in Hts.
  pose proof (noderef_in_prog_visit p (GoIndex.erase_ref tr)) as Hin.
  pose proof (tnft_complete (ef_type_name_facts facts) (GoIndex.erase_ref tr)
                (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref tr)) Hin) as Hfind.
  rewrite (occ_type_name_fact_some _ ts Hts) in Hfind.
  exact (type_name_fact_at_find facts tr _ Hfind).
Qed.

(** ★§8 byte/uint8 (and rune/int32): DISTINCT source type syntax, but the SAME resolved semantic [GoType]
    ([TInteger IUint8] / [TInteger IInt32]) — the fact stores the resolved type only, so a [byte] fact and a
    [uint8] fact are EQUAL even though their sources (and rendered spellings, [GoRender]) differ. *)
Example predeclared_byte_is_uint8 : predeclared_type (GoAST.tsyn GoNames.TNbyte) = TInteger IUint8. Proof. reflexivity. Qed.
Example predeclared_rune_is_int32 : predeclared_type (GoAST.tsyn GoNames.TNrune) = TInteger IInt32. Proof. reflexivity. Qed.
Theorem tnfact_byte_uint8_same_type :
  mkTypeNameFact (predeclared_type (GoAST.tsyn GoNames.TNbyte))
  = mkTypeNameFact (predeclared_type (GoAST.tsyn GoNames.TNuint8)).
Proof. reflexivity. Qed.
Theorem tnfact_rune_int32_same_type :
  mkTypeNameFact (predeclared_type (GoAST.tsyn GoNames.TNrune))
  = mkTypeNameFact (predeclared_type (GoAST.tsyn GoNames.TNint32)).
Proof. reflexivity. Qed.
Theorem tsyn_byte_neq_uint8 : GoAST.tsyn GoNames.TNbyte <> GoAST.tsyn GoNames.TNuint8.
Proof.
  intro H. apply (f_equal GoAST.ts_name) in H. rewrite !GoAST.ts_name_tsyn in H. discriminate H.
Qed.
Theorem tsyn_rune_neq_int32 : GoAST.tsyn GoNames.TNrune <> GoAST.tsyn GoNames.TNint32.
Proof.
  intro H. apply (f_equal GoAST.ts_name) in H. rewrite !GoAST.ts_name_tsyn in H. discriminate H.
Qed.

(** ★§5.2 ALL SIXTEEN SOURCE NAMES: the one closed conjunction pinning every predeclared mapping — the
    fourteen numeric names to their semantic [GoType], plus the two aliases [byte]->[uint8] and [rune]->[int32].
    No name resolves anywhere else; this is the whole source-name authority in one reviewed statement. *)
Theorem predeclared_all_sixteen :
     predeclared_type (GoAST.tsyn GoNames.TNint)        = TInteger IInt
  /\ predeclared_type (GoAST.tsyn GoNames.TNint8)       = TInteger IInt8
  /\ predeclared_type (GoAST.tsyn GoNames.TNint16)      = TInteger IInt16
  /\ predeclared_type (GoAST.tsyn GoNames.TNint32)      = TInteger IInt32
  /\ predeclared_type (GoAST.tsyn GoNames.TNint64)      = TInteger IInt64
  /\ predeclared_type (GoAST.tsyn GoNames.TNuint)       = TInteger IUint
  /\ predeclared_type (GoAST.tsyn GoNames.TNuint8)      = TInteger IUint8
  /\ predeclared_type (GoAST.tsyn GoNames.TNuint16)     = TInteger IUint16
  /\ predeclared_type (GoAST.tsyn GoNames.TNuint32)     = TInteger IUint32
  /\ predeclared_type (GoAST.tsyn GoNames.TNuint64)     = TInteger IUint64
  /\ predeclared_type (GoAST.tsyn GoNames.TNfloat32)    = TFloat F32
  /\ predeclared_type (GoAST.tsyn GoNames.TNfloat64)    = TFloat F64
  /\ predeclared_type (GoAST.tsyn GoNames.TNcomplex64)  = TComplex C64
  /\ predeclared_type (GoAST.tsyn GoNames.TNcomplex128) = TComplex C128
  /\ predeclared_type (GoAST.tsyn GoNames.TNbyte)       = TInteger IUint8
  /\ predeclared_type (GoAST.tsyn GoNames.TNrune)       = TInteger IInt32.
Proof. repeat split; reflexivity. Qed.

(** ★§5.3 REPEATED EQUAL NAMES AT DISTINCT OCCURRENCES: two conversions to the SAME source name ([uint8] here)
    at DISTINCT occurrences (distinct keys) obtain, THROUGH the retained index, TWO distinct target
    [TypeNameRef]s (distinct NodeKeys — occurrence identity, not name identity), yet their recovered source
    [TypeSyntax] values are EQUAL and their sealed [TypeNameFact]s are EQUAL.  Replaces the tautological
    [scar_repeated_uint8]; holds for ANY such pair, so any concrete two-[uint8] snapshot instantiates it. *)
Theorem repeated_name_distinct_refs {p} (ip : GoIndex.IndexedProgram p) (facts : ElaborationFacts p ip)
    (r1 : GoIndex.Snap.NodeRef p) occ1 (er1 : GoIndex.ExprRef p) x1
    (r2 : GoIndex.Snap.NodeRef p) occ2 (er2 : GoIndex.ExprRef p) x2 :
  let idx := GoIndex.indexed_syntax ip in
  In (r1, occ1) (prog_visit p) -> GoIndex.view_expr occ1 = Some (EConvert (GoAST.tsyn GoNames.TNuint8) x1) ->
    GoIndex.as_expr idx r1 = Some er1 ->
  In (r2, occ2) (prog_visit p) -> GoIndex.view_expr occ2 = Some (EConvert (GoAST.tsyn GoNames.TNuint8) x2) ->
    GoIndex.as_expr idx r2 = Some er2 ->
  GoIndex.Snap.node_ref_key r1 <> GoIndex.Snap.node_ref_key r2 ->
  exists tr1 tr2,
    conversion_target_ref idx er1 = Some tr1 /\ conversion_target_ref idx er2 = Some tr2
    /\ GoIndex.Snap.node_ref_key (GoIndex.erase_ref tr1) <> GoIndex.Snap.node_ref_key (GoIndex.erase_ref tr2)
    /\ GoIndex.type_name_ref_syntax tr1 = GoIndex.type_name_ref_syntax tr2
    /\ type_name_fact_at facts tr1 = type_name_fact_at facts tr2.
Proof.
  intros idx Hin1 Hv1 Ha1 Hin2 Hv2 Ha2 Hne.
  destruct (conversion_target_ref_conv idx r1 occ1 er1 (GoAST.tsyn GoNames.TNuint8) x1 Hin1 Hv1 Ha1) as [tr1 [Hc1 [Hk1 [_ Hs1]]]].
  destruct (conversion_target_ref_conv idx r2 occ2 er2 (GoAST.tsyn GoNames.TNuint8) x2 Hin2 Hv2 Ha2) as [tr2 [Hc2 [Hk2 [_ Hs2]]]].
  exists tr1, tr2. split; [exact Hc1 | split; [exact Hc2 | split; [ | split ]]].
  - intro Heq. apply Hne. rewrite Hk1, Hk2 in Heq. exact (type_name_key_inj r1 r2 Heq).
  - rewrite Hs1, Hs2. reflexivity.
  - rewrite (type_name_fact_at_resolves facts tr1 _ Hs1), (type_name_fact_at_resolves facts tr2 _ Hs2). reflexivity.
Qed.

(** ★§12 byte / rune ALIAS SCARS (semantic, through the predeclared resolver): [byte] ranges over [uint8]
    ([byte(0)]/[byte(255)] accepted, [byte(256)]/[byte(-1)] rejected), [rune] over [int32] (min/max accepted,
    one past either endpoint rejected); and [byte(255)] / [rune(65)] yield the SAME constant status as
    [uint8(255)] / [int32(65)] — distinct SOURCE spellings, identical SEMANTICS. *)
Example scar_byte_0_accepted   : resolve_expr UsePrintlnArg (EConvert (GoAST.tsyn GoNames.TNbyte) (EInt 0))   = Some (TInteger IUint8). Proof. reflexivity. Qed.
Example scar_byte_255_accepted : resolve_expr UsePrintlnArg (EConvert (GoAST.tsyn GoNames.TNbyte) (EInt 255)) = Some (TInteger IUint8). Proof. reflexivity. Qed.
Example scar_byte_256_rejected : resolve_expr UsePrintlnArg (EConvert (GoAST.tsyn GoNames.TNbyte) (EInt 256)) = None. Proof. reflexivity. Qed.
Example scar_byte_m1_rejected  : resolve_expr UsePrintlnArg (EConvert (GoAST.tsyn GoNames.TNbyte) (ENeg 1))   = None. Proof. reflexivity. Qed.
Example scar_uint8_255_eq_byte : const_info (EConvert (GoAST.tsyn GoNames.TNuint8) (EInt 255))
                               = const_info (EConvert (GoAST.tsyn GoNames.TNbyte)  (EInt 255)). Proof. reflexivity. Qed.
Example scar_rune_min_accepted  : resolve_expr UsePrintlnArg (EConvert (GoAST.tsyn GoNames.TNrune) (ENeg 2147483648)) = Some (TInteger IInt32). Proof. reflexivity. Qed.
Example scar_rune_max_accepted  : resolve_expr UsePrintlnArg (EConvert (GoAST.tsyn GoNames.TNrune) (EInt 2147483647))  = Some (TInteger IInt32). Proof. reflexivity. Qed.
Example scar_rune_under_rejected : resolve_expr UsePrintlnArg (EConvert (GoAST.tsyn GoNames.TNrune) (ENeg 2147483649)) = None. Proof. reflexivity. Qed.
Example scar_rune_over_rejected  : resolve_expr UsePrintlnArg (EConvert (GoAST.tsyn GoNames.TNrune) (EInt 2147483648))  = None. Proof. reflexivity. Qed.
Example scar_int32_65_eq_rune : const_info (EConvert (GoAST.tsyn GoNames.TNint32) (EInt 65))
                              = const_info (EConvert (GoAST.tsyn GoNames.TNrune)  (EInt 65)). Proof. reflexivity. Qed.
(** the MATCHING semantic-target boundaries: [uint8] over the same range as [byte], [int32] over the same range
    as [rune] — the accept/reject endpoints coincide (pairs with the pinned-Go alias accept/reject matrix). *)
Example scar_uint8_0_accepted    : resolve_expr UsePrintlnArg (EConvert (GoAST.tsyn GoNames.TNuint8) (EInt 0))          = Some (TInteger IUint8). Proof. reflexivity. Qed.
Example scar_uint8_255_accepted  : resolve_expr UsePrintlnArg (EConvert (GoAST.tsyn GoNames.TNuint8) (EInt 255))        = Some (TInteger IUint8). Proof. reflexivity. Qed.
Example scar_uint8_256_rejected  : resolve_expr UsePrintlnArg (EConvert (GoAST.tsyn GoNames.TNuint8) (EInt 256))        = None. Proof. reflexivity. Qed.
Example scar_uint8_m1_rejected   : resolve_expr UsePrintlnArg (EConvert (GoAST.tsyn GoNames.TNuint8) (ENeg 1))          = None. Proof. reflexivity. Qed.
Example scar_int32_min_accepted  : resolve_expr UsePrintlnArg (EConvert (GoAST.tsyn GoNames.TNint32) (ENeg 2147483648)) = Some (TInteger IInt32). Proof. reflexivity. Qed.
Example scar_int32_max_accepted  : resolve_expr UsePrintlnArg (EConvert (GoAST.tsyn GoNames.TNint32) (EInt 2147483647)) = Some (TInteger IInt32). Proof. reflexivity. Qed.
Example scar_int32_under_rejected : resolve_expr UsePrintlnArg (EConvert (GoAST.tsyn GoNames.TNint32) (ENeg 2147483649)) = None. Proof. reflexivity. Qed.
Example scar_int32_over_rejected  : resolve_expr UsePrintlnArg (EConvert (GoAST.tsyn GoNames.TNint32) (EInt 2147483648)) = None. Proof. reflexivity. Qed.
(** repeated equal type names at DISTINCT source occurrences: the REAL occurrence-distinctness property (two
    [uint8(...)] targets are the same closed symbol, DIFFERENT occurrences with distinct refs / keys, equal
    recovered syntax, equal facts) is [repeated_name_distinct_refs] above — not a tautology over one term. *)
(** a wrong-kind conversion operand still resolves through the ONE authority (nested source-named conversion). *)
Example scar_nested_byte_uint16 : resolve_expr UsePrintlnArg
  (EConvert (GoAST.tsyn GoNames.TNbyte) (EConvert (GoAST.tsyn GoNames.TNuint16) (EInt 255))) = Some (TInteger IUint8). Proof. reflexivity. Qed.

(** ★§12 INTRINSIC-DOMAIN EXCLUSION: a C4 conversion target is a [TypeSyntax] = [TSName (TNUnqualified stn)]
    over a [SupportedTypeName], whose [stn_exact] proof forces [classify (render stn) = Some] one of the sixteen
    closed lexical names.  [bool], [string], [uintptr], [any], [error], [comparable], an unknown [foo], and a
    qualified [pkg.T] are NOT among those sixteen ([GoNames.classify] returns [None]), so NO [SupportedTypeName]
    — hence NO conversion target — can carry them: they are UNREPRESENTABLE, not rejected. *)
Example excl_bool       : GoNames.classify "bool" = None.        Proof. reflexivity. Qed.
Example excl_string     : GoNames.classify "string" = None.      Proof. reflexivity. Qed.
Example excl_uintptr    : GoNames.classify "uintptr" = None.     Proof. reflexivity. Qed.
Example excl_any        : GoNames.classify "any" = None.         Proof. reflexivity. Qed.
Example excl_error      : GoNames.classify "error" = None.       Proof. reflexivity. Qed.
Example excl_comparable : GoNames.classify "comparable" = None.  Proof. reflexivity. Qed.
Example excl_foo        : GoNames.classify "foo" = None.         Proof. reflexivity. Qed.
Example excl_qualified  : GoNames.classify "pkg.T" = None.       Proof. reflexivity. Qed.
Fail Definition excl_bool_target : GoAST.TypeSyntax :=
  GoAST.TSName (GoAST.TNUnqualified (GoNames.mkSTN (GoNames.mkIdent "bool" eq_refl) GoNames.TNint eq_refl)).

(** ★§12 representative migrated conversion fixtures (results preserved — one accept + one reject per numeric
    family, a nested and a same-target-identity case, and the load-bearing scalar + complex-component
    double-round scars at the [const_info] level; the FULL deleted matrix is closed by the universal
    [convert_const]/[resolve] lemmas, not re-added as hundreds of fixtures). *)
Example rep_int8_127_accept : resolve_expr UsePrintlnArg (EConvert (GoAST.tsyn GoNames.TNint8) (EInt 127)) = Some (TInteger IInt8). Proof. reflexivity. Qed.
Example rep_int8_128_reject : resolve_expr UsePrintlnArg (EConvert (GoAST.tsyn GoNames.TNint8) (EInt 128)) = None. Proof. reflexivity. Qed.
Example rep_f32_accept      : resolve_expr UsePrintlnArg (EConvert (GoAST.tsyn GoNames.TNfloat32) (EFloat GoTypes.d_15em1)) = Some (TFloat F32). Proof. reflexivity. Qed.
Example rep_f32_bool_reject : resolve_expr UsePrintlnArg (EConvert (GoAST.tsyn GoNames.TNfloat32) (EBool true)) = None. Proof. reflexivity. Qed.
Example rep_c64_accept      : resolve_expr UsePrintlnArg (EConvert (GoAST.tsyn GoNames.TNcomplex64) (EComplex GoTypes.dc_1p5_m2p5)) = Some (TComplex C64). Proof. vm_compute. reflexivity. Qed.
Example rep_c128_str_reject : resolve_expr UsePrintlnArg (EConvert (GoAST.tsyn GoNames.TNcomplex128) (EString "x")) = None. Proof. reflexivity. Qed.
Example rep_nested_accept   : resolve_expr UsePrintlnArg (EConvert (GoAST.tsyn GoNames.TNint8) (EConvert (GoAST.tsyn GoNames.TNint16) (EInt 127))) = Some (TInteger IInt8). Proof. reflexivity. Qed.
Example rep_nested_reject   : resolve_expr UsePrintlnArg (EConvert (GoAST.tsyn GoNames.TNint8) (EConvert (GoAST.tsyn GoNames.TNint16) (EInt 128))) = None. Proof. reflexivity. Qed.
Example rep_same_f32_identity :
  const_info (EConvert (GoAST.tsyn GoNames.TNfloat32) (EConvert (GoAST.tsyn GoNames.TNfloat32) (EFloat GoTypes.d_scar)))
  = const_info (EConvert (GoAST.tsyn GoNames.TNfloat32) (EFloat GoTypes.d_scar)). Proof. vm_compute. reflexivity. Qed.
Example rep_scalar_double_round_scar :
  const_info (EConvert (GoAST.tsyn GoNames.TNfloat32) (EFloat GoTypes.d_scar))
  <> const_info (EConvert (GoAST.tsyn GoNames.TNfloat32) (EConvert (GoAST.tsyn GoNames.TNfloat64) (EFloat GoTypes.d_scar))). Proof. vm_compute. discriminate. Qed.
Example rep_complex_component_scar :
  const_info (EConvert (GoAST.tsyn GoNames.TNcomplex64) (EComplex (mkDC GoTypes.d_scar GoTypes.d_0_0)))
  <> const_info (EConvert (GoAST.tsyn GoNames.TNcomplex64)
        (EConvert (GoAST.tsyn GoNames.TNcomplex128) (EComplex (mkDC GoTypes.d_scar GoTypes.d_0_0)))). Proof. vm_compute. discriminate. Qed.
(** NO type-name fact on a wrong-kind (expression) occurrence — the fact table's domain is exactly the
    type-name occurrences (mirrors [ef_package]/[ef_expr] domain exactness). *)
Example rep_no_tnfact_on_expr : forall e par role sub,
  occ_type_name_fact (GoIndex.mkOcc GoIndex.KExpression (GoIndex.ViewExpression e) (Some par) role sub) = None.
Proof. reflexivity. Qed.

(** on SUCCESS each package's bucket is a singleton (length = main count = 1). *)
Lemma ef_package_singleton {p ip} (facts : ElaborationFacts p ip) dir l :
  PM.find dir (ef_package_refs facts) = Some l -> exists d, l = [d].
Proof.
  intro E. pose proof (ef_package_len facts dir l E) as Hlen.
  assert (Hmem : list_dir_mem dir (GoAST.file_bindings (prog_files p)) = true).
  { apply (ef_package_present facts dir). apply PMF.in_find_iff. rewrite E. discriminate. }
  assert (Hmt : PM.MapsTo dir (mkPkgSummary (pkg_main_count dir (prog_files p))) (package_summaries (prog_files p))).
  { apply PMF.find_mapsto_iff. rewrite package_summaries_find, Hmem. reflexivity. }
  pose proof (proj1 (current_package_rules_exactly_one p) (proj2 (ef_source_valid facts)) dir _ Hmt) as Hone. cbn [ps_main_count] in Hone.
  rewrite Hone in Hlen. destruct l as [|d [|d2 rest]]; cbn [length] in Hlen; try discriminate. exists d; reflexivity.
Qed.

(** the public package-main query, TOTAL on success: the package's ONE canonical main, a PROJECTION of the
    retained facts (the singleton bucket's head) — never recomputed from a separate index. *)
Definition package_main_at {p ip} (facts : ElaborationFacts p ip) (r : PackageRef p) : GoIndex.DeclRef p.
Proof.
  remember (PM.find (package_ref_key r) (ef_package_refs facts)) as o eqn:E.
  destruct o as [l|].
  - destruct l as [|d rest].
    + exfalso. destruct (ef_package_singleton facts (package_ref_key r) [] (eq_sym E)) as [d Hd]; discriminate Hd.
    + exact d.
  - exfalso.
    assert (Hin : PM.In (package_ref_key r) (ef_package_refs facts))
      by (apply (ef_package_present facts), (package_ref_ok r)).
    apply PMF.in_find_iff in Hin. exact (Hin (eq_sym E)).
Defined.

Inductive ElaborationResult (p : GoProgram) (ip : GoIndex.IndexedProgram p) : Type :=
| ElaborationOK     (facts : ElaborationFacts p ip)
| ElaborationFailed (ds : list (DiagnosticReason p)) (Hne : ds <> nil).
Arguments ElaborationOK {p ip} _.
Arguments ElaborationFailed {p ip} _ _.

Record ProgramElaboration (p : GoProgram) : Type := mkProgramElaboration {
  pe_indexed : GoIndex.IndexedProgram p;
  pe_result  : ElaborationResult p pe_indexed
}.
Arguments mkProgramElaboration {p} _ _.
Arguments pe_indexed {p} _.
Arguments pe_result {p} _.

Definition list_is_nil {A} (l : list A) : {l = nil} + {l <> nil}.
Proof. destruct l; [left; reflexivity | right; discriminate]. Defined.

(** the ONE elaboration pass.  The shared collections — the index, the visit stream, the occurrence status
    map, and the package buckets — are computed ONCE (let-bound) and feed BOTH the accept/reject decision AND
    the successful [ElaborationFacts]: the expression facts and the diagnostics are two linear passes over the
    SAME [visit]/[status], and the [buckets] serve BOTH the package diagnostics ([bucket_diags_elems] — the
    package acceptance is the bucket LENGTHS, never [package_summaries]) and the retained facts.
    There is no separate facts recomputation.  The DECISION is exactly "the diagnostic pass produced
    nothing"; on success the retained facts are exposed with the derived validity, on failure the EXACT
    diagnostic list.  ([diags] is definitionally [semantic_diagnostics p idx], so the decision theorems below are
    unchanged.) *)
(* the phase-projected command-ordered expression + package diagnostics EQUAL the canonical
   [semantic_diagnostics] (the phase diags are [expr_diags], the bucket diags are [pkg_diags], both by identity). *)
Lemma elaborate_phase_raw_eq (p : GoProgram) (ip : GoIndex.IndexedProgram p) :
  let input := build_compilation_input p ip in
  let ph := build_expression_phase input in
  let idx := ci_idx input in
  let buckets := prog_package_refs_from_visit idx (ci_visit input) in
  bucket_flatten (node_keyed (ep_diags ph
      ++ bucket_diags_elems buckets (bucket_key_present idx) (PM.elements buckets) (elements_all_mapsto buckets)))
    ++ pkg_primary (ep_diags ph
      ++ bucket_diags_elems buckets (bucket_key_present idx) (PM.elements buckets) (elements_all_mapsto buckets))
  = semantic_diagnostics p idx.
Proof.
  cbn zeta. rewrite (ep_diags_eq_expr_diags (build_compilation_input p ip) (build_expression_phase (build_compilation_input p ip))).
  reflexivity.
Qed.

(* the phase-projected command-ordered diagnostics EQUAL the canonical [elaboration_diagnostics] — the bridge
   the decision theorems use (so they need not re-derive the transport). *)
Lemma elaborate_diags_eq_elaboration (p : GoProgram) (ip : GoIndex.IndexedProgram p) :
  let input := build_compilation_input p ip in
  let ph := build_expression_phase input in
  let idx := ci_idx input in
  let buckets := prog_package_refs_from_visit idx (ci_visit input) in
  command_diagnostics_of p (fresh_build_plan_of (prog_module p) (map fst (PM.elements buckets)) (root_layout p))
    (bucket_flatten (node_keyed (ep_diags ph
        ++ bucket_diags_elems buckets (bucket_key_present idx) (PM.elements buckets) (elements_all_mapsto buckets)))
     ++ pkg_primary (ep_diags ph
        ++ bucket_diags_elems buckets (bucket_key_present idx) (PM.elements buckets) (elements_all_mapsto buckets)))
  = elaboration_diagnostics p idx.
Proof. cbn zeta. rewrite (elaborate_phase_raw_eq p ip). exact (command_plan_diags_eq p ip). Qed.

Definition elaborate_indexed (p : GoProgram) (ip : GoIndex.IndexedProgram p) : ElaborationResult p ip :=
  let input   := build_compilation_input p ip in   (* §3 the ONE retained input, built ONCE (the sole [prog_blocks p]) *)
  let idx     := ci_idx input in                   (* = [indexed_syntax ip]; every builder reads THIS retained index *)
  let phase   := build_expression_phase input in   (* §8 the ONE ExpressionPhase: the retained TypeNameFactTable + the proof-carrying OutcomeTable, from the SAME [input] *)
  let tnft    := ep_tnft phase in                  (* the SEALED type-name TABLE OBJECT — the SAME [ep_ot phase] consumed and the facts/diagnostics both project *)
  let buckets := prog_package_refs_from_visit idx (ci_visit input) in  (* over the RETAINED [ci_visit] (= [prog_package_refs idx]) *)
  let rl      := root_layout p in
  let plan    := fresh_build_plan_of (prog_module p) (map fst (PM.elements buckets)) rl in
  let raw     := ep_diags phase                    (* §9.2 the TOTAL diagnostic projection of [ep_ot phase] *)
                   ++ bucket_diags_elems buckets (bucket_key_present idx)
                        (PM.elements buckets) (elements_all_mapsto buckets) in
  let diags   := command_diagnostics_of p plan
                   (bucket_flatten (node_keyed raw) ++ pkg_primary raw) in
  match list_is_nil diags with
  | left He  =>
      let He' : elaboration_diagnostics p idx = nil :=
        eq_trans (eq_sym (elaborate_diags_eq_elaboration p ip)) He in
      ElaborationOK (mkElaborationFacts
                  (ep_eft phase)                (* §2.8 the RETAINED fact object, stored by IDENTITY — never rebuilt *)
                  tnft
                  buckets
                  (prog_package_refs_present idx)
                  (prog_package_refs_bucket_len idx)
                  (prog_package_refs_belongs idx)
                  (elaboration_no_diags_source_valid p idx He')
                  (elaboration_no_diags_preflight p idx He')
                  rl
                  eq_refl
                  plan
                  (fresh_build_plan_of_buckets p idx))
  | right Hne => ElaborationFailed diags Hne
  end.

Definition elaborate (p : GoProgram) : ProgramElaboration p :=
  let ip := GoIndex.index_program p in
  mkProgramElaboration ip (elaborate_indexed p ip).

(** ★§5/§3.8 THE SEALED TABLE IS THE CONSTRUCTED-AND-CONSUMED TABLE (OBJECT IDENTITY): the type-name-fact table
    sealed into a successful [ElaborationFacts] IS [ep_tnft] of the ExpressionPhase actually built in the retained
    phase — the SAME object the [ExprOutcomeTable] ([ep_ot phase]) was built consuming and the total facts +
    diagnostics both project.  This quantifies over the table object CONSTRUCTED in the phase, not a global helper. *)
Theorem elaborate_ok_seals_tnfacts (p : GoProgram) facts :
  pe_result (elaborate p) = ElaborationOK facts ->
  ef_type_name_facts facts
  = ep_tnft (build_expression_phase (build_compilation_input p (GoIndex.index_program p))).
Proof.
  unfold elaborate, elaborate_indexed; cbn [pe_result]; cbv zeta.
  match goal with |- context[list_is_nil ?d] => destruct (list_is_nil d) as [He|Hne] end.
  - intro H. injection H as <-. reflexivity.
  - discriminate.
Qed.

(** §9/§2.8 the SEALED ExprFactTable OBJECT (OBJECT IDENTITY, not map equality): a successful ElaborationFacts
    stores the EXACT [ep_eft] object retained in the phase actually built — the fact-side mirror of
    [elaborate_ok_seals_tnfacts].  The phase RETAINS the proof-backed table and [elaborate] stores THAT object;
    it is not a fresh [mkExprFactTable] whose map merely equals the projection. *)
Theorem elaborate_ok_seals_facts (p : GoProgram) facts :
  pe_result (elaborate p) = ElaborationOK facts ->
  ef_expr_facts facts
  = ep_eft (build_expression_phase (build_compilation_input p (GoIndex.index_program p))).
Proof.
  unfold elaborate, elaborate_indexed; cbn [pe_result]; cbv zeta.
  match goal with |- context[list_is_nil ?d] => destruct (list_is_nil d) as [He|Hne] end.
  - intro H. injection H as <-. reflexivity.
  - discriminate.
Qed.

(** §5/§2.9 the sealed type-name table has RETAINED-INPUT PROVENANCE: it IS the exact
    [build_type_name_fact_table] of the phase's own [CompilationInput] (composing the object-identity seal with
    the phase's [ep_tnft_prov]) — not merely some [TypeNameFactTable p]. *)
Corollary elaborate_ok_seals_tnfacts_from_input (p : GoProgram) facts :
  pe_result (elaborate p) = ElaborationOK facts ->
  ef_type_name_facts facts
  = build_type_name_fact_table (build_compilation_input p (GoIndex.index_program p)).
Proof.
  intro H. rewrite (elaborate_ok_seals_tnfacts p facts H).
  exact (ep_tnft_prov (build_expression_phase (build_compilation_input p (GoIndex.index_program p)))).
Qed.

(** ELABORATION EXACTNESS: elaboration succeeds (exposes facts) IFF the program is admissible ([GoCompile] =
    fresh-build preflight passes AND the source is valid); it fails (exposes nonempty command-ordered
    diagnostics) IFF it is inadmissible.  Success and failure are exclusive.  (The [diags] computed inside
    [elaborate_indexed] runs on the RETAINED bucket-derived [plan]; [command_plan_diags_eq] bridges it to the
    canonical [elaboration_diagnostics] — the only difference is the plan presentation — so both reduce through
    [elaboration_diagnostics_nil_iff_GoCompile].) *)
Theorem elaborate_ok_iff_GoCompile (p : GoProgram) :
  (exists facts, pe_result (elaborate p) = ElaborationOK facts) <-> GoCompile p.
Proof.
  unfold elaborate, elaborate_indexed; cbn [pe_result]; cbv zeta.
  match goal with |- context[list_is_nil ?d] => destruct (list_is_nil d) as [He|Hne] end.
  - split; intro Hx;
      [ exact (proj1 (elaboration_diagnostics_nil_iff_GoCompile p (GoIndex.indexed_syntax (GoIndex.index_program p)))
                 (eq_trans (eq_sym (elaborate_diags_eq_elaboration p (GoIndex.index_program p))) He))
      | eexists; reflexivity ].
  - split; intro Hx.
    + destruct Hx as [facts Hf]; discriminate Hf.
    + exfalso. apply Hne.
      exact (eq_trans (elaborate_diags_eq_elaboration p (GoIndex.index_program p))
               (proj2 (elaboration_diagnostics_nil_iff_GoCompile p (GoIndex.indexed_syntax (GoIndex.index_program p))) Hx)).
Qed.

Theorem elaborate_failed_iff_not_GoCompile (p : GoProgram) :
  (exists ds Hne, pe_result (elaborate p) = ElaborationFailed ds Hne) <-> ~ GoCompile p.
Proof.
  unfold elaborate, elaborate_indexed; cbn [pe_result]; cbv zeta.
  match goal with |- context[list_is_nil ?d] => destruct (list_is_nil d) as [He|Hne] end.
  - split; intro Hx.
    + destruct Hx as [ds [Hne Hf]]; discriminate Hf.
    + exfalso. apply Hx.
      exact (proj1 (elaboration_diagnostics_nil_iff_GoCompile p (GoIndex.indexed_syntax (GoIndex.index_program p)))
               (eq_trans (eq_sym (elaborate_diags_eq_elaboration p (GoIndex.index_program p))) He)).
  - split; intro Hx.
    + intro Hv. apply Hne.
      exact (eq_trans (elaborate_diags_eq_elaboration p (GoIndex.index_program p))
               (proj2 (elaboration_diagnostics_nil_iff_GoCompile p (GoIndex.indexed_syntax (GoIndex.index_program p))) Hv)).
    + eexists; eexists; reflexivity.
Qed.

(** on failure the exposed diagnostics ARE the command-ordered [elaboration_diagnostics] (used to project the legacy class). *)
Lemma elaborate_failed_ds (p : GoProgram) ds Hne :
  pe_result (elaborate p) = ElaborationFailed ds Hne ->
  ds = elaboration_diagnostics p (GoIndex.indexed_syntax (GoIndex.index_program p)).
Proof.
  unfold elaborate, elaborate_indexed; cbn [pe_result]; cbv zeta.
  match goal with |- context[list_is_nil ?d] => destruct (list_is_nil d) as [He|Hn] end.
  - intro H; discriminate H.
  - intro H. inversion H. exact (elaborate_diags_eq_elaboration p (GoIndex.index_program p)).
Qed.

(** A failed elaboration result is incompatible with validity (used to discharge the impossible branch when
    minting the provenance sigma from a validity proof). *)
Lemma elaborate_failed_not_valid (p : GoProgram) ds Hne :
  pe_result (elaborate p) = ElaborationFailed ds Hne -> GoCompile p -> False.
Proof.
  intros Heq Hv.
  exact (proj1 (elaborate_failed_iff_not_GoCompile p) (ex_intro _ ds (ex_intro _ Hne Heq)) Hv).
Qed.

(** The one production elaboration result, CASE-SPLIT into its OK / Failed shape WITH the defining equation
    retained (a plain [match] on the retained [pe_result], not a proof-mode convoy fight): every downstream
    [go_compile] fact is derived from this, so nothing re-destructs [elaborate] under its dependent motive. *)
Definition elaboration_result_cases (p : GoProgram) :
  {facts : ElaborationFacts p (pe_indexed (elaborate p)) & pe_result (elaborate p) = ElaborationOK facts} +
  {ds : list (DiagnosticReason p) & {Hne : ds <> nil & pe_result (elaborate p) = ElaborationFailed ds Hne}} :=
  match pe_result (elaborate p) as r
    return pe_result (elaborate p) = r ->
      {facts : ElaborationFacts p (pe_indexed (elaborate p)) & pe_result (elaborate p) = ElaborationOK facts} +
      {ds : list (DiagnosticReason p) & {Hne : ds <> nil & pe_result (elaborate p) = ElaborationFailed ds Hne}}
  with
  | ElaborationOK facts      => fun Heq => inl (existT _ facts Heq)
  | ElaborationFailed ds Hne => fun Heq => inr (existT _ ds (existT _ Hne Heq))
  end eq_refl.

(** From a validity proof, the EXACT [ElaborationOK] result + its facts (the failed branch is impossible).  This
    is the provenance witness a [CompilableProgram] must carry: the stored facts ARE [elaborate]'s output. *)
Definition elaboration_ok_sig (p : GoProgram) (H : GoCompile p) :
  {facts : ElaborationFacts p (pe_indexed (elaborate p)) & pe_result (elaborate p) = ElaborationOK facts} :=
  match elaboration_result_cases p with
  | inl s => s
  | inr b => False_rect _
      (elaborate_failed_not_valid p (projT1 b) (projT1 (projT2 b)) (projT2 (projT2 b)) H)
  end.

(* [GoCompile] and its [elaboration_diagnostics]-emptiness bridge are defined earlier (before [elaborate]), since the elaboration
   exactness theorems below are stated over [GoCompile]. *)

(** ---- destructuring the ONE retained [elaborate] WITHOUT re-projection: record eta re-assembles the elaboration
    from its projections, so a component-level [pe_result] fact lifts to a WHOLE-elaboration equation
    ([elaborate p = mkProgramElaboration ip (ElaborationOK/Failed …)] — homogeneous, no index transport).  The
    non-dependent [semantic_ok_flag] lets such a whole equation discriminate OK-vs-Failed by [rewrite] (no
    dependent [f_equal] over the indexed [pe_result]). ---- *)
Lemma program_elaboration_eta {p} (a : ProgramElaboration p) :
  a = mkProgramElaboration (pe_indexed a) (pe_result a).
Proof. destruct a; reflexivity. Qed.

Definition result_ok_b {p ip} (r : ElaborationResult p ip) : bool :=
  match r with ElaborationOK _ => true | ElaborationFailed _ _ => false end.
Definition semantic_ok_flag {p} (a : ProgramElaboration p) : bool := result_ok_b (pe_result a).

Lemma semantic_ok_flag_of_valid : forall p, GoCompile p -> semantic_ok_flag (elaborate p) = true.
Proof. intros p Hv. unfold semantic_ok_flag. destruct (elaboration_ok_sig p Hv) as [facts Heq]. rewrite Heq. reflexivity. Qed.

Lemma elaborate_ok_whole : forall p facts, pe_result (elaborate p) = ElaborationOK facts ->
  elaborate p = mkProgramElaboration (pe_indexed (elaborate p)) (ElaborationOK facts).
Proof.
  intros p facts H.
  transitivity (mkProgramElaboration (pe_indexed (elaborate p)) (pe_result (elaborate p))).
  - apply program_elaboration_eta.
  - rewrite H. reflexivity.
Qed.

Lemma elaborate_failed_whole : forall p ds Hne, pe_result (elaborate p) = ElaborationFailed ds Hne ->
  elaborate p = mkProgramElaboration (pe_indexed (elaborate p)) (ElaborationFailed ds Hne).
Proof.
  intros p ds Hne H.
  transitivity (mkProgramElaboration (pe_indexed (elaborate p)) (pe_result (elaborate p))).
  - apply program_elaboration_eta.
  - rewrite H. reflexivity.
Qed.

Lemma elaborate_whole_failed_not_valid : forall p ip ds Hne,
  elaborate p = mkProgramElaboration ip (ElaborationFailed ds Hne) -> GoCompile p -> False.
Proof.
  intros p ip ds Hne Hw Hv.
  pose proof (semantic_ok_flag_of_valid p Hv) as Hok.
  rewrite Hw in Hok. discriminate Hok.
Qed.

(** the witness-path destructuring: match the whole retained elaboration EXACTLY ONCE, binding its retained index
    [ip] and result; validity rules the Failed branch impossible.  [ip] and [facts] come from the SAME
    evaluation — never a [pe_indexed (elaborate p)] re-projection. *)
Definition elaboration_ok_full (p : GoProgram) (H : GoCompile p) :
  {ip : GoIndex.IndexedProgram p & {facts : ElaborationFacts p ip | elaborate p = mkProgramElaboration ip (ElaborationOK facts)}} :=
  match elaborate p as a
    return (elaborate p = a ->
      {ip : GoIndex.IndexedProgram p & {facts : ElaborationFacts p ip | elaborate p = mkProgramElaboration ip (ElaborationOK facts)}})
  with
  | mkProgramElaboration ip res =>
      fun Ha =>
      match res as r
        return (res = r ->
          {ip0 : GoIndex.IndexedProgram p & {facts : ElaborationFacts p ip0 | elaborate p = mkProgramElaboration ip0 (ElaborationOK facts)}})
      with
      | ElaborationOK facts      => fun Hr =>
          existT _ ip (exist _ facts (eq_trans Ha (f_equal (mkProgramElaboration ip) Hr)))
      | ElaborationFailed ds Hne => fun Hr =>
          False_rect _ (elaborate_whole_failed_not_valid p ip ds Hne (eq_trans Ha (f_equal (mkProgramElaboration ip) Hr)) H)
      end eq_refl
  end eq_refl.

(** a compiled program RETAINS the ONE evaluated elaboration by DESTRUCTURING it: the original
    program, the EXACT elaborated [IndexedProgram] ([cp_index]) BOUND from that elaboration, and its
    [ElaborationFacts] indexed BY that retained index ([cp_facts : ElaborationFacts cp_program cp_index] — no
    [pe_indexed (elaborate …)] re-projection).  The mandatory [cp_prov] field PROVES the WHOLE retained elaboration
    IS this record ([elaborate cp_program = mkProgramElaboration cp_index (ElaborationOK cp_facts)] — a HOMOGENEOUS
    equation, no index transport, pinning index + facts + success together).  There is therefore NO way to
    construct a [CompilableProgram] for a program [elaborate] rejects, the index is never reconstructed, and
    there is no parallel capability path.  [cp_ok] projects the retained facts' validity.  [cp_program] stays a
    direct first-field projection, so rendering/emission never reduce [elaborate] (the opaque,
    vm-compute-unfriendly index — the constraint). *)
Record CompilableProgram : Type := mkCompilable {
  cp_program : GoProgram;
  cp_index   : GoIndex.IndexedProgram cp_program;
  cp_facts   : ElaborationFacts cp_program cp_index;
  cp_prov    : elaborate cp_program = mkProgramElaboration cp_index (ElaborationOK cp_facts)
}.

Definition cp_ok (cp : CompilableProgram) : GoCompile (cp_program cp) :=
  conj (ef_preflight (cp_facts cp))
       (ef_source_valid (cp_facts cp)).

(** the PROVENANCE surfaces: every [CompilableProgram]'s WHOLE retained elaboration IS this record — index +
    facts + success together ([elaborate cp_program = mkProgramElaboration cp_index (ElaborationOK cp_facts)]); the
    retained index therefore IS [elaborate]'s (the projection retains, it does not reconstruct). *)
Theorem compilable_prov : forall cp : CompilableProgram,
  elaborate (cp_program cp) = mkProgramElaboration (cp_index cp) (ElaborationOK (cp_facts cp)).
Proof. intro cp; exact (cp_prov cp). Qed.

Theorem compilable_index_retained : forall cp : CompilableProgram,
  cp_index cp = pe_indexed (elaborate (cp_program cp)).
Proof. intro cp. rewrite (cp_prov cp). reflexivity. Qed.

(** The compiled evidence EXPOSES that the same program is typed through [GoTypes]: an immediate
    canonical projection, not a stored second copy of the typing proof. *)
Theorem compile_program_typed : forall p, GoCompile p -> ProgramTyped p.
Proof. intros p H; exact (proj1 (proj2 H)). Qed.

Theorem compilable_program_typed : forall cp : CompilableProgram, ProgramTyped (cp_program cp).
Proof. intro cp; exact (compile_program_typed _ (cp_ok cp)). Qed.

(** ---- the proof-producing executable compiler ---- *)

(** a structured failure bundle: the EXACT elaboration diagnostics + their nonempty proof. *)
Record CompileFailure (p : GoProgram) : Type := mkCompileFailure {
  cfail_diags    : list (DiagnosticReason p) ;
  cfail_nonempty : cfail_diags <> nil
}.
Arguments mkCompileFailure {p} _ _.
Arguments cfail_diags {p} _.
Arguments cfail_nonempty {p} _.

Inductive CompileOutcome (p : GoProgram) : Type :=
| CompiledOk    (cp : CompilableProgram) (Hcp : cp_program cp = p)
| CompileFailed (fail : CompileFailure p).
Arguments CompiledOk {p} _ _.
Arguments CompileFailed {p} _.

(** the LEGACY coarse class, a PROJECTION of the elaboration diagnostics (never a separate check): a typing-class
    diagnostic dominates, else a package-class diagnostic, else success. *)
Inductive LegacyCompileClass : Type := LCOk | LCTyping | LCPackageMainCount | LCBuildOutput.
(* the build-output failure takes PRECEDENCE: a preflight failure reports ONLY the
   build-output-directory diagnostic, so its class dominates. *)
Definition legacy_class_of_diags {p} (ds : list (DiagnosticReason p)) : LegacyCompileClass :=
  if existsb diag_is_build_output ds then LCBuildOutput
  else if existsb diag_is_typing ds then LCTyping
  else if existsb diag_is_package ds then LCPackageMainCount else LCOk.
Definition legacy_compile_class {p} (o : CompileOutcome p) : LegacyCompileClass :=
  match o with CompiledOk _ _ => LCOk | CompileFailed fail => legacy_class_of_diags (cfail_diags fail) end.

(** the production compiler DESTRUCTURES the ONE retained [elaborate] EXACTLY ONCE: [outcome_of_elaboration]
    matches the WHOLE [ProgramElaboration] (binding its retained index [ip] and result), so [ElaborationOK] mints a
    [CompilableProgram] whose [cp_index] IS that bound [ip] (never a [pe_indexed] re-projection) and whose
    [cp_prov] is [elaborate p = mkProgramElaboration ip (ElaborationOK facts)] (built from the two match equations).
    Failure CARRIES the exact elaboration diagnostics — never a second checker or a coarse recomputation. *)
Definition outcome_of_elaboration (p : GoProgram) (a : ProgramElaboration p) :
  elaborate p = a -> CompileOutcome p :=
  match a as a0 return (elaborate p = a0 -> CompileOutcome p) with
  | mkProgramElaboration ip res =>
      fun Ha =>
      match res as r return (res = r -> CompileOutcome p) with
      | ElaborationOK facts      => fun Hr =>
          CompiledOk (mkCompilable p ip facts (eq_trans Ha (f_equal (mkProgramElaboration ip) Hr))) eq_refl
      | ElaborationFailed ds Hne => fun _  => CompileFailed (mkCompileFailure ds Hne)
      end eq_refl
  end.

Definition go_compile (p : GoProgram) : CompileOutcome p :=
  outcome_of_elaboration p (elaborate p) eq_refl.

(** the two computation facts of [outcome_of_elaboration], stated over the whole elaboration pinned to a constructor:
    the nested matches collapse by iota (no dependent-convoy reasoning against [elaborate]). *)
Lemma outcome_of_elaboration_ok_eq : forall p ip facts (Ha : elaborate p = mkProgramElaboration ip (ElaborationOK facts)),
  outcome_of_elaboration p (mkProgramElaboration ip (ElaborationOK facts)) Ha = CompiledOk (mkCompilable p ip facts Ha) eq_refl.
Proof. intros p ip facts Ha. reflexivity. Qed.

Lemma outcome_of_elaboration_failed_eq : forall p ip ds Hne (Ha : elaborate p = mkProgramElaboration ip (ElaborationFailed ds Hne)),
  outcome_of_elaboration p (mkProgramElaboration ip (ElaborationFailed ds Hne)) Ha = CompileFailed (mkCompileFailure ds Hne).
Proof. intros p ip ds Hne Ha. reflexivity. Qed.

(** the shape facts over a genuine VARIABLE [a] equal to a constructor: [subst] collapses the nested
    matches by iota — no dependent [rewrite] against [elaborate] under a binder. *)
Lemma outcome_of_elaboration_eq_ok : forall p (a : ProgramElaboration p) (Ha : elaborate p = a) ip facts,
  a = mkProgramElaboration ip (ElaborationOK facts) ->
  exists cp Hcp, outcome_of_elaboration p a Ha = CompiledOk cp Hcp.
Proof.
  intros p a Ha ip facts Heq. revert Ha. rewrite Heq. intro Ha.
  exists (mkCompilable p ip facts Ha). exists eq_refl. apply outcome_of_elaboration_ok_eq.
Qed.

Lemma outcome_of_elaboration_eq_failed : forall p (a : ProgramElaboration p) (Ha : elaborate p = a) ip ds Hne,
  a = mkProgramElaboration ip (ElaborationFailed ds Hne) ->
  outcome_of_elaboration p a Ha = CompileFailed (mkCompileFailure ds Hne).
Proof.
  intros p a Ha ip ds Hne Heq. revert Ha. rewrite Heq. intro Ha. apply outcome_of_elaboration_failed_eq.
Qed.

Lemma go_compile_ok_shape : forall p ip facts,
  elaborate p = mkProgramElaboration ip (ElaborationOK facts) ->
  exists cp Hcp, go_compile p = CompiledOk cp Hcp.
Proof.
  intros p ip facts Hp. unfold go_compile.
  exact (outcome_of_elaboration_eq_ok p (elaborate p) eq_refl ip facts Hp).
Qed.

Lemma go_compile_failed_shape : forall p ip ds Hne,
  elaborate p = mkProgramElaboration ip (ElaborationFailed ds Hne) ->
  go_compile p = CompileFailed (mkCompileFailure ds Hne).
Proof.
  intros p ip ds Hne Hp. unfold go_compile.
  exact (outcome_of_elaboration_eq_failed p (elaborate p) eq_refl ip ds Hne Hp).
Qed.

(** (A) internal exactness: [go_compile] succeeds exactly on admissible programs, whole-program.  Success value
    carries its OWN validity (via [ef_source_valid (cp_facts cp)]) and program identity (via [Hcp]) — derivable from
    the compiled artifact's fields regardless of HOW it was produced. *)
Theorem go_compile_ok_valid : forall p cp Hcp,
  go_compile p = CompiledOk cp Hcp -> cp_program cp = p /\ GoCompile (cp_program cp).
Proof.
  intros p cp Hcp _. split; [ exact Hcp | exact (cp_ok cp) ].
Qed.

Theorem go_compile_complete : forall p,
  GoCompile p -> exists cp Hcp, go_compile p = CompiledOk cp Hcp.
Proof.
  intros p Hvalid.
  destruct (elaboration_ok_sig p Hvalid) as [ facts Heq ].
  exact (go_compile_ok_shape p (pe_indexed (elaborate p)) facts (elaborate_ok_whole p facts Heq)).
Qed.

(** fixture helper: acceptance through the theorems — the source decision ([source_spec_valid_b]) AND the fresh-build
    preflight decision together are exactly [GoCompile]. *)
Lemma go_compile_ok_of_source_spec_valid_b : forall p,
  source_spec_valid_b p = true -> fresh_build_disposition_ok (fresh_build_plan p) = true ->
  exists cp Hcp, go_compile p = CompiledOk cp Hcp.
Proof.
  intros p H Hpf. apply go_compile_complete. split.
  - unfold fresh_build_preflight_ok. exact Hpf.
  - apply (proj1 (source_spec_valid_b_iff p)); exact H.
Qed.

(** witness ergonomics: [GoCompile] from the two DECIDABLE checks — the source [source_spec_valid_b] AND the
    fresh-build output preflight (both discharge by [vm_compute]).  This is the intro the emit witnesses use. *)
Lemma GoCompile_of_source_spec_valid_b : forall p,
  source_spec_valid_b p = true -> fresh_build_disposition_ok (fresh_build_plan p) = true -> GoCompile p.
Proof.
  intros p H Hpf. split.
  - unfold fresh_build_preflight_ok. exact Hpf.
  - apply (proj1 (source_spec_valid_b_iff p)); exact H.
Qed.

(** DECLARATIVE AND EXECUTABLE EXACTNESS.  The three diagnostic layers each have an emptiness/equivalence
    characterization, and the two-branch command structure is pinned:

      A. [semantic_diagnostics_empty_iff_source_valid] : semantic report empty  <-> SourceProgramValid
      B. [fresh_build_diagnostics_nil_iff]             : fresh report empty      <-> fresh_build_preflight_ok
      C. [elaboration_diagnostics_nil_iff_GoCompile]   : final report empty      <-> GoCompile
      D. [elaborate_ok_iff_GoCompile]                  : elaboration exposes facts <-> GoCompile
      E. [elaborate_failed_iff_not_GoCompile]          : elaboration fails         <-> ~ GoCompile
      F. [elaboration_diagnostics_fresh_failure]       : preflight fails -> final report = [one build-output dir]
      G. [elaboration_diagnostics_eq_semantic]         : preflight succeeds -> final report = semantic report
      H. [go_compile_projects_elaborate]               : go_compile only PROJECTS one elaboration (no re-check)
      I. [compilable_prov]/[compilable_index_retained]/[cp_build_plan] : retention of program/index/facts/plan.

    (B, C, D, E, G are proved above at their definitions.)  J — the DirectoryImage layout bridge — lives in
    GoEmit.  The final equivalence to external cmd/go stays DIFFERENTIAL evidence, not a Rocq theorem. *)

(** SOURCE SEMANTICS: the semantic (source/compiler/package) diagnostics are empty EXACTLY on a
    source-valid program (composes [semantic_diagnostics_empty_iff] with the DIRECT [semantic_ok_b_SourceProgramValid]). *)
Theorem semantic_diagnostics_empty_iff_source_valid : forall p idx,
  semantic_diagnostics p idx = nil <-> SourceProgramValid p.
Proof.
  intros p idx. split.
  - intro H. apply (proj1 (semantic_ok_b_SourceProgramValid p)),
                   (proj1 (semantic_diagnostics_empty_iff p idx)); exact H.
  - intro H. apply (proj2 (semantic_diagnostics_empty_iff p idx)), (proj2 (semantic_ok_b_SourceProgramValid p)); exact H.
Qed.

(** the sole-package plan expressed exactly (iota over the singleton [selected_package_keys]). *)
Lemma fresh_build_plan_of_sole : forall p dir,
  selected_package_keys p = [dir] ->
  fresh_build_plan p = FBDWriteSingleMain dir (package_import_path (prog_module p) dir)
                          (default_exec_name (prog_module p) dir)
                          (PM.find (default_exec_name (prog_module p) dir) (root_layout p)).
Proof. intros p dir Hk. unfold fresh_build_plan. rewrite Hk. reflexivity. Qed.

(** FAILURE PRECEDENCE (fresh half): when the output preflight FAILS, the fresh-build report is EXACTLY
    the single build-output-directory diagnostic for the sole package. *)
Lemma fresh_build_diagnostics_fail_singleton : forall p,
  fresh_build_disposition_ok (fresh_build_plan p) = false ->
  exists pk name, fresh_build_diagnostics p = [DRBuildOutputIsDirectory pk name].
Proof.
  intros p Hpf. destruct (proj1 (preflight_fails_iff p) Hpf) as [dir [Hk Hfind]].
  destruct (sole_package_ref_some p dir (sole_package_present p dir Hk)) as [pk Hpk].
  exists pk. exists (default_exec_name (prog_module p) dir).
  unfold fresh_build_diagnostics, fresh_build_diagnostics_of. rewrite (fresh_build_plan_of_sole p dir Hk), Hfind, Hpk. reflexivity.
Qed.

(** the COMMAND-FACING report inherits it: a failed preflight hides ALL semantic diagnostics, exposing
    only the one build-output-directory diagnostic. *)
Theorem elaboration_diagnostics_fresh_failure : forall p idx,
  fresh_build_disposition_ok (fresh_build_plan p) = false ->
  exists pk name, elaboration_diagnostics p idx = [DRBuildOutputIsDirectory pk name].
Proof.
  intros p idx Hpf. rewrite (elaboration_diagnostics_eq_fresh p idx Hpf).
  apply (fresh_build_diagnostics_fail_singleton p Hpf).
Qed.

(** the production compiler is a PROJECTION of the ONE elaboration: [go_compile] IS DEFINITIONALLY the
    outcome of the retained [elaborate p].  It runs no [source_spec_valid_b] and no second checker. *)
Lemma go_compile_projects_elaborate : forall p,
  go_compile p = outcome_of_elaboration p (elaborate p) eq_refl.
Proof. intro p. reflexivity. Qed.

(** RETENTION: [compilable_prov]/[compilable_index_retained] retain the exact program/index/facts/
    provenance; the FreshBuildPlan is retained by DERIVATION from the retained program. *)
Definition cp_build_plan (cp : CompilableProgram) : FreshBuildDisposition :=
  ef_build_plan (cp_facts cp).

Definition cp_root_layout (cp : CompilableProgram) : PM.t FreshRootEntryKind :=
  ef_root_layout (cp_facts cp).

(** the retained plan / root layout are PROJECTIONS of the retained [ElaborationFacts], and they equal
    the program's (the coherence is carried IN the facts by the elaboration, not recomputed at the projection). *)
Lemma cp_build_plan_retained : forall cp, cp_build_plan cp = fresh_build_plan (cp_program cp).
Proof. intro cp. exact (ef_build_plan_ok (cp_facts cp)). Qed.

Lemma cp_root_layout_retained : forall cp, cp_root_layout cp = root_layout (cp_program cp).
Proof. intro cp. exact (ef_root_layout_ok (cp_facts cp)). Qed.

(** the witness builder: from validity, [elaboration_ok_full] destructures [elaborate p] ONCE, delivering the bound
    retained index [ip], its [ElaborationFacts], and the whole-elaboration provenance.  That single execution is
    let-bound and all three constructor arguments PROJECT it — [cp_index], [cp_facts], and [cp_prov] come from
    ONE elaboration, never three reruns.  [cp_program] is a direct first-field projection ([= p]) so
    rendering/emission never reduce the opaque, vm-compute-unfriendly index elaboration.  This is the SAME
    single-destructuring provenance [go_compile]'s success value carries — the two artifacts are built ONE way. *)
Definition compilable_of_valid (p : GoProgram) (H : GoCompile p) : CompilableProgram :=
  let s  := elaboration_ok_full p H in
  let fs := projT2 s in
  mkCompilable p (projT1 s) (proj1_sig fs) (proj2_sig fs).

(** fixture helper: a non-typed program is REJECTED at the TYPING legacy class — a projection of the carried
    diagnostics, never a [program_typedb] rerun. *)
Lemma go_compile_untyped : forall p, program_typedb p = false ->
  fresh_build_disposition_ok (fresh_build_plan p) = true ->
  legacy_compile_class (go_compile p) = LCTyping.
Proof.
  intros p Hf Hpf.
  destruct (elaboration_result_cases p) as [ [facts Hok] | [ds [Hne Hfail]] ].
  - exfalso. assert (Hgc : GoCompile p) by (apply (elaborate_ok_iff_GoCompile p); exists facts; exact Hok).
    pose proof (proj2 (program_typedb_iff predeclared_type p) (compile_program_typed p Hgc)) as Ht. rewrite Ht in Hf; discriminate Hf.
  - rewrite (go_compile_failed_shape p (pe_indexed (elaborate p)) ds Hne (elaborate_failed_whole p ds Hne Hfail)).
    cbn [legacy_compile_class cfail_diags]. unfold legacy_class_of_diags.
    rewrite (elaborate_failed_ds p ds Hne Hfail), (elaboration_diagnostics_eq_semantic p _ Hpf),
            existsb_build_output_semantic, existsb_typing_semantic, Hf. reflexivity.
Qed.

(** A rejected program yields no CompilableProgram (and hence no SafeProgram, no image). *)
Lemma reject_no_compile : forall p, source_spec_valid_b p = false -> ~ GoCompile p.
Proof.
  intros p E [_ Hsv].
  pose proof (proj2 (source_spec_valid_b_iff p) Hsv) as Hok.
  rewrite Hok in E; discriminate.
Qed.

(** ---- ORDER-INDEPENDENCE of admissibility: [GoCompile] / [go_compile] depend only on the file MAP,
    never on construction order (typing respects the map by [ProgramTyped_Equal]; the package summaries
    respect it by [package_summaries_Equal]). ---- *)

(* the SOURCE admission [SourceProgramValid] depends only on the file MAP (FilesEqual).  The FULL admission
   [GoCompile] also depends on the ModuleSpec (via the fresh-build preflight), so it needs [ProgramInputEqual]
   below.  (This is the SOLE map-equality proof; the old [ProgValid_Equal] is deleted.) *)
Theorem SourceProgramValid_Equal : forall p1 p2,
  GoAST.FilesEqual (prog_files p1) (prog_files p2) -> SourceProgramValid p1 -> SourceProgramValid p2.
Proof.
  intros p1 p2 Heq [Ht [Hdu Hme]]. split; [ exact (ProgramTyped_Equal predeclared_type p1 p2 Heq Ht) |].
  assert (Hconv : forall dir s, PM.MapsTo dir s (package_summaries (prog_files p2)) ->
                                PM.MapsTo dir s (package_summaries (prog_files p1))).
  { intros dir s Hmt. apply PMF.find_mapsto_iff.
    rewrite (package_summaries_Equal (prog_files p1) (prog_files p2) Heq dir).
    apply PMF.find_mapsto_iff. exact Hmt. }
  split; intros dir s Hmt; [ apply (Hdu dir s) | apply (Hme dir s) ]; apply Hconv; exact Hmt.
Qed.

Theorem source_spec_valid_b_Equal : forall p1 p2,
  GoAST.FilesEqual (prog_files p1) (prog_files p2) -> source_spec_valid_b p1 = source_spec_valid_b p2.
Proof.
  intros p1 p2 Heq.
  destruct (source_spec_valid_b p1) eqn:E1; destruct (source_spec_valid_b p2) eqn:E2; try reflexivity.
  - apply (proj1 (source_spec_valid_b_iff p1)) in E1. apply (SourceProgramValid_Equal p1 p2 Heq) in E1.
    apply (proj2 (source_spec_valid_b_iff p2)) in E1. rewrite E1 in E2; discriminate.
  - apply (proj1 (source_spec_valid_b_iff p2)) in E2. apply (SourceProgramValid_Equal p2 p1 (GoAST.FilesEqual_sym _ _ Heq)) in E2.
    apply (proj2 (source_spec_valid_b_iff p1)) in E2. rewrite E2 in E1; discriminate.
Qed.

(* [source_spec_valid_b] is exactly the conjunction of the two decision halves. *)
Lemma source_spec_valid_b_eq : forall p, source_spec_valid_b p = program_typedb p && source_spec_package_rules_b p.
Proof. reflexivity. Qed.

(** the [go_compile] LEGACY CLASS (a projection of the carried diagnostics) — invariant under file insertion
    order.  It matches the decision: success -> [LCOk]; not typed -> [LCTyping]; typed but bad package -> [LCPackageMainCount]. *)
Definition go_compile_class (p : GoProgram) : LegacyCompileClass := legacy_compile_class (go_compile p).

Lemma go_compile_class_spec : forall p,
  go_compile_class p
  = (if fresh_build_disposition_ok (fresh_build_plan p)
     then (if source_spec_valid_b p then LCOk else if program_typedb p then LCPackageMainCount else LCTyping)
     else LCBuildOutput).
Proof.
  intro p. unfold go_compile_class.
  destruct (elaboration_result_cases p) as [ [facts Hok] | [ds [Hne Hfail]] ].
  - assert (Hgc : GoCompile p) by (apply (elaborate_ok_iff_GoCompile p); exists facts; exact Hok).
    destruct Hgc as [Hpf Hsv]. unfold fresh_build_preflight_ok in Hpf. rewrite Hpf.
    destruct (go_compile_ok_shape p (pe_indexed (elaborate p)) facts (elaborate_ok_whole p facts Hok)) as [cp [Hcp Hgo]]. rewrite Hgo.
    cbn [legacy_compile_class]. rewrite (proj2 (source_spec_valid_b_iff p) Hsv). reflexivity.
  - rewrite (go_compile_failed_shape p (pe_indexed (elaborate p)) ds Hne (elaborate_failed_whole p ds Hne Hfail)).
    cbn [legacy_compile_class cfail_diags]. unfold legacy_class_of_diags.
    rewrite (elaborate_failed_ds p ds Hne Hfail).
    destruct (fresh_build_disposition_ok (fresh_build_plan p)) eqn:Ep.
    + rewrite (elaboration_diagnostics_eq_semantic p _ Ep), existsb_build_output_semantic,
              existsb_typing_semantic, existsb_package_semantic.
      assert (Hnv : ~ GoCompile p) by (apply (elaborate_failed_iff_not_GoCompile p); exists ds; exists Hne; exact Hfail).
      assert (Hpok : source_spec_valid_b p = false).
      { destruct (source_spec_valid_b p) eqn:Epk; [ | reflexivity ]. exfalso. apply Hnv. split.
        - unfold fresh_build_preflight_ok. exact Ep.
        - apply (proj1 (source_spec_valid_b_iff p)); exact Epk. }
      rewrite Hpok. destruct (program_typedb p) eqn:Ht; cbn [negb].
      * assert (Hpk : source_spec_package_rules_b p = false) by (rewrite source_spec_valid_b_eq, Ht, Bool.andb_true_l in Hpok; exact Hpok).
        rewrite Hpk. reflexivity.
      * reflexivity.
    + rewrite (elaboration_diagnostics_eq_fresh p _ Ep), (existsb_build_output_fresh p Ep). reflexivity.
Qed.

(** the legacy class is invariant under [ProgramInputEqual] (module + files); it depends on the ModuleSpec
    (via the preflight), so FilesEqual ALONE is NOT enough — see [class_input_counterexample] below. *)
Theorem go_compile_class_Equal : forall p1 p2,
  ProgramInputEqual p1 p2 -> go_compile_class p1 = go_compile_class p2.
Proof.
  intros p1 p2 H. pose proof (proj2 H) as Hf. rewrite !go_compile_class_spec.
  rewrite (fresh_build_disposition_InputEqual _ _ H), (source_spec_valid_b_Equal _ _ Hf), (program_typedb_Equal predeclared_type _ _ Hf).
  reflexivity.
Qed.

Theorem go_compile_class_build_permutation : forall ms nodes1 nodes2 p1 p2,
  Permutation nodes1 nodes2 ->
  build_program ms nodes1 = Some p1 -> build_program ms nodes2 = Some p2 ->
  go_compile_class p1 = go_compile_class p2.
Proof.
  intros ms n1 n2 p1 p2 Hperm Hb1 Hb2.
  unfold build_program in Hb1, Hb2.
  destruct (filemap_of_nodes n1) as [fm1|] eqn:F1; [ | discriminate Hb1 ].
  destruct (filemap_of_nodes n2) as [fm2|] eqn:F2; [ | discriminate Hb2 ].
  injection Hb1 as <-. injection Hb2 as <-.
  apply go_compile_class_Equal. split; [ reflexivity | cbn [prog_files] ].
  exact (filemap_of_nodes_permutation n1 n2 fm1 fm2 Hperm F1 F2).
Qed.

(** DETERMINISM, split correctly.  Source facts + the SEMANTIC report depend only on the file map (the
    [*_FilesEqual] theorems above).  The FreshBuildPlan, the FINAL command report, and the acceptance CLASS also
    depend on the ModuleSpec (the preflight's default exec name is a ModulePath function), so those need the FULL
    [ProgramInputEqual].  Do NOT claim full-report equality from FilesEqual alone — see the counterexample
    (equal files, different module -> different plan). *)

(** equal inputs -> equal root layout / package import path (the file-map and module halves). *)
Theorem root_layout_InputEqual : forall p1 p2,
  ProgramInputEqual p1 p2 -> root_layout p1 = root_layout p2.
Proof. intros p1 p2 H. exact (root_layout_Equal _ _ (proj2 H)). Qed.

(* the whole-program COROLLARY of [package_import_path_deterministic]: equal program inputs give an equal
   module path, hence an equal import path for any package directory.  Retained for full-program determinism;
   the direct API claim above is the load-bearing one (this is a consequence, not a substitute). *)
Theorem package_import_path_InputEqual : forall p1 p2 dir,
  ProgramInputEqual p1 p2 ->
  package_import_path (prog_module p1) dir = package_import_path (prog_module p2) dir.
Proof. intros p1 p2 dir H. apply package_import_path_deterministic; [ exact (proj1 H) | reflexivity ]. Qed.

(** the ERASED final (command-facing) report: snapshot-free, comparable across programs by [=]. *)
Definition erased_elaboration_report (p : GoProgram) (idx : GoIndex.Snap.SyntaxIndex p) : list ErasedDiagnostic :=
  map erase_diagnostic (elaboration_diagnostics p idx).

(** on a failed preflight the erased fresh report is EXACTLY the one build-output-directory diagnostic keyed by
    the sole package DIR, CARRYING the exact planned default-output NAME (the colliding directory) as its
    erased [ed_output] payload — so two erased build-output reports for different collision names differ. *)
Lemma erased_fresh_report_of_sole : forall p dir,
  selected_package_keys p = [dir] ->
  fresh_build_disposition_ok (fresh_build_plan p) = false ->
  map erase_diagnostic (fresh_build_diagnostics p)
    = [mkErasedDiagnostic DCBuildOutputIsDirectory (EAPackage dir) [] None
         (Some (default_exec_name (prog_module p) dir)) None].
Proof.
  intros p dir Hk Hpf.
  destruct (proj1 (preflight_fails_iff p) Hpf) as [dir' [Hk' Hfind]].
  assert (dir' = dir) as -> by (rewrite Hk in Hk'; congruence).
  unfold fresh_build_diagnostics, fresh_build_diagnostics_of. rewrite (fresh_build_plan_of_sole p dir Hk), Hfind.
  unfold sole_package_ref. destruct (Bool.bool_dec (package_present_b p dir) true) as [Ht|Hcon].
  - reflexivity.
  - exfalso. apply Hcon. exact (sole_package_present p dir Hk).
Qed.

(** equal PROGRAM INPUTS -> equal ERASED FINAL report (module + files): the preflight branch is
    ModuleSpec-dependent, so this needs [ProgramInputEqual], not [FilesEqual] alone. *)
Theorem erased_elaboration_report_InputEqual : forall p1 p2 idx1 idx2,
  ProgramInputEqual p1 p2 ->
  erased_elaboration_report p1 idx1 = erased_elaboration_report p2 idx2.
Proof.
  intros p1 p2 idx1 idx2 H. pose proof (proj2 H) as Hf.
  unfold erased_elaboration_report, elaboration_diagnostics, command_diagnostics_of.
  rewrite (fresh_build_disposition_InputEqual _ _ H).
  destruct (fresh_build_disposition_ok (fresh_build_plan p2)) eqn:Ed.
  - exact (erased_report_FilesEqual p1 p2 idx1 idx2 Hf).
  - assert (Ed1 : fresh_build_disposition_ok (fresh_build_plan p1) = false)
      by (rewrite (fresh_build_disposition_InputEqual _ _ H); exact Ed).
    destruct (proj1 (preflight_fails_iff p1) Ed1) as [dir [Hk1 _]].
    assert (Hk2 : selected_package_keys p2 = [dir])
      by (rewrite <- (selected_package_keys_Equal _ _ Hf); exact Hk1).
    fold (fresh_build_diagnostics p1) (fresh_build_diagnostics p2).
    rewrite (erased_fresh_report_of_sole p1 dir Hk1 Ed1),
            (erased_fresh_report_of_sole p2 dir Hk2 Ed).
    (* the erased build-output NAME is [default_exec_name], a function of the ModuleSpec (equal by inputs). *)
    rewrite (proj1 H). reflexivity.
Qed.

(** The empty program (empty file MAP) is accepted: no package to type and no `main` to count, so [source_spec_valid_b]
    holds vacuously (the file map's elements and the package map are both empty). *)
Lemma source_spec_valid_b_empty : forall ms, source_spec_valid_b (empty_program ms) = true.
Proof. intro ms. vm_compute. reflexivity. Qed.

(** the LIVE factored-root empty surface (public gate).  [SourceProgramValid_Equal] is proved once,
    above (the sole map-equality proof); [source_spec_valid_b_Equal]/[source_spec_valid_b_empty] are its decidable
    companions. *)
Theorem SourceProgramValid_empty : forall ms, SourceProgramValid (empty_program ms).
Proof.
  intro ms. apply (proj1 (source_spec_valid_b_iff (empty_program ms))). apply source_spec_valid_b_empty.
Qed.

(** ---- boundary fixture: an out-of-range argument rejects the WHOLE program BEFORE any emission ---- *)

(** A single-file program whose only `println` argument is [int_max + 1] (one past the one [Ints] upper
    bound; NOT a duplicated numeric literal) — unrepresentable as the default [TInteger IInt] through the
    [GoTypes] authority. *)
Definition over_program : GoProgram :=
  singleton_program
    (mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23)
    (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EInt (Z.to_N (int_max + 1)) ] ] ].

(* the whole program fails typing, so [source_spec_valid_b] rejects it and [go_compile] returns the honest typing
   error — and there is NO [CompilableProgram] for it (hence no [SafeProgram], no [DirectoryImage], no
   rendering/emission): rejection happens strictly in Rocq, before any bytes. *)
Example over_program_untyped   : program_typedb over_program = false.        Proof. vm_compute; reflexivity. Qed.
Example over_program_not_valid    : source_spec_valid_b over_program = false.               Proof. vm_compute; reflexivity. Qed.
Example over_program_rejected  : legacy_compile_class (go_compile over_program) = LCTyping.    Proof. exact (go_compile_untyped _ over_program_untyped ltac:(vm_compute; reflexivity)). Qed.
Example over_program_no_compile : ~ GoCompile over_program.
Proof. exact (reject_no_compile over_program over_program_not_valid). Qed.

(** ---- integer-family programs: a concrete accepted integer program compiles; an invalid nested
    conversion rejects the WHOLE program with the same honest typing error, before any bytes. ---- *)
Definition int_program : GoProgram :=
  singleton_program
    (mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23)
    (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNint8) (EInt 127)
                       ; EConvert (GoAST.tsyn GoNames.TNuint64) (EInt 18446744073709551615)
                       ; EConvert (GoAST.tsyn GoNames.TNint8) (EConvert (GoAST.tsyn GoNames.TNint16) (EInt 127)) ] ] ].
Example int_program_typed    : program_typedb int_program = true. Proof. vm_compute; reflexivity. Qed.
Example int_program_ok       : source_spec_valid_b int_program = true.        Proof. vm_compute; reflexivity. Qed.
Example int_program_compiles : exists cp Hcp, go_compile int_program = CompiledOk cp Hcp.
Proof. exact (go_compile_ok_of_source_spec_valid_b _ int_program_ok ltac:(vm_compute; reflexivity)). Qed.

(** A program whose only argument is [uint8(int(300))] — a valid inner [int(300)] whose value does NOT fit
    the outer [uint8]; the invalid nested conversion cannot be revived, so the whole program is rejected. *)
Definition bad_convert_program : GoProgram :=
  singleton_program
    (mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23)
    (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNuint8) (EConvert (GoAST.tsyn GoNames.TNint) (EInt 300)) ] ] ].
Example bad_convert_untyped     : program_typedb bad_convert_program = false. Proof. vm_compute; reflexivity. Qed.
Example bad_convert_rejected    : legacy_compile_class (go_compile bad_convert_program) = LCTyping. Proof. exact (go_compile_untyped _ bad_convert_untyped ltac:(vm_compute; reflexivity)). Qed.
Example bad_convert_no_compile  : ~ GoCompile bad_convert_program.
Proof. exact (reject_no_compile bad_convert_program eq_refl). Qed.

(** ---- a concrete STRING program is whole-program admissible: a single `main` whose `println`
    mixes a string literal with a bool and an int is typed and compiles to a [CompilableProgram]. ---- *)
Definition str_program : GoProgram :=
  singleton_program
    (mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23)
    (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EString "hello"; EBool true; EInt 7 ] ] ].
Example str_program_typed    : program_typedb str_program = true. Proof. vm_compute; reflexivity. Qed.
Example str_program_ok       : source_spec_valid_b str_program = true.        Proof. vm_compute; reflexivity. Qed.
Example str_program_compiles : exists cp Hcp, go_compile str_program = CompiledOk cp Hcp.
Proof. exact (go_compile_ok_of_source_spec_valid_b _ str_program_ok ltac:(vm_compute; reflexivity)). Qed.

(** ---- float programs: a concrete accepted float program (a bare float64, an explicit float32
    conversion, and an exact float->int conversion) compiles to a [CompilableProgram]; a fractional
    float->int conversion rejects the WHOLE program with the honest typing error, before any bytes — and there
    is NO [CompilableProgram] for it. ---- *)
Definition float_program : GoProgram :=
  singleton_program
    (mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23)
    (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EFloat (mkDecimal 15 (-1) eq_refl)
                       ; EConvert (GoAST.tsyn GoNames.TNfloat32) (EFloat (mkDecimal 15 (-1) eq_refl))
                       ; EConvert (GoAST.tsyn GoNames.TNint) (EFloat (mkDecimal 3 0 eq_refl)) ] ] ].
Example float_program_typed    : program_typedb float_program = true. Proof. vm_compute. reflexivity. Qed.
Example float_program_ok       : source_spec_valid_b float_program = true.        Proof. vm_compute. reflexivity. Qed.
Example float_program_compiles : exists cp Hcp, go_compile float_program = CompiledOk cp Hcp.
Proof. exact (go_compile_ok_of_source_spec_valid_b _ float_program_ok ltac:(vm_compute; reflexivity)). Qed.

Definition float_reject_program : GoProgram :=
  singleton_program
    (mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23)
    (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNint) (EFloat (mkDecimal 35 (-1) eq_refl)) ] ] ].   (* int(3.5): fractional *)
Example float_reject_untyped    : program_typedb float_reject_program = false. Proof. vm_compute. reflexivity. Qed.
Example float_reject_rejected   : legacy_compile_class (go_compile float_reject_program) = LCTyping.
Proof. exact (go_compile_untyped _ float_reject_untyped ltac:(vm_compute; reflexivity)). Qed.
Example float_reject_no_compile : ~ GoCompile float_reject_program.
Proof. apply (reject_no_compile float_reject_program); vm_compute; reflexivity. Qed.

(** ---- a whole COMPLEX program (bare complex default, complex64/complex128 conversions, a scalar->
    complex conversion, and a zero-imaginary complex->scalar conversion) is typed and compiles; a component-
    overflow program and a nonzero-imaginary complex->int program are ordinary [ErrTyping] rejections with no
    [CompilableProgram]. ---- *)
Definition complex_program : GoProgram :=
  singleton_program
    (mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23)
    (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EComplex (mkDC (mkDecimal 15 (-1) eq_refl) (mkDecimal (-25) (-1) eq_refl))
                       ; EConvert (GoAST.tsyn GoNames.TNcomplex64)  (EComplex (mkDC (mkDecimal 15 (-1) eq_refl) (mkDecimal 0 0 eq_refl)))
                       ; EConvert (GoAST.tsyn GoNames.TNcomplex128) (EComplex (mkDC (mkDecimal 15 (-1) eq_refl) (mkDecimal 0 0 eq_refl)))
                       ; EConvert (GoAST.tsyn GoNames.TNcomplex64)  (EInt 1)
                       ; EConvert (GoAST.tsyn GoNames.TNint) (EComplex (mkDC (mkDecimal 3 0 eq_refl) (mkDecimal 0 0 eq_refl))) ] ] ].
Example complex_program_typed    : program_typedb complex_program = true. Proof. vm_compute. reflexivity. Qed.
Example complex_program_ok       : source_spec_valid_b complex_program = true.        Proof. vm_compute. reflexivity. Qed.
Example complex_program_compiles : exists cp Hcp, go_compile complex_program = CompiledOk cp Hcp.
Proof. exact (go_compile_ok_of_source_spec_valid_b _ complex_program_ok ltac:(vm_compute; reflexivity)). Qed.

Definition complex_overflow_program : GoProgram :=
  singleton_program
    (mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23)
    (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNcomplex64) (EComplex (mkDC (mkDecimal 1 39 eq_refl) (mkDecimal 0 0 eq_refl))) ] ] ].
Example complex_overflow_untyped    : program_typedb complex_overflow_program = false. Proof. vm_compute. reflexivity. Qed.
Example complex_overflow_rejected   : legacy_compile_class (go_compile complex_overflow_program) = LCTyping. Proof. exact (go_compile_untyped _ complex_overflow_untyped ltac:(vm_compute; reflexivity)). Qed.
Example complex_overflow_no_compile : ~ GoCompile complex_overflow_program.
Proof. apply (reject_no_compile complex_overflow_program); vm_compute; reflexivity. Qed.

Definition complex_nonzero_imag_program : GoProgram :=
  singleton_program
    (mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23)
    (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNint) (EComplex (mkDC (mkDecimal 3 0 eq_refl) (mkDecimal 1 0 eq_refl))) ] ] ].
Example complex_nonzero_imag_untyped    : program_typedb complex_nonzero_imag_program = false. Proof. vm_compute. reflexivity. Qed.
Example complex_nonzero_imag_rejected   : legacy_compile_class (go_compile complex_nonzero_imag_program) = LCTyping. Proof. exact (go_compile_untyped _ complex_nonzero_imag_untyped ltac:(vm_compute; reflexivity)). Qed.
Example complex_nonzero_imag_no_compile : ~ GoCompile complex_nonzero_imag_program.
Proof. apply (reject_no_compile complex_nonzero_imag_program); vm_compute; reflexivity. Qed.

(** CONCRETE STRUCTURED-DIAGNOSTIC FIXTURES.  Because the occurrence index is an OPAQUE
    sealed module ([Snap : SNAP_SIG]), the elaboration ([elaborate]/[expr_diags]/[pkg_diags]/[erased_report]) does
    NOT reduce — a fixture cannot [vm_compute] a concrete report.  So each fixture pins the REAL index
    ([Snap.index_program] of the concrete program) and states its structured claim THROUGH the proven
    soundness/determinism/emptiness bridges.  Non-vacuity comes from the COMPUTABLE type checker
    ([program_typedb]/[source_spec_package_rules_b], which DO reduce): a rejected program has a provably NON-EMPTY report
    ([*_empty_iff] contrapositive), and every diagnostic in it is pinned by the family soundness theorem. *)

Definition c3_ms : ModuleSpec := mkModuleSpec (ModulePath.mkMP "fido.local/generated" eq_refl) GoVersion.Go1_23.

(** REORDERED CONSTRUCTION: the SAME semantic file map built from PERMUTED [GoFileNode] input has
    a byte-identical erased diagnostic report, the identical success/failure class, and the identical canonical
    fact enumeration — construction order is not observable. *)
Definition rnode_a : GoFileNode := main_file_node (mkFP "a.go" eq_refl) [ DMain [ SPrintln [ EInt 1 ] ] ].
Definition rnode_b : GoFileNode := main_file_node (mkFP "b.go" eq_refl) [ DMain [ SPrintln [ EInt 2 ] ] ].

Example reorder_builds1 : exists p, build_program c3_ms [rnode_a; rnode_b] = Some p.
Proof. eexists; vm_compute; reflexivity. Qed.
Example reorder_builds2 : exists p, build_program c3_ms [rnode_b; rnode_a] = Some p.
Proof. eexists; vm_compute; reflexivity. Qed.

Theorem reorder_construction_deterministic :
  forall p1 p2 (idx1 : GoIndex.Snap.SyntaxIndex p1) (idx2 : GoIndex.Snap.SyntaxIndex p2),
    build_program c3_ms [rnode_a; rnode_b] = Some p1 ->
    build_program c3_ms [rnode_b; rnode_a] = Some p2 ->
    erased_report p1 idx1 = erased_report p2 idx2
    /\ go_compile_class p1 = go_compile_class p2
    /\ GoIndex.NodeKeyMapBase.elements (prog_expr_facts p1) = GoIndex.NodeKeyMapBase.elements (prog_expr_facts p2).
Proof.
  intros p1 p2 idx1 idx2 H1 H2.
  assert (HIE : ProgramInputEqual p1 p2).
  { unfold build_program in H1, H2.
    destruct (filemap_of_nodes [rnode_a; rnode_b]) as [fm1|] eqn:F1; [ | discriminate ].
    destruct (filemap_of_nodes [rnode_b; rnode_a]) as [fm2|] eqn:F2; [ | discriminate ].
    injection H1 as <-. injection H2 as <-. split; [ reflexivity | cbn [prog_files] ].
    exact (filemap_of_nodes_permutation _ _ fm1 fm2 (perm_swap rnode_b rnode_a []) F1 F2). }
  pose proof (proj2 HIE) as HFE.
  split; [ exact (erased_report_FilesEqual p1 p2 idx1 idx2 HFE) |].
  split; [ exact (go_compile_class_Equal p1 p2 HIE) | exact (prog_expr_facts_enum_FilesEqual p1 p2 HFE) ].
Qed.

(** EMPTY PROGRAM: the module-only program is ACCEPTED with an EMPTY erased report and an EMPTY
    fact enumeration (no package to type, no `main` required). *)
Theorem empty_program_report :
  erased_report (empty_program c3_ms) (GoIndex.Snap.index_program (empty_program c3_ms)) = nil
  /\ GoIndex.NodeKeyMapBase.elements (prog_expr_facts (empty_program c3_ms)) = nil.
Proof.
  split.
  - apply (proj2 (erased_report_empty_iff (empty_program c3_ms) _)).
    rewrite semantic_ok_b_source_spec_valid_b. apply source_spec_valid_b_empty.
  - vm_compute. reflexivity.
Qed.

(** NESTED INVALID CONVERSION [float64(int8(128))]: the program is REJECTED, so its expression
    report is genuinely NON-EMPTY, and EVERY invalid-conversion diagnostic in it carries a same-file,
    nearest-first, duplicate-free STRICT-ANCESTOR conversion context (the outer [float64] strictly encloses the
    primary [int8] — never fabricated syntax). *)
Definition nested_conv_program : GoProgram :=
  singleton_program c3_ms (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNfloat64) (EConvert (GoAST.tsyn GoNames.TNint8) (EInt 128)) ] ] ].

Example nested_conv_untyped : program_typedb nested_conv_program = false.
Proof. vm_compute. reflexivity. Qed.

(* the EXACT whole erased report: EXACTLY ONE diagnostic, code DCInvalidConversion, PRIMARY anchored at the
   inner [int8] conversion (local 7 — the outer [float64] conversion is local 5, its source type name local 6),
   the outer [float64] conversion (local 5) in the RELATED context, and the target payload [TInteger IInt8].
   Computed through the source characterization of the report — non-vacuous, exact count, exact anchors, exact
   payload. *)
Theorem nested_conv_erased_report :
  erased_report nested_conv_program (GoIndex.Snap.index_program nested_conv_program)
  = [ mkErasedDiagnostic DCInvalidConversion
        (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 7%positive))
        [ EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive) ]
        (Some (TInteger IInt8)) None (Some (GoAST.tsyn GoNames.TNint8)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(** ---- THREE MAINS IN ONE PACKAGE: the program is REJECTED (a package with != 1 main), so its
    package report is genuinely NON-EMPTY, and EVERY duplicate-main diagnostic names a strictly-later,
    genuinely-DISTINCT main in the SAME package, with the related [earlier] the unique smallest-NodeKey main. ---- *)
Definition three_main_program : GoProgram :=
  singleton_program c3_ms (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EInt 1 ] ]; DMain [ SPrintln [ EInt 2 ] ]; DMain [ SPrintln [ EInt 3 ] ] ].

(* the EXACT whole erased report: EXACTLY TWO DCMainRedeclared diagnostics — the SECOND main (local 6) and the
   THIRD main (local 9) each PRIMARY, both RELATED to the FIRST canonical main (local 3, the smallest key).  No
   third diagnostic, no self-relation, no missing-main. *)
Theorem three_main_erased_report :
  erased_report three_main_program (GoIndex.Snap.index_program three_main_program)
  = [ mkErasedDiagnostic DCMainRedeclared
        (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 6%positive))
        [ EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 3%positive) ] None None None
    ; mkErasedDiagnostic DCMainRedeclared
        (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 9%positive))
        [ EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 3%positive) ] None None None ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(** PACKAGE WITH NO MAIN: a represented package whose only file declares NO `main` is REJECTED, so
    its package report is genuinely NON-EMPTY, and EVERY missing-main diagnostic anchors a genuinely represented
    package that contains EXACTLY ZERO `main` declarations (no fake file/node primary). *)
Definition missing_main_program : GoProgram :=
  singleton_program c3_ms (mkFP "main.go" eq_refl) [ ].

(* the EXACT whole erased report: EXACTLY ONE DCMissingMainEntry, anchored at the represented package (root "") —
   a PACKAGE anchor, never a fake file/node primary — with no related anchor and no target payload. *)
Theorem missing_main_erased_report :
  erased_report missing_main_program (GoIndex.Snap.index_program missing_main_program)
  = [ mkErasedDiagnostic DCMissingMainEntry (EAPackage "") [] None None None ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(** the EXACT expression-fact query: on ANY valid [ElaborationFacts], EVERY expression reference's
    queried fact is its occurrence's EXACT source-derived fact — the [ef_const_status] IS the occurrence's
    [const_info] and the [ef_use_resolved] IS its use-context resolution ([resolve_expr_const], rounded ONCE at
    conversion — no rerounding).  So the query PROJECTS the occurrence, never a recomputed value. *)
Lemma expr_fact_at_exact {p ip} (facts : ElaborationFacts p ip) (er : GoIndex.ExprRef p) :
  exists e ci,
    GoIndex.view_expr (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) = Some e
    /\ const_info e = Some ci
    /\ expr_fact_at facts er
       = mkExprFact ci (occ_use_resolved (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er))).
Proof.
  assert (Hkind : GoIndex.occurrence_kind (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) = GoIndex.KExpression)
    by exact (proj2_sig er).
  destruct (GoIndex.kind_view_expr _ Hkind) as [e Hv].
  pose proof (noderef_in_prog_visit p (GoIndex.erase_ref er)) as Hin.
  pose proof (proj2 (GoTypes.program_typedb_iff predeclared_type p) (proj1 (ef_source_valid facts))) as HPT.
  destruct (prog_visit_const_info_some p HPT (GoIndex.erase_ref er)
              (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) e Hin Hv) as [ci Hci].
  pose proof (eft_complete (ef_expr_facts facts) (GoIndex.erase_ref er)
                (GoIndex.Snap.source_occurrence_of_ref (GoIndex.erase_ref er)) Hin) as Hfind.
  rewrite (occ_expr_fact_status _ e ci Hv Hci) in Hfind.
  exists e, ci. split; [exact Hv | split; [exact Hci | exact (expr_fact_at_find facts er _ Hfind)]].
Qed.

Definition fact_program : GoProgram :=
  singleton_program c3_ms (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNfloat64) (EConvert (GoAST.tsyn GoNames.TNint) (EInt 5)) ] ] ].
Example fact_program_ok : source_spec_valid_b fact_program = true. Proof. vm_compute. reflexivity. Qed.

(** the EXACT per-occurrence facts of the VALID nested-conversion program [float64(int(5))].  The whole
    fact enumeration (three expression occurrences; the two source type-name occurrences at locals 6 and 8 carry
    no expression fact), projected to (local id, typed-target-if-any, [resolved_type_at]): the inner literal [5]
    (local 9) is UNTYPED and unresolved; the inner conversion [int(5)] (local 7) is TYPED at [TInteger IInt] and
    unresolved (a conversion operand); the outer println argument [float64(...)] (local 5) is TYPED at [TFloat
    F64] and RESOLVES to [TFloat F64] — exactly the GoTypes use-resolution, no rerounding. *)
Theorem fact_program_facts_exact :
  map (fun kv => (GoIndex.nk_local (fst kv),
                  match ef_const_status (snd kv) with CIUntyped _ => None | CITyped t _ => Some t end,
                  resolved_type_at (snd kv)))
      (GoIndex.NodeKeyMapBase.elements (prog_expr_facts fact_program))
  = [ (5%positive, Some (TFloat F64), Some (TFloat F64))
    ; (7%positive, Some (TInteger IInt), None)
    ; (9%positive, None, None) ].
Proof. rewrite prog_expr_facts_source, keyed_visit_source. vm_compute. reflexivity. Qed.

(* the two scalar occurrences carry their EXACT constants: the inner literal is the UNTYPED [CInt 5] (unresolved
   operand), the inner conversion is the TYPED [int(5)] (unresolved operand). *)
Theorem fact_program_inner_literal :
  GoIndex.NodeKeyMapBase.find (GoIndex.mkKey (mkFP "main.go" eq_refl) 9%positive) (prog_expr_facts fact_program)
  = Some (mkExprFact (CIUntyped (CInt 5)) None).
Proof. rewrite prog_expr_facts_source, keyed_visit_source. vm_compute. reflexivity. Qed.

Theorem fact_program_inner_conversion :
  GoIndex.NodeKeyMapBase.find (GoIndex.mkKey (mkFP "main.go" eq_refl) 7%positive) (prog_expr_facts fact_program)
  = Some (mkExprFact (CITyped (TInteger IInt) (TCInteger IInt 5 eq_refl)) None).
Proof. rewrite prog_expr_facts_source, keyed_visit_source. vm_compute. reflexivity. Qed.

(* the OUTER println argument [float64(int(5))]: its EXACT resolved constant is the rational [5/1] at [TFloat
   F64] — not merely "some float64".  [ef_const_status] is [CITyped (TFloat F64)], [resolved_type_at] is [TFloat
   F64], the resolved GoConst is [CFloat] with numerator 5 / denominator 1, and it resolves. *)
Theorem fact_program_outer_arg :
  option_map (fun f =>
     (match ef_const_status f with CITyped t _ => Some t | CIUntyped _ => None end,
      resolved_type_at f,
      match resolved_constant_at f with Some (CFloat fc) => Some (fc_num fc, fc_den fc) | _ => None end,
      match ef_use_resolved f with Some _ => true | None => false end))
     (GoIndex.NodeKeyMapBase.find (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive) (prog_expr_facts fact_program))
  = Some (Some (TFloat F64), Some (TFloat F64), Some (5%Z, 1%positive), true).
Proof. rewrite prog_expr_facts_source, keyed_visit_source. vm_compute. reflexivity. Qed.

(* the COMPLETE exact [ExprFact] of the outer argument — the full [CITyped] status (its proof-carrying float64
   TypedConst carrying the exact rational 5/1 and its once-rounded canonical runtime) and the exact resolved
   constant.  Any DIFFERENT resolved float64 value fails this equation. *)
Theorem fact_program_outer_fact :
  GoIndex.NodeKeyMapBase.find (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive) (prog_expr_facts fact_program)
  = Some {| ef_const_status :=
              CITyped (TFloat F64)
                (TCFloat F64
                   {| tfc_exact := {| fc_num := 5; fc_den := 1; fc_wf := reduce_fc_wf 5629499534213120 1125899906842624 |};
                      tfc_runtime := {| fv_sf := SpecFloat.S754_finite false 5629499534213120 (-50);
                                        fv_ok := const_runtime_canonical F64 {| fc_num := 5; fc_den := 1; fc_wf := gcd_z_1 5 |} |};
                      tfc_coh := eq_refl;
                      tfc_shape := const_runtime_shape F64 {| fc_num := 5; fc_den := 1; fc_wf := gcd_z_1 5 |}
                                     {| fc_num := 5; fc_den := 1; fc_wf := reduce_fc_wf 5629499534213120 1125899906842624 |} eq_refl |}) ;
            ef_use_resolved :=
              Some (pack_resolved (TFloat F64)
                      (TCFloat F64
                         {| tfc_exact := {| fc_num := 5; fc_den := 1; fc_wf := reduce_fc_wf 5629499534213120 1125899906842624 |};
                            tfc_runtime := {| fv_sf := SpecFloat.S754_finite false 5629499534213120 (-50);
                                              fv_ok := const_runtime_canonical F64 {| fc_num := 5; fc_den := 1; fc_wf := gcd_z_1 5 |} |};
                            tfc_coh := eq_refl;
                            tfc_shape := const_runtime_shape F64 {| fc_num := 5; fc_den := 1; fc_wf := gcd_z_1 5 |}
                                           {| fc_num := 5; fc_den := 1; fc_wf := reduce_fc_wf 5629499534213120 1125899906842624 |} eq_refl |})) |}.
Proof. rewrite prog_expr_facts_source, keyed_visit_source. vm_compute. reflexivity. Qed.

(** REPEATED EQUAL LITERALS [println(1, 1)] are NOT deduplicated: the fact table is keyed by
    OCCURRENCE identity (NodeKey), so two references with DISTINCT keys carry independent facts — each query
    projects its OWN occurrence's exact fact, even when the two expressions are syntactically equal. *)
Definition dup_lit_program : GoProgram :=
  singleton_program c3_ms (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EInt 1; EInt 1 ] ] ].
Example dup_lit_ok : source_spec_valid_b dup_lit_program = true. Proof. vm_compute. reflexivity. Qed.

(* the EXACT fact enumeration: TWO entries at DISTINCT keys (local 5 and local 6) with EQUAL fact values (both
   the untyped [1] resolving to [int(1)]).  Same syntax, two occurrences, two entries — the table is keyed by
   occurrence identity, so equal literals are NOT deduplicated by value. *)
Theorem dup_lit_facts_exact :
  GoIndex.NodeKeyMapBase.elements (prog_expr_facts dup_lit_program)
  = [ (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive,
        mkExprFact (CIUntyped (CInt 1)) (Some (pack_resolved (TInteger IInt) (TCInteger IInt 1 eq_refl))))
    ; (GoIndex.mkKey (mkFP "main.go" eq_refl) 6%positive,
        mkExprFact (CIUntyped (CInt 1)) (Some (pack_resolved (TInteger IInt) (TCInteger IInt 1 eq_refl)))) ].
Proof. rewrite prog_expr_facts_source, keyed_visit_source. vm_compute. reflexivity. Qed.

(** ★§3.5/§6 SINGLE USE-RESOLUTION AT THE USE SITE (nested conversion as a println argument): in
    [int16(int8(5))] the OUTER argument (local 5) is the ONLY occurrence whose use-context resolves
    ([ef_use_resolved] populated ONCE, from its own already-computed [ConstInfo] — never a second
    [const_info]/[resolve_expr_const] pass); the inner conversion (local 7) is a conversion OPERAND and the
    literal (local 9) an operand, so neither carries a use-resolution.  BOTH conversions ALSO carry the resolved
    semantic target ([int16] / [int8]) read from the once-built type-name table — the total table query cannot
    miss (§3.3), so every nested conversion is typed. *)
Definition nested_use_program : GoProgram :=
  singleton_program c3_ms (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNint16) (EConvert (GoAST.tsyn GoNames.TNint8) (EInt 5)) ] ] ].
Example nested_use_ok : source_spec_valid_b nested_use_program = true. Proof. vm_compute. reflexivity. Qed.
Theorem nested_use_single_resolution :
  map (fun kv => (GoIndex.nk_local (fst kv),
                  match ef_const_status (snd kv) with CIUntyped _ => None | CITyped t _ => Some t end,
                  match ef_use_resolved (snd kv) with Some _ => true | None => false end))
      (GoIndex.NodeKeyMapBase.elements (prog_expr_facts nested_use_program))
  = [ (5%positive, Some (TInteger IInt16), true)    (* the println ARGUMENT — resolves ONCE *)
    ; (7%positive, Some (TInteger IInt8),  false)   (* the inner conversion OPERAND — no use-resolution *)
    ; (9%positive, None,                   false)   (* the literal 5 — untyped operand *)
    ].
Proof. rewrite prog_expr_facts_source, keyed_visit_source. vm_compute. reflexivity. Qed.

(** ★§6 LOCALLY-FAILING INNER CONVERSION — ONE INNER DIAGNOSTIC, NO OUTER: in [int16(int8(300))] the inner
    [int8(300)] overflows (300 > 127), so the ONLY diagnostic anchors at the INNER conversion (local 7, resolved
    target [int8], source spelling [int8]) with its enclosing [int16] conversion (local 5) as the strict-ancestor
    context; the OUTER [int16(...)] outcome is blocked-by-child ([EOChildFail]) and emits NOTHING.  The stored
    invalid-conversion outcome carries the inner conversion's OWN refs, so the diagnostic projects them — no
    re-mint (§2.5). *)
Definition inner_fail_program : GoProgram :=
  singleton_program c3_ms (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNint16) (EConvert (GoAST.tsyn GoNames.TNint8) (EInt 300)) ] ] ].
Theorem inner_fail_one_inner_no_outer :
  erased_report inner_fail_program (GoIndex.Snap.index_program inner_fail_program)
  = [ mkErasedDiagnostic DCInvalidConversion (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 7%positive))
        [ EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive) ]
        (Some (TInteger IInt8)) None (Some (GoAST.tsyn GoNames.TNint8)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(* ---- §15/§10.8 DEEP NESTED CONVERSION PHASE FIXTURES: a four-deep conversion chain exercises the ONE
   [ExpressionPhase] over a genuinely nested tree.  (a) a VALID deep nest compiles and its TOTAL diagnostic
   projection is EMPTY — no fail-open spurious diagnostic anywhere in the tree; (b) a deep nest whose INNERMOST
   conversion overflows produces EXACTLY ONE diagnostic (at the inner failure; the three enclosing conversions
   are blocked-by-child with no outer reason) — the total projection neither drops it (fail-open) nor
   double-counts it per ancestor. ---- *)
Definition deep_nested_program : GoProgram :=
  singleton_program c3_ms (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNint64)
                          (EConvert (GoAST.tsyn GoNames.TNint32)
                            (EConvert (GoAST.tsyn GoNames.TNint16)
                              (EConvert (GoAST.tsyn GoNames.TNint8) (EInt 5)))) ] ] ].
Example deep_nested_valid : source_spec_valid_b deep_nested_program = true.
Proof. vm_compute. reflexivity. Qed.
Lemma deep_nested_compiles : GoCompile deep_nested_program.
Proof.
  split.
  - unfold fresh_build_preflight_ok. vm_compute. reflexivity.
  - exact (proj1 (source_spec_valid_b_iff deep_nested_program) deep_nested_valid).
Qed.
(* the phase's TOTAL diagnostic projection over the whole valid deep tree is empty — no fail-open. *)
Theorem deep_nested_no_diags :
  erased_report deep_nested_program (GoIndex.Snap.index_program deep_nested_program) = [].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

Definition deep_fail_program : GoProgram :=
  singleton_program c3_ms (mkFP "main.go" eq_refl)
    [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNint64)
                          (EConvert (GoAST.tsyn GoNames.TNint32)
                            (EConvert (GoAST.tsyn GoNames.TNint16)
                              (EConvert (GoAST.tsyn GoNames.TNint8) (EInt 300)))) ] ] ].
(* EXACTLY ONE diagnostic: the innermost int8(300) overflow, anchored at its own node with its stored operand
   ref; the three enclosing conversions are blocked-by-child (no second reason, no per-ancestor re-report). *)
Theorem deep_fail_one_diag :
  length (erased_report deep_fail_program (GoIndex.Snap.index_program deep_fail_program)) = 1%nat.
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(* ---- ★§5.3 CONCRETE-SNAPSHOT PLUMBING: on a REAL compiled program, the retained index mints a REAL [ExprRef]
   for a source conversion occurrence — the occurrence hypotheses of [conversion_target_ref_conv] are DISCHARGED
   from source-level facts (find_file / source_occurrence_at / view), never assumed. ---- *)
(* a source occurrence at [local] makes [local] a valid node index (its metadata is in the file's node table). *)
Lemma valid_localb_of_source (f : GoSourceFile) (local : positive) occ :
  GoIndex.source_occurrence_at f local = Some occ -> GoIndex.valid_localb f local = true.
Proof. intro H. unfold GoIndex.valid_localb. rewrite GoIndex.build_file_source_exact, H. reflexivity. Qed.

Lemma program_expr_ref_at (p : GoProgram) (path : FilePath) (f : GoSourceFile) (local : positive) occ e :
  find_file path (prog_files p) = Some f ->
  GoIndex.source_occurrence_at f local = Some occ ->
  GoIndex.view_expr occ = Some e ->
  exists (r : GoIndex.Snap.NodeRef p) (er : GoIndex.ExprRef p),
    In (r, occ) (prog_visit p)
    /\ GoIndex.as_expr (GoIndex.indexed_syntax (GoIndex.index_program p)) r = Some er
    /\ GoIndex.Snap.node_ref_key r = GoIndex.mkKey path local.
Proof.
  intros Hfind Hsrc Hview.
  destruct (GoIndex.Snap.ref_of_key_source p (GoIndex.indexed_syntax (GoIndex.index_program p))
              path f local Hfind (valid_localb_of_source f local occ Hsrc)) as [r [Hrok [Hrlocal Hrsource]]].
  pose proof (GoIndex.Snap.source_occ_of_ref_eq r) as Hso.
  rewrite Hrlocal, Hrsource, Hsrc in Hso. injection Hso as Hoccr.
  assert (Hk : GoIndex.Snap.node_kind (GoIndex.indexed_syntax (GoIndex.index_program p)) r = GoIndex.KExpression).
  { rewrite (GoIndex.Snap.node_kind_matches_source p _ r), <- Hoccr. exact (GoIndex.view_expr_kind occ e Hview). }
  destruct (GoIndex.as_kind_complete (GoIndex.indexed_syntax (GoIndex.index_program p)) r GoIndex.KExpression Hk)
    as [er [Hae Her]].
  exists r, er. split; [ | split ].
  - rewrite Hoccr. apply noderef_in_prog_visit.
  - exact Hae.
  - exact (GoIndex.Snap.ref_of_key_sound p (GoIndex.indexed_syntax (GoIndex.index_program p))
             (GoIndex.mkKey path local) r Hrok).
Qed.

(* the retained target [TypeNameRef] of a REAL source conversion occurrence: minted through the index, keyed at
   [Pos.succ local] (the target child), recovering the exact source [TypeSyntax]. *)
Lemma program_conv_target_ref (p : GoProgram) (path : FilePath) (f : GoSourceFile) (local : positive) occ ts x :
  find_file path (prog_files p) = Some f ->
  GoIndex.source_occurrence_at f local = Some occ ->
  GoIndex.view_expr occ = Some (EConvert ts x) ->
  exists (er : GoIndex.ExprRef p) tr,
    conversion_target_ref (GoIndex.indexed_syntax (GoIndex.index_program p)) er = Some tr
    /\ GoIndex.Snap.node_ref_key (GoIndex.erase_ref tr) = GoIndex.mkKey path (Pos.succ local)
    /\ GoIndex.type_name_ref_syntax tr = Some ts.
Proof.
  intros Hfind Hsrc Hview.
  destruct (program_expr_ref_at p path f local occ (EConvert ts x) Hfind Hsrc Hview)
    as [r [er [Hin [Hae Hkey]]]].
  destruct (conversion_target_ref_conv (GoIndex.indexed_syntax (GoIndex.index_program p)) r occ er ts x Hin Hview Hae)
    as [tr [Hc [Hktr [_ Hsyn]]]].
  assert (Hlocal : GoIndex.Snap.node_ref_local r = local).
  { pose proof Hkey as Hkey2. rewrite GoIndex.Snap.node_ref_key_eq in Hkey2. injection Hkey2 as _ Hl. exact Hl. }
  exists er, tr. split; [ exact Hc | split; [ | exact Hsyn ] ].
  rewrite Hktr. unfold type_name_key. rewrite Hkey. cbn [GoIndex.nk_file]. rewrite Hlocal. reflexivity.
Qed.

(** ★§5.3 THE CONCRETE TWO-[uint8] SNAPSHOT: a REAL compiled program with TWO [uint8(...)] conversions at
    DISTINCT println arguments.  The retained index mints TWO real target [TypeNameRef]s at DISTINCT NodeKeys
    (occurrence identity — NOT name identity: the same closed source symbol at two occurrences), yet their
    recovered source [TypeSyntax] is EQUAL and their queried [TypeNameFact]s are EQUAL.  This is the CONCRETE
    (non-hypothetical) instance of [repeated_name_distinct_refs]: the two occurrences and their real refs are
    DISCHARGED from the source, not assumed. *)
Definition two_uint8_src : GoSourceFile :=
  main_source [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNuint8) (EInt 0)
                                 ; EConvert (GoAST.tsyn GoNames.TNuint8) (EInt 1) ] ] ].
Definition two_uint8_program : GoProgram := singleton_program c3_ms (mkFP "main.go" eq_refl)
  [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNuint8) (EInt 0)
                     ; EConvert (GoAST.tsyn GoNames.TNuint8) (EInt 1) ] ] ].
Example two_uint8_ok : source_spec_valid_b two_uint8_program = true. Proof. vm_compute. reflexivity. Qed.

(* one uint8 conversion's real target ref (its source occurrence discharged by [vm_compute] in the caller). *)
Lemma two_uint8_conv_ref (local : positive) (n : N) occ :
  GoIndex.source_occurrence_at two_uint8_src local = Some occ ->
  GoIndex.view_expr occ = Some (EConvert (GoAST.tsyn GoNames.TNuint8) (EInt n)) ->
  exists (er : GoIndex.ExprRef two_uint8_program) tr,
    conversion_target_ref (GoIndex.indexed_syntax (GoIndex.index_program two_uint8_program)) er = Some tr
    /\ GoIndex.Snap.node_ref_key (GoIndex.erase_ref tr) = GoIndex.mkKey (mkFP "main.go" eq_refl) (Pos.succ local)
    /\ GoIndex.type_name_ref_syntax tr = Some (GoAST.tsyn GoNames.TNuint8).
Proof.
  intros Hsrc Hview.
  exact (program_conv_target_ref two_uint8_program (mkFP "main.go" eq_refl) two_uint8_src local occ
           (GoAST.tsyn GoNames.TNuint8) (EInt n) ltac:(vm_compute; reflexivity) Hsrc Hview).
Qed.

(* the concrete two-[uint8] program COMPILES: its source is valid and the fresh-build preflight passes, so
   [elaborate] succeeds and EXPOSES a real retained [ElaborationFacts]. *)
Lemma two_uint8_compiles : GoCompile two_uint8_program.
Proof.
  split.
  - unfold fresh_build_preflight_ok. vm_compute. reflexivity.
  - exact (proj1 (source_spec_valid_b_iff two_uint8_program) two_uint8_ok).
Qed.

Theorem two_uint8_distinct_target_refs :
  exists facts (er1 er2 : GoIndex.ExprRef two_uint8_program) tr1 tr2,
    (* the facts come from an ACTUAL successful elaboration — the RETAINED [ElaborationFacts], not a global builder *)
    pe_result (elaborate two_uint8_program) = ElaborationOK facts
    /\ conversion_target_ref (GoIndex.indexed_syntax (GoIndex.index_program two_uint8_program)) er1 = Some tr1
    /\ conversion_target_ref (GoIndex.indexed_syntax (GoIndex.index_program two_uint8_program)) er2 = Some tr2
    /\ GoIndex.Snap.node_ref_key (GoIndex.erase_ref tr1) <> GoIndex.Snap.node_ref_key (GoIndex.erase_ref tr2)
    /\ GoIndex.type_name_ref_syntax tr1 = GoIndex.type_name_ref_syntax tr2
    (* the two facts are EQUAL when queried through the SEALED [ef_type_name_facts facts] of that elaboration —
       DISTINCT occurrence refs, EQUAL recovered syntax, EQUAL sealed facts (occurrence identity, not name identity). *)
    /\ type_name_fact_at facts tr1 = type_name_fact_at facts tr2.
Proof.
  destruct (proj2 (elaborate_ok_iff_GoCompile two_uint8_program) two_uint8_compiles) as [facts Hfacts].
  destruct (GoIndex.source_occurrence_at two_uint8_src 5) as [occ1|] eqn:Eo1; [| vm_compute in Eo1; discriminate Eo1].
  destruct (GoIndex.source_occurrence_at two_uint8_src 8) as [occ2|] eqn:Eo2; [| vm_compute in Eo2; discriminate Eo2].
  destruct (two_uint8_conv_ref 5 0 occ1 Eo1
              ltac:(vm_compute in Eo1; injection Eo1 as <-; vm_compute; reflexivity)) as [er1 [tr1 [Hc1 [Hk1 Hs1]]]].
  destruct (two_uint8_conv_ref 8 1 occ2 Eo2
              ltac:(vm_compute in Eo2; injection Eo2 as <-; vm_compute; reflexivity)) as [er2 [tr2 [Hc2 [Hk2 Hs2]]]].
  exists facts, er1, er2, tr1, tr2.
  split; [ exact Hfacts | split; [ exact Hc1 | split; [ exact Hc2 | split; [ | split ] ] ] ].
  - rewrite Hk1, Hk2. intro Hbad. apply (f_equal GoIndex.nk_local) in Hbad. vm_compute in Hbad. discriminate Hbad.
  - rewrite Hs1, Hs2. reflexivity.
  - rewrite (type_name_fact_at_resolves facts tr1 _ Hs1),
            (type_name_fact_at_resolves facts tr2 _ Hs2). reflexivity.
Qed.

(** SINGLE-FAILURE SCARS: each concrete rejected program yields EXACTLY ONE diagnostic with
    the required code, primary anchor (the failing literal/conversion at local 5), and target payload. *)

(* default integer overflow: a bare [int_max+1] literal cannot default to [TInteger IInt]. *)
Definition over_default_int_program := singleton_program c3_ms (mkFP "main.go" eq_refl) [ DMain [ SPrintln [ EInt 9223372036854775808 ] ] ].
Theorem over_default_int_erased :
  erased_report over_default_int_program (GoIndex.Snap.index_program over_default_int_program)
  = [ mkErasedDiagnostic DCDefaultNotRepresentable (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive)) [] (Some (TInteger IInt)) None None ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(* default float overflow: a bare finite decimal outside finite [float64]. *)
Definition over_default_float_program := singleton_program c3_ms (mkFP "main.go" eq_refl) [ DMain [ SPrintln [ EFloat (mkDecimal 1 400 eq_refl) ] ] ].
Theorem over_default_float_erased :
  erased_report over_default_float_program (GoIndex.Snap.index_program over_default_float_program)
  = [ mkErasedDiagnostic DCDefaultNotRepresentable (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive)) [] (Some (TFloat F64)) None None ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(* default complex overflow: a bare complex whose component cannot default to [complex128]. *)
Definition over_default_complex_program := singleton_program c3_ms (mkFP "main.go" eq_refl) [ DMain [ SPrintln [ EComplex (mkDC (mkDecimal 1 400 eq_refl) (mkDecimal 0 0 eq_refl)) ] ] ].
Theorem over_default_complex_erased :
  erased_report over_default_complex_program (GoIndex.Snap.index_program over_default_complex_program)
  = [ mkErasedDiagnostic DCDefaultNotRepresentable (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive)) [] (Some (TComplex C128)) None None ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(* invalid explicit integer conversion [int8(128)]: anchored at the conversion, target [TInteger IInt8]. *)
Definition bad_int8_program := singleton_program c3_ms (mkFP "main.go" eq_refl) [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNint8) (EInt 128) ] ] ].
Theorem bad_int8_erased :
  erased_report bad_int8_program (GoIndex.Snap.index_program bad_int8_program)
  = [ mkErasedDiagnostic DCInvalidConversion (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive)) [] (Some (TInteger IInt8)) None (Some (GoAST.tsyn GoNames.TNint8)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(* fractional float -> integer [int(3.5)]: anchored at the conversion. *)
Definition frac_f2i_program := singleton_program c3_ms (mkFP "main.go" eq_refl) [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNint) (EFloat (mkDecimal 35 (-1) eq_refl)) ] ] ].
Theorem frac_f2i_erased :
  erased_report frac_f2i_program (GoIndex.Snap.index_program frac_f2i_program)
  = [ mkErasedDiagnostic DCInvalidConversion (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive)) [] (Some (TInteger IInt)) None (Some (GoAST.tsyn GoNames.TNint)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(* nonzero-imaginary complex -> scalar [int(complex(3,1))]: anchored at the conversion. *)
Definition nz_c2s_program := singleton_program c3_ms (mkFP "main.go" eq_refl) [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNint) (EComplex (mkDC (mkDecimal 3 0 eq_refl) (mkDecimal 1 0 eq_refl))) ] ] ].
Theorem nz_c2s_erased :
  erased_report nz_c2s_program (GoIndex.Snap.index_program nz_c2s_program)
  = [ mkErasedDiagnostic DCInvalidConversion (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive)) [] (Some (TInteger IInt)) None (Some (GoAST.tsyn GoNames.TNint)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(* wrong-kind conversion [int(true)]: anchored at the conversion, no generic unlocated typing error. *)
Definition wrongkind_program := singleton_program c3_ms (mkFP "main.go" eq_refl) [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNint) (EBool true) ] ] ].
Theorem wrongkind_erased :
  erased_report wrongkind_program (GoIndex.Snap.index_program wrongkind_program)
  = [ mkErasedDiagnostic DCInvalidConversion (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive)) [] (Some (TInteger IInt)) None (Some (GoAST.tsyn GoNames.TNint)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.

(** ★§4 SOURCE-TARGET IN THE ERASED REPORT: an invalid [byte(256)] and an invalid [uint8(256)] resolve to the
    SAME semantic target ([uint8]) but carry DIFFERENT erased source targets ([byte] vs [uint8]) — so the two
    cross-snapshot reports are DISTINGUISHABLE (the source spelling is not lost to the resolved [GoType]).  Same
    for [rune(2147483648)] vs [int32(2147483648)] (both resolve to [int32]). *)
Definition bad_byte256_program := singleton_program c3_ms (mkFP "main.go" eq_refl) [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNbyte) (EInt 256) ] ] ].
Definition bad_uint8_256_program := singleton_program c3_ms (mkFP "main.go" eq_refl) [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNuint8) (EInt 256) ] ] ].
Theorem bad_byte256_erased :
  erased_report bad_byte256_program (GoIndex.Snap.index_program bad_byte256_program)
  = [ mkErasedDiagnostic DCInvalidConversion (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive)) [] (Some (TInteger IUint8)) None (Some (GoAST.tsyn GoNames.TNbyte)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.
Theorem bad_uint8_256_erased :
  erased_report bad_uint8_256_program (GoIndex.Snap.index_program bad_uint8_256_program)
  = [ mkErasedDiagnostic DCInvalidConversion (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive)) [] (Some (TInteger IUint8)) None (Some (GoAST.tsyn GoNames.TNuint8)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.
Theorem byte_uint8_erased_differ :
  erased_report bad_byte256_program (GoIndex.Snap.index_program bad_byte256_program)
  <> erased_report bad_uint8_256_program (GoIndex.Snap.index_program bad_uint8_256_program).
Proof.
  intro H. rewrite bad_byte256_erased, bad_uint8_256_erased in H.
  apply tsyn_byte_neq_uint8. congruence.
Qed.

Definition bad_rune_over_program := singleton_program c3_ms (mkFP "main.go" eq_refl) [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNrune) (EInt 2147483648) ] ] ].
Definition bad_int32_over_program := singleton_program c3_ms (mkFP "main.go" eq_refl) [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNint32) (EInt 2147483648) ] ] ].
Theorem bad_rune_over_erased :
  erased_report bad_rune_over_program (GoIndex.Snap.index_program bad_rune_over_program)
  = [ mkErasedDiagnostic DCInvalidConversion (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive)) [] (Some (TInteger IInt32)) None (Some (GoAST.tsyn GoNames.TNrune)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.
Theorem bad_int32_over_erased :
  erased_report bad_int32_over_program (GoIndex.Snap.index_program bad_int32_over_program)
  = [ mkErasedDiagnostic DCInvalidConversion (EANode (GoIndex.mkKey (mkFP "main.go" eq_refl) 5%positive)) [] (Some (TInteger IInt32)) None (Some (GoAST.tsyn GoNames.TNint32)) ].
Proof. rewrite erased_report_src_eq. vm_compute. reflexivity. Qed.
Theorem rune_int32_erased_differ :
  erased_report bad_rune_over_program (GoIndex.Snap.index_program bad_rune_over_program)
  <> erased_report bad_int32_over_program (GoIndex.Snap.index_program bad_int32_over_program).
Proof.
  intro H. rewrite bad_rune_over_erased, bad_int32_over_erased in H.
  apply tsyn_rune_neq_int32. congruence.
Qed.

(** DUPLICATE MAINS ACROSS FILES: two root-package files each declaring `main`.  The report names
    the CANONICAL later main (path order: [b.go] after [a.go]) as primary, related to the FIRST canonical main
    ([a.go]); construction/insertion order does not change this (both files' mains are at local 3). *)
Theorem dup_across_files_erased :
  option_map (fun p => erased_report_src (prog_files p))
             (build_program c3_ms [ main_file_node (mkFP "a.go" eq_refl) [ DMain [ SPrintln [ EInt 1 ] ] ]
                                  ; main_file_node (mkFP "b.go" eq_refl) [ DMain [ SPrintln [ EInt 2 ] ] ] ])
  = Some [ mkErasedDiagnostic DCMainRedeclared (EANode (GoIndex.mkKey (mkFP "b.go" eq_refl) 3%positive))
             [ EANode (GoIndex.mkKey (mkFP "a.go" eq_refl) 3%positive) ] None None None ].
Proof. vm_compute. reflexivity. Qed.

(** MULTIPLE SIMULTANEOUS FAILURES: two invalid expressions in DIFFERENT files ([a/x.go]'s
    [int8(128)] and [b/y.go]'s [int(3.5)]), one duplicate-main package ([c]), and one missing-main package
    ([d]).  The whole erased report is EXACTLY these four diagnostics in CANONICAL order — expression scars by
    file path first ([a/x.go], [b/y.go]), then package diagnostics by package key ([c] duplicate, [d] missing).
    Construction order does not affect the result. *)
Theorem simultaneous_failures_erased :
  option_map (fun p => erased_report_src (prog_files p))
     (build_program c3_ms
        [ main_file_node (mkFP "a/x.go" eq_refl) [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNint8) (EInt 128) ] ] ]
        ; main_file_node (mkFP "b/y.go" eq_refl) [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNint) (EFloat (mkDecimal 35 (-1) eq_refl)) ] ] ]
        ; main_file_node (mkFP "c/p.go" eq_refl) [ DMain [ SPrintln [ EInt 1 ] ] ]
        ; main_file_node (mkFP "c/q.go" eq_refl) [ DMain [ SPrintln [ EInt 2 ] ] ]
        ; main_file_node (mkFP "d/z.go" eq_refl) [ ] ])
  = Some [ mkErasedDiagnostic DCInvalidConversion (EANode (GoIndex.mkKey (mkFP "a/x.go" eq_refl) 5%positive)) [] (Some (TInteger IInt8)) None (Some (GoAST.tsyn GoNames.TNint8))
         ; mkErasedDiagnostic DCInvalidConversion (EANode (GoIndex.mkKey (mkFP "b/y.go" eq_refl) 5%positive)) [] (Some (TInteger IInt)) None (Some (GoAST.tsyn GoNames.TNint))
         ; mkErasedDiagnostic DCMainRedeclared (EANode (GoIndex.mkKey (mkFP "c/q.go" eq_refl) 3%positive))
             [ EANode (GoIndex.mkKey (mkFP "c/p.go" eq_refl) 3%positive) ] None None None
         ; mkErasedDiagnostic DCMissingMainEntry (EAPackage "d") [] None None None ].
Proof. vm_compute. reflexivity. Qed.

(** MIXED NODE-PRIMARY ORDER: a duplicate-main in package [a] (a later-discovered node diagnostic)
    and an invalid-conversion in package [z] (an earlier-discovered expression diagnostic).  The canonical
    report orders BOTH node-primary diagnostics by NodeKey — the duplicate-main at [a/q.go:3] precedes the
    invalid-conversion at [z/main.go:5] (path [a] < [z]) — NOT by discovery phase (which would put the
    expression scar first).  This is the NodeKeyMap-canonical order the naive `expr ++ pkg` violated. *)
Theorem mixed_order_erased :
  option_map (fun p => erased_report_src (prog_files p))
     (build_program c3_ms
        [ main_file_node (mkFP "a/p.go" eq_refl) [ DMain [ SPrintln [ EInt 1 ] ] ]
        ; main_file_node (mkFP "a/q.go" eq_refl) [ DMain [ SPrintln [ EInt 2 ] ] ]
        ; main_file_node (mkFP "z/main.go" eq_refl) [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNint8) (EInt 128) ] ] ] ])
  = Some [ mkErasedDiagnostic DCMainRedeclared (EANode (GoIndex.mkKey (mkFP "a/q.go" eq_refl) 3%positive))
             [ EANode (GoIndex.mkKey (mkFP "a/p.go" eq_refl) 3%positive) ] None None None
         ; mkErasedDiagnostic DCInvalidConversion (EANode (GoIndex.mkKey (mkFP "z/main.go" eq_refl) 5%positive))
             [] (Some (TInteger IInt8)) None (Some (GoAST.tsyn GoNames.TNint8)) ].
Proof. vm_compute. reflexivity. Qed.

(* the fixtures spell string keys/paths/output-names directly, so reopen the string scope (list [;] and
   number literals are unaffected). *)
Local Open Scope string_scope.

(** CURRENT REQUIRED ROCQ FIXTURES (20.1-20.16).  The fresh-build plan, preflight disposition, [source_spec_valid_b],
    and [program_typedb] are ALL index-free, so a fixture [vm_compute]s them directly; the command-facing report
    (which anchors into the OPAQUE sealed index) is pinned THROUGH the proven bridges ([go_compile_class_spec],
    [elaboration_diagnostics_fresh_failure]).  Module paths are valid current [ModulePath]s; the pinned Go
    1.23.12 default-executable / directory-collision behaviour is what these encode. *)

Definition ex_ms : ModuleSpec := mkModuleSpec (ModulePath.mkMP "example.com/m" eq_refl) GoVersion.Go1_23.
Definition ex_main : list GoDecl := [ DMain [ SPrintln [ EInt 1 ] ] ].
(* a package-local SEMANTIC error: uint8(int(300)) — the inner int(300) is valid, the outer uint8 is not. *)
Definition ex_bad  : list GoDecl := [ DMain [ SPrintln [ EConvert (GoAST.tsyn GoNames.TNuint8) (EConvert (GoAST.tsyn GoNames.TNint) (EInt 300)) ] ] ].

(* 20.1 — EMPTY IMAGE: no packages -> FBDNoPackages, preflight succeeds vacuously, GoCompile, no diagnostics. *)
Example fx_2001_plan      : fresh_build_plan (empty_program ex_ms) = FBDNoPackages.                    Proof. vm_compute. reflexivity. Qed.
Example fx_2001_preflight : fresh_build_disposition_ok (fresh_build_plan (empty_program ex_ms)) = true. Proof. vm_compute. reflexivity. Qed.
Example fx_2001_gocompile : GoCompile (empty_program ex_ms).                Proof. apply GoCompile_of_source_spec_valid_b; vm_compute; reflexivity. Qed.
Example fx_2001_report    : forall idx, elaboration_diagnostics (empty_program ex_ms) idx = nil.
Proof. intro idx. apply (proj2 (elaboration_diagnostics_nil_iff_GoCompile _ idx)). exact fx_2001_gocompile. Qed.

(* 20.2 — ONE VALID ROOT PACKAGE, ABSENT OUTPUT: module basename "m" is neither go.mod nor a root file, so the
   single-main plan's output target is absent; preflight succeeds; GoCompile. *)
Definition fx_root : GoProgram := singleton_program ex_ms (mkFP "main.go" eq_refl) ex_main.
Example fx_2002_plan      : fresh_build_plan fx_root = FBDWriteSingleMain "" "example.com/m" "m" None.   Proof. vm_compute. reflexivity. Qed.
Example fx_2002_preflight : fresh_build_disposition_ok (fresh_build_plan fx_root) = true.               Proof. vm_compute. reflexivity. Qed.
Example fx_2002_gocompile : GoCompile fx_root.                              Proof. apply GoCompile_of_source_spec_valid_b; vm_compute; reflexivity. Qed.

(* 20.3 — SOLE IMMEDIATE CHILD sub/main.go: import path example.com/m/sub, output name "sub", the fresh root
   HAS a directory "sub" -> preflight FAILS; final report is EXACTLY one build-output-directory diagnostic; not
   GoCompile. *)
Definition fx_sub : GoProgram := singleton_program ex_ms (mkFP "sub/main.go" eq_refl) ex_main.
Example fx_2003_preflight_fails : fresh_build_disposition_ok (fresh_build_plan fx_sub) = false.   Proof. vm_compute. reflexivity. Qed.
Example fx_2003_not_gocompile   : ~ GoCompile fx_sub.
Proof. intros [Hpf _]. unfold fresh_build_preflight_ok in Hpf. vm_compute in Hpf. discriminate. Qed.
Example fx_2003_report : forall idx, exists pk name, elaboration_diagnostics fx_sub idx = [DRBuildOutputIsDirectory pk name].
Proof. intro idx. apply elaboration_diagnostics_fresh_failure. vm_compute. reflexivity. Qed.
Example fx_2003_class  : go_compile_class fx_sub = LCBuildOutput.
Proof. rewrite go_compile_class_spec. vm_compute. reflexivity. Qed.

(* 20.4 — IMMEDIATE CHILD WITH A SEMANTIC ERROR + the same output collision: the final report REMAINS only the
   build-output-directory diagnostic (PRECEDENCE — the sole package's typing error is hidden). *)
Definition fx_sub_err : GoProgram := singleton_program ex_ms (mkFP "sub/main.go" eq_refl) ex_bad.
Example fx_2004_untyped : program_typedb fx_sub_err = false.                                        Proof. vm_compute. reflexivity. Qed.
Example fx_2004_preflight_fails : fresh_build_disposition_ok (fresh_build_plan fx_sub_err) = false. Proof. vm_compute. reflexivity. Qed.
Example fx_2004_report_hides_semantic : forall idx, exists pk name, elaboration_diagnostics fx_sub_err idx = [DRBuildOutputIsDirectory pk name].
Proof. intro idx. apply elaboration_diagnostics_fresh_failure. vm_compute. reflexivity. Qed.
Example fx_2004_class : go_compile_class fx_sub_err = LCBuildOutput.
Proof. rewrite go_compile_class_spec. vm_compute. reflexivity. Qed.

(* 20.5 — SOLE DEEPER PACKAGE a/b/main.go: output name "b", but the fresh root directory is "a" (not "b"), so
   the output target is absent; preflight succeeds; GoCompile. *)
Definition fx_ab : GoProgram := singleton_program ex_ms (mkFP "a/b/main.go" eq_refl) ex_main.
Example fx_2005_preflight : fresh_build_disposition_ok (fresh_build_plan fx_ab) = true. Proof. vm_compute. reflexivity. Qed.
Example fx_2005_gocompile : GoCompile fx_ab.                Proof. apply GoCompile_of_source_spec_valid_b; vm_compute; reflexivity. Qed.

(* 20.6 — FINAL v2 PACKAGE PATH a/v2/main.go: import example.com/m/a/v2, the /v2 major-version element is
   stripped so the output name is "a"; the fresh root directory "a" EXISTS -> preflight FAILS. *)
Definition fx_av2 : GoProgram := singleton_program ex_ms (mkFP "a/v2/main.go" eq_refl) ex_main.
Example fx_2006_output_a       : fresh_build_plan fx_av2 = FBDWriteSingleMain "a/v2" "example.com/m/a/v2" "a" (Some FREDirectory). Proof. vm_compute. reflexivity. Qed.
Example fx_2006_preflight_fails : fresh_build_disposition_ok (fresh_build_plan fx_av2) = false. Proof. vm_compute. reflexivity. Qed.
Example fx_2006_not_gocompile   : ~ GoCompile fx_av2.
Proof. intros [Hpf _]. unfold fresh_build_preflight_ok in Hpf. vm_compute in Hpf. discriminate. Qed.
(* b — the ERASED build-output report carries the exact colliding output NAME "a" as [ed_output]
   (the erased payload distinguishes this collision from one at a different output name). *)
Example fx_2006_erased_output :
  map erase_diagnostic (fresh_build_diagnostics fx_av2)
  = [ mkErasedDiagnostic DCBuildOutputIsDirectory (EAPackage "a/v2") [] None (Some "a") None ].
Proof. vm_compute. reflexivity. Qed.

(* 20.7 — IMMEDIATE v2 PACKAGE v2/main.go: import example.com/m/v2 -> output name "m" (the module basename,
   after the /v2 strip); the fresh root directory "v2" does not collide with "m" -> preflight succeeds. *)
Definition fx_v2 : GoProgram := singleton_program ex_ms (mkFP "v2/main.go" eq_refl) ex_main.
Example fx_2007_output_m   : fresh_build_plan fx_v2 = FBDWriteSingleMain "v2" "example.com/m/v2" "m" None. Proof. vm_compute. reflexivity. Qed.
Example fx_2007_preflight  : fresh_build_disposition_ok (fresh_build_plan fx_v2) = true. Proof. vm_compute. reflexivity. Qed.
Example fx_2007_gocompile  : GoCompile fx_v2.               Proof. apply GoCompile_of_source_spec_valid_b; vm_compute; reflexivity. Qed.

(* 20.8 — MULTIPLE MAIN PACKAGES a/main.go + b/main.go: FBDDiscardMultiple, NO default-output preflight failure,
   a source-valid program succeeds. *)
Example fx_2008 : forall p,
  build_program ex_ms [ main_file_node (mkFP "a/main.go" eq_refl) ex_main
                      ; main_file_node (mkFP "b/main.go" eq_refl) ex_main ] = Some p ->
  fresh_build_plan p = FBDDiscardMultiple 2
  /\ fresh_build_disposition_ok (fresh_build_plan p) = true
  /\ GoCompile p.
Proof.
  intros p H. vm_compute in H. injection H as <-.
  split; [ vm_compute; reflexivity | split; [ vm_compute; reflexivity | apply GoCompile_of_source_spec_valid_b; vm_compute; reflexivity ] ].
Qed.

(* 20.9 — MULTIPLE PACKAGES WITH A SEMANTIC FAILURE: no default-output collision branch, so the semantic
   diagnostics ARE exposed (the class is the typing class). *)
Example fx_2009 : forall p,
  build_program ex_ms [ main_file_node (mkFP "a/main.go" eq_refl) ex_main
                      ; main_file_node (mkFP "b/main.go" eq_refl) ex_bad ] = Some p ->
  fresh_build_disposition_ok (fresh_build_plan p) = true /\ go_compile_class p = LCTyping.
Proof.
  intros p H. vm_compute in H. injection H as <-.
  split; [ vm_compute; reflexivity | rewrite go_compile_class_spec; vm_compute; reflexivity ].
Qed.

(* 20.10 — go.mod OVERWRITE: module final component "go.mod" -> output name "go.mod", whose root target is the
   REGULAR go.mod (FREGoMod, not a directory) -> preflight succeeds; the plan RECORDS the overwrite target. *)
Definition ex_ms_gomod : ModuleSpec := mkModuleSpec (ModulePath.mkMP "example.com/go.mod" eq_refl) GoVersion.Go1_23.
Definition fx_gomod : GoProgram := singleton_program ex_ms_gomod (mkFP "main.go" eq_refl) ex_main.
Example fx_2010_plan      : fresh_build_plan fx_gomod = FBDWriteSingleMain "" "example.com/go.mod" "go.mod" (Some FREGoMod). Proof. vm_compute. reflexivity. Qed.
Example fx_2010_preflight : fresh_build_disposition_ok (fresh_build_plan fx_gomod) = true. Proof. vm_compute. reflexivity. Qed.
Example fx_2010_gocompile : GoCompile fx_gomod.             Proof. apply GoCompile_of_source_spec_valid_b; vm_compute; reflexivity. Qed.

(* 20.11 — SOURCE OVERWRITE: module final component "main.go" -> output name "main.go", whose root target is a
   REGULAR source file (FRESourceFile, not a directory) -> preflight succeeds; GoCompile. *)
Definition ex_ms_srcname : ModuleSpec := mkModuleSpec (ModulePath.mkMP "example.com/main.go" eq_refl) GoVersion.Go1_23.
Definition fx_srcov : GoProgram := singleton_program ex_ms_srcname (mkFP "main.go" eq_refl) ex_main.
Example fx_2011_preflight : fresh_build_disposition_ok (fresh_build_plan fx_srcov) = true. Proof. vm_compute. reflexivity. Qed.
Example fx_2011_gocompile : GoCompile fx_srcov.             Proof. apply GoCompile_of_source_spec_valid_b; vm_compute; reflexivity. Qed.

(* 20.12 — ROOT SOURCE NAME COLLISION WITHOUT EXACT MODULE MATCH: the output target lookup is EXACT string
   identity — output name "m" does NOT match the root source file "main.go" (no prefix/substring match). *)
Example fx_2012 : PM.find "m" (root_layout fx_root) = None. Proof. vm_compute. reflexivity. Qed.

(* 20.13 — THREE MAINS in one package (n-1 = 2 redeclarations): with a build-output directory collision the
   final report HIDES them (LCBuildOutput); without a collision the class exposes the package-main-count. *)
Definition ex_3main : list GoDecl :=
  [ DMain [ SPrintln [ EInt 1 ] ]; DMain [ SPrintln [ EInt 2 ] ]; DMain [ SPrintln [ EInt 3 ] ] ].
Definition fx_3main_hidden : GoProgram := singleton_program ex_ms (mkFP "sub/main.go" eq_refl) ex_3main.
Definition fx_3main_shown  : GoProgram := singleton_program ex_ms (mkFP "main.go" eq_refl)     ex_3main.
Example fx_2013a_class  : go_compile_class fx_3main_hidden = LCBuildOutput.
Proof. rewrite go_compile_class_spec. vm_compute. reflexivity. Qed.
Example fx_2013a_report : forall idx, exists pk name, elaboration_diagnostics fx_3main_hidden idx = [DRBuildOutputIsDirectory pk name].
Proof. intro idx. apply elaboration_diagnostics_fresh_failure. vm_compute. reflexivity. Qed.
Example fx_2013b_class  : go_compile_class fx_3main_shown = LCPackageMainCount.
Proof. rewrite go_compile_class_spec. vm_compute. reflexivity. Qed.

(* 20.14 — MISSING MAIN ENTRY (a package file with no DMain): same two branches — a collision HIDES it, a
   collision-free layout EXPOSES the missing-main (package-main-count) class. *)
Definition fx_nomain_hidden : GoProgram := singleton_program ex_ms (mkFP "sub/main.go" eq_refl) nil.
Definition fx_nomain_shown  : GoProgram := singleton_program ex_ms (mkFP "main.go" eq_refl)     nil.
Example fx_2014a_class : go_compile_class fx_nomain_hidden = LCBuildOutput.
Proof. rewrite go_compile_class_spec. vm_compute. reflexivity. Qed.
Example fx_2014b_class : go_compile_class fx_nomain_shown = LCPackageMainCount.
Proof. rewrite go_compile_class_spec. vm_compute. reflexivity. Qed.

(* 20.15 — REORDERED CONSTRUCTION under the SAME ModuleSpec -> equal full plan, erased final report, and class
   (permuted file-node input is [ProgramInputEqual]). *)
Theorem fx_2015_full_determinism :
  forall p1 p2 (idx1 : GoIndex.Snap.SyntaxIndex p1) (idx2 : GoIndex.Snap.SyntaxIndex p2),
    build_program c3_ms [rnode_a; rnode_b] = Some p1 ->
    build_program c3_ms [rnode_b; rnode_a] = Some p2 ->
    fresh_build_plan p1 = fresh_build_plan p2
    /\ erased_elaboration_report p1 idx1 = erased_elaboration_report p2 idx2
    /\ go_compile_class p1 = go_compile_class p2.
Proof.
  intros p1 p2 idx1 idx2 H1 H2.
  assert (HIE : ProgramInputEqual p1 p2).
  { unfold build_program in H1, H2.
    destruct (filemap_of_nodes [rnode_a; rnode_b]) as [fm1|] eqn:F1; [ | discriminate ].
    destruct (filemap_of_nodes [rnode_b; rnode_a]) as [fm2|] eqn:F2; [ | discriminate ].
    injection H1 as <-. injection H2 as <-. split; [ reflexivity | cbn [prog_files] ].
    exact (filemap_of_nodes_permutation _ _ fm1 fm2 (perm_swap rnode_b rnode_a []) F1 F2). }
  split; [ exact (fresh_build_plan_InputEqual _ _ HIE) |].
  split; [ exact (erased_elaboration_report_InputEqual _ _ idx1 idx2 HIE)
         | exact (go_compile_class_Equal _ _ HIE) ].
Qed.

(* 20.16 — EQUAL FILES, DIFFERENT MODULE: the source file map is identical, but the two ModuleSpecs give the
   sole package DIFFERENT default executable names, so the FreshBuildPlans DIFFER — full-plan equality does NOT
   follow from FilesEqual alone (this is the counterexample). *)
Definition fx_cex_1 : GoProgram := singleton_program ex_ms (mkFP "v2/main.go" eq_refl) ex_main.
Definition fx_cex_2 : GoProgram :=
  singleton_program (mkModuleSpec (ModulePath.mkMP "example.com/other" eq_refl) GoVersion.Go1_23) (mkFP "v2/main.go" eq_refl) ex_main.
Example fx_2016_files_equal : GoAST.FilesEqual (prog_files fx_cex_1) (prog_files fx_cex_2).
Proof. assert (prog_files fx_cex_1 = prog_files fx_cex_2) as Heq by (vm_compute; reflexivity).
       rewrite Heq. apply GoAST.FilesEqual_refl. Qed.
Example fx_2016_plans_differ : fresh_build_plan fx_cex_1 <> fresh_build_plan fx_cex_2.
Proof. vm_compute. discriminate. Qed.

