(** ============================================================================
    GoRender — the DIRECT renderer of one file's raw declarations to Go source bytes.  No tokenizer/
    lexer/parser/round-trip/second tree.  The package CLAUSE is emitted from the compiler-derived package
    name (a CompilationFacts result, passed in — not raw metadata); each [DMain] renders as a
    `func main()` declaration; the builtin [println] is the fixed spelling of [SPrintln].

    Every rendered file begins with the exact generated header as its FIRST LINE (part of the
    Rocq-rendered bytes — the sink never adds or alters it).  [render_file] is an INTERNAL helper; the
    PUBLIC capability is [GoEmit.render_program : SafeProgram -> DirectoryImage].  Proved here: all
    output ASCII; the ROOT correspondence [render_expr_denotes] — the rendered primitive spelling
    denotes EXACTLY the semantic value (parser-free) — plus decimal faithfulness / no-leading-zero and
    the int boundary facts.
    ============================================================================ *)
From Stdlib Require Import String Ascii NArith ZArith List Bool Lia.
From Fido Require Import digits Ints GoAST GoCompile GoSafe.
Import ListNotations.
Open Scope string_scope.

Definition nl_c : ascii := ascii_of_nat 10.
Definition tab_c : ascii := ascii_of_nat 9.
Definition nl : string := String nl_c EmptyString.
Definition tab : string := String tab_c EmptyString.

(** The exact first line of every generated .go file (two spaces after the period). *)
Definition header : string := "// fido generated.  do not edit.".

Definition render_expr (e : GoExpr) : string :=
  match e with
  | EBool true  => "true"
  | EBool false => "false"
  | EInt n => print_Z (Z.of_N n)
  | ENeg n => String "-"%char (print_Z (Z.of_N n))
  end.

Fixpoint render_args (es : list GoExpr) : string :=
  match es with
  | []       => ""
  | [e]      => render_expr e
  | e :: es' => render_expr e ++ ", " ++ render_args es'
  end.

Definition render_stmt (s : GoStmt) : string :=
  match s with SPrintln args => tab ++ "println(" ++ render_args args ++ ")" ++ nl end.

Fixpoint render_stmts (ss : list GoStmt) : string :=
  match ss with [] => "" | s :: ss' => render_stmt s ++ render_stmts ss' end.

Definition render_decl (d : GoDecl) : string :=
  match d with DMain body => "func main() {" ++ nl ++ render_stmts body ++ "}" ++ nl end.

(** Each top-level declaration is preceded by a blank line (gofmt spacing). *)
Fixpoint render_decls (ds : list GoDecl) : string :=
  match ds with [] => "" | d :: ds' => nl ++ render_decl d ++ render_decls ds' end.

(** [render_file] is literally [header], the newline, then the package clause + declarations — so "the
    header is the exact first line" is definitional.  The package NAME comes from CompilationFacts. *)
Definition render_file (pkg : string) (f : GoFileAST) : string :=
  header ++ String nl_c (nl ++ "package " ++ pkg ++ nl ++ render_decls f).

(** The header is EXACTLY the first line (header, then the newline [nl_c]) — the ownership contract the
    sink reads with `input_line`, strictly stronger than "header is a prefix". *)
Lemma render_file_first_line : forall pkg f, exists rest, render_file pkg f = header ++ String nl_c rest.
Proof. intros pkg f. unfold render_file. eexists. reflexivity. Qed.

(** ---- all-ASCII output ---- *)

Definition is_ascii (c : ascii) : bool := Nat.ltb (nat_of_ascii c) 128.

Fixpoint str_ascii (s : string) : bool :=
  match s with EmptyString => true | String c s' => is_ascii c && str_ascii s' end.

Lemma str_ascii_app : forall a b, str_ascii (a ++ b) = str_ascii a && str_ascii b.
Proof.
  induction a as [ | c a' IH ]; intro b; simpl; [ reflexivity | rewrite IH, andb_assoc; reflexivity ].
Qed.

Lemma dec_digit_ascii : forall d, (d < 10)%nat -> is_ascii (dec_digit d) = true.
Proof. intros d Hd. do 10 (destruct d as [ | d ]; [ reflexivity | ]). lia. Qed.

Lemma render_digits_step : forall dig a ds acc,
  render_digits dig (a :: ds) acc = render_digits dig ds (String (dig a) acc).
Proof. reflexivity. Qed.

Lemma render_digits_ascii : forall ds acc,
  (forall d, In d ds -> is_ascii (dec_digit d) = true) ->
  str_ascii (render_digits dec_digit ds acc) = str_ascii acc.
Proof.
  induction ds as [ | a ds' IH ]; intros acc Hall.
  - reflexivity.
  - rewrite render_digits_step, IH.
    + cbn [str_ascii]. rewrite (Hall a (or_introl eq_refl)). reflexivity.
    + intros d Hd. apply Hall. right. exact Hd.
Qed.

Lemma print_Z_pos_ascii : forall p, str_ascii (print_Z_pos p) = true.
Proof.
  intro p. unfold print_Z_pos. rewrite render_digits_ascii; [ reflexivity | ].
  intros d Hd. apply dec_digit_ascii.
  pose proof (pos_digits_bound 10 p ltac:(lia)) as Hb. rewrite Forall_forall in Hb. apply Hb; exact Hd.
Qed.

Lemma print_Z_ascii : forall z, str_ascii (print_Z z) = true.
Proof.
  intros [ | p | p ].
  - reflexivity.
  - apply print_Z_pos_ascii.
  - cbn [print_Z]. rewrite str_ascii_app, print_Z_pos_ascii. reflexivity.
Qed.

Lemma render_expr_ascii : forall e, str_ascii (render_expr e) = true.
Proof.
  intros [ [] | n | n ]; cbn [render_expr].
  - reflexivity.
  - reflexivity.
  - apply print_Z_ascii.
  - cbn [str_ascii]. rewrite print_Z_ascii. reflexivity.
Qed.

Lemma render_args_ascii : forall es, str_ascii (render_args es) = true.
Proof.
  induction es as [ | e es' IH ]; [ reflexivity | ].
  destruct es' as [ | e2 es'' ].
  - apply render_expr_ascii.
  - change (render_args (e :: e2 :: es''))
      with (render_expr e ++ ", " ++ render_args (e2 :: es'')).
    rewrite !str_ascii_app, render_expr_ascii. simpl. exact IH.
Qed.

Lemma render_stmt_ascii : forall s, str_ascii (render_stmt s) = true.
Proof. intros [ args ]. cbn [render_stmt]. rewrite !str_ascii_app, render_args_ascii. reflexivity. Qed.

Lemma render_stmts_ascii : forall ss, str_ascii (render_stmts ss) = true.
Proof.
  induction ss as [ | s ss' IH ]; [ reflexivity | ].
  cbn [render_stmts]. rewrite str_ascii_app, render_stmt_ascii, IH. reflexivity.
Qed.

Lemma render_decl_ascii : forall d, str_ascii (render_decl d) = true.
Proof. intros [ body ]. cbn [render_decl]. rewrite !str_ascii_app, render_stmts_ascii. reflexivity. Qed.

Lemma render_decls_ascii : forall ds, str_ascii (render_decls ds) = true.
Proof.
  induction ds as [ | d ds' IH ]; [ reflexivity | ].
  cbn [render_decls]. rewrite !str_ascii_app, render_decl_ascii, IH. reflexivity.
Qed.

(** The whole file is ASCII when the (compiler-derived) package name is. *)
Theorem render_file_ascii : forall pkg f, str_ascii pkg = true -> str_ascii (render_file pkg f) = true.
Proof.
  intros pkg f Hpkg. unfold render_file. rewrite str_ascii_app. cbn [str_ascii].
  rewrite !str_ascii_app, Hpkg, render_decls_ascii. reflexivity.
Qed.

(** ---- decimal faithfulness: emitted decimal denotes EXACTLY the value, no leading zero ---- *)

Definition ascii_digit (c : ascii) : nat := nat_of_ascii c - 48.

Fixpoint dval (s : string) (acc : Z) : Z :=
  match s with EmptyString => acc | String c s' => dval s' (acc * 10 + Z.of_nat (ascii_digit c)) end.
Definition dval0 (s : string) : Z := dval s 0.

Lemma ascii_digit_dec_digit : forall d, (d < 10)%nat -> ascii_digit (dec_digit d) = d.
Proof. intros d Hd. do 10 (destruct d as [ | d ]; [ reflexivity | ]). lia. Qed.

Lemma render_digits_dval : forall ds base,
  (forall d, In d ds -> (d < 10)%nat) ->
  dval (render_digits dec_digit ds base) 0 = dval base (dlist_val 10 ds).
Proof.
  induction ds as [ | d ds' IH ]; intros base Hall.
  - reflexivity.
  - rewrite render_digits_step, (IH (String (dec_digit d) base))
      by (intros x Hx; apply Hall; right; exact Hx).
    cbn [dval]. rewrite ascii_digit_dec_digit by (apply Hall; left; reflexivity).
    cbn [dlist_val]. f_equal. change (Z.of_nat 10) with 10%Z. lia.
Qed.

Lemma print_Z_pos_dval : forall p, dval0 (print_Z_pos p) = Z.pos p.
Proof.
  intro p. unfold dval0, print_Z_pos. rewrite render_digits_dval.
  - cbn [dval]. rewrite pos_digits_val by lia. reflexivity.
  - intros d Hd. pose proof (pos_digits_bound 10 p ltac:(lia)) as Hb.
    rewrite Forall_forall in Hb. apply Hb; exact Hd.
Qed.

Theorem print_Z_dec_faithful : forall z, (0 <= z)%Z -> dval0 (print_Z z) = z.
Proof.
  intros [ | p | p ] H.
  - reflexivity.
  - apply print_Z_pos_dval.
  - exfalso; lia.
Qed.

Definition head_not_zero (s : string) : Prop :=
  match s with EmptyString => False | String c _ => c <> dec_digit 0 end.

Lemma render_digits_snoc : forall ds a base,
  render_digits dec_digit (ds ++ [a]) base = String (dec_digit a) (render_digits dec_digit ds base).
Proof. intros. unfold render_digits. rewrite fold_left_app. reflexivity. Qed.

Theorem print_Z_pos_no_leading_zero : forall p, head_not_zero (print_Z_pos p).
Proof.
  intro p. unfold print_Z_pos.
  destruct (exists_last (pos_digits_nonnil 10 p)) as [init [a Ha]].
  rewrite Ha, render_digits_snoc. cbn [head_not_zero].
  assert (Ha1 : (1 <= a)%nat).
  { pose proof (pos_digits_last 10 p ltac:(lia)) as Hl. rewrite Ha, last_last in Hl. exact Hl. }
  assert (Ha10 : (a < 10)%nat).
  { pose proof (pos_digits_bound 10 p ltac:(lia)) as Hb. rewrite Ha, Forall_forall in Hb.
    apply Hb, in_or_app; right; left; reflexivity. }
  intro Heq.
  assert (Hn : nat_of_ascii (dec_digit a) = nat_of_ascii (dec_digit 0)) by (rewrite Heq; reflexivity).
  unfold dec_digit in Hn.
  rewrite (nat_ascii_embedding (48 + a)) in Hn by lia.
  rewrite (nat_ascii_embedding (48 + 0)) in Hn by lia.
  lia.
Qed.

(** ---- ROOT correspondence: rendered spelling denotes EXACTLY the semantic value (parser-free) ---- *)

(** Read a rendered Go integer literal: an optional leading unary minus over the decimal magnitude. *)
Definition read_go_int (s : string) : Z :=
  match s with
  | String c s' => if Ascii.eqb c "-"%char then Z.opp (dval0 s') else dval0 s
  | EmptyString => dval0 s
  end.

Definition RenderedPrimitiveDenotes (s : string) (v : GoValue) : Prop :=
  match v with
  | VBool b => s = (if b then "true" else "false")
  | VInt z  => read_go_int s = z
  end.

(** print_Z of a nonnegative is nonempty and its first character is a decimal digit, not '-'. *)
Lemma print_Z_pos_head_not_minus : forall p,
  match print_Z_pos p with String c _ => Ascii.eqb c "-"%char = false | EmptyString => False end.
Proof.
  intro p. unfold print_Z_pos.
  destruct (exists_last (pos_digits_nonnil 10 p)) as [init [a Ha]].
  rewrite Ha, render_digits_snoc.
  assert (Ha10 : (a < 10)%nat).
  { pose proof (pos_digits_bound 10 p ltac:(lia)) as Hb. rewrite Ha, Forall_forall in Hb.
    apply Hb, in_or_app; right; left; reflexivity. }
  destruct (Ascii.eqb (dec_digit a) "-"%char) eqn:E; [ | reflexivity ].
  apply Ascii.eqb_eq in E.
  assert (Hn : nat_of_ascii (dec_digit a) = nat_of_ascii "-"%char) by (rewrite E; reflexivity).
  unfold dec_digit in Hn. rewrite (nat_ascii_embedding (48 + a)) in Hn by lia.
  vm_compute (nat_of_ascii "-"%char) in Hn. lia.
Qed.

Lemma read_go_int_nonneg : forall z, (0 <= z)%Z -> read_go_int (print_Z z) = dval0 (print_Z z).
Proof.
  intros [ | p | p ] H.
  - reflexivity.
  - cbn [print_Z]. pose proof (print_Z_pos_head_not_minus p) as Hh.
    destruct (print_Z_pos p) as [ | c s' ] eqn:E; [ contradiction | ].
    unfold read_go_int; rewrite Hh; reflexivity.
  - exfalso; lia.
Qed.

(** The one root theorem tying AST expression, admissibility, semantic value, and rendered spelling:
    a rendered admissible primitive denotes exactly its [eval_expr] value.  Booleans get their canonical
    spellings; nonnegative decimals denote exactly; a negative is unary minus over the magnitude
    (so `-0` denotes `0`, agreeing with [eval_zero_sign_agnostic]). *)
Theorem render_expr_denotes : forall e, ExprOk e -> RenderedPrimitiveDenotes (render_expr e) (eval_expr e).
Proof.
  intros e _. destruct e as [ [] | n | n ]; cbn [render_expr eval_expr RenderedPrimitiveDenotes].
  - reflexivity.
  - reflexivity.
  - rewrite read_go_int_nonneg by apply N2Z.is_nonneg.
    apply print_Z_dec_faithful, N2Z.is_nonneg.
  - unfold read_go_int; cbn [Ascii.eqb].
    rewrite print_Z_dec_faithful by apply N2Z.is_nonneg. reflexivity.
Qed.

Lemma render_boundary_max :
  eval_expr (EInt (Z.to_N int_max)) = VInt int_max /\ ExprOk (EInt (Z.to_N int_max)).
Proof. split; [ reflexivity | constructor; apply Z.le_refl ]. Qed.

Lemma render_boundary_min :
  eval_expr (ENeg (Z.to_N (- int_min))) = VInt int_min /\ ExprOk (ENeg (Z.to_N (- int_min))).
Proof. split; [ reflexivity | constructor; apply Z.le_refl ]. Qed.
