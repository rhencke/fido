(** ============================================================================
    GoSafe.v — supportedness now, behavioral safety later (AST-first spine; see ARCHITECTURE.md §2/§2a).
    [SupportedProgram] is a PHASE-1 SYNTACTIC gate — a supported-subset check — NOT behavioral safety, and it
    is NAMED so deliberately (naming is a correctness claim: never call a syntactic gate "Safe").  The
    semantic [BehaviorSafe] (no nil-deref / OOB / send-on-closed / illegal-close / data-race / …, defined over
    GoSem) lands once GoSem is COMPLETE — GoSem SLICE 1 (the [cmd.v] bridge [denote_program] + [gosem_sound]:
    denotation ⊆ SupportedProgram) now EXISTS, but does not yet denote enough behavior to define BehaviorSafe
    against; [unified.v] is an existing PROOF-ONLY operational semantics, NOT the certified path's, which GoSem
    must still bridge or retire) — at which point the blessed path becomes emit_safe over a [SafeProgram]
    (= EmittableProgram + BehaviorSafe).  Until then GoEmit emits only the SUPPORTED subset via emit_supported,
    and must NOT be described as behaviorally safe.
    ============================================================================ *)
From Fido Require Import GoAst.   (* GoAst supplies the syntax AND [classify] (the keyword -> GoTy map for scalar
                                     conversions).  DELIBERATELY NOT GoPrint — the SAFETY layer must NOT depend on
                                     the printer (ARCHITECTURE.md §2: GoAst -> GoPrint and GoAst -> GoSafe are
                                     SIBLINGS off GoAst, not a chain through the printer). *)
From Fido Require Import GoTypes. (* the SHARED constant-aware type-category checker — [ptype] / [svalue] +
                                     all numeric/conversion helpers — factored into the LOWER module GoTypes
                                     (imports only GoAst) so GoSafe AND GoSem (slice 1 consults [svalue] /
                                     [expr_stmt_ok] via importing GoSafe) consult the SAME authority (single
                                     source of truth, no duplicate predicate).  GoSafe reuses [ptype]/[svalue]. *)
From Stdlib Require Import String List Bool ZArith Eqdep_dec.
Import ListNotations.
Open Scope string_scope.

(** ===================================================================================================
    ===== The SEALED SCOPE + the scope-threading checker [type_expr] + the [ptype] BRIDGE (locals rung 3) =====
    ===================================================================================================
    This layer lives in GoSafe (GoTypes is Definitions-only by charter; the seal needs lemmas).
    THE SEAL — exactly what the types enforce: a local's CATEGORY is a [BoundCat]
    ([bind_category]'s image, by sig); a SCOPE is a [ScopeS] — a sig over the raw association
    list whose decidable well-formedness [scope_wf] demands every name be a valid NON-recognized,
    NON-blank Go identifier and all names pairwise distinct — so a scope carrying a
    constant-category local, a [len]/[int]/[_] binding, a duplicate, or a non-identifier string
    is UNREPRESENTABLE (the [Fail] pins below lock each shape).  [scope_declare] is the
    DECLARATION path: it binds from the RHS [PTy] through [bind_category] internally and DECIDES
    the whole-scope invariant at construction.  BOUNDARY OF THE CLAIM: construction PROVENANCE
    (that a scope arose from declarations, entries unmarked at birth) is NOT type-sealed — a
    well-formed [ScopeS] is directly constructible; that provenance is the scoped fold's property
    ([body_okS] declares exclusively through [scope_declare]; the program gate
    [supported_program] runs the fold from [scope_empty]).  (Full module-opacity would
    seal provenance too but blocks the [vm_compute] fixture discipline this repo's gates rest on —
    precise claims over opacity.)  [type_expr] takes [ScopeS] only. *)
Definition bound_cat_ok (c : PTy) : bool :=
  match c with
  | PtRunInt _ | PtRunFloat _ | PtBool | PtStr => true
  | PtIntConst _ | PtTIntConst _ _ | PtFloatConst _ _ | PtAgg | PtMap | PtNil => false
  end.
Record BoundCat : Type := mkBoundCat { bc_cat : PTy ; bc_ok : bound_cat_ok bc_cat = true }.

(** The BINDING authority: the category a short declaration [x := e] binds from its RHS category —
    TOTAL over [PTy], every rejection a WRITTEN arm, the accepted arms constructing the sealed
    [BoundCat] with its witness.  A short decl is a DEFAULTING value context (the untyped-const row
    carries the same default-[int] representability boundary as [svalue]/[printable_arg_ok]);
    typed constants were range-checked where their category was built; RUNTIME categories bind as
    themselves; [PtAgg]/[PtMap] are REJECTED (the evaluator has no aggregate/map VALUES — a
    structural hole, not a frontier; a conformance NARROWING, Go permits slice/map locals);
    [PtNil] is Go's "use of untyped nil" compile error. *)
Definition bind_category (c : PTy) : option BoundCat :=
  match c with
  | PtIntConst z     => if int_const_repr z GTInt
                        then Some (mkBoundCat (PtRunInt GTInt) eq_refl) else None
  | PtTIntConst t _  => Some (mkBoundCat (PtRunInt t) eq_refl)
  | PtFloatConst t _ => Some (mkBoundCat (PtRunFloat t) eq_refl)
  | PtRunInt t       => Some (mkBoundCat (PtRunInt t) eq_refl)
  | PtRunFloat t     => Some (mkBoundCat (PtRunFloat t) eq_refl)
  | PtBool           => Some (mkBoundCat PtBool eq_refl)
  | PtStr            => Some (mkBoundCat PtStr eq_refl)
  | PtAgg            => None
  | PtMap            => None
  | PtNil            => None
  end.

(** The DECLARATION-NAME gate: a declarable local name is UNRECOGNIZED (the [special_ident] table
    rejects every checker-recognized string uniformly) and not the blank identifier ([_ := e] is
    Go's "no new variables"). *)
Definition decl_ident_ok (s : string) : bool :=
  match special_ident s with
  | None => negb (String.eqb s "_")
  | Some _ => false
  end.

(** The raw association list is INTERNAL plumbing; its decidable well-formedness is the sig's
    membership condition. *)
Definition scope_list : Type := list (string * (BoundCat * bool)).
Fixpoint scope_get (l : scope_list) (s : string) : option (BoundCat * bool) :=
  match l with
  | nil => None
  | (n, ent) :: l' => if String.eqb n s then Some ent else scope_get l' s
  end.
Fixpoint scope_mark (l : scope_list) (s : string) : scope_list :=
  match l with
  | nil => nil
  | (n, (c, u)) :: l' => if String.eqb n s then (n, (c, true)) :: l'
                         else (n, (c, u)) :: scope_mark l' s
  end.
Fixpoint scope_wf (l : scope_list) : bool :=
  match l with
  | nil => true
  | (n, _) :: l' =>
      go_ident n && decl_ident_ok n
      && negb (existsb (fun p => String.eqb n (fst p)) l')
      && scope_wf l'
  end.
Record ScopeS : Type := mkScope { sc_list : scope_list ; sc_ok : scope_wf sc_list = true }.
Definition scope_empty : ScopeS := mkScope nil eq_refl.

(** MARKING preserves well-formedness (it flips only a [bool]; names untouched) — so the sealed
    marker is TOTAL. *)
Lemma scope_mark_fst : forall l s p,
  existsb (fun q => String.eqb p (fst q)) (scope_mark l s)
  = existsb (fun q => String.eqb p (fst q)) l.
Proof.
  induction l as [|[n [c u]] l' IHl]; intros s p; cbn; [reflexivity|].
  destruct (String.eqb n s); cbn; [reflexivity|].
  rewrite IHl. reflexivity.
Qed.
Lemma scope_mark_ok : forall l s, scope_wf l = true -> scope_wf (scope_mark l s) = true.
Proof.
  induction l as [|[n [c u]] l' IHl]; intros s H; cbn in *; [reflexivity|].
  destruct (String.eqb n s); cbn.
  - exact H.
  - apply andb_true_iff in H. destruct H as [H1 H2].
    apply andb_true_iff in H1. destruct H1 as [H1 H3].
    rewrite scope_mark_fst, H3, (IHl s H2).
    rewrite H1. reflexivity.
Qed.
Definition scope_markS (G : ScopeS) (s : string) : ScopeS :=
  mkScope (scope_mark (sc_list G) s) (scope_mark_ok (sc_list G) s (sc_ok G)).

(** SCOPE INSERTION — the ONE boundary: takes a validated [Ident] (a non-identifier string cannot
    even be spelled), binds the RHS category through [bind_category] INTERNALLY (no caller-chosen
    [BoundCat]), and DECIDES the whole-scope invariant at construction ([bool_dec] — the
    recognized-name/blank/freshness rejections are exactly [scope_wf]'s head conjuncts;
    a drift anywhere fail-closes to [None]). *)
Definition scope_declare (G : ScopeS) (x : Ident) (rhs : PTy) : option ScopeS :=
  match bind_category rhs with
  | Some bc =>
      match Bool.bool_dec (scope_wf ((proj1_sig x, (bc, false)) :: sc_list G)) true with
      | left H => Some (mkScope ((proj1_sig x, (bc, false)) :: sc_list G) H)
      | right _ => None
      end
  | None => None
  end.

Fixpoint type_expr (G : ScopeS) (e : GExpr) : option (PTy * ScopeS) :=
  match e with
  | EId i =>
      let s := proj1_sig i in
      match scope_get (sc_list G) s with
      | Some (bc, _) => Some (bc_cat bc, scope_markS G s)   (* a LOCAL: resolve + MARK USED *)
      | None =>
          match special_ident s with
          | Some SnNil => Some (PtNil, G)
          | Some (SnType _) | Some SnLen | Some SnCap
          | Some SnPrintln | Some SnPrint | Some SnPanic => None
          | None => None
          end
      end
  | EInt z => Some (PtIntConst z, G)
  | EHex zc => Some (PtIntConst (proj1_sig zc), G)
  | EStr _ => Some (PtStr, G)
  | EBn o l r =>
      match type_expr G l with
      | Some (cl, G1) =>
          match type_expr G1 r with
          | Some (cr, G2) =>
              match (match o with
                     | BAdd => match cl, cr with
                               | PtStr, PtStr => Some PtStr
                               | _, _ => num_binop o cl cr
                               end
                     | BMul|BDiv|BRem|BShl|BShr|BAnd|BAndNot|BSub|BOr|BXor => num_binop o cl cr
                     | BEq|BNe => if eq_comparable cl cr then Some PtBool else None
                     | BLt|BLe|BGt|BGe => if ord_comparable cl cr then Some PtBool else None
                     | BLAnd|BLOr => if andb (is_bool_cat cl) (is_bool_cat cr) then Some PtBool else None
                     end) with
              | Some c => Some (c, G2)
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | EUn o e0 =>
      match type_expr G e0 with
      | Some (c0, G1) =>
          match (match o with
                 | UNeg => match c0 with
                           | PtIntConst z => Some (PtIntConst (Z.opp z))
                           | PtTIntConst t z =>
                               let r := Z.opp z in if int_const_repr r t then Some (PtTIntConst t r) else None
                           | PtFloatConst t d =>
                               let d' := dy_make (Z.opp (dy_m d)) (dy_e d) in
                               if float_dyadic_repr t (dy_m d') (dy_e d') then Some (PtFloatConst t d') else None
                           | PtRunInt t => Some (PtRunInt t) | PtRunFloat t => Some (PtRunFloat t)
                           | _ => None end
                 | UXor => match c0 with
                           | PtIntConst z => Some (PtIntConst (Z.lnot z))
                           | PtTIntConst t z =>
                               match complement_const t z with
                               | Some r => if int_const_repr r t then Some (PtTIntConst t r) else None
                               | None => None
                               end
                           | PtRunInt t => Some (PtRunInt t)
                           | _ => None end
                 | UNot => match c0 with PtBool => Some PtBool | _ => None end
                 | UDeref | UAddr => None
                 end) with
          | Some c => Some (c, G1)
          | None => None
          end
      | None => None
      end
  | ECall (EId i) (a :: nil) =>
      match scope_get (sc_list G) (proj1_sig i) with
      | Some _ => None   (* a LOCAL callee: no local is a function in this fragment — REJECT (local-first, so a scoped name can never silently become a builtin/conversion) *)
      | None =>
      match type_expr G a with
      | Some (ca, G1) =>
          match (match special_ident (proj1_sig i) with
                 | Some SnLen =>
                     match a, ca with
                     | EStr str, _ => Some (PtIntConst (Z.of_nat (String.length str)))
                     | _, (PtAgg | PtMap) => Some (PtRunInt GTInt)
                     | _, _ => None
                     end
                 | Some SnCap =>
                     match ca with PtAgg => Some (PtRunInt GTInt) | _ => None end
                 | Some (SnType t) => conv_to_scalar ca t
                 | Some SnNil | Some SnPrintln | Some SnPrint | Some SnPanic => None
                 | None => None
                 end) with
          | Some c => Some (c, G1)
          | None => None
          end
      | None => None
      end
      end
  | ECall _ _ => None
  | EConv c e0 =>
      match c with
      | CTMap _ _ => None
      | CTSlice _ | CTChan _ =>
          if goty_supported (convty_ty c)
          then match type_expr G e0 with
               | Some (c0, G1) =>
                   match (match c0 with PtNil => Some PtAgg | _ => None end) with
                   | Some cc => Some (cc, G1)
                   | None => None
                   end
               | None => None
               end
          else None
      end
  | EIndex (ESliceLit t es) idx =>
      if is_int_goty t
      then match (fix go_els (G0 : ScopeS) (l : list GExpr) {struct l} : option ScopeS :=
                    match l with
                    | nil => Some G0
                    | el :: l' =>
                        match type_expr G0 el with
                        | Some (ce, G1) => if assignable_to_ty ce t then go_els G1 l' else None
                        | None => None
                        end
                    end) G es with
           | Some Ges =>
               match type_expr Ges idx with
               | Some (ci, Gi) =>
                   match (if is_int_cat ci then
                            match int_const_val ci with
                            | Some k => if (0 <=? k)%Z && int_const_repr k GTInt then Some (PtRunInt t) else None
                            | None   => Some (PtRunInt t)
                            end
                          else None) with
                   | Some c => Some (c, Gi)
                   | None => None
                   end
               | None => None
               end
           | None => None
           end
      else None
  | ESliceLit t es =>
      if goty_supported t
      then match (fix go_els (G0 : ScopeS) (l : list GExpr) {struct l} : option ScopeS :=
                    match l with
                    | nil => Some G0
                    | el :: l' =>
                        match type_expr G0 el with
                        | Some (ce, G1) => if assignable_to_ty ce t then go_els G1 l' else None
                        | None => None
                        end
                    end) G es with
           | Some Ges => Some (PtAgg, Ges)
           | None => None
           end
      else None
  | EMapLit kt vt kvs =>
      if andb (is_int_goty kt) (goty_supported vt)
      then match (fix go_kvs (G0 : ScopeS) (acc : list Z) (l : list (GExpr * GExpr)) {struct l}
                    : option (list Z * ScopeS) :=
                    match l with
                    | nil => Some (rev acc, G0)
                    | (k, v) :: l' =>
                        match type_expr G0 k with
                        | Some (ck, G1) =>
                            match type_expr G1 v with
                            | Some (cv, G2) =>
                                match int_const_val ck with
                                | Some z =>
                                    if andb (assignable_to_ty ck kt) (assignable_to_ty cv vt)
                                    then go_kvs G2 (z :: acc) l' else None
                                | None => None
                                end
                            | None => None
                            end
                        | None => None
                        end
                    end) G nil kvs with
           | Some (zs, Gk) => if nodup_z zs then Some (PtMap, Gk) else None
           | None => None
           end
      else None
  | ESel _ _ | EIndex _ _ | ESlice _ _ _ | EAssert _ _ => None
  end.

(** the one option-pair shape every dispatch case reduces to: both traversals compute the SAME
    dispatch term [d]; the scope result is the unchanged [g]. *)
Lemma opt_pair_agree : forall (A B : Type) (d : option A) (g : B),
  match (match d with Some c => Some (c, g) | None => None end) with
  | Some cg => d = Some (fst cg) /\ snd cg = g
  | None => d = None
  end.
Proof. intros A B [c|] g; cbn; auto. Qed.

(** The BRIDGE: at the EMPTY scope the two spellings of the category logic agree exactly and no
    marks occur — any divergence in either spelling fails the build here.  (Scope of the claim:
    EMPTY-scope agreement; the nonempty-scope behavior is [type_expr]'s own, exercised by the
    rung-4 gate fixtures.) *)
Lemma type_expr_nil_agrees : forall e,
  match type_expr scope_empty e with
  | Some cg => ptype e = Some (fst cg) /\ snd cg = scope_empty
  | None => ptype e = None
  end.
Proof.
  fix IH 1. intro e.
  destruct e as [i|z|o e0|o l r|e0 f|e0 idx|e0 lo hi|e0 args|e0 T|c e0|t es|kt vt kvs|str|zc].
  - (* EId *)
    cbn [type_expr ptype scope_get sc_list scope_empty].
    destruct (special_ident (proj1_sig i)) as [[?| | | | | |]|]; cbn; auto.
  - (* EInt *) cbn; auto.
  - (* EUn *)
    pose proof (IH e0) as H0. cbn [type_expr ptype].
    destruct (type_expr scope_empty e0) as [[c0 G1]|].
    + cbn [fst snd] in H0. destruct H0 as [Hp ->]. rewrite Hp.
      apply opt_pair_agree.
    + rewrite H0. reflexivity.
  - (* EBn *)
    pose proof (IH l) as Hl. cbn [type_expr ptype].
    destruct (type_expr scope_empty l) as [[cl G1]|].
    + cbn [fst snd] in Hl. destruct Hl as [Hpl ->]. rewrite Hpl.
      pose proof (IH r) as Hr.
      destruct (type_expr scope_empty r) as [[cr G2]|].
      * cbn [fst snd] in Hr. destruct Hr as [Hpr ->]. rewrite Hpr.
        apply opt_pair_agree.
      * rewrite Hr. reflexivity.
    + rewrite Hl. reflexivity.
  - (* ESel *) cbn; reflexivity.
  - (* EIndex *)
    destruct e0 as [ | | | | | | | | | |t es| | | ]; try (cbn; reflexivity).
    cbn [type_expr ptype].
    destruct (is_int_goty t) eqn:Hit; cbn [andb]; [|reflexivity].
    set (F := (fix go_els (G0 : ScopeS) (l : list GExpr) {struct l} : option ScopeS :=
                    match l with
                    | nil => Some G0
                    | el :: l' =>
                        match type_expr G0 el with
                        | Some (ce, G1) => if assignable_to_ty ce t then go_els G1 l' else None
                        | None => None
                        end
                    end)).
    assert (Hels :
      match F scope_empty es with
      | Some Ges => Ges = scope_empty /\
          forallb (fun el => match ptype el with Some ce => assignable_to_ty ce t | None => false end) es = true
      | None =>
          forallb (fun el => match ptype el with Some ce => assignable_to_ty ce t | None => false end) es = false
      end).
    { subst F. induction es as [|el es' IHes]; cbn.
      - auto.
      - pose proof (IH el) as Hel.
        destruct (type_expr scope_empty el) as [[ce G1]|].
        + cbn [fst snd] in Hel. destruct Hel as [Hpe ->]. rewrite Hpe.
          destruct (assignable_to_ty ce t); cbn.
          * exact IHes.
          * reflexivity.
        + rewrite Hel. reflexivity. }
    destruct (F scope_empty es) as [Ges|].
    + destruct Hels as [-> Hfb]. rewrite Hfb. cbn [andb].
      pose proof (IH idx) as Hi.
      destruct (type_expr scope_empty idx) as [[ci Gi]|].
      * cbn [fst snd] in Hi. destruct Hi as [Hpi ->]. rewrite Hpi.
        apply opt_pair_agree.
      * rewrite Hi. reflexivity.
    + rewrite Hels. cbn. reflexivity.
  - (* ESlice *) cbn; reflexivity.
  - (* ECall *)
    destruct e0 as [i| | | | | | | | | | | | | ]; try (destruct args as [|a0 [|b0 args']]; cbn; reflexivity).
    destruct args as [|a [|b0 args']]; try (cbn; reflexivity).
    pose proof (IH a) as Ha. cbn [type_expr ptype scope_get sc_list scope_empty].
    destruct (type_expr scope_empty a) as [[ca G1]|].
    + cbn [fst snd] in Ha. destruct Ha as [Hpa ->]. rewrite Hpa.
      apply opt_pair_agree.
    + rewrite Ha. reflexivity.
  - (* EAssert *) cbn; reflexivity.
  - (* EConv *)
    destruct c as [ty|ty|mkt mvt]; cbn [type_expr ptype convty_ty].
    + destruct (goty_supported (GTSlice ty)); [|cbn; reflexivity].
      pose proof (IH e0) as H0.
      destruct (type_expr scope_empty e0) as [[c0 G1]|].
      * cbn [fst snd] in H0. destruct H0 as [Hp ->]. rewrite Hp.
        apply opt_pair_agree.
      * rewrite H0. reflexivity.
    + destruct (goty_supported (GTChan ty)); [|cbn; reflexivity].
      pose proof (IH e0) as H0.
      destruct (type_expr scope_empty e0) as [[c0 G1]|].
      * cbn [fst snd] in H0. destruct H0 as [Hp ->]. rewrite Hp.
        apply opt_pair_agree.
      * rewrite H0. reflexivity.
    + reflexivity.
  - (* ESliceLit *)
    cbn [type_expr ptype].
    destruct (goty_supported t) eqn:Hgs; cbn [andb]; [|reflexivity].
    set (F := (fix go_els (G0 : ScopeS) (l : list GExpr) {struct l} : option ScopeS :=
                    match l with
                    | nil => Some G0
                    | el :: l' =>
                        match type_expr G0 el with
                        | Some (ce, G1) => if assignable_to_ty ce t then go_els G1 l' else None
                        | None => None
                        end
                    end)).
    assert (Hels :
      match F scope_empty es with
      | Some Ges => Ges = scope_empty /\
          forallb (fun el => match ptype el with Some ce => assignable_to_ty ce t | None => false end) es = true
      | None =>
          forallb (fun el => match ptype el with Some ce => assignable_to_ty ce t | None => false end) es = false
      end).
    { subst F. induction es as [|el es' IHes]; cbn.
      - auto.
      - pose proof (IH el) as Hel.
        destruct (type_expr scope_empty el) as [[ce G1]|].
        + cbn [fst snd] in Hel. destruct Hel as [Hpe ->]. rewrite Hpe.
          destruct (assignable_to_ty ce t); cbn.
          * exact IHes.
          * reflexivity.
        + rewrite Hel. reflexivity. }
    destruct (F scope_empty es) as [Ges|].
    + destruct Hels as [-> Hfb]. rewrite Hfb. cbn; auto.
    + rewrite Hels. cbn. reflexivity.
  - (* EMapLit *)
    cbn [type_expr ptype].
    destruct (is_int_goty kt) eqn:Hik; cbn [andb]; [|reflexivity].
    destruct (goty_supported vt) eqn:Hgv; cbn [andb]; [|reflexivity].
    set (F := (fix go_kvs (G0 : ScopeS) (acc : list Z) (l : list (GExpr * GExpr)) {struct l}
                    : option (list Z * ScopeS) :=
                    match l with
                    | nil => Some (rev acc, G0)
                    | (k, v) :: l' =>
                        match type_expr G0 k with
                        | Some (ck, G1) =>
                            match type_expr G1 v with
                            | Some (cv, G2) =>
                                match int_const_val ck with
                                | Some z =>
                                    if andb (assignable_to_ty ck kt) (assignable_to_ty cv vt)
                                    then go_kvs G2 (z :: acc) l' else None
                                | None => None
                                end
                            | None => None
                            end
                        | None => None
                        end
                    end)).
    assert (Hfold : forall acc,
      match F scope_empty acc kvs with
      | Some zsG => snd zsG = scope_empty
          /\ fst zsG = (rev acc ++ map_key_vals_with ptype kvs)%list
          /\ forallb (fun kv => match kv with
                                | (k, v) =>
                                    match ptype k, ptype v with
                                    | Some ck, Some cv =>
                                        match int_const_val ck with
                                        | Some _ => andb (assignable_to_ty ck kt) (assignable_to_ty cv vt)
                                        | None => false
                                        end
                                    | _, _ => false
                                    end
                                end) kvs = true
      | None =>
          forallb (fun kv => match kv with
                             | (k, v) =>
                                 match ptype k, ptype v with
                                 | Some ck, Some cv =>
                                     match int_const_val ck with
                                     | Some _ => andb (assignable_to_ty ck kt) (assignable_to_ty cv vt)
                                     | None => false
                                     end
                                 | _, _ => false
                                 end
                             end) kvs = false
      end).
    { subst F. induction kvs as [|[k v] kvs' IHkvs]; intro acc; cbn.
      - rewrite app_nil_r. auto.
      - pose proof (IH k) as Hk.
        destruct (type_expr scope_empty k) as [[ck G1]|].
        + cbn [fst snd] in Hk. destruct Hk as [Hpk ->]. rewrite Hpk.
          pose proof (IH v) as Hv.
          destruct (type_expr scope_empty v) as [[cv G2]|].
          * cbn [fst snd] in Hv. destruct Hv as [Hpv ->]. rewrite Hpv.
            destruct (int_const_val ck) as [z|]; cbn.
            -- destruct (andb (assignable_to_ty ck kt) (assignable_to_ty cv vt)); cbn.
               ++ specialize (IHkvs (z :: acc)%list).
                  destruct ((fix go_kvs (G0 : ScopeS) (acc : list Z) (l : list (GExpr * GExpr)) {struct l}
                    : option (list Z * ScopeS) :=
                    match l with
                    | nil => Some (rev acc, G0)
                    | (k, v) :: l' =>
                        match type_expr G0 k with
                        | Some (ck, G1) =>
                            match type_expr G1 v with
                            | Some (cv, G2) =>
                                match int_const_val ck with
                                | Some z =>
                                    if andb (assignable_to_ty ck kt) (assignable_to_ty cv vt)
                                    then go_kvs G2 (z :: acc) l' else None
                                | None => None
                                end
                            | None => None
                            end
                        | None => None
                        end
                    end) scope_empty (z :: acc)%list kvs') as [[zs Gk]|].
                  ** cbn [fst snd] in IHkvs. destruct IHkvs as [-> [Hzs Hfb]].
                     cbn [fst snd]. split; [reflexivity|]. split; [|exact Hfb].
                     rewrite Hzs. cbn [rev]. rewrite <- app_assoc. reflexivity.
                  ** exact IHkvs.
               ++ reflexivity.
            -- reflexivity.
          * rewrite Hv. reflexivity.
        + rewrite Hk. reflexivity. }
    specialize (Hfold nil).
    destruct (F scope_empty nil kvs) as [[zs Gk]|].
    + cbn [fst snd] in Hfold. destruct Hfold as [-> [Hzs Hfb]].
      rewrite Hfb. cbn [andb]. cbn [rev app] in Hzs. subst zs.
      destruct (nodup_z (map_key_vals_with ptype kvs)); cbn; auto.
    + rewrite Hfold. cbn. reflexivity.
  - (* EStr *) cbn; auto.
  - (* EHex *) cbn; auto.
Qed.

(** The rung-3 ENDPOINT: closed [ptype] IS the empty-scope projection of [type_expr]. *)
Theorem type_expr_nil_ptype : forall e,
  option_map fst (type_expr scope_empty e) = ptype e.
Proof.
  intro e. pose proof (type_expr_nil_agrees e) as H.
  destruct (type_expr scope_empty e) as [[c G']|]; cbn.
  - cbn [fst snd] in H. destruct H as [-> _]. reflexivity.
  - rewrite H. reflexivity.
Qed.
Print Assumptions type_expr_nil_ptype.

(** ===== MARK-INSENSITIVITY (locals rung 5b): categories do not see used flags =====
    The env evaluator instance (landed rung 5b, GoSemDenote's [denote_expr_env]) queries categories
    at a FIXED statement-entry scope while the checker
    THREADS marks through the same expression — this suite proves the two views agree: marking a
    name changes NO category, and the threaded scope of a marked run is the marked threaded scope
    ([type_expr_mark_agrees]); the consumer-facing corollary is [tcat_mark_insensitive]. *)

(** [scope_get] through a mark: the entry's category is untouched; only the looked-up name's flag
    absorbs the mark. *)
Lemma scope_get_mark : forall l s x,
  scope_get (scope_mark l s) x
  = match scope_get l x with
    | Some (bc, u) => Some (bc, orb u (String.eqb x s))
    | None => None
    end.
Proof.
  induction l as [|[n [c u]] l' IHl]; intros s x; cbn; [reflexivity|].
  destruct (String.eqb n s) eqn:Ens; cbn.
  - destruct (String.eqb n x) eqn:Enx.
    + apply String.eqb_eq in Ens, Enx. subst.
      rewrite String.eqb_refl, orb_true_r. reflexivity.
    + assert (Exs : String.eqb x s = false).
      { apply String.eqb_neq. apply String.eqb_eq in Ens. subst.
        intro Hxs. subst. rewrite String.eqb_refl in Enx. discriminate Enx. }
      destruct (scope_get l' x) as [[bc u0]|]; [rewrite Exs, orb_false_r|]; reflexivity.
  - destruct (String.eqb n x) eqn:Enx; cbn.
    + assert (Exs : String.eqb x s = false).
      { apply String.eqb_neq. apply String.eqb_eq in Enx. subst.
        intro Hxs. subst. rewrite String.eqb_refl in Ens. discriminate Ens. }
      rewrite Exs, orb_false_r. reflexivity.
    + apply IHl.
Qed.

(** Marks COMMUTE (flags only; entry order and names untouched). *)
Lemma scope_mark_comm : forall l s x,
  scope_mark (scope_mark l s) x = scope_mark (scope_mark l x) s.
Proof.
  induction l as [|[n [c u]] l' IHl]; intros s x; cbn; [reflexivity|].
  destruct (String.eqb n s) eqn:Es, (String.eqb n x) eqn:Ex; cbn;
    rewrite ?Es, ?Ex; cbn; try reflexivity.
  rewrite IHl. reflexivity.
Qed.

(** [ScopeS] equality from LIST equality — the wf witness is a bool-equation, so it is unique
    ([UIP_dec] on [bool], a theorem, not an axiom). *)
Lemma scopeS_eq : forall G1 G2 : ScopeS, sc_list G1 = sc_list G2 -> G1 = G2.
Proof.
  intros [l1 ok1] [l2 ok2]; cbn. intros ->.
  f_equal. apply (UIP_dec Bool.bool_dec).
Qed.

Lemma scope_markS_comm : forall G s x,
  scope_markS (scope_markS G s) x = scope_markS (scope_markS G x) s.
Proof. intros G s x. apply scopeS_eq. cbn. apply scope_mark_comm. Qed.

(** the marked run of every dispatch case: SAME dispatch [d], threaded scopes mark-related. *)
Lemma opt_pair_mark_agree : forall (A : Type) (d : option A) (G1 : ScopeS) (s : string),
  match (match d with Some c => Some (c, scope_markS G1 s) | None => None end),
        (match d with Some c => Some (c, G1) | None => None end) with
  | Some (c1, Ga), Some (c2, Gb) => c1 = c2 /\ Ga = scope_markS Gb s
  | None, None => True
  | _, _ => False
  end.
Proof. intros A [c|] G1 s; cbn; auto. Qed.

Lemma type_expr_mark_agrees : forall e G s,
  match type_expr (scope_markS G s) e, type_expr G e with
  | Some (c1, Ga), Some (c2, Gb) => c1 = c2 /\ Ga = scope_markS Gb s
  | None, None => True
  | _, _ => False
  end.
Proof.
  fix IH 1. intro e.
  destruct e as [i|z|o e0|o l r|e0 f|e0 idx|e0 lo hi|e0 args|e0 T|c e0|t es|kt vt kvs|str|zc];
    intros G s.
  - (* EId *)
    cbn [type_expr sc_list scope_markS].
    rewrite scope_get_mark.
    destruct (scope_get (sc_list G) (proj1_sig i)) as [[bc u]|].
    + split; [reflexivity|]. apply scope_markS_comm.
    + destruct (special_ident (proj1_sig i)) as [[?| | | | | |]|]; cbn; auto.
  - (* EInt *) cbn; auto.
  - (* EUn *)
    pose proof (IH e0 G s) as H0. cbn [type_expr].
    destruct (type_expr (scope_markS G s) e0) as [[c1 Ga]|];
      destruct (type_expr G e0) as [[c0 G1]|]; try exact H0; try contradiction.
    destruct H0 as [-> ->]. apply opt_pair_mark_agree.
  - (* EBn *)
    pose proof (IH l G s) as Hl. cbn [type_expr].
    destruct (type_expr (scope_markS G s) l) as [[cl1 Ga]|];
      destruct (type_expr G l) as [[cl G1]|]; try exact Hl; try contradiction.
    destruct Hl as [-> ->].
    pose proof (IH r G1 s) as Hr.
    destruct (type_expr (scope_markS G1 s) r) as [[cr1 Gb]|];
      destruct (type_expr G1 r) as [[cr G2]|]; try exact Hr; try contradiction.
    destruct Hr as [-> ->]. apply opt_pair_mark_agree.
  - (* ESel *) cbn; exact I.
  - (* EIndex *)
    destruct e0 as [ | | | | | | | | | |t es| | | ]; try (cbn; exact I).
    cbn [type_expr].
    destruct (is_int_goty t) eqn:Hit; [|cbn; exact I].
    set (F := (fix go_els (G0 : ScopeS) (l : list GExpr) {struct l} : option ScopeS :=
                    match l with
                    | nil => Some G0
                    | el :: l' =>
                        match type_expr G0 el with
                        | Some (ce, G1) => if assignable_to_ty ce t then go_els G1 l' else None
                        | None => None
                        end
                    end)).
    assert (Hels : forall es' G0,
      match F (scope_markS G0 s) es', F G0 es' with
      | Some Ga, Some Gb => Ga = scope_markS Gb s
      | None, None => True
      | _, _ => False
      end).
    { subst F. induction es' as [|el es'' IHes]; intro G0; cbn.
      - reflexivity.
      - pose proof (IH el G0 s) as Hel.
        destruct (type_expr (scope_markS G0 s) el) as [[ce1 Ga]|];
          destruct (type_expr G0 el) as [[ce G1]|]; try exact Hel; try contradiction.
        destruct Hel as [-> ->].
        destruct (assignable_to_ty ce t); [apply IHes|exact I]. }
    specialize (Hels es G).
    destruct (F (scope_markS G s) es) as [Ga|];
      destruct (F G es) as [Ges|]; try exact Hels; try contradiction.
    subst Ga.
    pose proof (IH idx Ges s) as Hi.
    destruct (type_expr (scope_markS Ges s) idx) as [[ci1 Gb]|];
      destruct (type_expr Ges idx) as [[ci Gi]|]; try exact Hi; try contradiction.
    destruct Hi as [-> ->]. apply opt_pair_mark_agree.
  - (* ESlice *) cbn; exact I.
  - (* ECall *)
    destruct e0 as [i| | | | | | | | | | | | | ]; try (destruct args as [|a0 [|b0 args']]; cbn; exact I).
    destruct args as [|a [|b0 args']]; try (cbn; exact I).
    cbn [type_expr sc_list scope_markS].
    rewrite scope_get_mark.
    destruct (scope_get (sc_list G) (proj1_sig i)) as [[bc u]|]; [cbn; exact I|].
    pose proof (IH a G s) as Ha.
    destruct (type_expr (scope_markS G s) a) as [[ca1 Ga]|];
      destruct (type_expr G a) as [[ca G1]|]; try exact Ha; try contradiction.
    destruct Ha as [-> ->]. apply opt_pair_mark_agree.
  - (* EAssert *) cbn; exact I.
  - (* EConv *)
    destruct c as [ty|ty|mkt mvt]; cbn [type_expr convty_ty].
    + destruct (goty_supported (GTSlice ty)); [|cbn; exact I].
      pose proof (IH e0 G s) as H0.
      destruct (type_expr (scope_markS G s) e0) as [[c1 Ga]|];
        destruct (type_expr G e0) as [[c0 G1]|]; try exact H0; try contradiction.
      destruct H0 as [-> ->]. apply opt_pair_mark_agree.
    + destruct (goty_supported (GTChan ty)); [|cbn; exact I].
      pose proof (IH e0 G s) as H0.
      destruct (type_expr (scope_markS G s) e0) as [[c1 Ga]|];
        destruct (type_expr G e0) as [[c0 G1]|]; try exact H0; try contradiction.
      destruct H0 as [-> ->]. apply opt_pair_mark_agree.
    + cbn; exact I.
  - (* ESliceLit *)
    cbn [type_expr].
    destruct (goty_supported t) eqn:Hgs; [|cbn; exact I].
    set (F := (fix go_els (G0 : ScopeS) (l : list GExpr) {struct l} : option ScopeS :=
                    match l with
                    | nil => Some G0
                    | el :: l' =>
                        match type_expr G0 el with
                        | Some (ce, G1) => if assignable_to_ty ce t then go_els G1 l' else None
                        | None => None
                        end
                    end)).
    assert (Hels : forall es' G0,
      match F (scope_markS G0 s) es', F G0 es' with
      | Some Ga, Some Gb => Ga = scope_markS Gb s
      | None, None => True
      | _, _ => False
      end).
    { subst F. induction es' as [|el es'' IHes]; intro G0; cbn.
      - reflexivity.
      - pose proof (IH el G0 s) as Hel.
        destruct (type_expr (scope_markS G0 s) el) as [[ce1 Ga]|];
          destruct (type_expr G0 el) as [[ce G1]|]; try exact Hel; try contradiction.
        destruct Hel as [-> ->].
        destruct (assignable_to_ty ce t); [apply IHes|exact I]. }
    specialize (Hels es G).
    destruct (F (scope_markS G s) es) as [Ga|];
      destruct (F G es) as [Ges|]; try exact Hels; try contradiction.
    subst Ga. cbn; auto.
  - (* EMapLit *)
    cbn [type_expr].
    destruct (andb (is_int_goty kt) (goty_supported vt)) eqn:Hik; [|cbn; exact I].
    set (F := (fix go_kvs (G0 : ScopeS) (acc : list Z) (l : list (GExpr * GExpr)) {struct l}
                    : option (list Z * ScopeS) :=
                    match l with
                    | nil => Some (rev acc, G0)
                    | (k, v) :: l' =>
                        match type_expr G0 k with
                        | Some (ck, G1) =>
                            match type_expr G1 v with
                            | Some (cv, G2) =>
                                match int_const_val ck with
                                | Some z =>
                                    if andb (assignable_to_ty ck kt) (assignable_to_ty cv vt)
                                    then go_kvs G2 (z :: acc) l' else None
                                | None => None
                                end
                            | None => None
                            end
                        | None => None
                        end
                    end)).
    assert (Hkvs : forall l G0 acc,
      match F (scope_markS G0 s) acc l, F G0 acc l with
      | Some (zs1, Ga), Some (zs2, Gb) => zs1 = zs2 /\ Ga = scope_markS Gb s
      | None, None => True
      | _, _ => False
      end).
    { subst F. induction l as [|[k v] l' IHl]; intros G0 acc; cbn.
      - auto.
      - pose proof (IH k G0 s) as Hk.
        destruct (type_expr (scope_markS G0 s) k) as [[ck1 Ga]|];
          destruct (type_expr G0 k) as [[ck G1]|]; try exact Hk; try contradiction.
        destruct Hk as [-> ->].
        pose proof (IH v G1 s) as Hv.
        destruct (type_expr (scope_markS G1 s) v) as [[cv1 Gb]|];
          destruct (type_expr G1 v) as [[cv G2]|]; try exact Hv; try contradiction.
        destruct Hv as [-> ->].
        destruct (int_const_val ck) as [z|]; [|exact I].
        destruct (andb (assignable_to_ty ck kt) (assignable_to_ty cv vt)); [apply IHl|exact I]. }
    specialize (Hkvs kvs G nil).
    destruct (F (scope_markS G s) nil kvs) as [[zs1 Ga]|];
      destruct (F G nil kvs) as [[zs Gk]|]; try exact Hkvs; try contradiction.
    destruct Hkvs as [-> ->].
    destruct (nodup_z zs); cbn; auto.
  - (* EStr *) cbn; auto.
  - (* EHex *) cbn; auto.
Qed.

(** The scope-aware CATEGORY PROJECTION — the env evaluator's category authority (instantiated at
    rung 5b: GoSemDenote's [denote_expr_env]). *)
Definition tcat (G : ScopeS) (e : GExpr) : option PTy := option_map fst (type_expr G e).

Corollary tcat_mark_insensitive : forall G s e, tcat (scope_markS G s) e = tcat G e.
Proof.
  intros G s e. unfold tcat. pose proof (type_expr_mark_agrees e G s) as H.
  destruct (type_expr (scope_markS G s) e) as [[c1 Ga]|];
    destruct (type_expr G e) as [[c2 Gb]|]; try contradiction.
  - destruct H as [-> _]. reflexivity.
  - reflexivity.
Qed.

(** The rung-3 bridge in [tcat] vocabulary: at the empty scope the projection IS closed [ptype]. *)
Corollary tcat_nil_ptype : forall e, tcat scope_empty e = ptype e.
Proof. exact type_expr_nil_ptype. Qed.
(* zero-axiom gating for the tcat suite rides its consumers' surface registration
   ([gosem_core_surface], GoSem.v — [denote_expr_env_nil] + [tcat_mark_insensitive]). *)

(** The SEAL pins — every forged shape is UNREPRESENTABLE (its witness cannot be built):
    constant/aggregate/nil local categories; recognized-name, blank, duplicate, and
    non-identifier scopes. *)
Example scope_entry_bindable : forall bc : BoundCat, bound_cat_ok (bc_cat bc) = true.
Proof. intro bc. exact (bc_ok bc). Qed.
Fail Definition forged_const_local : BoundCat := mkBoundCat (PtIntConst 0) eq_refl.
Fail Definition forged_agg_local : BoundCat := mkBoundCat PtAgg eq_refl.
Fail Definition forged_nil_local : BoundCat := mkBoundCat PtNil eq_refl.
Fail Definition forged_scope_len : ScopeS :=
  mkScope (("len", (mkBoundCat PtBool eq_refl, false)) :: nil) eq_refl.
Fail Definition forged_scope_int : ScopeS :=
  mkScope (("int", (mkBoundCat PtBool eq_refl, false)) :: nil) eq_refl.
Fail Definition forged_scope_blank : ScopeS :=
  mkScope (("_", (mkBoundCat PtBool eq_refl, false)) :: nil) eq_refl.
Fail Definition forged_scope_dup : ScopeS :=
  mkScope (("x", (mkBoundCat PtBool eq_refl, false))
             :: ("x", (mkBoundCat PtStr eq_refl, false)) :: nil) eq_refl.
Fail Definition forged_scope_badstr : ScopeS :=
  mkScope (("1x", (mkBoundCat PtBool eq_refl, false)) :: nil) eq_refl.
(** The INSERTION boundary decides, from the RHS category: a fresh unrecognized name with a
    bindable RHS binds; recognized/blank names, redeclarations, and unbindable RHS categories
    ([nil], aggregates) reject. *)
Example scope_declare_decides :
  (exists G', scope_declare scope_empty (mkIdent "x" eq_refl) PtBool = Some G')
  /\ scope_declare scope_empty (mkIdent "len" eq_refl) PtBool = None
  /\ scope_declare scope_empty (mkIdent "int" eq_refl) PtBool = None
  /\ scope_declare scope_empty (mkIdent "_" eq_refl) PtBool = None
  /\ scope_declare scope_empty (mkIdent "x" eq_refl) PtNil = None
  /\ scope_declare scope_empty (mkIdent "x" eq_refl) PtAgg = None
  /\ (forall G', scope_declare scope_empty (mkIdent "x" eq_refl) PtBool = Some G' ->
        scope_declare G' (mkIdent "x" eq_refl) PtStr = None).
Proof.
  split; [eexists; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  intros G' H. vm_compute in H. injection H as <-. vm_compute. reflexivity.
Qed.

(** ===================================================================================================
    ===== STRUCTURAL: statement-shape / supported-syntax — the CLOSED fragment [stmt_ok], the
    ===== internal scope-threaded checkers [stmt_okS]/[body_okS], and the program gate
    ===== [supported_program] (locals rung 4) =====
    =================================================================================================== *)

(** Is a builtin [f] valid as a standalone EXPRESSION-STATEMENT call, by NAME and ARITY only?  [println]/
    [print] are variadic in arg COUNT; [panic] takes exactly one.  This checks only name+arity — argument
    TYPES are checked SEPARATELY and per-builtin in [expr_stmt_ok] ([printable_arg_ok] for [print]/[println]
    — NOT "any type": only the guaranteed-printable SCALAR subset — and [svalue] for [panic], which takes an
    [interface{}]).  Deliberately EXACT for the current AST (no user funcs / imports yet).  Excluded on
    purpose: CONVERSIONS ([int(x)] is not a call) and VALUE-returning builtins ([len(x)]/… — "evaluated but
    not used" as a statement).  ([close]/[delete] add a channel/map arg-type constraint — deferred to GoSem.)
    Widens with user funcs / a symbol table. *)
Definition stmt_call_ok (f : string) (args : list GExpr) : bool :=
  match special_ident f with                                           (* the ONE recognized-name table (GoAst) *)
  | Some SnPrintln | Some SnPrint => true                              (* variadic in arg COUNT *)
  | Some SnPanic => match args with _ :: nil => true | _ => false end  (* exactly 1 *)
  | Some (SnType _) | Some SnNil | Some SnLen | Some SnCap => false    (* recognized, but not statement-position callees *)
  | None => false
  end.

(** A [print]/[println] argument GUARANTEED-printable by the Go spec.  ★Go-spec NOTE (Bootstrapping): [print]/
    [println] are bootstrapping builtins whose implementations need NOT accept arbitrary argument types — only
    BOOLEAN, NUMERIC, and STRING are always supported.  So a printable arg is one [ptype] gives a SCALAR
    category (a numeric — [PtIntConst]/[PtTIntConst]/[PtFloatConst]/[PtRunInt]/[PtRunFloat] — or [PtBool]/
    [PtStr]).  This reuses the structural type-checker, so it INHERITS its rejection of closed type-errors —
    e.g. [len(1)] (an int is not len-able), [bool(1)], [1 && 2], [!1], [int([]int{1})], [float64(1) %
    float64(2)], [uint8(300)], [uint8(int(300))], [1/int(0)] — and of EVERY non-scalar category ([PtAgg]
    slice/chan literals and conversions AND [PtMap] map literals — both rejected by this scalar-only whitelist),
    of [nil] ([PtNil]), and of FREE identifiers (a bare [x] is undefined -> [ptype] [None]):
    emit a scalar value instead.  ([println(int64(3))] / [println(len([]int{1}))] stay admitted: a conversion of
    a constant / a [len] of an aggregate has a KNOWN scalar category.)  ★The default-[int] boundary applies: a
    bare UNTYPED int constant arg gets default type [int], so it must FIT in (conservative 32-bit) [int] —
    [println(1)] ✓, [println(<huge>)] REJECT (a TYPED constant was already range-checked at its conversion). *)
Definition printable_cat (c : PTy) : bool :=
  match c with
  | PtIntConst z => int_const_repr z GTInt   (* default-[int] boundary: a bare untyped const must fit int *)
  | PtTIntConst _ _ | PtFloatConst _ _
  | PtRunInt _ | PtRunFloat _ | PtBool | PtStr => true
  | PtAgg | PtMap | PtNil => false
  end.
Arguments printable_cat !c /.
Definition printable_arg_ok (e : GExpr) : bool :=
  match ptype e with
  | Some c => printable_cat c
  | None => false
  end.

(** A [GExpr] legal as an EXPRESSION STATEMENT in Go.  Per the Go spec a bare expression statement must be a
    CALL (a plain value [1] / [a + b] is "evaluated but not used"), AND — crucially — a genuine function call,
    NOT a CONVERSION ([int(x)] is a conversion, also invalid as a statement).  Since no user functions exist
    yet, the statement-valid callees are EXACTLY the whitelisted builtins at their correct arity
    ([stmt_call_ok]).  ARGUMENTS are checked PER BUILTIN: [print]/[println] admit only the guaranteed-printable
    SCALAR subset ([printable_arg_ok] — NOT arbitrary [svalue], so [println(<slice/map>)] / aggregate printing
    is excluded as implementation-defined); [panic] admits any [svalue] (it takes an [interface{}]).  So
    [int64(3)] / [Foo(x)] / [1()] / [len([]int{1})] / [panic()] / [println([]int{1})] / [panic(x)] (free [x]) as
    statements are all rejected; [println(int64(3))] / [println(1 + 2)] / [panic(1)] are accepted. *)
Definition expr_stmt_ok (e : GExpr) : bool :=
  match e with
  | ECall (EId f) args =>
      let fn := proj1_sig f in
      stmt_call_ok fn args &&
      (match special_ident fn with
       | Some SnPanic => forallb svalue args                (* [panic] takes an [interface{}]: any svalue *)
       | Some SnPrintln | Some SnPrint => forallb printable_arg_ok args   (* the printable SCALAR subset *)
       | Some (SnType _) | Some SnNil | Some SnLen | Some SnCap
       | None => forallb printable_arg_ok args              (* dead under [stmt_call_ok]'s false — kept for exact equivalence *)
       end)
  | _                  => false
  end.

(** A statement in the CLOSED (scope-free) supported fragment: an expression statement must be [expr_stmt_ok];
    a bare [return] is
    always fine (a valid tail of a void func like [main]); a blank assign [_ = e] needs [svalue e]; a deferred
    call [defer <e>] ([GsDefer]) reuses [expr_stmt_ok] (Go requires the deferred expr be a CALL — so
    [defer 1] / [defer len(..)] / [defer panic()] / [defer println(<slice>)] are rejected exactly as the
    matching expr statements, pinned in [bad_programs]); a VALUE return [return e] ([GsReturnVal]) is REJECTED —
    the only function we emit is [main], which is VOID, so `return <value>` is invalid Go ("too many return
    values").  (It becomes supported, conditional on the enclosing function's result type, once NON-void
    functions enter the AST — a clean demonstration that GoAst represents more than the gate admits.)
    This fragment is what GoSemDenote's slice-1 evaluator is gated on; the program gate is
    [supported_program] below, and the [.._nil] bridge lemmas prove the spellings agree on decl-free bodies. *)
Definition stmt_ok (s : GoStmt) : bool :=
  match s with
  | GsExprStmt e    => expr_stmt_ok e
  | GsReturn        => true
  | GsReturnVal _   => false   (* value return is invalid in the void [main] — the only function emitted today *)
  | GsBlankAssign e => svalue e  (* [_ = e] is valid iff [e] PRODUCES a value — so [_ = println(1)] (void) is rejected *)
  | GsDefer e       => expr_stmt_ok e  (* [defer <call>]: Go requires the deferred expr be a function CALL — same gate as an expr statement *)
  | GsShortDecl _ _ => false  (* [x := e] needs SCOPE STATE, so it is never CLOSED-supported; [stmt_okS] below is where it is admitted (locals rung 4) *)
  end.

(** ===== The SCOPE-THREADED checkers (locals rung 4) — ONE fold over the sealed [ScopeS],
    ===== run by the program gate [supported_program] below =====
    The scope-aware twins of [expr_stmt_ok]/[stmt_ok]: the SAME per-builtin discipline through the SAME
    category predicates ([printable_cat]/[svalue_cat]) and name table, but every argument/operand goes
    through [type_expr], so identifier USES resolve against the scope and are MARKED in the same traversal.
    Statements THREAD the scope left to right; [GsShortDecl] is admitted HERE — the RHS is typed first
    (Go's order, marking its uses), then [scope_declare] binds (the ONE insertion path: [bind_category] +
    [decl_ident_ok] + freshness — so overflow / recognized-name / blank / redeclare all reject there). *)
Fixpoint args_okS (catp : PTy -> bool) (G : ScopeS) (args : list GExpr) : option ScopeS :=
  match args with
  | nil => Some G
  | a :: args' =>
      match type_expr G a with
      | Some (c, G1) => if catp c then args_okS catp G1 args' else None
      | None => None
      end
  end.

Definition expr_stmt_okS (G : ScopeS) (e : GExpr) : option ScopeS :=
  match e with
  | ECall (EId f) args =>
      let fn := proj1_sig f in
      match scope_get (sc_list G) fn with
      | Some _ => None   (* a LOCAL callee: no local is a function in this fragment (local-first, mirroring [type_expr]) *)
      | None =>
          if stmt_call_ok fn args then
            match special_ident fn with
            | Some SnPanic => args_okS svalue_cat G args
            | Some SnPrintln | Some SnPrint => args_okS printable_cat G args
            | Some (SnType _) | Some SnNil | Some SnLen | Some SnCap
            | None => args_okS printable_cat G args   (* dead under [stmt_call_ok]'s false — kept for exact equivalence *)
            end
          else None
      end
  | _ => None
  end.

Definition stmt_okS (G : ScopeS) (s : GoStmt) : option ScopeS :=
  match s with
  | GsExprStmt e    => expr_stmt_okS G e
  | GsReturn        => Some G
  | GsReturnVal _   => None
  | GsBlankAssign e =>
      match type_expr G e with
      | Some (c, G1) => if svalue_cat c then Some G1 else None
      | None => None
      end
  | GsDefer e       => expr_stmt_okS G e
  | GsShortDecl x e =>
      match type_expr G e with
      | Some (c, G1) => scope_declare G1 x c
      | None => None
      end
  end.

Fixpoint body_okS (G : ScopeS) (b : list GoStmt) : option ScopeS :=
  match b with
  | nil => Some G
  | s :: rest =>
      match stmt_okS G s with
      | Some G1 => body_okS G1 rest
      | None => None
      end
  end.

(** Go's "declared and not used" (a COMPILE error — certifying an unused local would be fail-open),
    decided on the fold's FINAL scope: an O(locals) check over the state the one traversal built,
    not a second pass over the program. *)
Definition scope_all_used (G : ScopeS) : bool :=
  forallb (fun ent => snd (snd ent)) (sc_list G).

(** PHASE-1 supportedness — DECIDABLE (bool-reflected): the program is a runnable `package main` whose body is
    entirely in the printer/emitter's STRUCTURALLY-supported statement subset, judged by the ONE scope-threaded
    fold [body_okS] from the empty scope: each statement is a [return], a structurally-well-formed call
    expression statement, a blank assign of a value, a [defer] of such a call, or a short declaration
    ([x := e], bound through [scope_declare]) — with every declared local USED ([scope_all_used]).
    It rejects the structural absurdities Go's grammar/
    statement rules forbid: a bare-value statement `func main(){ 1 }` ("evaluated but not used") and a call of a
    non-callable `func main(){ 1() }` are both [false], so no certificate exists and [emit_supported] can never
    print them.  SCOPE OF THE CLAIM (kept honest): this is CONSERVATIVE STRUCTURAL scope + type-category
    supportedness — it REJECTS a free (undefined) identifier, a use before its declaration, a redeclaration,
    an unused local, and a structurally-evident type/constant error, but it is NOT full Go type-checking
    or behavioral safety (the [BehaviorSafe]/GoSem layer, later).  So it is SUPPORTEDNESS, not "guaranteed-
    compiling" and not behavioral safety. *)
Definition supported_program (p : Program) : bool :=
  String.eqb (proj1_sig (prog_pkg p)) "main"
  && match body_okS scope_empty (prog_body p) with
     | Some Gfin => scope_all_used Gfin
     | None => false
     end.
Definition SupportedProgram (p : Program) : Prop := supported_program p = true.

(** ===== The DECL-FREE bridge: the scoped fold at [scope_empty] IS the closed fragment =====
    [type_expr_nil_ptype] one level up: on a body with no short declaration the fold can neither bind
    nor mark, so it agrees EXACTLY with [forallb stmt_ok] — drift between the two statement spellings
    fails the build here.  ([gosem_sound] rides this: slice-1 denotable bodies are decl-free since
    [denote_stmt (GsShortDecl _ _) = None].) *)
Lemma printable_arg_ok_cat : forall e c, ptype e = Some c -> printable_arg_ok e = printable_cat c.
Proof. intros e c H. unfold printable_arg_ok. rewrite H. reflexivity. Qed.
Lemma printable_arg_ok_absent : forall e, ptype e = None -> printable_arg_ok e = false.
Proof. intros e H. unfold printable_arg_ok. rewrite H. reflexivity. Qed.
Lemma svalue_cat_of : forall e c, ptype e = Some c -> svalue e = svalue_cat c.
Proof. intros e c H. unfold svalue. rewrite H. reflexivity. Qed.
Lemma svalue_absent : forall e, ptype e = None -> svalue e = false.
Proof. intros e H. unfold svalue. rewrite H. reflexivity. Qed.

Lemma args_okS_nil : forall (catp : PTy -> bool) (argf : GExpr -> bool),
  (forall a c, ptype a = Some c -> argf a = catp c) ->
  (forall a, ptype a = None -> argf a = false) ->
  forall args,
    args_okS catp scope_empty args = if forallb argf args then Some scope_empty else None.
Proof.
  intros catp argf Hsome Hnone.
  induction args as [|a args' IH]; cbn [args_okS forallb]; [reflexivity|].
  pose proof (type_expr_nil_agrees a) as Ha.
  destruct (type_expr scope_empty a) as [[c G']|]; cbn in Ha.
  - destruct Ha as [Hp HG]; subst G'.
    rewrite (Hsome a c Hp). destruct (catp c); [exact IH | reflexivity].
  - rewrite (Hnone a Ha). reflexivity.
Qed.

Lemma expr_stmt_okS_nil : forall e,
  expr_stmt_okS scope_empty e = if expr_stmt_ok e then Some scope_empty else None.
Proof.
  intro e.
  destruct e as [i|z|u a|o l r|a f|a i|a lo hi|h args|a t|ct a|t es|kt vt kvs|s|zc]; try reflexivity.
  destruct h as [f|z|u a2|o l r|a2 f2|a2 i2|a2 lo hi|h2 args2|a2 t|ct a2|t es|kt vt kvs|s|zc];
    try reflexivity.
  cbn [expr_stmt_okS expr_stmt_ok sc_list scope_empty scope_get].
  destruct (stmt_call_ok (proj1_sig f) args); [|reflexivity].
  destruct (special_ident (proj1_sig f)) as [[t| | | | | |]|];
    first [ rewrite (args_okS_nil _ _ svalue_cat_of svalue_absent args); reflexivity
          | rewrite (args_okS_nil _ _ printable_arg_ok_cat printable_arg_ok_absent args); reflexivity ].
Qed.

Definition is_shortdecl (s : GoStmt) : bool :=
  match s with
  | GsShortDecl _ _ => true
  | GsExprStmt _ | GsReturn | GsReturnVal _ | GsBlankAssign _ | GsDefer _ => false
  end.

Lemma stmt_okS_nil : forall s, is_shortdecl s = false ->
  stmt_okS scope_empty s = if stmt_ok s then Some scope_empty else None.
Proof.
  intros s Hd. destruct s as [e| |e|e|e|x e]; cbn [stmt_okS stmt_ok].
  - apply expr_stmt_okS_nil.
  - reflexivity.
  - reflexivity.
  - pose proof (type_expr_nil_agrees e) as He.
    destruct (type_expr scope_empty e) as [[c G']|]; cbn in He.
    + destruct He as [Hp HG]; subst G'. rewrite (svalue_cat_of e c Hp). reflexivity.
    + rewrite (svalue_absent e He). reflexivity.
  - apply expr_stmt_okS_nil.
  - discriminate Hd.
Qed.

Lemma body_okS_nil_declfree : forall b,
  forallb (fun s => negb (is_shortdecl s)) b = true ->
  body_okS scope_empty b = if forallb stmt_ok b then Some scope_empty else None.
Proof.
  induction b as [|s rest IH]; cbn [body_okS forallb]; intro Hd; [reflexivity|].
  apply andb_true_iff in Hd as [Hs Hr]. apply negb_true_iff in Hs.
  rewrite (stmt_okS_nil s Hs).
  destruct (stmt_ok s); [exact (IH Hr)|reflexivity].
Qed.

(** The decl-free premise is FREE on closed-supported bodies ([stmt_ok] never admits a decl). *)
Lemma stmt_ok_declfree : forall s, stmt_ok s = true -> negb (is_shortdecl s) = true.
Proof.
  intros s H.
  destruct s; [reflexivity|reflexivity|reflexivity|reflexivity|reflexivity|discriminate H].
Qed.

Lemma body_okS_of_stmt_ok : forall b,
  forallb stmt_ok b = true -> body_okS scope_empty b = Some scope_empty.
Proof.
  intros b Hb. rewrite (body_okS_nil_declfree b); [rewrite Hb; reflexivity|].
  revert Hb. induction b as [|s rest IH]; cbn [forallb]; intro Hb; [reflexivity|].
  apply andb_true_iff in Hb as [Hs Hr].
  rewrite (stmt_ok_declfree s Hs). cbn [andb]. exact (IH Hr).
Qed.

(** The consumer-facing corollary ([gosem_sound]'s repair): a main-package body in the CLOSED
    fragment is accepted by [supported_program]. *)
Lemma supported_program_of_stmt_ok : forall p,
  String.eqb (proj1_sig (prog_pkg p)) "main" = true ->
  forallb stmt_ok (prog_body p) = true ->
  supported_program p = true.
Proof.
  intros p Hpkg Hb. unfold supported_program.
  rewrite Hpkg, (body_okS_of_stmt_ok _ Hb). reflexivity.
Qed.

(** ============================================================================================
    REGRESSIONS — grouped boolean fixtures.  INVARIANT: [ptype]/[svalue] is a CONSERVATIVE supported-subset
    CLASSIFIER, not Go's typechecker; add NO new rule unless it rejects a real accepted-bad program or admits a
    needed demo.  Coverage is pinned by [forallb] over THREE ledgers with DISTINCT contracts — [bad_programs]
    (INVALID Go; each [supported_program] is [false] — the SOUNDNESS obligation), [valid_unsupported_programs]
    (VALID Go the gate STILL rejects; each [false] — bounded fail-loud INCOMPLETENESS), and [good_programs]
    (each [true]) — plus a small set of [Fail … := eq_refl] forge-attempts proving the CERTIFICATE itself cannot
    be inhabited for a rejected program.  The helpers below build the fixtures.
    ============================================================================================ *)

(** Program / expression builders shared by the lists (KEEP — they make the fixtures readable).  [pl_arg a] is
    `func main(){ println(<a>) }` (a value in a print arg); [gs_blank a] is `func main(){ _ = <a> }` (a value
    via a blank assign); the [gs_*] wrap a scalar conversion. *)
Definition pl_arg (a : GExpr) : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [a])].
Definition gs_blank (a : GExpr) : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsBlankAssign a].
Definition gs_defer (a : GExpr) : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsDefer a; GsReturn].
Definition gs_f64 (a : GExpr) : GExpr := ECall (EId (mkIdent "float64" eq_refl)) [a].
Definition gs_i64 (a : GExpr) : GExpr := ECall (EId (mkIdent "int64" eq_refl)) [a].
Definition gs_i32 (a : GExpr) : GExpr := ECall (EId (mkIdent "int32" eq_refl)) [a].
Definition gs_str (a : GExpr) : GExpr := ECall (EId (mkIdent "string" eq_refl)) [a].
Definition gs_int (a : GExpr) : GExpr := ECall (EId (mkIdent "int" eq_refl)) [a].
Definition gs_u8  (a : GExpr) : GExpr := ECall (EId (mkIdent "uint8" eq_refl)) [a].
Definition gs_i8  (a : GExpr) : GExpr := ECall (EId (mkIdent "int8" eq_refl)) [a].
(** Locals-fixture shorthands: [gs_main b] is `func main(){ <b> }`; [gs_use i] is the `_ = <i>` use idiom. *)
Definition gs_main (b : list GoStmt) : Program := mkProgram (mkIdent "main" eq_refl) b.
Definition id_x : Ident := mkIdent "x" eq_refl.
Definition id_y : Ident := mkIdent "y" eq_refl.
Definition id_m : Ident := mkIdent "m" eq_refl.
Definition gs_use (i : Ident) : GoStmt := GsBlankAssign (EId i).

(** The bare-value statement `func main(){ 1 }` — NAMED because GoEmit's certificate-forge test references it
    ([Fail Definition … := mkEmittable unsupported_value_stmt eq_refl], proving no [EmittableProgram] exists
    for an unsupported program).  It is also the first [bad_programs] / [forge_value_stmt] fixture below. *)
Definition unsupported_value_stmt : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsExprStmt (EInt 1)].

(** REJECTED — every entry is INVALID Go the gate must refuse ([supported_program = false]): statement-shape
    errors (bare value / call-of-non-callable / assertion- or conversion- or aggregate-as-statement / value
    return in void [main] / [len] in statement context / [panic] arity), value-position errors (void call,
    conversion arity), the [ptype] CLOSED type-errors ([len]/[bool]/[&&]/[!]/int-of-slice; the four REJECTION-CLASS
    numeric category / overflow / zero-divisor / shift / comparison / [cap]-of-string / aggregate-conversion
    cases; the transitive NUMERIC typed-constant rules — INCL. the [int8(len(<non-literal string const>)+200)] overflow
    companions that LOCK the [valid_unsupported_programs] [len] witnesses' soundness boundary; float-rounding +
    platform-[uint] complement), the INVALID [EMapLit]/[CTMap] instances (slice key / an invalid NESTED map-key type, even in an
    EMPTY literal ([goty_supported]) / key-or-value not
    representable in the element type / DUPLICATE constant keys / [cap] of a map / map as a [println] arg /
    free-ident map conversion — these LOCK the now-supported map literal's boundary), and FREE-identifier use
    (no declarations in the model).  ⚠ This
    list is the SOUNDNESS obligation — invalid Go that MUST be refused — NOT the incompleteness ledger.  A
    program Go's typechecker ACCEPTS but [ptype] still rejects (a bounded, fail-loud conservatism) belongs in
    [valid_unsupported_programs] below, NEVER here. *)
Definition bad_programs : list Program :=
  [ (* statement shape *)
    unsupported_value_stmt                                               (* bare value statement *)
  ; mkProgram (mkIdent "lib" eq_refl) [GsReturn]
  ; mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EInt 1) nil)]
  ; mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EAssert (EId (mkIdent "x" eq_refl)) GTInt) nil)]
  ; mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "int" eq_refl)) [EId (mkIdent "x" eq_refl)])]
  ; mkProgram (mkIdent "main" eq_refl) [GsExprStmt (EConv (CTSlice GTInt) (EId (mkIdent "nil" eq_refl)))]
  ; mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ESliceLit GTInt [EInt 1])]
  ; mkProgram (mkIdent "main" eq_refl) [GsExprStmt (EMapLit GTInt GTInt [(EInt 1, EInt 2)])]
  ; mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]])]
  ; mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) nil)]
  ; mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) [EInt 1; EInt 2])]
  ; mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) [EId (mkIdent "x" eq_refl)])]
  ; mkProgram (mkIdent "main" eq_refl) [GsExprStmt (EStr "x")]
  ; mkProgram (mkIdent "main" eq_refl) [GsReturnVal (EInt 1)]
    (* short declarations (locals rung 4) — each row ISOLATES one rule; every placement verified gc *)
  ; gs_main [GsShortDecl id_x (EInt 1)]                                  (* x := 1 alone: "declared and not used" — rejected by [scope_all_used] (the decl itself is admitted by [scope_declare]) *)
  ; gs_main [GsShortDecl id_x (EInt 1); GsReturn]                        (* x := 1; return: "declared and not used" — the SAME fold's final step, no second pass *)
  ; gs_main [GsShortDecl id_x (EInt 9223372036854775808); gs_use id_x]      (* x := 2^63; _ = x: "overflows" on EVERY target — [bind_category]'s untyped-const arm repr-checks the bound *)
  ; gs_main [GsShortDecl id_x (EInt 1); GsShortDecl id_x (EInt 2); gs_use id_x]  (* x := 1; x := 2: "no new variables on left side of :=" — [scope_declare]'s freshness conjunct *)
  ; gs_main [GsShortDecl (mkIdent "_" eq_refl) (EInt 1)]                 (* _ := 1: "no new variables" — [decl_ident_ok] rejects the blank identifier mechanically ([go_ident "_"] is true, so this needs a rule, not hope) *)
  ; gs_main [GsShortDecl id_x (EId (mkIdent "nil" eq_refl)); gs_use id_x]   (* x := nil: "use of untyped nil in assignment" — [bind_category]'s [PtNil] arm *)
  ; gs_main [gs_use id_x; GsShortDecl id_x (EInt 1); gs_use id_x]              (* _ = x; x := 1; _ = x: "undefined: x" at the FIRST use — SEQUENTIAL visibility (the trailing use keeps the decl used, isolating the rule) *)
  ; gs_main [GsShortDecl id_m (EMapLit (GTSlice GTInt) GTInt [(ESliceLit GTInt [EInt 1], EInt 2)]);
             GsBlankAssign (ECall (EId (mkIdent "len" eq_refl)) [EId id_m])]  (* m := map[[]int]int{..}: "invalid map key type" — the invalid-RHS companion of the VALID agg/map locals in [valid_unsupported_programs] *)
    (* [defer <call>] reuses [expr_stmt_ok], so it rejects the SAME non-call / value-builtin / arity / arg shapes *)
  ; gs_defer (EInt 1)                                                    (* defer of a NON-call value *)
  ; gs_defer (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]])  (* defer of [len] — a value builtin, not a statement call *)
  ; gs_defer (ECall (EId (mkIdent "panic" eq_refl)) nil)                 (* defer panic() — bad arity *)
  ; gs_defer (ECall (EId (mkIdent "println" eq_refl)) [ESliceLit GTInt [EInt 1]])  (* defer println(<slice>) — non-printable arg *)
    (* value position / arg errors *)
  ; pl_arg (ECall (EId (mkIdent "println" eq_refl)) [EInt 1])            (* void call used as value *)
  ; pl_arg (ECall (EId (mkIdent "int" eq_refl)) [EInt 1; EInt 2])        (* conversion arity *)
  ; pl_arg (EConv (CTSlice GTInt) (EId (mkIdent "nil" eq_refl)))         (* println of an aggregate *)
  ; pl_arg (ESliceLit GTInt [EInt 1])                                    (* println of a slice literal *)
  ; pl_arg (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]; ESliceLit GTInt [EInt 1]])  (* len arity *)
  ; gs_blank (ECall (EId (mkIdent "println" eq_refl)) [EInt 1])          (* _ = void call *)
    (* ptype closed type-errors *)
  ; pl_arg (ECall (EId (mkIdent "len" eq_refl)) [EInt 1])
  ; pl_arg (ECall (EId (mkIdent "bool" eq_refl)) [EInt 1])
  ; pl_arg (EBn BLAnd (EInt 1) (EInt 2))
  ; pl_arg (EUn UNot (EInt 1))
  ; pl_arg (gs_int (ESliceLit GTInt [EInt 1]))
    (* REJECTION CLASS 1 — numeric category / overflow / zero-divisor / shift *)
  ; pl_arg (EBn BRem (gs_f64 (EInt 1)) (gs_f64 (EInt 2)))
  ; pl_arg (EBn BShl (gs_f64 (EInt 1)) (EInt 2))
  ; pl_arg (EBn BAnd (gs_f64 (EInt 1)) (gs_f64 (EInt 2)))
  ; pl_arg (EUn UXor (gs_f64 (EInt 1)))
  ; pl_arg (gs_u8 (EInt 300))
  ; pl_arg (gs_i8 (EInt 128))
  ; gs_blank (ESliceLit GTU8 [EInt 300])
  ; pl_arg (EBn BAdd (gs_i64 (EInt 3)) (gs_i32 (EInt 2)))
  ; gs_blank (ESliceLit GTInt [gs_i64 (EInt 1)])
  ; pl_arg (EBn BDiv (EInt 1) (EInt 0))
  ; pl_arg (EBn BDiv (EInt 1) (EBn BSub (EInt 1) (EInt 1)))
  ; pl_arg (EBn BRem (EInt 1) (EInt 0))
  ; pl_arg (EBn BShl (EInt 1) (EInt (-1)))
    (* REJECTION CLASS 2 — comparison split (== needs comparable, < needs ordered) *)
  ; pl_arg (EBn BEq (ESliceLit GTInt [EInt 1]) (ESliceLit GTInt [EInt 1]))
  ; pl_arg (EBn BLt (ESliceLit GTInt [EInt 1]) (ESliceLit GTInt [EInt 1]))
  ; pl_arg (EBn BLt (EBn BEq (EInt 1) (EInt 1)) (EBn BEq (EInt 2) (EInt 2)))
  ; pl_arg (EBn BEq (EInt 1) (EBn BEq (EInt 2) (EInt 2)))
    (* REJECTION CLASS 3 — cap of a string *)
  ; gs_blank (ECall (EId (mkIdent "cap" eq_refl)) [gs_str (EInt 65)])
  ; gs_blank (ECall (EId (mkIdent "cap" eq_refl)) [EStr "hi"])
    (* REJECTION CLASS 4 — aggregate conversion soundness *)
  ; gs_blank (EConv (CTChan GTInt) (ESliceLit GTInt [EInt 1]))
  ; gs_blank (EConv (CTSlice GTInt) (ESliceLit GTString []))
    (* transitive NUMERIC typed-constant rules (a numeric const's value survives conversions/binops) *)
  ; pl_arg (EBn BDiv (EInt 1) (gs_int (EInt 0)))
  ; pl_arg (EBn BRem (EInt 1) (gs_int (EInt 0)))
  ; pl_arg (EBn BShl (EInt 1) (gs_int (EInt (-1))))
  ; pl_arg (gs_u8 (gs_int (EInt 300)))
  ; pl_arg (gs_u8 (gs_f64 (EInt 300)))
  ; pl_arg (EBn BAdd (gs_i8 (EInt 100)) (gs_i8 (EInt 100)))
  ; pl_arg (gs_u8 (gs_int (gs_int (EInt 300))))
  ; pl_arg (EBn BDiv (EInt 1) (EBn BSub (gs_int (EInt 1)) (gs_int (EInt 1))))
  ; pl_arg (gs_i8 (EBn BAdd (ECall (EId (mkIdent "len" eq_refl)) [EStr "hi"]) (EInt 200)))  (* int8(len("hi")+200): [len] of a string LITERAL folds to 2, 2+200=202 overflows int8 -> REJECTED.  Locks the len-string-LITERAL soundness fix (a runtime-int model would WRONGLY admit this) *)
  ; pl_arg (gs_i8 (EBn BAdd (ECall (EId (mkIdent "len" eq_refl)) [gs_str (EInt 65)]) (EInt 200)))  (* int8(len(string(65))+200): the NON-LITERAL companion to the [valid_unsupported_programs] witness `len(string(65))`.  string(65)="A", len folds to 1 EXACTLY, 1+200=201 overflows int8 — INVALID Go, REJECTED.  EXACT byte-length folding (the legitimate way to admit the witness) keeps THIS rejected; a sloppy [PtStr -> PtRunInt] runtime-int shortcut would make int8(runtime+200) SUPPORTED and FLIP [bad_programs_rejected] *)
  ; pl_arg (gs_i8 (EBn BAdd (ECall (EId (mkIdent "len" eq_refl)) [EBn BAdd (EStr "a") (EStr "b")]) (EInt 200)))  (* int8(len("a"+"b")+200): the companion to the other witness `len("a"+"b")`.  "a"+"b"="ab", len folds to 2 EXACTLY, 2+200=202 overflows int8 — same soundness lock on the concat witness *)
  ; pl_arg (EBn BAdd (EStr "a") (EInt 1))                                (* "a" + 1: string + number is INVALID Go — REJECTED ([num_binop] gives None on the non-numeric [PtStr] operand) *)
  ; gs_blank (ESliceLit GTU8 [gs_int (EInt 300)])
  ; pl_arg (EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (EStr "x"))      (* []int{10,20}["x"]: a STRING index is INVALID Go — a slice index must be an integer; [ptype idx] = [PtStr] so [is_int_cat] fails -> UNSUPPORTED *)
  ; pl_arg (EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (EUn UNeg (EInt 1)))  (* []int{10,20}[-1]: a NEGATIVE constant index is INVALID Go (verified gc: "index -1 must not be negative") — REJECTED by the [0 <=? k] guard.  (An OOB *positive* constant is NOT here — it is valid Go, in good_programs.) *)
  ; pl_arg (EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (EInt 9223372036854775808))  (* []int{10,20}[2^63]: 2^63 overflows int on ANY platform — INVALID Go (verified gc: "overflows int"), REJECTED by the [int_const_repr k GTInt] guard (pins the overflow arm, distinct from the negative one).  NB: that guard is CONSERVATIVE 32-bit, so it also over-rejects some indices a 64-bit gc accepts — this fixture is only the genuinely-invalid end *)
    (* float-constant rounding + platform-uint complement (the rep must not lie) *)
  ; pl_arg (gs_i64 (gs_f64 (EInt 9223372036854775807)))                  (* int64(float64(maxint64)) rounds up *)
  ; pl_arg (gs_i32 (ECall (EId (mkIdent "float32" eq_refl)) [EInt 2147483647]))
  ; gs_blank (EBn BDiv (EId (mkIdent "x" eq_refl)) (gs_f64 (EInt 0)))     (* x / float64(0) — const-zero divisor (ALSO a free-ident rejection; the CLOSED witnesses below isolate the zero-divisor rule itself) *)
  ; gs_blank (EBn BDiv (gs_f64 (EInt 1)) (gs_f64 (EInt 0)))                (* float64(1)/float64(0): CLOSED const-zero float divisor — Go compile error; FLIPS if [is_zero_const] stops seeing [PtFloatConst] *)
  ; gs_blank (EBn BDiv (ECall (EId (mkIdent "float32" eq_refl)) [EInt 1]) (ECall (EId (mkIdent "float32" eq_refl)) [EInt 0]))  (* float32(1)/float32(0): the float32 width of the same rule *)
  ; gs_blank (EBn BDiv (gs_f64 (EInt 1)) (EBn BSub (gs_f64 (EInt 1)) (gs_f64 (EInt 1))))  (* float64(1)/(float64(1)-float64(1)): the divisor's ZERO arises by FOLDING — locks that the zero test runs on the folded dyadic *)
  ; pl_arg (ECall (EId (mkIdent "uint32" eq_refl)) [EUn UXor (ECall (EId (mkIdent "uint" eq_refl)) [EInt 0])])
    (* INVALID [EMapLit]/[CTMap] instances — now rejected by the STRUCTURAL [EMapLit] check (was a blanket
       quarantine; the supported witness `_ = map[int]int{1:2}` GRADUATED to [good_programs]).  Each LOCKS the
       supported map literal's boundary — a checker that skipped one of comparability / representability /
       distinctness / map-is-not-cap-able would wrongly admit it and FLIP [bad_programs_rejected]: a
       non-comparable slice KEY (caught by the integer-key restriction); a non-representable VALUE then KEY (300
       in [uint8] — caught by [assignable_to_ty]); DUPLICATE constant keys (caught by [nodup_z] — Go forbids
       them); an INVALID NESTED map-key type hidden in a VALUE/element/conversion type (caught by [goty_supported]
       — even an EMPTY literal, where no entry check could see it); [cap] of a map (Go forbids it — caught by
       [PtMap]≠[PtAgg], so the [cap] arm gives [None]); a map as
       a [println] arg (a map is not a printable arg); and a map CONVERSION of a FREE IDENT (an
       invalid-operand rejection — the map-conversion QUARANTINE itself is pinned on a VALID nil operand in
       [valid_unsupported_programs]) *)
  ; gs_blank (EMapLit (GTSlice GTInt) GTInt [(ESliceLit GTInt [EInt 1], EInt 2)])  (* map[[]int]int{..}: slice key not comparable *)
  ; gs_blank (EMapLit GTInt (GTMap (GTSlice GTInt) GTInt) [])              (* map[int]map[[]int]int{}: a non-comparable slice KEY hidden in the VALUE type — invalid Go even EMPTY ([goty_supported]) *)
  ; pl_arg (ECall (EId (mkIdent "len" eq_refl)) [EMapLit GTInt (GTMap (GTSlice GTInt) GTInt) []])  (* println(len(map[int]map[[]int]int{})): the len of an invalid-typed literal is rejected at the ROOT *)
  ; gs_blank (EBn BDiv (EInt 1) (ECall (EId (mkIdent "len" eq_refl)) [EMapLit GTInt (GTMap (GTSlice GTInt) GTInt) []]))  (* 1/len(map[int]map[[]int]int{}): no divide-by-zero behavior for invalid source *)
  ; gs_blank (ESliceLit (GTMap (GTSlice GTInt) GTInt) [])                  (* []map[[]int]int{}: the same invalid nested key type through a SLICE literal *)
  ; gs_blank (EConv (CTSlice (GTMap (GTSlice GTInt) GTInt)) (EId (mkIdent "nil" eq_refl)))  (* []map[[]int]int(nil): ... and through the aggregate-conversion arm *)
  ; gs_blank (EMapLit GTInt GTU8 [(EInt 1, EInt 300)])                    (* map[int]uint8{1:300}: value 300 overflows uint8 *)
  ; gs_blank (EMapLit GTU8 GTInt [(EInt 300, EInt 1)])                    (* map[uint8]int{300:1}: key 300 overflows uint8 *)
  ; gs_blank (EMapLit GTInt GTInt [(EInt 1, EInt 2); (EInt 1, EInt 3)])   (* map[int]int{1:2, 1:3}: DUPLICATE constant key 1 — a Go compile error *)
  ; gs_blank (ECall (EId (mkIdent "cap" eq_refl)) [EMapLit GTInt GTInt [(EInt 1, EInt 2)]])  (* cap(map[int]int{1:2}): [cap] of a MAP is invalid Go — REJECTED ([PtMap] is not [cap]-able, unlike a slice) *)
  ; gs_blank (EConv (CTMap GTInt GTInt) (EId (mkIdent "x" eq_refl)))      (* map[int]int(x): a FREE-IDENT operand — undefined; the CTMap quarantine's valid-operand witness lives in [valid_unsupported_programs] *)
  ; gs_blank (EConv (CTMap (GTSlice GTInt) GTInt) (EId (mkIdent "nil" eq_refl)))  (* _ = map[[]int]int(nil): a NON-COMPARABLE key in the conversion TARGET type — INVALID Go; this pin FLIPS if CTMap is ever admitted without a target key-comparability check *)
  ; gs_blank (EConv (CTMap GTInt (GTMap (GTSlice GTInt) GTInt)) (EId (mkIdent "nil" eq_refl)))  (* _ = map[int]map[[]int]int(nil): the invalid key hidden in the target's NESTED value type — an outer-key-only CTMap admission would wrongly accept this *)
  ; gs_blank (EConv (CTMap GTInt (GTSlice (GTMap (GTSlice GTInt) GTInt))) (EId (mkIdent "nil" eq_refl)))  (* _ = map[int][]map[[]int]int(nil): the invalid key under a SLICE wrapper inside the target — a direct-map-value-only check would wrongly accept this.  These rows are WITNESSES; the CLASS gate is the ∀-theorem [ctmap_conv_unsupported_target_rejected] below *)
  ; pl_arg (EMapLit GTInt GTInt [(EInt 1, EInt 2)])                       (* println(map[int]int{1:2}): a supported map VALUE, but not a printable [println] arg *)
    (* free-identifier use — undefined in the no-declaration model *)
  ; gs_blank (EId (mkIdent "x" eq_refl))
  ; pl_arg (ECall (EId (mkIdent "len" eq_refl)) [EId (mkIdent "x" eq_refl)])
  ; gs_blank (ECall (EId (mkIdent "cap" eq_refl)) [EId (mkIdent "x" eq_refl)])
  ; gs_blank (EConv (CTSlice GTInt) (EId (mkIdent "x" eq_refl)))
  ; pl_arg (gs_int (EId (mkIdent "x" eq_refl)))
  ].
Example bad_programs_rejected :
  forallb (fun p => negb (supported_program p)) bad_programs = true.
Proof. vm_compute. reflexivity. Qed.

(** REJECTED-BUT-VALID — a SEPARATE contract from [bad_programs].  Go's typechecker ACCEPTS every program here,
    yet [ptype] still rejects it ([supported_program = false]): each falls outside the SOUND supported subset,
    so the gate refuses it rather than risk a plausible-but-wrong emission (rule 2 — fail loud, never
    plausible-but-wrong).  This is BOUNDED, principled INCOMPLETENESS, not a soundness obligation.  ⚠ Admitting
    a member is legitimate growth ONLY via an EXACT, soundly-STRUCTURAL rule that STILL rejects its INVALID
    companion in [bad_programs] — NEVER a sloppy widening.  ★WORKED EXAMPLE (done): the map literal
    `map[int]int{1:2}` GRADUATED from here to [good_programs] once [ptype] gained a structural
    integer-key/representability/distinctness check — and its companions `map[int]uint8{1:300}` /
    `map[uint8]int{300:1}` / `map[int]int{1:2,1:3}` STAYED in [bad_programs], exactly as this contract demands.
    Each current class's own FUTURE path (per the contract above, each names the companion that must stay
    rejected): the len-string members graduate by folding [len] of a NON-LITERAL string const to its exact
    byte length (keeping `int8(len(string(65))+200)` / `int8(len("a"+"b")+200)` rejected — a
    [PtStr -> PtRunInt] runtime-int shortcut would reopen those); the [map[int]int(nil)] CONVERSION
    graduates only when the CTMap arm consults the FULL recursive target-type gate — enforced by the GATED
    ∀-theorem [ctmap_conv_unsupported_target_rejected] below (every [goty_supported]-rejected target stays
    unsupported), which a graduating arm must RE-ESTABLISH; the [bad_programs] CTMap rows (root / nested /
    slice-wrapped) are its witnesses; the ptr/chan-key block graduates when
    [goty_key_supported] grows past scalars on a modelled ptr/chan key-equality semantics (keeping the
    slice/map-key members of [bad_programs] rejected); the float ROUNDING members ([float64(1)/float64(3)],
    the cross-width [float32(<inexact-at-32>)]) graduate only with a correctly-ROUNDING const model — the
    exact-or-reject dyadic fold refuses them today (keeping the const-ZERO-divisor [bad_programs] member
    rejected); ★the SHORT-DECLARATION member GRADUATED at locals rung 4 exactly per this contract —
    `x := 1; _ = x; return` moved to [good_programs] (admitted by [supported_program]'s scope fold) while its
    unused / redeclared / blank / untyped-nil / overflowing / use-before-declare companions all sit in
    [bad_programs]; the decl members still HERE (the 2^40 decl, the shadowed special names, the
    aggregate/map locals) each name their narrowing at their row.  The two contracts must not be confused — a
    [bad_programs] regression means an UNSOUND
    emission reopened; admitting one of THESE (with its companion preserved) is the subset legitimately GROWING.
    (NO separate member inventory here: [valid_unsupported_programs] below IS the member authority,
    each member's detail at its row — a prose copy of an executable list drifts.) *)
(** The valid-but-out-of-core ptr/chan MAP-KEY class, pinned STRUCTURALLY: generated as the full CARTESIAN
    product (out-of-core key type × rejecting surface), so a new key type or surface added here extends
    every pin at once — "quarantined" stays an executable per-surface claim, never a hand-picked sample.
    Surfaces: root literal (the int-only key restriction), nested map VALUE type, slice ELEMENT type
    ([goty_supported]), and the three nil-conversion arms (CTSlice / CTChan / the blanket CTMap
    quarantine).  Every generated program is VALID Go — [nil] converts to any slice/chan/map type
    (https://go.dev/ref/spec#Conversions). *)
Definition oo_core_key_tys : list GoTy := [GTPtr GTInt; GTChan GTInt].
Definition ptrchan_key_quarantine : list Program :=
  flat_map (fun k =>
    [ gs_blank (EMapLit k GTInt [])                                              (* _ = map[K]int{} — root literal *)
    ; gs_blank (EMapLit GTInt (GTMap k GTInt) [])                                (* _ = map[int]map[K]int{} — nested value type *)
    ; gs_blank (ESliceLit (GTMap k GTInt) [])                                    (* _ = []map[K]int{} — slice element type *)
    ; gs_blank (EConv (CTSlice (GTMap k GTInt)) (EId (mkIdent "nil" eq_refl)))   (* _ = []map[K]int(nil) *)
    ; gs_blank (EConv (CTChan  (GTMap k GTInt)) (EId (mkIdent "nil" eq_refl)))   (* _ = (chan map[K]int)(nil) *)
    ; gs_blank (EConv (CTMap k GTInt) (EId (mkIdent "nil" eq_refl)))             (* _ = map[K]int(nil) — the CTMap arm *)
    ]) oo_core_key_tys.
Definition valid_unsupported_programs : list Program :=
  [ pl_arg (ECall (EId (mkIdent "len" eq_refl)) [gs_str (EInt 65)])       (* println(len(string(65))): string(65)="A" (a rune-const conversion — compiles; go vet warns), len folds to 1.  A NON-LITERAL [PtStr] (not [EStr]), so [len] hits the [_, _ => None] fallback — REJECTED (fail-loud).  Pinned just below: [string_rune_const_is_supported_PtStr] + [len_of_nonliteral_PtStr_rejected] *)
  ; pl_arg (ECall (EId (mkIdent "len" eq_refl)) [EBn BAdd (EStr "a") (EStr "b")])  (* println(len("a"+"b")): "a"+"b"="ab", len folds to 2.  The concat is a NON-literal [PtStr], so [len] hits the same non-literal fallback — REJECTED *)
  ; gs_blank (EConv (CTMap GTInt GTInt) (EId (mkIdent "nil" eq_refl)))    (* _ = map[int]int(nil): VALID Go (nil converts to a map type) — the blanket CTMap quarantine pinned on a VALID operand (the [bad_programs] free-ident row is an invalid-operand rejection, NOT this witness) *)
  ; gs_blank (EBn BDiv (gs_f64 (EInt 1)) (gs_f64 (EInt 3)))               (* _ = float64(1)/float64(3): VALID Go (rounds to ~0.333); the exact-or-reject dyadic fold REFUSES a non-representable quotient ([dy_div] inexact) — quarantined, never a rounded lie *)
  ; pl_arg (ECall (EId (mkIdent "float32" eq_refl)) [gs_f64 (EInt 16777217)])  (* println(float32(float64(16777217))): VALID Go (rounds to 16777216 — 2^24+1 is inexact at binary32); the cross-width const conversion is EXACT-only ([float_dyadic_repr]) — quarantined *)
    (* the CONSERVATIVE default-[int] boundary: 2^40 fits 64-bit gc's [int] (verified — compiles and prints)
       but not the 32-bit [int] the checker assumes to stay sound on EVERY target ([int_const_repr .. GTInt]) *)
  ; pl_arg (EInt 1099511627776)                                          (* println(2^40) *)
  ; gs_blank (EInt 1099511627776)                                        (* _ = 2^40 *)
  ; gs_main [GsShortDecl id_x (EInt 1099511627776); gs_use id_x]            (* x := 2^40; _ = x — the same boundary through [bind_category]'s untyped-const arm *)
    (* checker-recognized names as locals: LEGAL Go (predeclared identifiers are shadowable; each verified gc)
       — [decl_ident_ok] rejects EVERY recognized name uniformly, a NAMED NARROWING (plans/gosem-locals.md rule 5) *)
  ; gs_main [GsShortDecl (mkIdent "len" eq_refl) (EInt 1); GsBlankAssign (EId (mkIdent "len" eq_refl))]   (* len := 1; _ = len *)
  ; gs_main [GsShortDecl (mkIdent "int" eq_refl) (EInt 1); GsBlankAssign (EId (mkIdent "int" eq_refl))]   (* int := 1; _ = int *)
  ; gs_main [GsShortDecl (mkIdent "nil" eq_refl) (EInt 1); GsBlankAssign (EId (mkIdent "nil" eq_refl))]   (* nil := 1; _ = nil *)
    (* aggregate/map LOCALS: VALID Go (verified gc) — [bind_category]'s [PtAgg]/[PtMap] arms are a NAMED
       NARROWING (the evaluator has no aggregate/map VALUES, so admitting the binding would create locals
       that can never value); the [len] uses isolate that rejection from unused/undeclared noise *)
  ; gs_main [GsShortDecl id_x (ESliceLit GTInt [EInt 1]);
             GsBlankAssign (ECall (EId (mkIdent "len" eq_refl)) [EId id_x])]   (* x := []int{1}; _ = len(x) *)
  ; gs_main [GsShortDecl id_m (EMapLit GTInt GTInt [(EInt 1, EInt 2)]);
             GsBlankAssign (ECall (EId (mkIdent "len" eq_refl)) [EId id_m])]   (* m := map[int]int{1:2}; _ = len(m) *)
  ] ++ ptrchan_key_quarantine.
Example valid_unsupported_rejected :
  forallb (fun p => negb (supported_program p)) valid_unsupported_programs = true.
Proof. vm_compute. reflexivity. Qed.

(** [stmt_ok] — the CLOSED (scope-free) fragment — never admits a short declaration, pinned at the
    CONSTRUCTOR for every ident/expression.  This is what makes the decl-free bridge's premise free
    on closed-supported bodies ([stmt_ok_declfree]) and — via [gosem_sound] — why slice-1 denotable
    bodies are decl-free.  [supported_program] DOES admit declarations — its [body_okS] fold binds
    exclusively through [scope_declare], with [scope_all_used] still required at the end (the
    [good_programs] locals rows).  (The denotation-side absence pin,
    [denote_stmt (GsShortDecl _ _) = None], lives with [denote_stmt] in GoSemDenote.v.) *)
Example shortdecl_stmt_ok_false : forall x e, stmt_ok (GsShortDecl x e) = false.
Proof. reflexivity. Qed.

(** [body_okS] is the INTERNAL body checker, NOT the program gate: on an unused-local body the fold
    SUCCEEDS (binding and threading are fine) while [supported_program] REJECTS via the final
    [scope_all_used] — the all-used side condition lives in the GATE, so naming [body_okS] as the
    gate would leak it.  ([supported_program] also adds the package-main check.) *)
Example body_okS_not_the_gate :
  match body_okS scope_empty [GsShortDecl id_x (EInt 1); GsReturn] with
  | Some G => scope_all_used G = false
  | None => False
  end
  /\ supported_program (gs_main [GsShortDecl id_x (EInt 1); GsReturn]) = false.
Proof. split; vm_compute; reflexivity. Qed.

(** ★ THE CTMAP TARGET CLASS GATE — universal, NOT sample rows: for EVERY target type [map[k]v] the
    supported-type authority rejects ([goty_supported (GTMap k v) = false]), the nil map CONVERSION to it
    is NOT a supported program.  Today this holds because the CTMap arm fail-closes outright; if CTMap ever
    GRADUATES, re-establishing THIS gated theorem forces the new arm to consult the same recursive target
    authority — no outer-key-only or direct-map-value-only shortcut can satisfy it.  The [bad_programs]
    CTMap rows are concrete witnesses of this class, not the gate. *)
Theorem ctmap_conv_unsupported_target_rejected : forall k v,
  goty_supported (GTMap k v) = false ->
  supported_program (gs_blank (EConv (CTMap k v) (EId (mkIdent "nil" eq_refl)))) = false.
Proof. intros k v _. reflexivity. Qed.

(** The [len(string(65))] entry above ([valid_unsupported_programs]) rejects via the NON-LITERAL-[PtStr] [len]
    fallback SPECIFICALLY, not via an unsupported argument — pinned by the pair below: [string(65)] IS a
    SUPPORTED [PtStr] (a rune-const conversion), yet [len] of it is [None].  Since the arg type-checks
    ([Some PtStr]), the [len] [None] can only be the [_, _ => None] fallback — [PtStr] is neither a string
    LITERAL ([EStr], which folds) nor an aggregate ([PtAgg]/[PtMap], the other [len]-accepted cases).  This is
    what makes the [valid_unsupported_programs] entry a genuine lock on that fallback (a regression that restored
    [PtStr -> PtRunInt] would flip [len_of_nonliteral_PtStr_rejected] to [Some _]). *)
Example string_rune_const_is_supported_PtStr :
  ptype (ECall (EId (mkIdent "string" eq_refl)) [EInt 65]) = Some PtStr.
Proof. reflexivity. Qed.
Example len_of_nonliteral_PtStr_rejected :
  ptype (ECall (EId (mkIdent "len" eq_refl)) [ECall (EId (mkIdent "string" eq_refl)) [EInt 65]]) = None.
Proof. reflexivity. Qed.

(** ACCEPTED — the smaller-but-SOUND subset the gate still admits ([supported_program = true]): a conversion of
    a constant in value position, value-position aggregates (slice/chan [PtAgg] AND map [PtMap], all valid
    values) with [len] on ANY of them but [cap] on slice/chan [PtAgg] ONLY (a map is len-able, not cap-able),
    in-range / folded constants and same-width typed arithmetic, [panic]/bare-return/blank-assign/string
    literals, the EXACT float→int constant tracking ([uint8(float64(255))] is in range) + fixed-width complement,
    and an INTEGER-key map LITERAL whose value TYPE is [goty_supported], constant keys distinct + assignable
    to the key type, values assignable to the value type ([map[int]int{1:2}]). *)
Definition good_programs : list Program :=
  [ pl_arg (gs_i64 (EInt 3))                                             (* println(int64(3)) *)
  ; gs_blank (EConv (CTSlice GTInt) (EId (mkIdent "nil" eq_refl)))       (* _ = []int(nil) *)
  ; gs_blank (ESliceLit GTInt [EInt 1])                                  (* _ = []int{1} *)
  ; mkProgram (mkIdent "main" eq_refl) [GsExprStmt (ECall (EId (mkIdent "panic" eq_refl)) [EInt 1])]
  ; mkProgram (mkIdent "main" eq_refl) [GsReturn]
  ; gs_blank (EInt 1)                                                    (* _ = 1 *)
  ; pl_arg (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]])
  ; gs_blank (ECall (EId (mkIdent "cap" eq_refl)) [ESliceLit GTInt [EInt 1]])
  ; pl_arg (EStr "hi")                                                   (* println("hi") *)
  ; gs_blank (EStr "x")                                                  (* _ = "x" *)
  ; pl_arg (ECall (EId (mkIdent "len" eq_refl)) [EStr "hi"])             (* len of a string LITERAL folds to a CONST (2) — printable *)
  ; pl_arg (EBn BAdd (EStr "a") (EStr "b"))                             (* "a" + "b" string CONCATENATION -> a string *)
  ; pl_arg (gs_i8 (EInt 127))                                            (* int8(127) in range *)
  ; pl_arg (EBn BRem (EInt 5) (EInt 2))
  ; pl_arg (EBn BShl (EInt 1) (EInt 4))
  ; gs_blank (ESliceLit GTFloat64 [EInt 1])                             (* untyped const into a float element *)
  ; pl_arg (EBn BAdd (gs_i64 (EInt 3)) (gs_i64 (EInt 2)))               (* same-width add *)
  ; pl_arg (gs_u8 (gs_f64 (EInt 255)))                                  (* uint8(float64(255)) — exact, in range *)
  ; pl_arg (EBn BAdd (gs_i8 (EInt 100)) (gs_i8 (EInt 20)))              (* folded typed-const, in range *)
  ; pl_arg (EInt 2147483647)                                            (* 32-bit default-int boundary *)
  ; pl_arg (gs_u8 (EUn UXor (ECall (EId (mkIdent "uint8" eq_refl)) [EInt 0])))  (* uint8(^uint8(0)) fixed width *)
  ; gs_blank (EMapLit GTInt GTInt [(EInt 1, EInt 2)])                   (* _ = map[int]int{1: 2} — integer-key map literal, const key distinct + assignable *)
  ; gs_blank (EMapLit GTInt GTInt [(EInt 1, EInt 2); (EInt 2, EInt 3)]) (* multi-element map, DISTINCT constant keys *)
  ; gs_blank (EMapLit GTInt GTString [])                               (* _ = map[int]string{} — empty (int key; value type gated only by [goty_supported]) *)
  ; gs_blank (EMapLit GTU8 GTU8 [(EInt 1, EInt 2)])                     (* map[uint8]uint8{1: 2} — typed key/value, consts in range *)
  ; pl_arg (ECall (EId (mkIdent "len" eq_refl)) [EMapLit GTInt GTInt [(EInt 1, EInt 2)]])  (* println(len(map[int]int{1:2})): [len] of a map IS valid (a runtime int) — unlike [cap] *)
  ; pl_arg (EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (EInt 1))       (* println([]int{10,20}[1]): CONSTANT in-bounds index into a slice literal — VALID Go, a RUNTIME int (supported, like [len]) *)
  ; pl_arg (EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (EInt 5))       (* []int{10,20}[5]: an OOB POSITIVE constant index is VALID Go — for a SLICE (unlike an array) gc does NOT compile-check bounds; it's a run-time PANIC.  So SUPPORTED (verified: gc builds it); its OOB-safety is BEHAVIORAL (since tier R2 GoSem DENOTES its true [rt_index_oob] panic; the behavioral gate rejects it), NOT supportedness *)
  ; pl_arg (EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]))  (* []int{10,20}[len([]int{1})]: a RUNTIME (non-constant) integer index — VALID Go, bounds are a run-time property; supported.  Locks that the rule is NOT [EInt]-only *)
  ; mkProgram (mkIdent "main" eq_refl)                                   (* defer println("bye"); return — a deferred CALL is supported (same gate as an expr statement) *)
      [GsDefer (ECall (EId (mkIdent "println" eq_refl)) [EStr "bye"]); GsReturn]
    (* short declarations (locals rung 4 — declared AND used, through the [body_okS] scope fold) *)
  ; gs_main [GsShortDecl id_x (EInt 1); gs_use id_x; GsReturn]              (* x := 1; _ = x; return — GRADUATED from [valid_unsupported_programs] *)
  ; gs_main [GsShortDecl id_x (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]); gs_use id_x]  (* x := len([]int{1}); _ = x — a RUNTIME binding *)
  ; gs_main [GsShortDecl id_x (EInt 1); GsShortDecl id_y (EId id_x); gs_use id_y]  (* x := 1; y := x; _ = y — a runtime category binds AS ITSELF; the RHS use marks x *)
  ; gs_main [GsShortDecl id_x (gs_i64 (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]])); gs_use id_x]  (* x := int64(len([]int{1})); _ = x — a TYPED-runtime binding *)
  ; gs_main [GsShortDecl id_x (EInt 1); GsBlankAssign (EBn BAdd (EId id_x) (EInt 1))]  (* x := 1; _ = x + 1 — the use is marked INSIDE a subexpression *)
  ; gs_main [GsShortDecl id_x (EInt 1); GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EId id_x])]  (* x := 1; println(x) — the use is marked through a CALL ARGUMENT *)
  ].
Example good_programs_supported : forallb supported_program good_programs = true.
Proof. vm_compute. reflexivity. Qed.

(** EXPRESSION-LEVEL direct pins — predicates not surfaced through the program lists: the [EStr] literal is a
    printable scalar / value, and the unsound platform-[uint] complement is sealed INSIDE [complement_const]
    (returns [None]) while fixed-width unsigned ([uint8]) / signed ([int]) still fold exactly. *)
Example str_printable : printable_arg_ok (EStr "hi") = true.  Proof. reflexivity. Qed.
Example str_svalue    : svalue (EStr "x") = true.            Proof. reflexivity. Qed.
Example complement_const_uint_none  : complement_const GTUint 0 = None.        Proof. reflexivity. Qed.
Example complement_const_u8_exact   : complement_const GTU8 0 = Some 255%Z.    Proof. reflexivity. Qed.
Example complement_const_int_signed : complement_const GTInt 0 = Some (-1)%Z.  Proof. reflexivity. Qed.

(** FORGE-RESISTANCE — [eq_refl] cannot inhabit [SupportedProgram <bad>] (= [false = true]); a representative
    sample (bare value statement · non-main package · free identifier · constant overflow) locks that NO
    certificate exists for a rejected program.  (The boolean lists above pin every rejection; these prove the
    certificate is unforgeable.  Note: [Fail Lemma … . Proof. … Qed.] would NOT work — [Fail] guards only the
    goal-opening vernac, which always succeeds; the [:= eq_refl] term form is what must fail to typecheck.) *)
Fail Example forge_value_stmt :
  SupportedProgram unsupported_value_stmt := eq_refl.
Fail Example forge_nonmain_pkg :
  SupportedProgram (mkProgram (mkIdent "lib" eq_refl) [GsReturn]) := eq_refl.
Fail Example forge_free_blank :
  SupportedProgram (gs_blank (EId (mkIdent "x" eq_refl))) := eq_refl.
Fail Example forge_uint8_overflow :
  SupportedProgram (pl_arg (gs_u8 (EInt 300))) := eq_refl.
Fail Example forge_unused_local :
  SupportedProgram (gs_main [GsShortDecl id_x (EInt 1); GsReturn]) := eq_refl.

(** ===================================================================================================
    ===== SEMANTIC: BehaviorSafe over GoSem (future) =====
    =================================================================================================== *)

(** Reserved for GoSem COMPLETION: the behavioral-safety GATE over the AST's denotation.  The GATE is NOT yet
    defined — GoSem's slice-1 denotation ([denote_program]) is too PARTIAL to define it against — and a
    placeholder [Definition BehaviorSafe _ := True] would be exactly the decorative/overclaiming gate the
    charter forbids (§8 Rule 4).  (FIRST proof-only PROPERTIES do exist in [GoSemSafe.v] — a NARROW DECIDABLE
    emission gate [GoSemSafe.panic_free_gate] / [emit_panic_free_gated] (end-to-end sound): accepted iff the
    program denotes to [c] with [cmd_no_panic c] — denotable panics rejected there, an ABSENT (undenoted)
    program by non-denotation — but that
    is NOT this full [BehaviorSafe] gate and does NOT gate the main output.)  When GoSem is
    complete enough: [BehaviorSafe (p : Program) : Prop := <no nil-deref / race / … over its GoSem denotation>],
    and GoEmit gains [SafeProgram]/[emit_safe]. *)

(** GATE — GoSafe is on the blessed emission path; keep it axiom-free (checked by the GOEMIT_GATE, mirroring
    the GoAst/GoPrint printer gate). *)
Print Assumptions SupportedProgram.
Print Assumptions bad_programs_rejected.
Print Assumptions ctmap_conv_unsupported_target_rejected.
Print Assumptions body_okS_nil_declfree.
