(** ============================================================================
    GoSafe.v — supportedness now, behavioral safety later (AST-first spine; ARCHITECTURE.md §2/§2a).
    [SupportedProgram] is a PHASE-1 SYNTACTIC gate, NOT behavioral safety (naming is a correctness
    claim — never call a syntactic gate "Safe").  [BehaviorSafe] lands once GoSem denotes enough;
    until then GoEmit emits only the SUPPORTED subset and must not be described as safe.
    GoSafe is a CONSERVATIVE supported-subset checker, not Go's typechecker.  [ScopeS] seals
    valid distinct names and bound categories; used flags are threaded STATE whose provenance is
    owned by the fold from [scope_empty] ([supported_program], which rejects unused locals).
    ============================================================================ *)
From Fido Require Import GoAst.   (* syntax + [classify]; deliberately NOT GoPrint — safety must not depend on the printer *)
From Fido Require Import GoTypes. (* the shared type-category checker ([ptype]/[svalue]) — one authority for GoSafe AND GoSem *)
From Stdlib Require Import String List Bool ZArith Eqdep_dec.
Import ListNotations.
Open Scope string_scope.

(** ===== The SEALED SCOPE + the scope-threading checker [type_expr] + the [ptype] bridge =====
    A local's category is a [BoundCat] ([bind_category]'s image, by sig); a scope is a [ScopeS]
    (sig over [scope_wf]: names valid, unrecognized, non-blank, pairwise distinct — the forged
    shapes are UNREPRESENTABLE, [Fail]-pinned below).  [scope_declare] is the one declaration
    path (binds from the RHS [PTy] internally, decides [scope_wf] at construction).  BOUNDARY:
    construction PROVENANCE is not type-sealed — it is the scoped fold's property ([body_okS]
    declares only via [scope_declare]; [supported_program] runs the fold from [scope_empty]);
    full module-opacity would block the [vm_compute] fixture discipline. *)
Definition bound_cat_ok (c : PTy) : bool :=
  match c with
  | PtRunInt _ | PtRunFloat _ | PtBool | PtStr => true
  | PtIntConst _ | PtTIntConst _ _ | PtFloatConst _ _ | PtAgg | PtMap | PtNil => false
  end.
Record BoundCat : Type := mkBoundCat { bc_cat : PTy ; bc_ok : bound_cat_ok bc_cat = true }.

(** The BINDING authority — total over [PTy], every rejection a written arm.  A short decl is a
    DEFAULTING value context (the untyped-const row carries [svalue]'s default-[int] boundary);
    runtime categories bind as themselves; [PtAgg]/[PtMap] rejected (the evaluator has no
    aggregate values — a NAMED conformance narrowing); [PtNil] is Go's "use of untyped nil". *)
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

(** A declarable name is UNRECOGNIZED ([special_ident] = None, a uniform rejection) and not the
    blank identifier ([_ := e] is Go's "no new variables"). *)
Definition decl_ident_ok (s : string) : bool :=
  match special_ident s with
  | None => negb (String.eqb s "_")
  | Some _ => false
  end.

(** The raw list is internal plumbing; [scope_wf] is the sig's membership condition. *)
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

(** Marking flips only a [bool] (names untouched), so the sealed marker is TOTAL. *)
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

(** SCOPE INSERTION — the ONE boundary: binds the RHS category through [bind_category]
    internally (no caller-chosen [BoundCat]) and decides [scope_wf] at construction
    ([bool_dec]; drift fail-closes to [None]). *)
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

(** the one option-pair shape every dispatch case reduces to. *)
Lemma opt_pair_agree : forall (A B : Type) (d : option A) (g : B),
  match (match d with Some c => Some (c, g) | None => None end) with
  | Some cg => d = Some (fst cg) /\ snd cg = g
  | None => d = None
  end.
Proof. intros A B [c|] g; cbn; auto. Qed.

(** The BRIDGE: at the EMPTY scope the two spellings agree exactly and no marks occur — any
    divergence fails the build here.  (EMPTY-scope agreement only; nonempty-scope behavior is
    [type_expr]'s own, exercised by the gate fixtures.) *)
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

(** Closed [ptype] IS the empty-scope projection of [type_expr]. *)
Theorem type_expr_nil_ptype : forall e,
  option_map fst (type_expr scope_empty e) = ptype e.
Proof.
  intro e. pose proof (type_expr_nil_agrees e) as H.
  destruct (type_expr scope_empty e) as [[c G']|]; cbn.
  - cbn [fst snd] in H. destruct H as [-> _]. reflexivity.
  - rewrite H. reflexivity.
Qed.
Print Assumptions type_expr_nil_ptype.

(** ===== MARK-INSENSITIVITY: categories do not see used flags =====
    The env evaluator (GoSemDenote's [denote_expr_env]) queries categories at a FIXED scope while
    the checker THREADS marks — this suite proves the views agree ([type_expr_mark_agrees];
    consumer corollary [tcat_mark_insensitive]). *)

(** [scope_get] through a mark: categories untouched; only the looked-up name's flag absorbs it. *)
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

(** Marks COMMUTE (flags only). *)
Lemma scope_mark_comm : forall l s x,
  scope_mark (scope_mark l s) x = scope_mark (scope_mark l x) s.
Proof.
  induction l as [|[n [c u]] l' IHl]; intros s x; cbn; [reflexivity|].
  destruct (String.eqb n s) eqn:Es, (String.eqb n x) eqn:Ex; cbn;
    rewrite ?Es, ?Ex; cbn; try reflexivity.
  rewrite IHl. reflexivity.
Qed.

(** [ScopeS] equality from LIST equality ([UIP_dec] on [bool] — a theorem, not an axiom). *)
Lemma scopeS_eq : forall G1 G2 : ScopeS, sc_list G1 = sc_list G2 -> G1 = G2.
Proof.
  intros [l1 ok1] [l2 ok2]; cbn. intros ->.
  f_equal. apply (UIP_dec Bool.bool_dec).
Qed.

Lemma scope_markS_comm : forall G s x,
  scope_markS (scope_markS G s) x = scope_markS (scope_markS G x) s.
Proof. intros G s x. apply scopeS_eq. cbn. apply scope_mark_comm. Qed.

(** the marked-run dispatch shape: same [d], scopes mark-related. *)
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

(** The scope-aware CATEGORY PROJECTION — the env evaluator's category authority. *)
Definition tcat (G : ScopeS) (e : GExpr) : option PTy := option_map fst (type_expr G e).

Corollary tcat_mark_insensitive : forall G s e, tcat (scope_markS G s) e = tcat G e.
Proof.
  intros G s e. unfold tcat. pose proof (type_expr_mark_agrees e G s) as H.
  destruct (type_expr (scope_markS G s) e) as [[c1 Ga]|];
    destruct (type_expr G e) as [[c2 Gb]|]; try contradiction.
  - destruct H as [-> _]. reflexivity.
  - reflexivity.
Qed.

(** The bridge in [tcat] vocabulary: at the empty scope the projection IS closed [ptype]. *)
Corollary tcat_nil_ptype : forall e, tcat scope_empty e = ptype e.
Proof. exact type_expr_nil_ptype. Qed.
(* zero-axiom gating for the tcat suite rides its consumers' surface registration
   ([gosem_core_surface], GoSem.v — [denote_expr_env_nil] + [tcat_mark_insensitive]). *)

(** SEAL pins — every forged shape is UNREPRESENTABLE. *)
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
(** The insertion boundary decides: fresh+bindable binds; recognized/blank/redeclared names and
    unbindable RHS categories reject. *)
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

(** ===== STRUCTURAL: the CLOSED fragment [stmt_ok], the internal scope-threaded checkers
    ===== [stmt_okS]/[body_okS], and the program gate [supported_program] ===== *)

(** A builtin valid as a standalone EXPRESSION-STATEMENT call, by NAME and ARITY only (argument
    TYPES are per-builtin in [expr_stmt_ok]).  Conversions and value builtins are excluded
    ("evaluated but not used").  Widens with user funcs / a symbol table. *)
Definition stmt_call_ok (f : string) (args : list GExpr) : bool :=
  match special_ident f with                                           (* the ONE recognized-name table (GoAst) *)
  | Some SnPrintln | Some SnPrint => true                              (* variadic in arg COUNT *)
  | Some SnPanic => match args with _ :: nil => true | _ => false end  (* exactly 1 *)
  | Some (SnType _) | Some SnNil | Some SnLen | Some SnCap => false    (* recognized, but not statement-position callees *)
  | None => false
  end.

(** A GUARANTEED-printable [print]/[println] argument (Go spec, Bootstrapping: only boolean,
    numeric, and string are always supported) — a SCALAR [ptype] category.  Inherits [ptype]'s
    closed type-error rejections; a bare untyped int const carries the default-[int]
    (conservative 32-bit) boundary. *)
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

(** A [GExpr] legal as an EXPRESSION STATEMENT: a genuine builtin CALL at correct arity
    ([stmt_call_ok] — a bare value or a conversion is invalid Go), arguments checked PER BUILTIN
    ([printable_arg_ok] for [print]/[println]; [svalue] for [panic], which takes [interface{}]). *)
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

(** The CLOSED (scope-free) supported statement fragment — what GoSemDenote's slice-1 evaluator
    is gated on; the program gate is [supported_program] below, and the [.._nil] bridge lemmas
    prove the spellings agree on decl-free bodies.  [GsReturnVal] is invalid in the void [main];
    [defer] requires a CALL (same gate as an expr statement). *)
Definition stmt_ok (s : GoStmt) : bool :=
  match s with
  | GsExprStmt e    => expr_stmt_ok e
  | GsReturn        => true
  | GsReturnVal _   => false   (* value return is invalid in the void [main] — the only function emitted today *)
  | GsBlankAssign e => svalue e  (* [_ = e] is valid iff [e] PRODUCES a value — so [_ = println(1)] (void) is rejected *)
  | GsDefer e       => expr_stmt_ok e  (* [defer <call>]: Go requires the deferred expr be a function CALL — same gate as an expr statement *)
  | GsShortDecl _ _ => false  (* needs SCOPE STATE — never closed-supported; admitted by [stmt_okS] *)
  end.

(** ===== The SCOPE-THREADED checkers — ONE fold over the sealed [ScopeS], run by
    ===== [supported_program] below =====
    The scope-aware twins of [expr_stmt_ok]/[stmt_ok]: the same per-builtin discipline, but every
    argument/operand goes through [type_expr] (uses resolve AND mark in one traversal).
    [GsShortDecl] is admitted here — RHS typed first (Go's order), then [scope_declare] binds
    (overflow / recognized-name / blank / redeclare all reject there). *)
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

(** Go's "declared and not used" (a COMPILE error — certifying an unused local would be
    fail-open), decided on the fold's FINAL scope — not a second pass over the program. *)
Definition scope_all_used (G : ScopeS) : bool :=
  forallb (fun ent => snd (snd ent)) (sc_list G).

(** THE PROGRAM GATE — decidable PHASE-1 supportedness: package-main + the ONE scope-threaded
    fold [body_okS] from [scope_empty] + every declared local USED ([scope_all_used]).
    CONSERVATIVE structural scope + type-category supportedness — rejects free identifiers,
    use-before-declare, redeclaration, unused locals, and structurally-evident type/constant
    errors, but it is NOT full Go type-checking and NOT behavioral safety. *)
Definition supported_program (p : Program) : bool :=
  String.eqb (proj1_sig (prog_pkg p)) "main"
  && match body_okS scope_empty (prog_body p) with
     | Some Gfin => scope_all_used Gfin
     | None => false
     end.
Definition SupportedProgram (p : Program) : Prop := supported_program p = true.

(** ===== The DECL-FREE bridge: the scoped fold at [scope_empty] IS the closed fragment =====
    On a decl-free body the fold can neither bind nor mark, so it agrees EXACTLY with
    [forallb stmt_ok] — drift between the spellings fails the build here.  ([gosem_sound] rides
    this: denotable bodies are decl-free.) *)
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

(** ===== REGRESSIONS — three ledgers with DISTINCT contracts =====
    [bad_programs]: INVALID Go the gate MUST refuse (the soundness obligation).
    [valid_unsupported_programs]: VALID Go the gate still rejects (bounded incompleteness; a
    member graduates only via an exact structural rule that keeps its invalid companion
    rejected).  [good_programs]: accepted.  Plus [Fail … := eq_refl] forge pins.  Ledger
    placements are ground-truthed against gc via `make go-verify`.  Add NO new checker rule
    unless it rejects a real accepted-bad program or admits a needed demo. *)

(** Fixture builders: [pl_arg a] = `println(<a>)`; [gs_blank a] = `_ = <a>`; [gs_main b] =
    `func main(){ <b> }`; [gs_use i] = `_ = <i>`. *)
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
Definition gs_main (b : list GoStmt) : Program := mkProgram (mkIdent "main" eq_refl) b.
Definition id_x : Ident := mkIdent "x" eq_refl.
Definition id_y : Ident := mkIdent "y" eq_refl.
Definition id_m : Ident := mkIdent "m" eq_refl.
Definition gs_use (i : Ident) : GoStmt := GsBlankAssign (EId i).

(** NAMED because GoEmit's certificate-forge test references it. *)
Definition unsupported_value_stmt : Program :=
  mkProgram (mkIdent "main" eq_refl) [GsExprStmt (EInt 1)].

(** REJECTED — every entry is INVALID Go the gate must refuse ([supported_program = false]).
    ⚠ This list is the SOUNDNESS obligation; valid-but-rejected programs belong in
    [valid_unsupported_programs], never here. *)
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
    (* short declarations — each row isolates ONE rule *)
  ; gs_main [GsShortDecl id_x (EInt 1)]                                  (* x := 1 alone: declared and not used *)
  ; gs_main [GsShortDecl id_x (EInt 1); GsReturn]                        (* x := 1; return: declared and not used *)
  ; gs_main [GsShortDecl id_x (EInt 9223372036854775808); gs_use id_x]      (* x := 2^63: overflows int on every target *)
  ; gs_main [GsShortDecl id_x (EInt 1); GsShortDecl id_x (EInt 2); gs_use id_x]  (* x := 1; x := 2: no new variables *)
  ; gs_main [GsShortDecl (mkIdent "_" eq_refl) (EInt 1)]                 (* _ := 1: no new variables (blank LHS) *)
  ; gs_main [GsShortDecl id_x (EId (mkIdent "nil" eq_refl)); gs_use id_x]   (* x := nil: use of untyped nil *)
  ; gs_main [gs_use id_x; GsShortDecl id_x (EInt 1); gs_use id_x]              (* _ = x; x := 1; _ = x: use before declare *)
  ; gs_main [GsShortDecl id_m (EMapLit (GTSlice GTInt) GTInt [(ESliceLit GTInt [EInt 1], EInt 2)]);
             GsBlankAssign (ECall (EId (mkIdent "len" eq_refl)) [EId id_m])]  (* m := map[[]int]int{..}: invalid map key on a decl RHS *)
    (* defer reuses [expr_stmt_ok] *)
  ; gs_defer (EInt 1)                                                    (* defer of a non-call *)
  ; gs_defer (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]])  (* defer len(..) *)
  ; gs_defer (ECall (EId (mkIdent "panic" eq_refl)) nil)                 (* defer panic(): arity *)
  ; gs_defer (ECall (EId (mkIdent "println" eq_refl)) [ESliceLit GTInt [EInt 1]])  (* defer println(<slice>) *)
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
  ; pl_arg (gs_i8 (EBn BAdd (ECall (EId (mkIdent "len" eq_refl)) [EStr "hi"]) (EInt 200)))  (* int8(len("hi")+200): exact fold overflows int8 *)
  ; pl_arg (gs_i8 (EBn BAdd (ECall (EId (mkIdent "len" eq_refl)) [gs_str (EInt 65)]) (EInt 200)))  (* int8(len(string(65))+200): the non-literal len witness's INVALID companion — a PtStr->PtRunInt shortcut would flip this *)
  ; pl_arg (gs_i8 (EBn BAdd (ECall (EId (mkIdent "len" eq_refl)) [EBn BAdd (EStr "a") (EStr "b")]) (EInt 200)))  (* int8(len("a"+"b")+200): the concat witness's companion *)
  ; pl_arg (EBn BAdd (EStr "a") (EInt 1))                                (* "a" + 1: string + number *)
  ; gs_blank (ESliceLit GTU8 [gs_int (EInt 300)])
  ; pl_arg (EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (EStr "x"))      (* []int{10,20}["x"]: string index *)
  ; pl_arg (EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (EUn UNeg (EInt 1)))  (* []int{10,20}[-1]: negative const index (an OOB POSITIVE index is valid Go — good_programs) *)
  ; pl_arg (EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (EInt 9223372036854775808))  (* []int{10,20}[2^63]: index overflows int on any platform *)
    (* float-constant rounding + platform-uint complement (the rep must not lie) *)
  ; pl_arg (gs_i64 (gs_f64 (EInt 9223372036854775807)))                  (* int64(float64(maxint64)) rounds *)
  ; pl_arg (gs_i32 (ECall (EId (mkIdent "float32" eq_refl)) [EInt 2147483647]))
  ; gs_blank (EBn BDiv (EId (mkIdent "x" eq_refl)) (gs_f64 (EInt 0)))     (* x / float64(0): const-zero divisor (also free-ident) *)
  ; gs_blank (EBn BDiv (gs_f64 (EInt 1)) (gs_f64 (EInt 0)))                (* float64(1)/float64(0): const-zero float divisor *)
  ; gs_blank (EBn BDiv (ECall (EId (mkIdent "float32" eq_refl)) [EInt 1]) (ECall (EId (mkIdent "float32" eq_refl)) [EInt 0]))  (* float32 width of the same rule *)
  ; gs_blank (EBn BDiv (gs_f64 (EInt 1)) (EBn BSub (gs_f64 (EInt 1)) (gs_f64 (EInt 1))))  (* divisor zero arises by FOLDING *)
  ; pl_arg (ECall (EId (mkIdent "uint32" eq_refl)) [EUn UXor (ECall (EId (mkIdent "uint" eq_refl)) [EInt 0])])
    (* INVALID EMapLit/CTMap instances — each locks one face of the supported map literal's
       boundary (comparability / representability / distinctness / not-cap-able / nested key) *)
  ; gs_blank (EMapLit (GTSlice GTInt) GTInt [(ESliceLit GTInt [EInt 1], EInt 2)])  (* slice key not comparable *)
  ; gs_blank (EMapLit GTInt (GTMap (GTSlice GTInt) GTInt) [])              (* invalid key hidden in the VALUE type, even EMPTY *)
  ; pl_arg (ECall (EId (mkIdent "len" eq_refl)) [EMapLit GTInt (GTMap (GTSlice GTInt) GTInt) []])  (* len of an invalid-typed literal *)
  ; gs_blank (EBn BDiv (EInt 1) (ECall (EId (mkIdent "len" eq_refl)) [EMapLit GTInt (GTMap (GTSlice GTInt) GTInt) []]))  (* no div-by-zero behavior for invalid source *)
  ; gs_blank (ESliceLit (GTMap (GTSlice GTInt) GTInt) [])                  (* the same key through a SLICE literal *)
  ; gs_blank (EConv (CTSlice (GTMap (GTSlice GTInt) GTInt)) (EId (mkIdent "nil" eq_refl)))  (* ... and through the aggregate-conversion arm *)
  ; gs_blank (EMapLit GTInt GTU8 [(EInt 1, EInt 300)])                    (* value overflows uint8 *)
  ; gs_blank (EMapLit GTU8 GTInt [(EInt 300, EInt 1)])                    (* key overflows uint8 *)
  ; gs_blank (EMapLit GTInt GTInt [(EInt 1, EInt 2); (EInt 1, EInt 3)])   (* duplicate constant key *)
  ; gs_blank (ECall (EId (mkIdent "cap" eq_refl)) [EMapLit GTInt GTInt [(EInt 1, EInt 2)]])  (* cap of a map *)
  ; gs_blank (EConv (CTMap GTInt GTInt) (EId (mkIdent "x" eq_refl)))      (* map conversion of a free ident *)
  ; gs_blank (EConv (CTMap (GTSlice GTInt) GTInt) (EId (mkIdent "nil" eq_refl)))  (* non-comparable key in the conversion TARGET *)
  ; gs_blank (EConv (CTMap GTInt (GTMap (GTSlice GTInt) GTInt)) (EId (mkIdent "nil" eq_refl)))  (* invalid key in the target's NESTED value type *)
  ; gs_blank (EConv (CTMap GTInt (GTSlice (GTMap (GTSlice GTInt) GTInt))) (EId (mkIdent "nil" eq_refl)))  (* key under a SLICE wrapper in the target; the CLASS gate is [ctmap_conv_unsupported_target_rejected] *)
  ; pl_arg (EMapLit GTInt GTInt [(EInt 1, EInt 2)])                       (* a supported map VALUE is not a printable arg *)
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

(** REJECTED-BUT-VALID: Go ACCEPTS every program here; the gate still rejects (bounded fail-loud
    incompleteness, NOT a soundness obligation).  A member graduates ONLY via an exact structural
    rule that keeps its INVALID [bad_programs] companion rejected; a graduating CTMap arm must
    also re-establish [ctmap_conv_unsupported_target_rejected].  The list is the member
    authority; detail at each row. *)
(** The valid-but-out-of-core ptr/chan MAP-KEY class, pinned as the full CARTESIAN product
    (key type × rejecting surface) — an executable per-surface claim, never a sample.  Every
    generated program is VALID Go (nil converts to any slice/chan/map type). *)
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
  [ pl_arg (ECall (EId (mkIdent "len" eq_refl)) [gs_str (EInt 65)])       (* len(string(65)): non-literal PtStr — the len fallback (pinned below) *)
  ; pl_arg (ECall (EId (mkIdent "len" eq_refl)) [EBn BAdd (EStr "a") (EStr "b")])  (* len("a"+"b"): the concat is a non-literal PtStr *)
  ; gs_blank (EConv (CTMap GTInt GTInt) (EId (mkIdent "nil" eq_refl)))    (* map[int]int(nil): the CTMap quarantine on a VALID operand *)
  ; gs_blank (EBn BDiv (gs_f64 (EInt 1)) (gs_f64 (EInt 3)))               (* float64(1)/float64(3): inexact quotient, exact-or-reject *)
  ; pl_arg (ECall (EId (mkIdent "float32" eq_refl)) [gs_f64 (EInt 16777217)])  (* float32(2^24+1): inexact at binary32, exact-only *)
    (* the conservative default-[int] boundary: 2^40 fits 64-bit gc but not the sound-everywhere 32-bit window *)
  ; pl_arg (EInt 1099511627776)                                          (* println(2^40) *)
  ; gs_blank (EInt 1099511627776)                                        (* _ = 2^40 *)
  ; gs_main [GsShortDecl id_x (EInt 1099511627776); gs_use id_x]            (* x := 2^40 — the same boundary at the decl *)
    (* recognized names as locals: LEGAL Go (predeclared idents are shadowable) — [decl_ident_ok] rejects uniformly, a NAMED narrowing *)
  ; gs_main [GsShortDecl (mkIdent "len" eq_refl) (EInt 1); GsBlankAssign (EId (mkIdent "len" eq_refl))]   (* len := 1; _ = len *)
  ; gs_main [GsShortDecl (mkIdent "int" eq_refl) (EInt 1); GsBlankAssign (EId (mkIdent "int" eq_refl))]   (* int := 1; _ = int *)
  ; gs_main [GsShortDecl (mkIdent "nil" eq_refl) (EInt 1); GsBlankAssign (EId (mkIdent "nil" eq_refl))]   (* nil := 1; _ = nil *)
    (* aggregate/map LOCALS: VALID Go — [bind_category]'s [PtAgg]/[PtMap] arms, a NAMED narrowing
       (the evaluator has no aggregate values); the [len] uses isolate the rejection *)
  ; gs_main [GsShortDecl id_x (ESliceLit GTInt [EInt 1]);
             GsBlankAssign (ECall (EId (mkIdent "len" eq_refl)) [EId id_x])]   (* x := []int{1}; _ = len(x) *)
  ; gs_main [GsShortDecl id_m (EMapLit GTInt GTInt [(EInt 1, EInt 2)]);
             GsBlankAssign (ECall (EId (mkIdent "len" eq_refl)) [EId id_m])]   (* m := map[int]int{1:2}; _ = len(m) *)
  ] ++ ptrchan_key_quarantine.
Example valid_unsupported_rejected :
  forallb (fun p => negb (supported_program p)) valid_unsupported_programs = true.
Proof. vm_compute. reflexivity. Qed.

(** The CLOSED fragment never admits a short declaration (pinned at the constructor) — why
    denotable bodies are decl-free; [supported_program] DOES admit declarations (the
    [good_programs] locals rows). *)
Example shortdecl_stmt_ok_false : forall x e, stmt_ok (GsShortDecl x e) = false.
Proof. reflexivity. Qed.

(** [body_okS] is the INTERNAL body checker, NOT the program gate: it can SUCCEED on an
    unused-local body that [supported_program] rejects via [scope_all_used]. *)
Example body_okS_not_the_gate :
  match body_okS scope_empty [GsShortDecl id_x (EInt 1); GsReturn] with
  | Some G => scope_all_used G = false
  | None => False
  end
  /\ supported_program (gs_main [GsShortDecl id_x (EInt 1); GsReturn]) = false.
Proof. split; vm_compute; reflexivity. Qed.

(** ★ THE CTMAP TARGET CLASS GATE — universal: every [goty_supported]-rejected map target's nil
    conversion is unsupported.  A graduating CTMap arm must re-establish this theorem (no
    outer-key-only shortcut can satisfy it). *)
Theorem ctmap_conv_unsupported_target_rejected : forall k v,
  goty_supported (GTMap k v) = false ->
  supported_program (gs_blank (EConv (CTMap k v) (EId (mkIdent "nil" eq_refl)))) = false.
Proof. intros k v _. reflexivity. Qed.

(** The [len(string(65))] ledger row rejects via the NON-LITERAL-[PtStr] [len] fallback
    SPECIFICALLY: the arg IS a supported [PtStr], yet [len] of it is [None] — the pair below
    locks that fallback (a restored [PtStr -> PtRunInt] shortcut would flip it). *)
Example string_rune_const_is_supported_PtStr :
  ptype (ECall (EId (mkIdent "string" eq_refl)) [EInt 65]) = Some PtStr.
Proof. reflexivity. Qed.
Example len_of_nonliteral_PtStr_rejected :
  ptype (ECall (EId (mkIdent "len" eq_refl)) [ECall (EId (mkIdent "string" eq_refl)) [EInt 65]]) = None.
Proof. reflexivity. Qed.

(** ACCEPTED — the smaller-but-SOUND subset the gate admits. *)
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
  ; pl_arg (EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (EInt 5))       (* []int{10,20}[5]: OOB POSITIVE const index is VALID Go (gc bounds-checks arrays, not slices) — supported; the panic is BEHAVIORAL (GoSem denotes [rt_index_oob]; the behavioral gate rejects) *)
  ; pl_arg (EIndex (ESliceLit GTInt [EInt 10; EInt 20]) (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]))  (* a RUNTIME (non-constant) index — valid Go, supported; the rule is not [EInt]-only *)
  ; mkProgram (mkIdent "main" eq_refl)                                   (* defer println("bye"); return — a deferred CALL is supported (same gate as an expr statement) *)
      [GsDefer (ECall (EId (mkIdent "println" eq_refl)) [EStr "bye"]); GsReturn]
    (* short declarations — declared AND used *)
  ; gs_main [GsShortDecl id_x (EInt 1); gs_use id_x; GsReturn]              (* x := 1; _ = x; return *)
  ; gs_main [GsShortDecl id_x (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]]); gs_use id_x]  (* a RUNTIME binding *)
  ; gs_main [GsShortDecl id_x (EInt 1); GsShortDecl id_y (EId id_x); gs_use id_y]  (* y := x: a runtime category binds AS ITSELF *)
  ; gs_main [GsShortDecl id_x (gs_i64 (ECall (EId (mkIdent "len" eq_refl)) [ESliceLit GTInt [EInt 1]])); gs_use id_x]  (* a TYPED-runtime binding *)
  ; gs_main [GsShortDecl id_x (EInt 1); GsBlankAssign (EBn BAdd (EId id_x) (EInt 1))]  (* use marked INSIDE a subexpression *)
  ; gs_main [GsShortDecl id_x (EInt 1); GsExprStmt (ECall (EId (mkIdent "println" eq_refl)) [EId id_x])]  (* use marked through a CALL ARGUMENT *)
  ].
Example good_programs_supported : forallb supported_program good_programs = true.
Proof. vm_compute. reflexivity. Qed.

(** EXPRESSION-LEVEL direct pins not surfaced through the program lists. *)
Example str_printable : printable_arg_ok (EStr "hi") = true.  Proof. reflexivity. Qed.
Example str_svalue    : svalue (EStr "x") = true.            Proof. reflexivity. Qed.
Example complement_const_uint_none  : complement_const GTUint 0 = None.        Proof. reflexivity. Qed.
Example complement_const_u8_exact   : complement_const GTU8 0 = Some 255%Z.    Proof. reflexivity. Qed.
Example complement_const_int_signed : complement_const GTInt 0 = Some (-1)%Z.  Proof. reflexivity. Qed.

(** FORGE-RESISTANCE — [eq_refl] cannot inhabit [SupportedProgram <bad>]: no certificate exists
    for a rejected program.  (The [:= eq_refl] term form is what must fail; [Fail Lemma] would
    only guard the vernac.) *)
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

(** Reserved: the behavioral-safety GATE over GoSem's denotation.  NOT yet defined — slice-1
    denotation is too partial, and a placeholder [BehaviorSafe _ := True] is the overclaiming
    gate the charter forbids.  ([GoSemSafe.panic_free_gate] is a narrow off-main seed, not this
    gate.)  When GoSem suffices: [BehaviorSafe] + [SafeProgram]/[emit_safe]. *)

(** GATE — GoSafe is on the blessed emission path; keep it axiom-free (checked by the GOEMIT_GATE, mirroring
    the digits/GoAst/GoPrint printer gate). *)
Print Assumptions SupportedProgram.
Print Assumptions bad_programs_rejected.
Print Assumptions ctmap_conv_unsupported_target_rejected.
Print Assumptions body_okS_nil_declfree.
