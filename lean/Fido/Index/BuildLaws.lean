-- Port of Index/BuildLaws.v (lean/README.md).
import Fido.Collections
import Fido.Syntax
import Fido.Index.Model
import Fido.Index.Build

open Fido

/-! divergences:
  * Section 1 (`.v` lines 1–650: spans, the root cell, the parent inverse, the first-edge law, coverage,
    `roots_resolve`, one numbered sublist).  The `.v`'s inline `do_args` is Build.lean's named companion
    `number_args b i bi es`, so the three inner `assert (Hda : …)` of `number_expr_span` /
    `number_expr_edge_wf` / `number_expr_cpo` over the inline fix are the private `number_args_span_of` /
    `number_args_edge_wf_of` / `number_args_cpo_of` about `number_args`, each stating the `.v`'s conclusion
    under the `.1` / `.2.1` / `.2.2` projections of the `(cells, next, roots)` triple in place of
    `let '(ac, bf, _) := …`.
  * Statement mapping (README + Build.lean): `fst (fst t)` / `snd (fst t)` / `snd t` are `t.1` / `t.2.1` /
    `t.2.2`; Rocq's `let '(c, b', _) := number_list f b xs in (c, b')` (`number_list_span`,
    `number_opttype_span`) is `match … with | (c, b', _) => (c, b')`; `S self` is `self + 1`; `seq b n` is
    `List.range' b n` and `seq 0 n` (`number_file_positions`) is `List.range n`; `map fst` is
    `List.map Prod.fst`; `length` is `List.length`; `In` is `∈`; `Forall (fun kv => …) occs` (`ewf`) is
    `∀ kv ∈ occs, …`; Rocq's `if` on the `bool` `requires_first_edge` (`edge_wf`) is `bif` (Model.lean);
    `{A}` is `{A : Type}`.  The stdlib `Forall` constructors, `Forall_app` and `Forall_impl` the `.v` uses
    are the private `ewf_nil` / `ewf_cons` / `ewf_app` and `ewf_weaken`'s own body; the `.v` lemma
    `ewf_node` is `ewf_cons` itself.
  * `lia` (32 sites in this range of the `.v`) is NOT `omega`.  Core finding: `omega` puts `propext` and `Quot.sound`
    into every closure it touches, and on a goal that is a conjunction it reaches `Classical.choice`
    (probe: `∀ a b : Nat, a < b → a + 1 ≤ b ∧ a ≤ b`; the single-inequality form carries only `propext` +
    `Quot.sound`).  Every arithmetic side goal here is one core lemma — `Nat.add_assoc` /
    `Nat.add_comm` / `Nat.add_right_comm` rewrites, `Nat.le_trans`, `Nat.le_add_right`,
    `Nat.lt_add_of_pos_right`, `Nat.lt_of_lt_of_le`, `Nat.zero_lt_succ`, `Nat.zero_lt_one`, `Nat.le_of_eq`,
    all axiom-free — so it is written by hand.  A later section that does use `omega` must split every
    conjunction first.
  * The stdlib list lemmas the `.v` uses (`map_app`, `seq_app`, `app_nil_r`, `length_map`, `seq_length`,
    `in_app_or`) are private inductions here (`map_app`, `range'_app`, `app_nil`, `length_map`,
    `mem_app_or`): core's `List.map_append`, `List.range'_append_1`, `List.append_nil`, `List.length_map`
    and `List.mem_append` carry `propext`.  `in_or_app` is core's axiom-free `List.mem_append_left` /
    `List.mem_append_right`; `map_cons`, `seq_length` and `seq 0 n = seq' 0 n` are core's axiom-free
    `List.map_cons`, `List.length_range'` and `List.range_eq_range'`.
  * Rocq's `destruct (number_expr …) as [kc nxt]` on the structural calls is not needed: each composite
    call's `.1` / `.2` unfolds by `rfl` through structure eta (the private `number_expr_unary_fst` …
    `number_list_cons_roots` equations), so the `Expr_ind'` inductions and the `number_list` inductions
    rewrite with those and never destructure.  The non-recursive composites (`number_constspec` …
    `number_file`) are destructured as in the `.v` (`rcases h : … with ⟨…⟩`, then `rw [h] at …`) after
    `unfold` + `dsimp only`; the `dsimp only` must precede the destructuring, since a call under a
    not-yet-reduced `match init with …` alternative is not yet in the goal.  The `Record` arguments are
    destructured at `intro` (`⟨names, init⟩`, `⟨stmts⟩`) where the `.v` destructs `const_init cs` etc.
  * Axiom closure (the audit's finding; no statement changes): every constant of this section — the 49
    `.v` items and the private helpers — is axiom-free (`axioms used anywhere: []`), exactly as the `.v`;
    nothing here mentions a map.
  * Section 2 (`.v` lines 651–1600: the root facts, the parent inverse, the root bijection, `pbounds`,
    `covered`, the coverage of every composite and the file, `occ_unique`, `occurrences_distinct`,
    `number_file_complete`, `child_lt`).  The two inner `assert (Hda : …)` of `number_expr_pbounds` /
    `number_expr_cover` over the inline fix are the private `number_args_pbounds_of` /
    `number_args_cover_of` about `number_args`; the `.v`'s `let '(ac, bf, roots) := do_args … in ∀ q,
    bi <= q < bf -> In q roots \/ covered ac q` is stated under the `.1` / `.2.1` / `.2.2` projections.
  * Statement mapping: `b < q < x` is `b < q ∧ q < x`; `In q (snd (number_list …))` is `q ∈ ….2.2` and
    `snd (fst …)` is `.2.1`; `NoDup (map fst …)` is `List.Nodup (List.map Prod.fst …)`; `seq b n` is
    `List.range' b n` (`child_lt`); `length` is `List.length`; `Some pp` is `some pp`.
  * `lia` (49 sites in this range of the `.v`) is again written by hand, one core lemma each — `Nat.lt_of_lt_of_le`,
    `Nat.lt_of_le_of_lt`, `Nat.le_add_right`, `Nat.lt_succ_self`, `Nat.le_of_lt`, `Nat.lt_irrefl`,
    `Nat.le_antisymm`, `Nat.le_of_lt_succ`, `Nat.lt_of_le_of_ne`, `Nat.le_of_eq`, `Nat.add_comm`,
    `Nat.zero_add`, `Nat.not_succ_le_self`, `Nat.lt_add_of_pos_right` — all axiom-free; where the `.v`
    needs `lia` to pass from `S b <= b1` to `b < b1` Lean's `b < b1` IS `b + 1 ≤ b1` (`Nat.lt`), so the
    hypothesis is used as is.  Every site was first closed with `omega` (each on a single inequality,
    equation or `False` after splitting the conjunction, per the section-1 finding): it compiles and audits
    with `[propext, Quot.sound]` and no `Classical.choice`; the hand form is kept so the module's closure
    stays `[]`.  `le_lt_dec` (9 sites) is `Nat.lt_or_ge`, `Nat.eq_dec` (9 sites) is `by_cases` on `Nat`'s
    `DecidableEq` — both probed axiom-free (`by_cases` picks the `Decidable` instance over `Classical`).
  * The stdlib facts this range adds are private hand inductions: `in_map` is `mem_map_of_mem` (Syntax.lean's
    copy is private to that module), `in_seq` (the direction used) is `mem_range'_bounds`, `seq_NoDup` is
    `nodup_range'` — core's `List.mem_range'` / `List.mem_range` carry `propext` and its `List.nodup_range'`
    takes a `0 < step` autoParam.  `seq 0 count` (`number_file_positions`) is bridged to `range'` by core's
    axiom-free `List.range_eq_range'`; `length_seq` is `List.length_range'`; `NoDup_cons_iff` is `cases`
    on the `List.Pairwise`; `inversion` / `injection` on `Some` is `Option.some.inj`; `in_eq` / `in_cons`
    are `List.Mem.head` / `List.Mem.tail`; `in_or_app` is `List.mem_append_left` / `_right`.
  * The ten root lemmas: the `.v` destructs each composite's calls before `do 2 eexists; split; reflexivity`;
    here `⟨_, _, rfl, rfl⟩` after `cases` on the record / initializer alone, because the `.1` projection of
    every composite unfolds by definitional structure eta (the section-1 finding), so nothing is
    destructured.  The cpo / pbounds / cover lemmas ARE destructured as in the `.v` (`rcases h : …`, then
    `rw [h] at …`), since their sublist hypotheses are stated about the un-destructured calls.  `cbn
    [number_typeexpr number_leaf …]` (`number_varspec_cover`) is `dsimp only [number_typeexpr, number_leaf]`;
    where the `.v` `cbn`s a leaf's `snd` to `S b` the reduced form is reached by a type ascription
    (`have Hqhi' : q < b + 1 := Hqhi`), definitional unfolding.
  * Axiom closure (the audit's finding; no statement changes): every constant of this section — the 62
    `.v` items and the five private helpers — is axiom-free; the whole module still audits
    `axioms used anywhere: []`, exactly as the `.v`.
  * Section 3 (`.v` lines 1601–2446: `ext_ok` and the extent of every composite and the file, extent
    exactness, the role/kind classification `role_kind_of` … `number_file_class`, the tag round-trip,
    `number_main`, `asc`, the reverse layout clauses, `child_layout_ok`, the per-cell shape law).  The two
    inner `assert (Hda : …)` of `number_expr_ext` / `number_expr_class` over the inline fix are the private
    `number_args_ext_of` / `number_args_class_of` about `number_args`, stated under the `.1` / `.2.1`
    projections of the `(cells, next, roots)` triple.
  * Statement mapping: `Forall (fun '(pos, cell) => …) occs` (`ext_ok`, `class_ok`) and
    `Forall (fun kv => …) occs` (`shape_ok`) are `∀ kv ∈ occs, … kv.1 … kv.2`; `pos <= x < bnd` is
    `pos ≤ x ∧ x < bnd`, parenthesised exactly as Rocq's `_ <= _ < _` notation parses under `/\` (`ext_ok`,
    `number_file_extent`); `nth_error l k = Some y` is `l[k]? = some y` (`asc_head_lt`, `asc_nth`,
    `child_layout_ok`); `occs <> []` is `occs ≠ []`; `[S b]` / `In (S b, bcell) rest` are `[b + 1]` /
    `(b + 1, bcell) ∈ rest`; `length` is `List.length`.  Rocq infers `t : list nat` in `asc_head_lt` /
    `asc_nth` from `asc`; Lean elaborates `t[j]?` / `x < y` before that unification, so those binders carry
    their types (`(t : List Nat)`, `(a j y : Nat)`) — the same statement.
  * The two catch-all arms are enumerated (Integer.lean): `asc`'s `| _ => True` is `| [] => True | [_] =>
    True` (still one structural recursion on the list), `no_reverse`'s `| _ => True` lists the nine views.
  * `lia` (69 sites in this range of the `.v`) is again written by hand, one axiom-free core lemma each —
    `Nat.le_sub_one_of_lt`, `Nat.sub_lt`, `Nat.lt_add_of_pos_right`, `Nat.lt_of_le_of_lt`,
    `Nat.lt_of_lt_of_le`, `Nat.lt_trans`, `Nat.le_trans`, `Nat.le_add_right`, `Nat.le_refl`,
    `Nat.lt_succ_self`, `Nat.zero_le`, `Nat.zero_lt_one`, `Nat.zero_lt_succ`, `Nat.lt_irrefl`,
    `Nat.not_lt_zero`, `Nat.lt_of_succ_lt_succ`, `Nat.add_comm`, `Nat.zero_add`.  The root cell's own extent
    clause, which the `.v` closes at every composite by `lia` from `child_lt`, is the private `ext_head`:
    the block end is past the cell's position and past each listed child, so the extent `bfin - 1` is at or
    above both and below `bfin`.  `map_seq_pos`'s `discriminate` is `nomatch`; `Forall_forall`
    (`number_file_extent`) is definitional, `ext_ok` already being the `∀ kv ∈` form; `rv_ok_mk`'s
    `destruct (role_kind_of role)` is `cases role` (eight arms, each a `rfl`-typed transitivity); the
    reverse-clause `discriminate`s are `nomatch` on the constructor equation and `spec_view_of_flavor`'s
    `False` alternatives are `False.elim`.  The stdlib `Forall` constructors and `Forall_app` are the
    private `ext_ok_nil` / `ext_ok_cons` / `class_ok_nil` / `class_ok_cons` and `ext_ok_app` /
    `class_ok_app` / `shape_ok_app`'s own bodies.
  * The nine view lemmas and `number_main`: as the root lemmas (section 2), `⟨_, _, rfl, rfl, rfl⟩` after
    `cases` on the record / initializer alone, the `.1` projection unfolding by definitional structure eta;
    `number_main` destructures `number_block` as the `.v` does so `number_block_view`'s equation rewrites the
    child list.  The `_ext` lemmas destructure every call as the `.v` does (`unfold … at Hcpo Hmap Hsnd ⊢`,
    `rcases h : …`, `rw [h] at …`), since their `_cpo` / `_span` hypotheses are about the whole composite.
  * Axiom closure (the audit's finding; no statement changes): the five items whose statements mention
    `l[k]?` — `asc_head_lt`, `asc_nth`, `child_layout_ok`, `child_layout_ok_app`, `child_layout_ok_node` —
    carry `propext`, and they alone: core's `List.get?Internal` (what `l[k]?` on lists unfolds to in v4.33)
    is itself `propext`-dependent through its own wildcard arm, the Model.lean finding
    (`nth_lt_nth_error`); their proofs add nothing (`Option.some.inj`, `Nat.lt_trans`, `cases`).  Every other
    constant of this section — the remaining 60 `.v` items and the seven private helpers — is axiom-free,
    so the module's closure becomes `[propext]`; nothing reaches `Classical.choice`.
  * Section 4 (`.v` lines 2447–3983: `number_list_roots` — the roots account of a numbered segment — the
    opttype roots, and the per-composite shape, layout and kind laws through `number_file_kind`, with
    `number_file_root`, `child_kind_ok` and the `expr_view` facts).  The three inner `assert (Hda : …)` of
    `number_expr_shape` / `number_expr_layout` / `number_expr_kind` over the inline fix are the private
    `number_args_shape_of` / `number_args_layout_of` / `number_args_kind_of` about `number_args`, stated
    under the `.1` / `.2.1` / `.2.2` projections of the `(cells, next, roots)` triple; the argument root's
    role is `RApplicationArg (i0 + k)` exactly as the `.v`, and Lean's `Nat.add` recursing on its second
    argument makes the `.v`'s `Nat.add_0_r` step a `rfl`, its `Nat.add_succ_comm` a `Nat.add_right_comm`,
    and the `0 + i` at the application head a `Nat.zero_add`.
  * Statement mapping: `let '(c, b', roots) := number_list g b xs in …` (`number_list_roots`) and
    `let '(c, b', roots) := number_opttype (Some self) b ot in …` (`number_opttype_roots`) are
    `match … with | (c, b', roots) => …` (the section-1 rendering); `nth_error roots k = Some r0` is
    `roots[k]? = some r0` with the index binder typed (`∀ (k : Nat) r0` — the pattern variable `roots` has
    no type when the index is elaborated and `GetElem?` resolution sticks, the section-3 finding);
    `b <= r0 < b'` is `b ≤ r0 ∧ r0 < b'`; `fst (fst …)` is `.1`; `match ot with Some _ => 1 | None => 0
    end` is the same two-arm `match`; `In` is `∈`; `length` is `List.length`; `{A}` is `{A : Type}`.  The
    `.v`'s `(fun _ => True)` root facts built by `match … with ex_intro … end` are the private
    `root_true_of_view` / `expr_root_true`; its inline role-and-no-reverse and kind root facts (`Hnroot`,
    `Hvroot`) are `root_role_noreverse_of_view` / `expr_root_role_noreverse` / `root_kind_of_view` /
    `expr_root_kind`, one each over the view lemma; the `∃ sh0, …` spec / statement ones stay inline
    `have`s as in the `.v`.
  * `lia` (45 sites in this range of the `.v`) is again written by hand, one axiom-free core lemma each —
    `Nat.lt_of_lt_of_le`, `Nat.le_trans`, `Nat.le_of_lt`, `Nat.lt_add_of_pos_right`, `Nat.le_add_right`,
    `Nat.le_refl`, `Nat.le_succ`, `Nat.lt_succ_self`, `Nat.zero_lt_succ`, `Nat.lt_irrefl`,
    `Nat.not_lt_zero`, `Nat.lt_of_lt_of_eq`, `Nat.le_of_eq`, `Nat.le_antisymm`, `Nat.le_of_lt_succ`,
    `Nat.eq_zero_of_le_zero`, `Nat.le_of_sub_eq_zero`, `Nat.sub_self`, `Nat.not_succ_le_zero`,
    `Nat.add_assoc`, `Nat.add_right_comm`, `Nat.zero_add` (all probed `[]`); the `.v`'s
    `destruct roots as [|r1 t1]` head condition of `asc_cons` is the private `asc_cons_lt` (every tail
    element above the head).  The `.v`'s `Nat.ltb_lt` / `Nat.ltb_ge` / `Nat.eqb_eq` / `Nat.eqb_neq`
    rewrites of `k <? NN` / `k =? NN` under `layout_role` / `layout_kind` are the private
    `cond_decide_true` / `cond_decide_false` (by `cases` on the `Decidable` instance — `rw [decide_eq_true
    …]` leaves a `cond true …` that `rw`'s own `rfl` may or may not close), composed by `Eq.trans` against
    the role / kind fact so the `bif decide (k < nn)` layout is reached by definitional unfolding alone;
    `Nat.lt_ge_cases` is `Nat.lt_or_ge`, and `k ≥ nn` against `k <? nn` is the private `not_lt_of_len_le`.
  * The stdlib list facts this range adds are private hand inductions: `length_app` (core's
    `List.length_append` goes through `simp`), and `nth_error_app1` / `nth_error_app2` are
    `getElem?_app_left` / `getElem?_app_right` on `l[k]?`, the latter's `S n - S m = n - m` step the private
    `succ_sub_succ'` (core's `Nat.add_sub_add_right` carries `propext`).  The `Forall` constructors for
    `shape_ok` are the private `shape_ok_nil` / `shape_ok_cons`.  `injection Hcp as <-` on `nth_error [x]
    0` is `Option.some.inj` + `subst`; `destruct (k - length nroots) as [|k2] eqn:Hk2` is `cases Hk2 : k -
    List.length nroots with`; the late `destruct ot` is `cases ot`, the `match ot with …` in `Holen` and in
    the shape then reducing by defeq (an explicit `show` of that match in tactic mode auto-generalizes the
    hypotheses depending on `ot`, so the count goal is `show … = _`); `injection He as He; subst fl` on a
    `VDecl fl` equation is `cases` on the ascribed equation (`have He' : VDecl ConstSpecF = VDecl fl := He`);
    the reverse-clause `discriminate`s are `nomatch`; `rewrite Hv; exact I` on a `no_reverse` goal is
    `Eq.mpr (congrArg no_reverse Hv) True.intro`, and on a `kind_of_view` goal `(congrArg kind_of_view
    Hv).trans rfl`, so no `rw` is asked to close an `Eq` by its own `rfl`.  `number_typespec_shape` /
    `_layout` / `_kind` reduce the two leaf calls to their cells (`dsimp only [number_bindingname,
    number_typeexpr, number_leaf]`, the section-2 rendering) where the `.v` destructs `number_typeexpr`;
    every other composite is destructured exactly as the `.v` (`rcases h : …`, `rw [h] at …`, `dsimp
    only`).  `number_opttype_class` supplies the type cell's kind in `number_constspec_kind` /
    `number_varspec_kind` exactly as the `.v` (`rv_ok` unfolded, the role rewritten in).
  * Axiom closure (the audit's finding; no statement changes): 40 of the 50 `.v` items carry `propext`, and
    they alone — every statement that mentions `l[k]?` (`number_list_roots`, `number_opttype_roots`),
    `child_layout_ok` or `child_kind_ok` (the thirteen layout and twelve kind laws, `child_kind_ok` and its
    two combinators, `number_list_layout` / `number_list_kind`, `number_leaf_layout` / `_kind`), and the
    seven composite shape laws `number_constspec_shape` … `number_file_shape`, whose proofs consume
    `number_list_roots`; the carrier is core's `List.get?Internal` under `l[k]?` (the Model.lean / section-3
    finding) and their proofs add nothing.  The other ten (`number_list_shape`, `number_expr_shape`, the
    three leaf shapes, `number_typespec_shape`, `expr_view_not_const` / `expr_view_no_reverse` /
    `expr_view_kind`, `number_file_root`) and fifteen of the nineteen private helpers are axiom-free
    (`getElem?_app_left` / `_right`, `number_args_layout_of` / `_kind_of` carry `propext` for the same
    reason).  The module's closure stays `[propext]`; nothing reaches `Classical.choice` or `Quot.sound`
    (`FIDO_AUDIT_VERBOSE=1` lists no classical constant), and `omega` is not used.
-/

namespace Fido.Index.BuildLaws
open Fido.Index.Model Fido.Index.Build

/-! ### the `.v`'s stdlib list facts (`map_app`, `seq_app`, `app_nil_r`, `length_map`, `in_app_or`), by hand -/

private theorem map_app {A B : Type} (f : A → B) : ∀ l1 l2 : List A,
    List.map f (l1 ++ l2) = List.map f l1 ++ List.map f l2
  | [], _ => rfl
  | x :: xs, l2 => congrArg (fun l => f x :: l) (map_app f xs l2)

private theorem range'_app (m : Nat) : ∀ s n : Nat,
    List.range' s m ++ List.range' (s + m) n = List.range' s (m + n) := by
  induction m with
  | zero => intro s n; rw [Nat.zero_add]; rfl
  | succ m IH =>
    intro s n
    rw [Nat.add_right_comm m 1 n]
    show s :: (List.range' (s + 1) m ++ List.range' (s + m + 1) n) = s :: List.range' (s + 1) (m + n)
    rw [Nat.add_right_comm s m 1, IH (s + 1) n]

private theorem app_nil {A : Type} : ∀ l : List A, l ++ [] = l
  | [] => rfl
  | x :: xs => congrArg (fun l => x :: l) (app_nil xs)

private theorem length_map {A B : Type} (f : A → B) : ∀ l : List A, (List.map f l).length = l.length
  | [] => rfl
  | _ :: xs => congrArg (fun n => n + 1) (length_map f xs)

private theorem mem_app_or {A : Type} {x : A} : ∀ {l1 l2 : List A}, x ∈ l1 ++ l2 → x ∈ l1 ∨ x ∈ l2 := by
  intro l1 l2 h
  induction l1 with
  | nil => exact Or.inr h
  | cons y ys IH =>
    cases h with
    | head => exact Or.inl (List.Mem.head _)
    | tail _ h' =>
      cases IH h' with
      | inl h1 => exact Or.inl (List.Mem.tail _ h1)
      | inr h2 => exact Or.inr h2

/-! ### the numbering equations as projections: the `.v` destructures `let '(x, y) := …`; here each
    composite call's `.1` / `.2` unfolds by `rfl` through structure eta -/

private theorem number_expr_unary_fst (par : Option Nat) (role : Role) (b : Nat) (op : Syntax.UnaryOp)
    (e' : Syntax.Expr) :
    (number_expr par role b (Syntax.Unary op e')).1
      = (b, mkCell (VUnary op) role par ((number_expr (some b) RUnaryOperand (b + 1) e').2 - 1) [b + 1] 0)
        :: (number_expr (some b) RUnaryOperand (b + 1) e').1 := rfl
private theorem number_expr_unary_snd (par : Option Nat) (role : Role) (b : Nat) (op : Syntax.UnaryOp)
    (e' : Syntax.Expr) :
    (number_expr par role b (Syntax.Unary op e')).2 = (number_expr (some b) RUnaryOperand (b + 1) e').2 := rfl
private theorem number_expr_app_fst (par : Option Nat) (role : Role) (b : Nat) (head : Syntax.Expr)
    (args : List Syntax.Expr) :
    (number_expr par role b (Syntax.Application head args)).1
      = (b, mkCell VApplication role par
            ((number_args b 0 (number_expr (some b) RApplicationHead (b + 1) head).2 args).2.1 - 1)
            ((b + 1) :: (number_args b 0 (number_expr (some b) RApplicationHead (b + 1) head).2 args).2.2) 0)
        :: ((number_expr (some b) RApplicationHead (b + 1) head).1
            ++ (number_args b 0 (number_expr (some b) RApplicationHead (b + 1) head).2 args).1) := rfl
private theorem number_expr_app_snd (par : Option Nat) (role : Role) (b : Nat) (head : Syntax.Expr)
    (args : List Syntax.Expr) :
    (number_expr par role b (Syntax.Application head args)).2
      = (number_args b 0 (number_expr (some b) RApplicationHead (b + 1) head).2 args).2.1 := rfl
private theorem number_args_cons_fst (b i bi : Nat) (a : Syntax.Expr) (rest : List Syntax.Expr) :
    (number_args b i bi (a :: rest)).1
      = (number_expr (some b) (RApplicationArg i) bi a).1
        ++ (number_args b (i + 1) (number_expr (some b) (RApplicationArg i) bi a).2 rest).1 := rfl
private theorem number_args_cons_next (b i bi : Nat) (a : Syntax.Expr) (rest : List Syntax.Expr) :
    (number_args b i bi (a :: rest)).2.1
      = (number_args b (i + 1) (number_expr (some b) (RApplicationArg i) bi a).2 rest).2.1 := rfl
private theorem number_args_cons_roots (b i bi : Nat) (a : Syntax.Expr) (rest : List Syntax.Expr) :
    (number_args b i bi (a :: rest)).2.2
      = bi :: (number_args b (i + 1) (number_expr (some b) (RApplicationArg i) bi a).2 rest).2.2 := rfl
private theorem number_list_cons_fst {A : Type} (f : Nat → A → List (Nat × Cell) × Nat) (b : Nat) (x : A)
    (rest : List A) :
    (number_list f b (x :: rest)).1 = (f b x).1 ++ (number_list f (f b x).2 rest).1 := rfl
private theorem number_list_cons_next {A : Type} (f : Nat → A → List (Nat × Cell) × Nat) (b : Nat) (x : A)
    (rest : List A) :
    (number_list f b (x :: rest)).2.1 = (number_list f (f b x).2 rest).2.1 := rfl
private theorem number_list_cons_roots {A : Type} (f : Nat → A → List (Nat × Cell) × Nat) (b : Nat) (x : A)
    (rest : List A) :
    (number_list f b (x :: rest)).2.2 = b :: (number_list f (f b x).2 rest).2.2 := rfl

/-! every number_expr call emits its cells at exactly the consecutive positions [b, b+n), advancing to b+n,
    n>0 -/

-- the `.v`'s inner `assert (Hda : …)` over the inline fix, stated once about `number_args`
private theorem number_args_span_of (b : Nat) : ∀ es : List Syntax.Expr,
    (∀ a ∈ es, ∀ par role bb,
      ∃ n, List.map Prod.fst (number_expr par role bb a).1 = List.range' bb n
           ∧ (number_expr par role bb a).2 = bb + n ∧ 0 < n) →
    ∀ i0 bi, ∃ k, List.map Prod.fst (number_args b i0 bi es).1 = List.range' bi k
                  ∧ (number_args b i0 bi es).2.1 = bi + k := by
  intro es
  induction es with
  | nil => intro _ i0 bi; exact ⟨0, rfl, rfl⟩
  | cons a rest IH =>
    intro Hall i0 bi
    obtain ⟨k1, Hac1, Hbi', _⟩ := Hall a (List.Mem.head _) (some b) (RApplicationArg i0) bi
    obtain ⟨k2, Hrc, Hbf⟩ := IH (fun x hx => Hall x (List.Mem.tail _ hx)) (i0 + 1)
      (number_expr (some b) (RApplicationArg i0) bi a).2
    refine ⟨k1 + k2, ?_, ?_⟩
    · rw [number_args_cons_fst, map_app, Hac1, Hrc, Hbi', range'_app]
    · rw [number_args_cons_next, Hbf, Hbi', Nat.add_assoc]

theorem number_expr_span : ∀ e par role b,
    ∃ n, List.map Prod.fst (number_expr par role b e).1 = List.range' b n
         ∧ (number_expr par role b e).2 = b + n ∧ 0 < n := by
  intro e
  induction e using Syntax.Expr_ind' with
  | HName n => intro par role b; exact ⟨1, rfl, rfl, Nat.zero_lt_one⟩
  | HLit l => intro par role b; exact ⟨1, rfl, rfl, Nat.zero_lt_one⟩
  | HUnary op e' IH =>
    intro par role b
    obtain ⟨m, Hkc, Hnxt, _⟩ := IH (some b) RUnaryOperand (b + 1)
    refine ⟨m + 1, ?_, ?_, ?_⟩
    · rw [number_expr_unary_fst, List.map_cons, Hkc]; rfl
    · rw [number_expr_unary_snd, Hnxt, Nat.add_assoc, Nat.add_comm 1 m]
    · exact Nat.zero_lt_succ m
  | HApp head args IHh IHa =>
    intro par role b
    obtain ⟨m1, Hhc, Hb1, _⟩ := IHh (some b) RApplicationHead (b + 1)
    obtain ⟨k, Hac, Hbf⟩ := number_args_span_of b args IHa 0 (number_expr (some b) RApplicationHead (b + 1) head).2
    refine ⟨m1 + k + 1, ?_, ?_, ?_⟩
    · rw [number_expr_app_fst, List.map_cons, map_app, Hhc, Hac, Hb1, range'_app]; rfl
    · rw [number_expr_app_snd, Hbf, Hb1, Nat.add_assoc (b + 1) m1 k, Nat.add_assoc b 1 (m1 + k),
        Nat.add_comm 1 (m1 + k)]
    · exact Nat.zero_lt_succ (m1 + k)

/-! number_expr's first emitted cell is the occurrence's own root at b, carrying the passed role, view, and
    parent -/
theorem number_expr_root : ∀ e par role b,
    ∃ rest rc, (number_expr par role b e).1 = (b, rc) :: rest
               ∧ c_role rc = role ∧ c_view rc = expr_view e ∧ c_parent rc = par := by
  intro e par role b
  cases e with
  | Name n => exact ⟨_, _, rfl, rfl, rfl, rfl⟩
  | LiteralExpr l => exact ⟨_, _, rfl, rfl, rfl, rfl⟩
  | Unary op e' => exact ⟨_, _, number_expr_unary_fst par role b op e', rfl, rfl, rfl⟩
  | Application hd args => exact ⟨_, _, number_expr_app_fst par role b hd args, rfl, rfl, rfl⟩

/-! the parent inverse: every child position resolves to a member whose parent edge points back to the
    cell -/
def child_parent_ok (occs : List (Nat × Cell)) : Prop :=
  ∀ pos cell, (pos, cell) ∈ occs →
    ∀ cp, cp ∈ c_children cell →
      ∃ ccell, (cp, ccell) ∈ occs ∧ c_parent ccell = some pos

theorem child_parent_ok_app : ∀ c1 c2,
    child_parent_ok c1 → child_parent_ok c2 → child_parent_ok (c1 ++ c2) := by
  intro c1 c2 H1 H2 pos cell Hin cp Hcp
  cases mem_app_or Hin with
  | inl Hin =>
    obtain ⟨cc, Hc, Hp⟩ := H1 pos cell Hin cp Hcp
    exact ⟨cc, List.mem_append_left c2 Hc, Hp⟩
  | inr Hin =>
    obtain ⟨cc, Hc, Hp⟩ := H2 pos cell Hin cp Hcp
    exact ⟨cc, List.mem_append_right c1 Hc, Hp⟩

theorem child_parent_ok_node : ∀ self cell kids,
    (∀ cp, cp ∈ c_children cell →
       ∃ cc, (cp, cc) ∈ (self, cell) :: kids ∧ c_parent cc = some self) →
    child_parent_ok kids → child_parent_ok ((self, cell) :: kids) := by
  intro self cell kids Hself Hkids pos c Hin cp Hcp
  cases Hin with
  | head => exact Hself cp Hcp
  | tail _ Hin =>
    obtain ⟨cc, Hc, Hp⟩ := Hkids pos c Hin cp Hcp
    exact ⟨cc, List.Mem.tail _ Hc, Hp⟩

/-! the exact first-child edge law: a view carrying a required first edge has that edge at S pos, in range -/
def edge_wf (pos : Nat) (cell : Cell) (bnd : Nat) : Prop :=
  bif requires_first_edge (c_view cell) then first_child_wf (c_children cell) pos bnd else True
def ewf (occs : List (Nat × Cell)) (bnd : Nat) : Prop :=
  ∀ kv ∈ occs, edge_wf kv.1 kv.2 bnd

theorem first_child_wf_mono : ∀ ch pos m M, m ≤ M → first_child_wf ch pos m → first_child_wf ch pos M := by
  intro ch pos m M Hle
  cases ch with
  | nil => exact fun H => H
  | cons hp tl =>
    show hp = pos + 1 ∧ hp < m → hp = pos + 1 ∧ hp < M
    intro ⟨Heq, Hlt⟩
    exact ⟨Heq, Nat.lt_of_lt_of_le Hlt Hle⟩
theorem edge_wf_mono : ∀ pos cell m M, m ≤ M → edge_wf pos cell m → edge_wf pos cell M := by
  intro pos cell m M Hle
  unfold edge_wf
  cases requires_first_edge (c_view cell) with
  | true => exact first_child_wf_mono (c_children cell) pos m M Hle
  | false => exact fun H => H
theorem ewf_weaken : ∀ occs m M, m ≤ M → ewf occs m → ewf occs M :=
  fun _ m M Hle H kv Hkv => edge_wf_mono kv.1 kv.2 m M Hle (H kv Hkv)

-- Rocq's `Forall` constructors and `Forall_app`, for `ewf` (core has no `List.Forall`)
private theorem ewf_nil (bnd : Nat) : ewf [] bnd := fun _ H => nomatch H
private theorem ewf_cons (self : Nat) (cell : Cell) (kids : List (Nat × Cell)) (bnd : Nat)
    (H : edge_wf self cell bnd) (Hk : ewf kids bnd) : ewf ((self, cell) :: kids) bnd := by
  intro kv Hkv
  cases Hkv with
  | head => exact H
  | tail _ Hkv' => exact Hk kv Hkv'
private theorem ewf_app (l1 l2 : List (Nat × Cell)) (bnd : Nat) (H1 : ewf l1 bnd) (H2 : ewf l2 bnd) :
    ewf (l1 ++ l2) bnd := by
  intro kv Hkv
  cases mem_app_or Hkv with
  | inl H => exact H1 kv H
  | inr H => exact H2 kv H

-- the `.v`'s inner `assert (Hda : …)` of number_expr_edge_wf, about `number_args`
private theorem number_args_edge_wf_of (b : Nat) : ∀ es : List Syntax.Expr,
    (∀ a ∈ es, ∀ par role bb, ewf (number_expr par role bb a).1 (number_expr par role bb a).2) →
    ∀ i0 bi, ewf (number_args b i0 bi es).1 (number_args b i0 bi es).2.1
             ∧ bi ≤ (number_args b i0 bi es).2.1 := by
  intro es
  induction es with
  | nil => intro _ i0 bi; exact ⟨ewf_nil _, Nat.le_refl bi⟩
  | cons a rest IH =>
    intro Hall i0 bi
    obtain ⟨na, _, Hbi', _⟩ := number_expr_span a (some b) (RApplicationArg i0) bi
    have Ha := Hall a (List.Mem.head _) (some b) (RApplicationArg i0) bi
    obtain ⟨Hrcwf, Hle2⟩ := IH (fun x hx => Hall x (List.Mem.tail _ hx)) (i0 + 1)
      (number_expr (some b) (RApplicationArg i0) bi a).2
    rw [number_args_cons_fst, number_args_cons_next]
    exact ⟨ewf_app _ _ _ (ewf_weaken _ _ _ Hle2 Ha) Hrcwf,
           Nat.le_trans (by rw [Hbi']; exact Nat.le_add_right bi na) Hle2⟩

theorem number_expr_edge_wf : ∀ e par role b,
    ewf (number_expr par role b e).1 (number_expr par role b e).2 := by
  intro e
  induction e using Syntax.Expr_ind' with
  | HName n => intro par role b; exact ewf_cons _ _ _ _ True.intro (ewf_nil _)
  | HLit l => intro par role b; exact ewf_cons _ _ _ _ True.intro (ewf_nil _)
  | HUnary op e' IH =>
    intro par role b
    have IH' := IH (some b) RUnaryOperand (b + 1)
    obtain ⟨n1, _, Hnxt, Hn1pos⟩ := number_expr_span e' (some b) RUnaryOperand (b + 1)
    rw [number_expr_unary_fst, number_expr_unary_snd]
    exact ewf_cons _ _ _ _ (And.intro rfl (by rw [Hnxt]; exact Nat.lt_add_of_pos_right Hn1pos)) IH'
  | HApp head args IHh IHa =>
    intro par role b
    have IHh' := IHh (some b) RApplicationHead (b + 1)
    obtain ⟨nh, _, Hb1, Hnhpos⟩ := number_expr_span head (some b) RApplicationHead (b + 1)
    obtain ⟨Hacwf, Hble⟩ := number_args_edge_wf_of b args IHa 0
      (number_expr (some b) RApplicationHead (b + 1) head).2
    rw [number_expr_app_fst, number_expr_app_snd]
    exact ewf_cons _ _ _ _
      (And.intro rfl (Nat.lt_of_lt_of_le (by rw [Hb1]; exact Nat.lt_add_of_pos_right Hnhpos) Hble))
      (ewf_app _ _ _ (ewf_weaken _ _ _ Hble IHh') Hacwf)

/-! every expression's children resolve back: each child position is a member whose parent edge is this
    cell -/

private theorem cpo_leaf (v : NodeView) (par : Option Nat) (role : Role) (b : Nat) :
    child_parent_ok (number_leaf v par role b).1 := by
  intro pos c Hin cp Hcp
  have Hin' : (pos, c) ∈ [(b, mkCell v role par b [] 0)] := Hin
  cases Hin' with
  | head => exact nomatch (Hcp : cp ∈ ([] : List Nat))
  | tail _ H => exact nomatch H

-- the `.v`'s inner `assert (Hda : …)` of number_expr_cpo, about `number_args`
private theorem number_args_cpo_of (b : Nat) : ∀ es : List Syntax.Expr,
    (∀ a ∈ es, ∀ par role bb, child_parent_ok (number_expr par role bb a).1) →
    ∀ i0 bi, child_parent_ok (number_args b i0 bi es).1
             ∧ ∀ ar, ar ∈ (number_args b i0 bi es).2.2 →
                 ∃ cc, (ar, cc) ∈ (number_args b i0 bi es).1 ∧ c_parent cc = some b := by
  intro es
  induction es with
  | nil =>
    intro _ i0 bi
    exact ⟨(fun _ _ Hin => nomatch (Hin : _ ∈ ([] : List (Nat × Cell)))),
           fun _ Har => nomatch (Har : _ ∈ ([] : List Nat))⟩
  | cons a rest IH =>
    intro Hall i0 bi
    obtain ⟨arest, arc, Haroot, _, _, Hapar⟩ := number_expr_root a (some b) (RApplicationArg i0) bi
    have Ha := Hall a (List.Mem.head _) (some b) (RApplicationArg i0) bi
    obtain ⟨Hrcok, Hroots⟩ := IH (fun x hx => Hall x (List.Mem.tail _ hx)) (i0 + 1)
      (number_expr (some b) (RApplicationArg i0) bi a).2
    rw [number_args_cons_fst, number_args_cons_roots]
    refine ⟨child_parent_ok_app _ _ Ha Hrcok, ?_⟩
    intro ar Har
    cases Har with
    | head => exact ⟨arc, List.mem_append_left _ (by rw [Haroot]; exact List.Mem.head _), Hapar⟩
    | tail _ Har =>
      obtain ⟨cc, Hcc, Hccpar⟩ := Hroots ar Har
      exact ⟨cc, List.mem_append_right _ Hcc, Hccpar⟩

theorem number_expr_cpo : ∀ e par role b, child_parent_ok (number_expr par role b e).1 := by
  intro e
  induction e using Syntax.Expr_ind' with
  | HName n => intro par role b; exact cpo_leaf (VName n) par role b
  | HLit l => intro par role b; exact cpo_leaf (VLiteral l) par role b
  | HUnary op e' IH =>
    intro par role b
    have IH' := IH (some b) RUnaryOperand (b + 1)
    obtain ⟨urest, urc, Huroot, _, _, Hupar⟩ := number_expr_root e' (some b) RUnaryOperand (b + 1)
    rw [number_expr_unary_fst]
    apply child_parent_ok_node
    · intro cp Hcp
      have Hcp' : cp ∈ [b + 1] := Hcp
      cases Hcp' with
      | head => exact ⟨urc, List.Mem.tail _ (by rw [Huroot]; exact List.Mem.head _), Hupar⟩
      | tail _ H => exact nomatch H
    · exact IH'
  | HApp head args IHh IHa =>
    intro par role b
    have IHh' := IHh (some b) RApplicationHead (b + 1)
    obtain ⟨hrest, hrc, Hhroot, _, _, Hhpar⟩ := number_expr_root head (some b) RApplicationHead (b + 1)
    obtain ⟨Hacok, Haroots⟩ := number_args_cpo_of b args IHa 0
      (number_expr (some b) RApplicationHead (b + 1) head).2
    rw [number_expr_app_fst]
    apply child_parent_ok_node
    · intro cp Hcp
      have Hcp' : cp ∈ (b + 1)
          :: (number_args b 0 (number_expr (some b) RApplicationHead (b + 1) head).2 args).2.2 := Hcp
      cases Hcp' with
      | head =>
        exact ⟨hrc, List.Mem.tail _ (List.mem_append_left _ (by rw [Hhroot]; exact List.Mem.head _)), Hhpar⟩
      | tail _ H =>
        obtain ⟨cc, Hcc, Hccpar⟩ := Haroots cp H
        exact ⟨cc, List.Mem.tail _ (List.mem_append_right _ Hcc), Hccpar⟩
    · exact child_parent_ok_app _ _ IHh' Hacok

/-! coverage foundation: [spans out b] says a numbering call filled exactly the contiguous positions
    [b, b+n) -/
def spans (out : List (Nat × Cell) × Nat) (b : Nat) : Prop :=
  ∃ n, List.map Prod.fst out.1 = List.range' b n ∧ out.2 = b + n

theorem spans_app : ∀ c1 b1 c2 b2 b,
    spans (c1, b1) b → spans (c2, b2) b1 → spans (c1 ++ c2, b2) b := by
  intro c1 b1 c2 b2 b ⟨n1, H1, E1⟩ ⟨n2, H2, E2⟩
  dsimp only at H1 E1 H2 E2
  refine ⟨n1 + n2, ?_, ?_⟩
  · show List.map Prod.fst (c1 ++ c2) = List.range' b (n1 + n2)
    rw [map_app, H1, H2, E1, range'_app]
  · show b2 = b + (n1 + n2)
    rw [E2, E1, Nat.add_assoc]

theorem spans_node : ∀ self (cell : Cell) kids bfin,
    spans (kids, bfin) (self + 1) → spans ((self, cell) :: kids, bfin) self := by
  intro self cell kids bfin ⟨m, H, E⟩
  dsimp only at H E
  refine ⟨m + 1, ?_, ?_⟩
  · show List.map Prod.fst ((self, cell) :: kids) = List.range' self (m + 1)
    rw [List.map_cons, H]; rfl
  · show bfin = self + (m + 1)
    rw [E, Nat.add_assoc, Nat.add_comm 1 m]

theorem spans_leaf : ∀ v par role b, spans (number_leaf v par role b) b :=
  fun _ _ _ _ => ⟨1, rfl, rfl⟩

theorem number_expr_spans : ∀ e par role b, spans (number_expr par role b e) b := by
  intro e par role b
  obtain ⟨n, H1, H2, _⟩ := number_expr_span e par role b
  exact ⟨n, H1, H2⟩

theorem number_list_span {A : Type} (f : Nat → A → List (Nat × Cell) × Nat) :
    (∀ b x, spans (f b x) b) →
    ∀ xs b, spans (match number_list f b xs with | (c, b', _) => (c, b')) b := by
  intro Hf xs
  induction xs with
  | nil => intro b; exact ⟨0, rfl, rfl⟩
  | cons x rest IH =>
    intro b
    have Hx := Hf b x
    have IH' := IH (f b x).2
    show spans ((number_list f b (x :: rest)).1, (number_list f b (x :: rest)).2.1) b
    rw [number_list_cons_fst, number_list_cons_next]
    exact spans_app _ _ _ _ _ Hx IH'

theorem number_typeexpr_spans : ∀ par role b t, spans (number_typeexpr par role b t) b :=
  fun par role b t => spans_leaf (VTypeExpr t) par role b
theorem number_bindingname_spans : ∀ par role b bn, spans (number_bindingname par role b bn) b :=
  fun par role b bn => spans_leaf (VBindingName bn) par role b

theorem number_opttype_span : ∀ par b ot,
    spans (match number_opttype par b ot with | (c, b', _) => (c, b')) b := by
  intro par b ot
  cases ot with
  | some t => exact number_typeexpr_spans par RTypeUse b t
  | none => exact ⟨0, rfl, rfl⟩

theorem number_constspec_span : ∀ par role b cs, spans (number_constspec par role b cs) b := by
  intro par role b ⟨names, init⟩
  have Hn := number_list_span (number_bindingname (some b) (RSpecName ConstSpecF))
    (fun bb x => number_bindingname_spans (some b) (RSpecName ConstSpecF) bb x)
    (Collections.ne_to_list names) (b + 1)
  unfold number_constspec
  dsimp only
  rcases h1 : number_list (number_bindingname (some b) (RSpecName ConstSpecF)) (b + 1)
    (Collections.ne_to_list names) with ⟨nc, b1, nroots⟩
  rw [h1] at Hn
  dsimp only at Hn ⊢
  cases init with
  | ExplicitConstInit ot vals =>
    dsimp only
    have Ho := number_opttype_span (some b) b1 ot
    rcases h2 : number_opttype (some b) b1 ot with ⟨oc, b2, oroots⟩
    rw [h2] at Ho
    dsimp only at Ho ⊢
    have Hv := number_list_span (number_expr (some b) RPlain)
      (fun bb x => number_expr_spans x (some b) RPlain bb) (Collections.ne_to_list vals) b2
    rcases h3 : number_list (number_expr (some b) RPlain) b2 (Collections.ne_to_list vals)
      with ⟨vc, b3, vroots⟩
    rw [h3] at Hv
    dsimp only at Hv ⊢
    apply spans_node
    exact spans_app nc b1 (oc ++ vc) b3 (b + 1) Hn (spans_app oc b2 vc b3 b1 Ho Hv)
  | InheritedConstInit =>
    dsimp only
    apply spans_node
    rw [app_nil]
    exact Hn

theorem number_varspec_span : ∀ par role b vs, spans (number_varspec par role b vs) b := by
  intro par role b ⟨names, init⟩
  have Hn := number_list_span (number_bindingname (some b) (RSpecName VarSpecF))
    (fun bb x => number_bindingname_spans (some b) (RSpecName VarSpecF) bb x)
    (Collections.ne_to_list names) (b + 1)
  unfold number_varspec
  dsimp only
  rcases h1 : number_list (number_bindingname (some b) (RSpecName VarSpecF)) (b + 1)
    (Collections.ne_to_list names) with ⟨nc, b1, nroots⟩
  rw [h1] at Hn
  dsimp only at Hn ⊢
  cases init with
  | VarTypeOnly t =>
    dsimp only
    have Ht := number_typeexpr_spans (some b) RTypeUse b1 t
    rcases h2 : number_typeexpr (some b) RTypeUse b1 t with ⟨c, b2⟩
    rw [h2] at Ht
    dsimp only
    apply spans_node
    exact spans_app nc b1 c b2 (b + 1) Hn Ht
  | VarValues ot vals =>
    dsimp only
    have Ho := number_opttype_span (some b) b1 ot
    rcases h2 : number_opttype (some b) b1 ot with ⟨oc, b2, oroots⟩
    rw [h2] at Ho
    dsimp only at Ho ⊢
    have Hv := number_list_span (number_expr (some b) RPlain)
      (fun bb x => number_expr_spans x (some b) RPlain bb) (Collections.ne_to_list vals) b2
    rcases h3 : number_list (number_expr (some b) RPlain) b2 (Collections.ne_to_list vals)
      with ⟨vc, b3, vroots⟩
    rw [h3] at Hv
    dsimp only at Hv ⊢
    apply spans_node
    exact spans_app nc b1 (oc ++ vc) b3 (b + 1) Hn (spans_app oc b2 vc b3 b1 Ho Hv)

theorem number_typespec_span : ∀ par role b ts, spans (number_typespec par role b ts) b := by
  intro par role b ts
  cases ts with
  | AliasSpec bn t | DefSpec bn t =>
    unfold number_typespec
    dsimp only
    have Hb := number_bindingname_spans (some b) (RSpecName TypeSpecF) (b + 1) bn
    rcases h1 : number_bindingname (some b) (RSpecName TypeSpecF) (b + 1) bn with ⟨bc, b1⟩
    rw [h1] at Hb
    have Ht := number_typeexpr_spans (some b) RTypeUse b1 t
    rcases h2 : number_typeexpr (some b) RTypeUse b1 t with ⟨tc, bfin⟩
    rw [h2] at Ht
    dsimp only
    apply spans_node
    exact spans_app bc b1 tc bfin (b + 1) Hb Ht

theorem number_decl_span : ∀ par role b d, spans (number_decl par role b d) b := by
  intro par role b d
  cases d with
  | ConstDecl cs =>
    unfold number_decl
    dsimp only
    have Hs := number_list_span (number_constspec (some b) RPlain)
      (fun bb x => number_constspec_span (some b) RPlain bb x) cs (b + 1)
    rcases h : number_list (number_constspec (some b) RPlain) (b + 1) cs with ⟨kc, bfin, roots⟩
    rw [h] at Hs
    dsimp only at Hs ⊢
    apply spans_node
    exact Hs
  | VarDecl vs =>
    unfold number_decl
    dsimp only
    have Hs := number_list_span (number_varspec (some b) RPlain)
      (fun bb x => number_varspec_span (some b) RPlain bb x) vs (b + 1)
    rcases h : number_list (number_varspec (some b) RPlain) (b + 1) vs with ⟨kc, bfin, roots⟩
    rw [h] at Hs
    dsimp only at Hs ⊢
    apply spans_node
    exact Hs
  | TypeDecl ts =>
    unfold number_decl
    dsimp only
    have Hs := number_list_span (number_typespec (some b) RPlain)
      (fun bb x => number_typespec_span (some b) RPlain bb x) ts (b + 1)
    rcases h : number_list (number_typespec (some b) RPlain) (b + 1) ts with ⟨kc, bfin, roots⟩
    rw [h] at Hs
    dsimp only at Hs ⊢
    apply spans_node
    exact Hs

theorem number_stmt_span : ∀ par role b s, spans (number_stmt par role b s) b := by
  intro par role b s
  cases s with
  | ExprStmt e =>
    unfold number_stmt
    dsimp only
    have He := number_expr_spans e (some b) RExprStatementExpr (b + 1)
    rcases h : number_expr (some b) RExprStatementExpr (b + 1) e with ⟨c, b'⟩
    rw [h] at He
    dsimp only
    apply spans_node
    exact He
  | DeclarationStmt d =>
    unfold number_stmt
    dsimp only
    have Hd := number_decl_span (some b) RPlain (b + 1) d
    rcases h : number_decl (some b) RPlain (b + 1) d with ⟨c, b'⟩
    rw [h] at Hd
    dsimp only
    apply spans_node
    exact Hd
  | ShortVarDecl names vals =>
    unfold number_stmt
    dsimp only
    have Hn := number_list_span (number_bindingname (some b) RShortLhs)
      (fun bb x => number_bindingname_spans (some b) RShortLhs bb x) (Collections.ne_to_list names) (b + 1)
    rcases h1 : number_list (number_bindingname (some b) RShortLhs) (b + 1) (Collections.ne_to_list names)
      with ⟨nc, b1, nroots⟩
    rw [h1] at Hn
    have Hv := number_list_span (number_expr (some b) RPlain)
      (fun bb x => number_expr_spans x (some b) RPlain bb) (Collections.ne_to_list vals) b1
    rcases h2 : number_list (number_expr (some b) RPlain) b1 (Collections.ne_to_list vals)
      with ⟨vc, b2, vroots⟩
    rw [h2] at Hv
    dsimp only at Hn Hv ⊢
    apply spans_node
    exact spans_app nc b1 vc b2 (b + 1) Hn Hv

theorem number_block_span : ∀ par role b blk, spans (number_block par role b blk) b := by
  intro par role b ⟨stmts⟩
  unfold number_block
  dsimp only
  have Hs := number_list_span (number_stmt (some b) RPlain)
    (fun bb x => number_stmt_span (some b) RPlain bb x) stmts (b + 1)
  rcases h : number_list (number_stmt (some b) RPlain) (b + 1) stmts with ⟨kc, bfin, roots⟩
  rw [h] at Hs
  dsimp only at Hs ⊢
  apply spans_node
  exact Hs

theorem number_toplevel_span : ∀ par role b td, spans (number_toplevel par role b td) b := by
  intro par role b td
  cases td with
  | TopDeclaration d =>
    unfold number_toplevel
    dsimp only
    have Hd := number_decl_span (some b) RPlain (b + 1) d
    rcases h : number_decl (some b) RPlain (b + 1) d with ⟨c, b'⟩
    rw [h] at Hd
    dsimp only
    apply spans_node
    exact Hd
  | Main blk =>
    unfold number_toplevel
    dsimp only
    have Hb := number_block_span (some b) RPlain (b + 1) blk
    rcases h : number_block (some b) RPlain (b + 1) blk with ⟨c, b'⟩
    rw [h] at Hb
    dsimp only
    apply spans_node
    exact Hb

/-! file coverage: occurrence positions are exactly the contiguous source-preorder block [0, n) from the
    file root -/
theorem number_file_positions : ∀ f, ∃ n, List.map Prod.fst (number_file f) = List.range n := by
  intro f
  unfold number_file
  have Hs := number_list_span (number_toplevel (some 0) RPlain)
    (fun bb x => number_toplevel_span (some 0) RPlain bb x) (Syntax.declarations f) 1
  rcases h : number_list (number_toplevel (some 0) RPlain) 1 (Syntax.declarations f) with ⟨dc, bfin, droots⟩
  rw [h] at Hs
  dsimp only at Hs ⊢
  obtain ⟨m, Hdc, _⟩ := Hs
  dsimp only at Hdc
  refine ⟨m + 1, ?_⟩
  rw [List.map_cons, Hdc, List.range_eq_range']
  rfl

/-! the exact first-edge law over a whole file numbering: each required first edge is S-of-its-position, in
    range -/
theorem span_final_ge : ∀ out b, spans out b → b ≤ out.2 := by
  intro out b ⟨n, _, H⟩
  rw [H]
  exact Nat.le_add_right b n

theorem ewf_node : ∀ self cell kids bnd,
    edge_wf self cell bnd → ewf kids bnd → ewf ((self, cell) :: kids) bnd := ewf_cons

theorem number_list_edge_wf {A : Type} (f : Nat → A → List (Nat × Cell) × Nat) :
    (∀ b x, ewf (f b x).1 (f b x).2) →
    (∀ b x, b ≤ (f b x).2) →
    ∀ b xs, ewf (number_list f b xs).1 (number_list f b xs).2.1
            ∧ b ≤ (number_list f b xs).2.1 := by
  intro Hf Hmono b xs
  induction xs generalizing b with
  | nil => exact ⟨ewf_nil _, Nat.le_refl b⟩
  | cons x rest IH =>
    have Hfx := Hf b x
    have Hm := Hmono b x
    obtain ⟨Hrc, Hle⟩ := IH (f b x).2
    rw [number_list_cons_fst, number_list_cons_next]
    exact ⟨ewf_app _ _ _ (ewf_weaken _ _ _ Hle Hfx) Hrc, Nat.le_trans Hm Hle⟩

theorem number_typeexpr_edge_wf : ∀ par role b t,
    ewf (number_typeexpr par role b t).1 (number_typeexpr par role b t).2 :=
  fun _ _ _ _ => ewf_node _ _ _ _ True.intro (ewf_nil _)
theorem number_bindingname_edge_wf : ∀ par role b bn,
    ewf (number_bindingname par role b bn).1 (number_bindingname par role b bn).2 :=
  fun _ _ _ _ => ewf_node _ _ _ _ True.intro (ewf_nil _)

theorem number_opttype_edge_wf : ∀ par b ot,
    ewf (number_opttype par b ot).1 (number_opttype par b ot).2.1 := by
  intro par b ot
  cases ot with
  | some t => exact number_typeexpr_edge_wf par RTypeUse b t
  | none => exact ewf_nil _

theorem number_constspec_edge_wf : ∀ par role b cs,
    ewf (number_constspec par role b cs).1 (number_constspec par role b cs).2 := by
  intro par role b ⟨names, init⟩
  obtain ⟨Hnc, _⟩ := number_list_edge_wf (number_bindingname (some b) (RSpecName ConstSpecF))
    (fun bb x => number_bindingname_edge_wf (some b) (RSpecName ConstSpecF) bb x)
    (fun bb x => span_final_ge _ _ (number_bindingname_spans (some b) (RSpecName ConstSpecF) bb x))
    (b + 1) (Collections.ne_to_list names)
  unfold number_constspec
  dsimp only
  rcases h1 : number_list (number_bindingname (some b) (RSpecName ConstSpecF)) (b + 1)
    (Collections.ne_to_list names) with ⟨nc, b1, nroots⟩
  rw [h1] at Hnc
  dsimp only at Hnc ⊢
  cases init with
  | ExplicitConstInit ot vals =>
    dsimp only
    have Hoc := number_opttype_edge_wf (some b) b1 ot
    have Hocle := span_final_ge _ _ (number_opttype_span (some b) b1 ot)
    rcases h2 : number_opttype (some b) b1 ot with ⟨oc, b2, oroots⟩
    rw [h2] at Hoc Hocle
    dsimp only at Hoc Hocle ⊢
    obtain ⟨Hvc, Hvcle⟩ := number_list_edge_wf (number_expr (some b) RPlain)
      (fun bb x => number_expr_edge_wf x (some b) RPlain bb)
      (fun bb x => span_final_ge _ _ (number_expr_spans x (some b) RPlain bb))
      b2 (Collections.ne_to_list vals)
    rcases h3 : number_list (number_expr (some b) RPlain) b2 (Collections.ne_to_list vals)
      with ⟨vc, b3, vroots⟩
    rw [h3] at Hvc Hvcle
    dsimp only at Hvc Hvcle ⊢
    exact ewf_node _ _ _ _ True.intro
      (ewf_app _ _ _ (ewf_weaken _ _ _ (Nat.le_trans Hocle Hvcle) Hnc)
        (ewf_app _ _ _ (ewf_weaken _ _ _ Hvcle Hoc) Hvc))
  | InheritedConstInit =>
    dsimp only
    exact ewf_node _ _ _ _ True.intro (ewf_app _ _ _ Hnc (ewf_nil _))

theorem number_varspec_edge_wf : ∀ par role b vs,
    ewf (number_varspec par role b vs).1 (number_varspec par role b vs).2 := by
  intro par role b ⟨names, init⟩
  obtain ⟨Hnc, _⟩ := number_list_edge_wf (number_bindingname (some b) (RSpecName VarSpecF))
    (fun bb x => number_bindingname_edge_wf (some b) (RSpecName VarSpecF) bb x)
    (fun bb x => span_final_ge _ _ (number_bindingname_spans (some b) (RSpecName VarSpecF) bb x))
    (b + 1) (Collections.ne_to_list names)
  unfold number_varspec
  dsimp only
  rcases h1 : number_list (number_bindingname (some b) (RSpecName VarSpecF)) (b + 1)
    (Collections.ne_to_list names) with ⟨nc, b1, nroots⟩
  rw [h1] at Hnc
  dsimp only at Hnc ⊢
  cases init with
  | VarTypeOnly t =>
    dsimp only
    have Ht := number_typeexpr_edge_wf (some b) RTypeUse b1 t
    have Htle := span_final_ge _ _ (number_typeexpr_spans (some b) RTypeUse b1 t)
    rcases h2 : number_typeexpr (some b) RTypeUse b1 t with ⟨c, b2⟩
    rw [h2] at Ht Htle
    dsimp only at Ht Htle ⊢
    exact ewf_node _ _ _ _ True.intro (ewf_app _ _ _ (ewf_weaken _ _ _ Htle Hnc) Ht)
  | VarValues ot vals =>
    dsimp only
    have Hoc := number_opttype_edge_wf (some b) b1 ot
    have Hocle := span_final_ge _ _ (number_opttype_span (some b) b1 ot)
    rcases h2 : number_opttype (some b) b1 ot with ⟨oc, b2, oroots⟩
    rw [h2] at Hoc Hocle
    dsimp only at Hoc Hocle ⊢
    obtain ⟨Hvc, Hvcle⟩ := number_list_edge_wf (number_expr (some b) RPlain)
      (fun bb x => number_expr_edge_wf x (some b) RPlain bb)
      (fun bb x => span_final_ge _ _ (number_expr_spans x (some b) RPlain bb))
      b2 (Collections.ne_to_list vals)
    rcases h3 : number_list (number_expr (some b) RPlain) b2 (Collections.ne_to_list vals)
      with ⟨vc, b3, vroots⟩
    rw [h3] at Hvc Hvcle
    dsimp only at Hvc Hvcle ⊢
    exact ewf_node _ _ _ _ True.intro
      (ewf_app _ _ _ (ewf_weaken _ _ _ (Nat.le_trans Hocle Hvcle) Hnc)
        (ewf_app _ _ _ (ewf_weaken _ _ _ Hvcle Hoc) Hvc))

theorem number_typespec_edge_wf : ∀ par role b ts,
    ewf (number_typespec par role b ts).1 (number_typespec par role b ts).2 := by
  intro par role b ts
  cases ts with
  | AliasSpec bn t | DefSpec bn t =>
    unfold number_typespec
    dsimp only
    have Hbc := number_bindingname_edge_wf (some b) (RSpecName TypeSpecF) (b + 1) bn
    rcases h1 : number_bindingname (some b) (RSpecName TypeSpecF) (b + 1) bn with ⟨bc, b1⟩
    rw [h1] at Hbc
    have Htc := number_typeexpr_edge_wf (some b) RTypeUse b1 t
    have Htcle := span_final_ge _ _ (number_typeexpr_spans (some b) RTypeUse b1 t)
    rcases h2 : number_typeexpr (some b) RTypeUse b1 t with ⟨tc, bfin⟩
    rw [h2] at Htc Htcle
    dsimp only at Hbc Htc Htcle ⊢
    exact ewf_node _ _ _ _ True.intro (ewf_app _ _ _ (ewf_weaken _ _ _ Htcle Hbc) Htc)

theorem number_decl_edge_wf : ∀ par role b d,
    ewf (number_decl par role b d).1 (number_decl par role b d).2 := by
  intro par role b d
  cases d with
  | ConstDecl cs =>
    unfold number_decl
    dsimp only
    obtain ⟨Hk, _⟩ := number_list_edge_wf (number_constspec (some b) RPlain)
      (fun bb x => number_constspec_edge_wf (some b) RPlain bb x)
      (fun bb x => span_final_ge _ _ (number_constspec_span (some b) RPlain bb x)) (b + 1) cs
    rcases h : number_list (number_constspec (some b) RPlain) (b + 1) cs with ⟨kc, bfin, roots⟩
    rw [h] at Hk
    dsimp only at Hk ⊢
    exact ewf_node _ _ _ _ True.intro Hk
  | VarDecl vs =>
    unfold number_decl
    dsimp only
    obtain ⟨Hk, _⟩ := number_list_edge_wf (number_varspec (some b) RPlain)
      (fun bb x => number_varspec_edge_wf (some b) RPlain bb x)
      (fun bb x => span_final_ge _ _ (number_varspec_span (some b) RPlain bb x)) (b + 1) vs
    rcases h : number_list (number_varspec (some b) RPlain) (b + 1) vs with ⟨kc, bfin, roots⟩
    rw [h] at Hk
    dsimp only at Hk ⊢
    exact ewf_node _ _ _ _ True.intro Hk
  | TypeDecl ts =>
    unfold number_decl
    dsimp only
    obtain ⟨Hk, _⟩ := number_list_edge_wf (number_typespec (some b) RPlain)
      (fun bb x => number_typespec_edge_wf (some b) RPlain bb x)
      (fun bb x => span_final_ge _ _ (number_typespec_span (some b) RPlain bb x)) (b + 1) ts
    rcases h : number_list (number_typespec (some b) RPlain) (b + 1) ts with ⟨kc, bfin, roots⟩
    rw [h] at Hk
    dsimp only at Hk ⊢
    exact ewf_node _ _ _ _ True.intro Hk

theorem number_stmt_edge_wf : ∀ par role b s,
    ewf (number_stmt par role b s).1 (number_stmt par role b s).2 := by
  intro par role b s
  cases s with
  | ExprStmt e =>
    unfold number_stmt
    dsimp only
    have He := number_expr_edge_wf e (some b) RExprStatementExpr (b + 1)
    obtain ⟨ne, _, Hb', Hnepos⟩ := number_expr_span e (some b) RExprStatementExpr (b + 1)
    rcases h : number_expr (some b) RExprStatementExpr (b + 1) e with ⟨c, b'⟩
    rw [h] at He Hb'
    dsimp only at He Hb' ⊢
    exact ewf_node _ _ _ _ (And.intro rfl (by rw [Hb']; exact Nat.lt_add_of_pos_right Hnepos)) He
  | DeclarationStmt d =>
    unfold number_stmt
    dsimp only
    have Hd := number_decl_edge_wf (some b) RPlain (b + 1) d
    rcases h : number_decl (some b) RPlain (b + 1) d with ⟨c, b'⟩
    rw [h] at Hd
    dsimp only at Hd ⊢
    exact ewf_node _ _ _ _ True.intro Hd
  | ShortVarDecl names vals =>
    unfold number_stmt
    dsimp only
    obtain ⟨Hnc, _⟩ := number_list_edge_wf (number_bindingname (some b) RShortLhs)
      (fun bb x => number_bindingname_edge_wf (some b) RShortLhs bb x)
      (fun bb x => span_final_ge _ _ (number_bindingname_spans (some b) RShortLhs bb x))
      (b + 1) (Collections.ne_to_list names)
    rcases h1 : number_list (number_bindingname (some b) RShortLhs) (b + 1) (Collections.ne_to_list names)
      with ⟨nc, b1, nroots⟩
    rw [h1] at Hnc
    dsimp only at Hnc ⊢
    obtain ⟨Hvc, Hvcle⟩ := number_list_edge_wf (number_expr (some b) RPlain)
      (fun bb x => number_expr_edge_wf x (some b) RPlain bb)
      (fun bb x => span_final_ge _ _ (number_expr_spans x (some b) RPlain bb))
      b1 (Collections.ne_to_list vals)
    rcases h2 : number_list (number_expr (some b) RPlain) b1 (Collections.ne_to_list vals)
      with ⟨vc, b2, vroots⟩
    rw [h2] at Hvc Hvcle
    dsimp only at Hvc Hvcle ⊢
    exact ewf_node _ _ _ _ True.intro (ewf_app _ _ _ (ewf_weaken _ _ _ Hvcle Hnc) Hvc)

theorem number_block_edge_wf : ∀ par role b blk,
    ewf (number_block par role b blk).1 (number_block par role b blk).2 := by
  intro par role b ⟨stmts⟩
  unfold number_block
  dsimp only
  obtain ⟨Hk, _⟩ := number_list_edge_wf (number_stmt (some b) RPlain)
    (fun bb x => number_stmt_edge_wf (some b) RPlain bb x)
    (fun bb x => span_final_ge _ _ (number_stmt_span (some b) RPlain bb x)) (b + 1) stmts
  rcases h : number_list (number_stmt (some b) RPlain) (b + 1) stmts with ⟨kc, bfin, roots⟩
  rw [h] at Hk
  dsimp only at Hk ⊢
  exact ewf_node _ _ _ _ True.intro Hk

theorem number_toplevel_edge_wf : ∀ par role b td,
    ewf (number_toplevel par role b td).1 (number_toplevel par role b td).2 := by
  intro par role b td
  cases td with
  | TopDeclaration d =>
    unfold number_toplevel
    dsimp only
    have Hd := number_decl_edge_wf (some b) RPlain (b + 1) d
    rcases h : number_decl (some b) RPlain (b + 1) d with ⟨c, b'⟩
    rw [h] at Hd
    dsimp only at Hd ⊢
    exact ewf_node _ _ _ _ True.intro Hd
  | Main blk =>
    unfold number_toplevel
    dsimp only
    have Hb := number_block_edge_wf (some b) RPlain (b + 1) blk
    rcases h : number_block (some b) RPlain (b + 1) blk with ⟨c, b'⟩
    rw [h] at Hb
    dsimp only at Hb ⊢
    exact ewf_node _ _ _ _ True.intro Hb

theorem number_file_edge_wf : ∀ f, ewf (number_file f) (List.length (number_file f)) := by
  intro f
  unfold number_file
  obtain ⟨Hd, _⟩ := number_list_edge_wf (number_toplevel (some 0) RPlain)
    (fun bb x => number_toplevel_edge_wf (some 0) RPlain bb x)
    (fun bb x => span_final_ge _ _ (number_toplevel_span (some 0) RPlain bb x)) 1 (Syntax.declarations f)
  have Hsp := number_list_span (number_toplevel (some 0) RPlain)
    (fun bb x => number_toplevel_span (some 0) RPlain bb x) (Syntax.declarations f) 1
  rcases h : number_list (number_toplevel (some 0) RPlain) 1 (Syntax.declarations f) with ⟨dc, bfin, droots⟩
  rw [h] at Hd Hsp
  dsimp only at Hd Hsp ⊢
  obtain ⟨ntop, Hmap, Hbfin⟩ := Hsp
  dsimp only at Hmap Hbfin
  have Hlen : List.length dc = ntop := by
    have H := congrArg List.length Hmap
    rw [length_map, List.length_range'] at H
    exact H
  show ewf ((0, mkCell VFile RPlain none (bfin - 1) droots 0) :: dc) (List.length dc + 1)
  exact ewf_node _ _ _ _ True.intro
    (ewf_weaken _ _ _ (Nat.le_of_eq (by rw [Hbfin, Hlen, Nat.add_comm 1 ntop])) Hd)

/-! [roots_resolve occs self roots]: every root position is a member of [occs] whose parent edge is
    [self] -/
def roots_resolve (occs : List (Nat × Cell)) (self : Nat) (roots : List Nat) : Prop :=
  ∀ ar, ar ∈ roots → ∃ cc, (ar, cc) ∈ occs ∧ c_parent cc = some self

theorem roots_resolve_app_l : ∀ occs extra self roots,
    roots_resolve occs self roots → roots_resolve (occs ++ extra) self roots := by
  intro occs extra self roots H ar Har
  obtain ⟨cc, Hin, Hpar⟩ := H ar Har
  exact ⟨cc, List.mem_append_left extra Hin, Hpar⟩

theorem roots_resolve_app_r : ∀ occs extra self roots,
    roots_resolve occs self roots → roots_resolve (extra ++ occs) self roots := by
  intro occs extra self roots H ar Har
  obtain ⟨cc, Hin, Hpar⟩ := H ar Har
  exact ⟨cc, List.mem_append_right extra Hin, Hpar⟩

theorem roots_resolve_concat : ∀ occs self r1 r2,
    roots_resolve occs self r1 → roots_resolve occs self r2 → roots_resolve occs self (r1 ++ r2) := by
  intro occs self r1 r2 H1 H2 ar Har
  cases mem_app_or Har with
  | inl Har => exact H1 ar Har
  | inr Har => exact H2 ar Har

theorem cpo_node : ∀ self cell kids,
    roots_resolve kids self (c_children cell) →
    child_parent_ok kids → child_parent_ok ((self, cell) :: kids) := by
  intro self cell kids Hres Hkids
  apply child_parent_ok_node
  · intro cp Hcp
    obtain ⟨cc, Hin, Hpar⟩ := Hres cp Hcp
    exact ⟨cc, List.Mem.tail _ Hin, Hpar⟩
  · exact Hkids

/-! one sublist numbered by [g]: its cells resolve internally and its roots point back to the shared
    parent -/
theorem number_list_cpo {A : Type} (g : Nat → A → List (Nat × Cell) × Nat) (par : Nat) :
    (∀ b x, child_parent_ok (g b x).1) →
    (∀ b x, ∃ cc rest, (g b x).1 = (b, cc) :: rest ∧ c_parent cc = some par) →
    ∀ b xs,
      child_parent_ok (number_list g b xs).1 ∧
      roots_resolve (number_list g b xs).1 par (number_list g b xs).2.2 := by
  intro Hcpo Hroot b xs
  induction xs generalizing b with
  | nil =>
    exact ⟨(fun _ _ Hin => nomatch (Hin : _ ∈ ([] : List (Nat × Cell)))),
           fun _ Har => nomatch (Har : _ ∈ ([] : List Nat))⟩
  | cons x rest IH =>
    obtain ⟨rc, rest', Hgx, Hrcpar⟩ := Hroot b x
    have Hc := Hcpo b x
    obtain ⟨Hcpol, Hresl⟩ := IH (g b x).2
    rw [number_list_cons_fst, number_list_cons_roots]
    refine ⟨child_parent_ok_app _ _ Hc Hcpol, ?_⟩
    intro ar Har
    cases Har with
    | head => exact ⟨rc, List.mem_append_left _ (by rw [Hgx]; exact List.Mem.head _), Hrcpar⟩
    | tail _ Har =>
      obtain ⟨cc, Hin, Hpar⟩ := Hresl ar Har
      exact ⟨cc, List.mem_append_right _ Hin, Hpar⟩

/-! ## Section 2 (`.v` lines 651–1600) -/

/-! ### the `.v`'s stdlib facts this section adds (`in_map`, `in_seq`, `seq_NoDup`), by hand -/

-- Rocq: `in_map`, by induction on the membership (core's `List.mem_map_of_mem` goes through `simp`).
private theorem mem_map_of_mem {A B : Type} (f : A → B) :
    ∀ {a : A} {l : List A}, a ∈ l → f a ∈ List.map f l := by
  intro a l H
  induction H with
  | head _ => exact List.Mem.head _
  | tail _ _ IH => exact List.Mem.tail _ IH

-- Rocq: `in_seq`, the forward direction, on `range'` (`seq 0 n` is `List.range n = List.range' 0 n`).
private theorem mem_range'_bounds : ∀ {n s x : Nat}, x ∈ List.range' s n → s ≤ x ∧ x < s + n := by
  intro n
  induction n with
  | zero => intro s x H; exact nomatch H
  | succ n IH =>
    intro s x H
    have H' : x ∈ s :: List.range' (s + 1) n := H
    cases H' with
    | head => exact ⟨Nat.le_refl s, Nat.lt_add_of_pos_right (Nat.zero_lt_succ n)⟩
    | tail _ H'' =>
      obtain ⟨H1, H2⟩ := IH H''
      exact ⟨Nat.le_trans (Nat.le_succ s) H1, by rw [Nat.add_succ, ← Nat.succ_add]; exact H2⟩

-- Rocq: `seq_NoDup`, on `range'`.
private theorem nodup_range' : ∀ (n s : Nat), List.Nodup (List.range' s n)
  | 0, _ => List.Pairwise.nil
  | n + 1, s =>
    List.Pairwise.cons
      (fun _ Hx Heq => Nat.not_succ_le_self s (Heq ▸ (mem_range'_bounds Hx).1))
      (nodup_range' n (s + 1))

/-! ### each composite occurrence begins with its own cell, carrying the passed parent edge — the root fact -/

theorem number_expr_root' : ∀ par role b e,
    ∃ cc rest, (number_expr par role b e).1 = (b, cc) :: rest ∧ c_parent cc = par := by
  intro par role b e
  obtain ⟨rest, rc, H, _, _, Hpar⟩ := number_expr_root e par role b
  exact ⟨rc, rest, H, Hpar⟩

theorem number_typeexpr_root : ∀ par role b t,
    ∃ cc rest, (number_typeexpr par role b t).1 = (b, cc) :: rest ∧ c_parent cc = par :=
  fun _ _ _ _ => ⟨_, _, rfl, rfl⟩

theorem number_bindingname_root : ∀ par role b bn,
    ∃ cc rest, (number_bindingname par role b bn).1 = (b, cc) :: rest ∧ c_parent cc = par :=
  fun _ _ _ _ => ⟨_, _, rfl, rfl⟩

theorem number_constspec_root : ∀ par role b cs,
    ∃ cc rest, (number_constspec par role b cs).1 = (b, cc) :: rest ∧ c_parent cc = par := by
  intro par role b ⟨names, init⟩
  cases init with
  | ExplicitConstInit ot vals => exact ⟨_, _, rfl, rfl⟩
  | InheritedConstInit => exact ⟨_, _, rfl, rfl⟩

theorem number_varspec_root : ∀ par role b vs,
    ∃ cc rest, (number_varspec par role b vs).1 = (b, cc) :: rest ∧ c_parent cc = par := by
  intro par role b ⟨names, init⟩
  cases init with
  | VarTypeOnly t => exact ⟨_, _, rfl, rfl⟩
  | VarValues ot vals => exact ⟨_, _, rfl, rfl⟩

theorem number_typespec_root : ∀ par role b ts,
    ∃ cc rest, (number_typespec par role b ts).1 = (b, cc) :: rest ∧ c_parent cc = par := by
  intro par role b ts
  cases ts with
  | AliasSpec bn t | DefSpec bn t => exact ⟨_, _, rfl, rfl⟩

theorem number_decl_root : ∀ par role b d,
    ∃ cc rest, (number_decl par role b d).1 = (b, cc) :: rest ∧ c_parent cc = par := by
  intro par role b d
  cases d with
  | ConstDecl cs => exact ⟨_, _, rfl, rfl⟩
  | VarDecl vs => exact ⟨_, _, rfl, rfl⟩
  | TypeDecl ts => exact ⟨_, _, rfl, rfl⟩

theorem number_stmt_root : ∀ par role b s,
    ∃ cc rest, (number_stmt par role b s).1 = (b, cc) :: rest ∧ c_parent cc = par := by
  intro par role b s
  cases s with
  | ExprStmt e => exact ⟨_, _, rfl, rfl⟩
  | DeclarationStmt d => exact ⟨_, _, rfl, rfl⟩
  | ShortVarDecl names vals => exact ⟨_, _, rfl, rfl⟩

theorem number_block_root : ∀ par role b blk,
    ∃ cc rest, (number_block par role b blk).1 = (b, cc) :: rest ∧ c_parent cc = par := by
  intro par role b ⟨stmts⟩
  exact ⟨_, _, rfl, rfl⟩

theorem number_toplevel_root : ∀ par role b td,
    ∃ cc rest, (number_toplevel par role b td).1 = (b, cc) :: rest ∧ c_parent cc = par := by
  intro par role b td
  cases td with
  | TopDeclaration d => exact ⟨_, _, rfl, rfl⟩
  | Main blk => exact ⟨_, _, rfl, rfl⟩

/-! ### the parent inverse for every composite, then the whole file -/

theorem number_typeexpr_cpo : ∀ par role b t, child_parent_ok (number_typeexpr par role b t).1 :=
  fun par role b t => cpo_leaf (VTypeExpr t) par role b

theorem number_bindingname_cpo : ∀ par role b bn, child_parent_ok (number_bindingname par role b bn).1 :=
  fun par role b bn => cpo_leaf (VBindingName bn) par role b

theorem number_opttype_cpo : ∀ self b ot,
    child_parent_ok (number_opttype (some self) b ot).1 ∧
    roots_resolve (number_opttype (some self) b ot).1 self (number_opttype (some self) b ot).2.2 := by
  intro self b ot
  cases ot with
  | some t =>
    refine ⟨number_typeexpr_cpo (some self) RTypeUse b t, ?_⟩
    intro ar Har
    have Har' : ar ∈ [b] := Har
    cases Har' with
    | head => exact ⟨_, List.Mem.head _, rfl⟩
    | tail _ H => exact nomatch H
  | none =>
    exact ⟨(fun _ _ Hin => nomatch (Hin : _ ∈ ([] : List (Nat × Cell)))),
           fun _ Har => nomatch (Har : _ ∈ ([] : List Nat))⟩

theorem number_constspec_cpo : ∀ par role b cs, child_parent_ok (number_constspec par role b cs).1 := by
  intro par role b ⟨names, init⟩
  obtain ⟨Hnc_cpo, Hnc_res⟩ := number_list_cpo (number_bindingname (some b) (RSpecName ConstSpecF)) b
    (fun bb x => number_bindingname_cpo (some b) (RSpecName ConstSpecF) bb x)
    (fun bb x => number_bindingname_root (some b) (RSpecName ConstSpecF) bb x)
    (b + 1) (Collections.ne_to_list names)
  unfold number_constspec
  dsimp only
  rcases h1 : number_list (number_bindingname (some b) (RSpecName ConstSpecF)) (b + 1)
    (Collections.ne_to_list names) with ⟨nc, b1, nroots⟩
  rw [h1] at Hnc_cpo Hnc_res
  dsimp only at Hnc_cpo Hnc_res ⊢
  cases init with
  | ExplicitConstInit ot vals =>
    dsimp only
    obtain ⟨Hoc_cpo, Hoc_res⟩ := number_opttype_cpo b b1 ot
    rcases h2 : number_opttype (some b) b1 ot with ⟨oc, b2, oroots⟩
    rw [h2] at Hoc_cpo Hoc_res
    dsimp only at Hoc_cpo Hoc_res ⊢
    obtain ⟨Hvc_cpo, Hvc_res⟩ := number_list_cpo (number_expr (some b) RPlain) b
      (fun bb x => number_expr_cpo x (some b) RPlain bb)
      (fun bb x => number_expr_root' (some b) RPlain bb x)
      b2 (Collections.ne_to_list vals)
    rcases h3 : number_list (number_expr (some b) RPlain) b2 (Collections.ne_to_list vals)
      with ⟨vc, b3, vroots⟩
    rw [h3] at Hvc_cpo Hvc_res
    dsimp only at Hvc_cpo Hvc_res ⊢
    apply cpo_node
    · show roots_resolve (nc ++ (oc ++ vc)) b (nroots ++ (oroots ++ vroots))
      exact roots_resolve_concat _ _ _ _ (roots_resolve_app_l _ _ _ _ Hnc_res)
        (roots_resolve_app_r _ _ _ _ (roots_resolve_concat _ _ _ _
          (roots_resolve_app_l _ _ _ _ Hoc_res) (roots_resolve_app_r _ _ _ _ Hvc_res)))
    · exact child_parent_ok_app _ _ Hnc_cpo (child_parent_ok_app _ _ Hoc_cpo Hvc_cpo)
  | InheritedConstInit =>
    dsimp only
    apply cpo_node
    · show roots_resolve (nc ++ []) b (nroots ++ [])
      rw [app_nil, app_nil]
      exact Hnc_res
    · rw [app_nil]
      exact Hnc_cpo

theorem number_varspec_cpo : ∀ par role b vs, child_parent_ok (number_varspec par role b vs).1 := by
  intro par role b ⟨names, init⟩
  obtain ⟨Hnc_cpo, Hnc_res⟩ := number_list_cpo (number_bindingname (some b) (RSpecName VarSpecF)) b
    (fun bb x => number_bindingname_cpo (some b) (RSpecName VarSpecF) bb x)
    (fun bb x => number_bindingname_root (some b) (RSpecName VarSpecF) bb x)
    (b + 1) (Collections.ne_to_list names)
  unfold number_varspec
  dsimp only
  rcases h1 : number_list (number_bindingname (some b) (RSpecName VarSpecF)) (b + 1)
    (Collections.ne_to_list names) with ⟨nc, b1, nroots⟩
  rw [h1] at Hnc_cpo Hnc_res
  dsimp only at Hnc_cpo Hnc_res ⊢
  cases init with
  | VarTypeOnly t =>
    dsimp only
    have Htc_cpo := number_typeexpr_cpo (some b) RTypeUse b1 t
    obtain ⟨tc0, trest, Htr, Htpar⟩ := number_typeexpr_root (some b) RTypeUse b1 t
    rcases h2 : number_typeexpr (some b) RTypeUse b1 t with ⟨tc, b2⟩
    rw [h2] at Htc_cpo Htr
    dsimp only at Htc_cpo Htr ⊢
    apply cpo_node
    · show roots_resolve (nc ++ tc) b (nroots ++ [b1])
      refine roots_resolve_concat _ _ _ _ (roots_resolve_app_l _ _ _ _ Hnc_res)
        (roots_resolve_app_r _ _ _ _ ?_)
      intro ar Har
      have Har' : ar ∈ [b1] := Har
      cases Har' with
      | head => exact ⟨tc0, by rw [Htr]; exact List.Mem.head _, Htpar⟩
      | tail _ H => exact nomatch H
    · exact child_parent_ok_app _ _ Hnc_cpo Htc_cpo
  | VarValues ot vals =>
    dsimp only
    obtain ⟨Hoc_cpo, Hoc_res⟩ := number_opttype_cpo b b1 ot
    rcases h2 : number_opttype (some b) b1 ot with ⟨oc, b2, oroots⟩
    rw [h2] at Hoc_cpo Hoc_res
    dsimp only at Hoc_cpo Hoc_res ⊢
    obtain ⟨Hvc_cpo, Hvc_res⟩ := number_list_cpo (number_expr (some b) RPlain) b
      (fun bb x => number_expr_cpo x (some b) RPlain bb)
      (fun bb x => number_expr_root' (some b) RPlain bb x)
      b2 (Collections.ne_to_list vals)
    rcases h3 : number_list (number_expr (some b) RPlain) b2 (Collections.ne_to_list vals)
      with ⟨vc, b3, vroots⟩
    rw [h3] at Hvc_cpo Hvc_res
    dsimp only at Hvc_cpo Hvc_res ⊢
    apply cpo_node
    · show roots_resolve (nc ++ (oc ++ vc)) b (nroots ++ (oroots ++ vroots))
      exact roots_resolve_concat _ _ _ _ (roots_resolve_app_l _ _ _ _ Hnc_res)
        (roots_resolve_app_r _ _ _ _ (roots_resolve_concat _ _ _ _
          (roots_resolve_app_l _ _ _ _ Hoc_res) (roots_resolve_app_r _ _ _ _ Hvc_res)))
    · exact child_parent_ok_app _ _ Hnc_cpo (child_parent_ok_app _ _ Hoc_cpo Hvc_cpo)

theorem number_typespec_cpo : ∀ par role b ts, child_parent_ok (number_typespec par role b ts).1 := by
  intro par role b ts
  cases ts with
  | AliasSpec bn t | DefSpec bn t =>
    unfold number_typespec
    dsimp only
    have Hbc_cpo := number_bindingname_cpo (some b) (RSpecName TypeSpecF) (b + 1) bn
    obtain ⟨bc0, brest, Hbr, Hbpar⟩ := number_bindingname_root (some b) (RSpecName TypeSpecF) (b + 1) bn
    rcases h1 : number_bindingname (some b) (RSpecName TypeSpecF) (b + 1) bn with ⟨bc, b1⟩
    rw [h1] at Hbc_cpo Hbr
    have Htc_cpo := number_typeexpr_cpo (some b) RTypeUse b1 t
    obtain ⟨tc0, trest, Htr, Htpar⟩ := number_typeexpr_root (some b) RTypeUse b1 t
    rcases h2 : number_typeexpr (some b) RTypeUse b1 t with ⟨tc, bfin⟩
    rw [h2] at Htc_cpo Htr
    dsimp only at Hbc_cpo Hbr Htc_cpo Htr ⊢
    apply cpo_node
    · show roots_resolve (bc ++ tc) b [b + 1, b1]
      intro ar Har
      have Har' : ar ∈ [b + 1, b1] := Har
      cases Har' with
      | head => exact ⟨bc0, List.mem_append_left _ (by rw [Hbr]; exact List.Mem.head _), Hbpar⟩
      | tail _ H =>
        cases H with
        | head => exact ⟨tc0, List.mem_append_right _ (by rw [Htr]; exact List.Mem.head _), Htpar⟩
        | tail _ H' => exact nomatch H'
    · exact child_parent_ok_app _ _ Hbc_cpo Htc_cpo

theorem number_decl_cpo : ∀ par role b d, child_parent_ok (number_decl par role b d).1 := by
  intro par role b d
  cases d with
  | ConstDecl cs =>
    unfold number_decl
    dsimp only
    obtain ⟨Hk_cpo, Hk_res⟩ := number_list_cpo (number_constspec (some b) RPlain) b
      (fun bb x => number_constspec_cpo (some b) RPlain bb x)
      (fun bb x => number_constspec_root (some b) RPlain bb x) (b + 1) cs
    rcases h : number_list (number_constspec (some b) RPlain) (b + 1) cs with ⟨kc, bfin, roots⟩
    rw [h] at Hk_cpo Hk_res
    dsimp only at Hk_cpo Hk_res ⊢
    exact cpo_node _ _ _ Hk_res Hk_cpo
  | VarDecl vs =>
    unfold number_decl
    dsimp only
    obtain ⟨Hk_cpo, Hk_res⟩ := number_list_cpo (number_varspec (some b) RPlain) b
      (fun bb x => number_varspec_cpo (some b) RPlain bb x)
      (fun bb x => number_varspec_root (some b) RPlain bb x) (b + 1) vs
    rcases h : number_list (number_varspec (some b) RPlain) (b + 1) vs with ⟨kc, bfin, roots⟩
    rw [h] at Hk_cpo Hk_res
    dsimp only at Hk_cpo Hk_res ⊢
    exact cpo_node _ _ _ Hk_res Hk_cpo
  | TypeDecl ts =>
    unfold number_decl
    dsimp only
    obtain ⟨Hk_cpo, Hk_res⟩ := number_list_cpo (number_typespec (some b) RPlain) b
      (fun bb x => number_typespec_cpo (some b) RPlain bb x)
      (fun bb x => number_typespec_root (some b) RPlain bb x) (b + 1) ts
    rcases h : number_list (number_typespec (some b) RPlain) (b + 1) ts with ⟨kc, bfin, roots⟩
    rw [h] at Hk_cpo Hk_res
    dsimp only at Hk_cpo Hk_res ⊢
    exact cpo_node _ _ _ Hk_res Hk_cpo

theorem number_stmt_cpo : ∀ par role b s, child_parent_ok (number_stmt par role b s).1 := by
  intro par role b s
  cases s with
  | ExprStmt e =>
    unfold number_stmt
    dsimp only
    have Hc_cpo := number_expr_cpo e (some b) RExprStatementExpr (b + 1)
    obtain ⟨c0, crest, Hcr, Hcpar⟩ := number_expr_root' (some b) RExprStatementExpr (b + 1) e
    rcases h : number_expr (some b) RExprStatementExpr (b + 1) e with ⟨c, b'⟩
    rw [h] at Hc_cpo Hcr
    dsimp only at Hc_cpo Hcr ⊢
    apply cpo_node
    · show roots_resolve c b [b + 1]
      intro ar Har
      have Har' : ar ∈ [b + 1] := Har
      cases Har' with
      | head => exact ⟨c0, by rw [Hcr]; exact List.Mem.head _, Hcpar⟩
      | tail _ H => exact nomatch H
    · exact Hc_cpo
  | DeclarationStmt d =>
    unfold number_stmt
    dsimp only
    have Hc_cpo := number_decl_cpo (some b) RPlain (b + 1) d
    obtain ⟨c0, crest, Hcr, Hcpar⟩ := number_decl_root (some b) RPlain (b + 1) d
    rcases h : number_decl (some b) RPlain (b + 1) d with ⟨c, b'⟩
    rw [h] at Hc_cpo Hcr
    dsimp only at Hc_cpo Hcr ⊢
    apply cpo_node
    · show roots_resolve c b [b + 1]
      intro ar Har
      have Har' : ar ∈ [b + 1] := Har
      cases Har' with
      | head => exact ⟨c0, by rw [Hcr]; exact List.Mem.head _, Hcpar⟩
      | tail _ H => exact nomatch H
    · exact Hc_cpo
  | ShortVarDecl names vals =>
    unfold number_stmt
    dsimp only
    obtain ⟨Hnc_cpo, Hnc_res⟩ := number_list_cpo (number_bindingname (some b) RShortLhs) b
      (fun bb x => number_bindingname_cpo (some b) RShortLhs bb x)
      (fun bb x => number_bindingname_root (some b) RShortLhs bb x)
      (b + 1) (Collections.ne_to_list names)
    rcases h1 : number_list (number_bindingname (some b) RShortLhs) (b + 1) (Collections.ne_to_list names)
      with ⟨nc, b1, nroots⟩
    rw [h1] at Hnc_cpo Hnc_res
    dsimp only at Hnc_cpo Hnc_res ⊢
    obtain ⟨Hvc_cpo, Hvc_res⟩ := number_list_cpo (number_expr (some b) RPlain) b
      (fun bb x => number_expr_cpo x (some b) RPlain bb)
      (fun bb x => number_expr_root' (some b) RPlain bb x)
      b1 (Collections.ne_to_list vals)
    rcases h2 : number_list (number_expr (some b) RPlain) b1 (Collections.ne_to_list vals)
      with ⟨vc, b2, vroots⟩
    rw [h2] at Hvc_cpo Hvc_res
    dsimp only at Hvc_cpo Hvc_res ⊢
    apply cpo_node
    · show roots_resolve (nc ++ vc) b (nroots ++ vroots)
      exact roots_resolve_concat _ _ _ _ (roots_resolve_app_l _ _ _ _ Hnc_res)
        (roots_resolve_app_r _ _ _ _ Hvc_res)
    · exact child_parent_ok_app _ _ Hnc_cpo Hvc_cpo

theorem number_block_cpo : ∀ par role b blk, child_parent_ok (number_block par role b blk).1 := by
  intro par role b ⟨stmts⟩
  unfold number_block
  dsimp only
  obtain ⟨Hk_cpo, Hk_res⟩ := number_list_cpo (number_stmt (some b) RPlain) b
    (fun bb x => number_stmt_cpo (some b) RPlain bb x)
    (fun bb x => number_stmt_root (some b) RPlain bb x) (b + 1) stmts
  rcases h : number_list (number_stmt (some b) RPlain) (b + 1) stmts with ⟨kc, bfin, roots⟩
  rw [h] at Hk_cpo Hk_res
  dsimp only at Hk_cpo Hk_res ⊢
  exact cpo_node _ _ _ Hk_res Hk_cpo

theorem number_toplevel_cpo : ∀ par role b td, child_parent_ok (number_toplevel par role b td).1 := by
  intro par role b td
  cases td with
  | TopDeclaration d =>
    unfold number_toplevel
    dsimp only
    have Hc_cpo := number_decl_cpo (some b) RPlain (b + 1) d
    obtain ⟨c0, crest, Hcr, Hcpar⟩ := number_decl_root (some b) RPlain (b + 1) d
    rcases h : number_decl (some b) RPlain (b + 1) d with ⟨c, b'⟩
    rw [h] at Hc_cpo Hcr
    dsimp only at Hc_cpo Hcr ⊢
    apply cpo_node
    · show roots_resolve c b [b + 1]
      intro ar Har
      have Har' : ar ∈ [b + 1] := Har
      cases Har' with
      | head => exact ⟨c0, by rw [Hcr]; exact List.Mem.head _, Hcpar⟩
      | tail _ H => exact nomatch H
    · exact Hc_cpo
  | Main blk =>
    unfold number_toplevel
    dsimp only
    have Hc_cpo := number_block_cpo (some b) RPlain (b + 1) blk
    obtain ⟨c0, crest, Hcr, Hcpar⟩ := number_block_root (some b) RPlain (b + 1) blk
    rcases h : number_block (some b) RPlain (b + 1) blk with ⟨c, b'⟩
    rw [h] at Hc_cpo Hcr
    dsimp only at Hc_cpo Hcr ⊢
    apply cpo_node
    · show roots_resolve c b [b + 1]
      intro ar Har
      have Har' : ar ∈ [b + 1] := Har
      cases Har' with
      | head => exact ⟨c0, by rw [Hcr]; exact List.Mem.head _, Hcpar⟩
      | tail _ H => exact nomatch H
    · exact Hc_cpo

/-! the whole-file parent inverse: every child position resolves to a member whose parent edge points
    back -/
theorem number_file_cpo : ∀ f, child_parent_ok (number_file f) := by
  intro f
  unfold number_file
  obtain ⟨Hd_cpo, Hd_res⟩ := number_list_cpo (number_toplevel (some 0) RPlain) 0
    (fun bb x => number_toplevel_cpo (some 0) RPlain bb x)
    (fun bb x => number_toplevel_root (some 0) RPlain bb x) 1 (Syntax.declarations f)
  rcases h : number_list (number_toplevel (some 0) RPlain) 1 (Syntax.declarations f) with ⟨dc, bfin, droots⟩
  rw [h] at Hd_cpo Hd_res
  dsimp only at Hd_cpo Hd_res ⊢
  exact cpo_node _ _ _ Hd_res Hd_cpo

/-! one root position per numbered element — the enumeration is a bijection onto the source list -/
theorem number_list_roots_length {A : Type} (g : Nat → A → List (Nat × Cell) × Nat) :
    ∀ b xs, List.length (number_list g b xs).2.2 = List.length xs := by
  intro b xs
  induction xs generalizing b with
  | nil => rfl
  | cons x rest IH =>
    rw [number_list_cons_roots]
    show List.length (number_list g (g b x).2 rest).2.2 + 1 = List.length rest + 1
    rw [IH]

/-! file roots are exact: the file cell heads the traversal and lists exactly one child per top-level
    decl -/
theorem number_file_roots_exact : ∀ f,
    ∃ filecell dc, number_file f = (0, filecell) :: dc
      ∧ List.length (c_children filecell) = List.length (Syntax.declarations f) := by
  intro f
  unfold number_file
  have Hlen := number_list_roots_length (number_toplevel (some 0) RPlain) 1 (Syntax.declarations f)
  rcases h : number_list (number_toplevel (some 0) RPlain) 1 (Syntax.declarations f) with ⟨dc, bfin, droots⟩
  rw [h] at Hlen
  dsimp only at Hlen ⊢
  exact ⟨mkCell VFile RPlain none (bfin - 1) droots 0, dc, rfl, Hlen⟩

/-! every parent edge lands inside the block: [lo, pos) — no edge escapes below lo or forward past its
    child -/
def pbounds (lo : Nat) (occs : List (Nat × Cell)) : Prop :=
  ∀ pos cell, (pos, cell) ∈ occs → ∀ pp, c_parent cell = some pp → lo ≤ pp ∧ pp < pos

theorem pbounds_app : ∀ lo c1 c2, pbounds lo c1 → pbounds lo c2 → pbounds lo (c1 ++ c2) := by
  intro lo c1 c2 H1 H2 pos cell Hin pp Hpp
  cases mem_app_or Hin with
  | inl Hin => exact H1 pos cell Hin pp Hpp
  | inr Hin => exact H2 pos cell Hin pp Hpp

theorem pbounds_weaken : ∀ lo hi occs, lo ≤ hi → pbounds hi occs → pbounds lo occs := by
  intro lo hi occs Hle H pos cell Hin pp Hpp
  obtain ⟨Ha, Hb⟩ := H pos cell Hin pp Hpp
  exact ⟨Nat.le_trans Hle Ha, Hb⟩

theorem pbounds_node : ∀ lo b rootcell subforest,
    c_parent rootcell = some lo → lo < b →
    pbounds lo subforest → pbounds lo ((b, rootcell) :: subforest) := by
  intro lo b rootcell sf Hrp Hlt Hsf pos cell Hin pp Hpp
  cases Hin with
  | head =>
    rw [Hrp] at Hpp
    have Hlo : lo = pp := Option.some.inj Hpp
    subst Hlo
    exact ⟨Nat.le_refl lo, Hlt⟩
  | tail _ Hin => exact Hsf pos cell Hin pp Hpp

/-! the shared sublist form: with the parent below its first element, every element edge stays in
    [lo, pos) -/
theorem number_list_pbounds {A : Type} (g : Nat → A → List (Nat × Cell) × Nat) (lo : Nat) :
    (∀ b x, lo < b → pbounds lo (g b x).1) →
    (∀ b x, b ≤ (g b x).2) →
    ∀ b xs, lo < b → pbounds lo (number_list g b xs).1 := by
  intro Hg Hmono b xs
  induction xs generalizing b with
  | nil => intro _ pos cell Hin; exact nomatch (Hin : _ ∈ ([] : List (Nat × Cell)))
  | cons x rest IH =>
    intro Hlt
    have Hgx := Hg b x Hlt
    have Hlt' : lo < (g b x).2 := Nat.lt_of_lt_of_le Hlt (Hmono b x)
    rw [number_list_cons_fst]
    exact pbounds_app _ _ _ Hgx (IH (g b x).2 Hlt')

-- the `.v`'s inner `assert (Hda : …)` of number_expr_pbounds, about `number_args`
private theorem number_args_pbounds_of (b : Nat) : ∀ es : List Syntax.Expr,
    (∀ a ∈ es, ∀ pv role bb, pv < bb → pbounds pv (number_expr (some pv) role bb a).1) →
    ∀ i0 bi, b < bi → pbounds b (number_args b i0 bi es).1 := by
  intro es
  induction es with
  | nil => intro _ i0 bi _ pos cell Hin; exact nomatch (Hin : _ ∈ ([] : List (Nat × Cell)))
  | cons a rest IH =>
    intro Hall i0 bi Hbi
    have Ha := Hall a (List.Mem.head _) b (RApplicationArg i0) bi Hbi
    obtain ⟨na, _, Hbi', _⟩ := number_expr_span a (some b) (RApplicationArg i0) bi
    have Hbi2 : b < (number_expr (some b) (RApplicationArg i0) bi a).2 := by
      rw [Hbi']; exact Nat.lt_of_lt_of_le Hbi (Nat.le_add_right bi na)
    have IHrest := IH (fun x hx => Hall x (List.Mem.tail _ hx)) (i0 + 1) _ Hbi2
    rw [number_args_cons_fst]
    exact pbounds_app _ _ _ Ha IHrest

theorem number_expr_pbounds : ∀ e pv role b,
    pv < b → pbounds pv (number_expr (some pv) role b e).1 := by
  intro e
  induction e using Syntax.Expr_ind' with
  | HName n =>
    intro pv role b Hlt
    exact pbounds_node _ _ _ _ rfl Hlt (fun _ _ Hin => nomatch (Hin : _ ∈ ([] : List (Nat × Cell))))
  | HLit l =>
    intro pv role b Hlt
    exact pbounds_node _ _ _ _ rfl Hlt (fun _ _ Hin => nomatch (Hin : _ ∈ ([] : List (Nat × Cell))))
  | HUnary op e' IH =>
    intro pv role b Hlt
    have IH' := IH b RUnaryOperand (b + 1) (Nat.lt_succ_self b)
    rw [number_expr_unary_fst]
    exact pbounds_node _ _ _ _ rfl Hlt (pbounds_weaken _ _ _ (Nat.le_of_lt Hlt) IH')
  | HApp head args IHh IHa =>
    intro pv role b Hlt
    have IHh' := IHh b RApplicationHead (b + 1) (Nat.lt_succ_self b)
    obtain ⟨nh, _, Hb1, _⟩ := number_expr_span head (some b) RApplicationHead (b + 1)
    have Hb1' : b < (number_expr (some b) RApplicationHead (b + 1) head).2 := by
      rw [Hb1]; exact Nat.lt_of_lt_of_le (Nat.lt_succ_self b) (Nat.le_add_right (b + 1) nh)
    have Hda := number_args_pbounds_of b args IHa 0 _ Hb1'
    rw [number_expr_app_fst]
    exact pbounds_node _ _ _ _ rfl Hlt
      (pbounds_app _ _ _ (pbounds_weaken _ _ _ (Nat.le_of_lt Hlt) IHh')
        (pbounds_weaken _ _ _ (Nat.le_of_lt Hlt) Hda))

theorem number_typeexpr_pbounds : ∀ t pv role b, pv < b → pbounds pv (number_typeexpr (some pv) role b t).1 := by
  intro t pv role b Hlt
  exact pbounds_node _ _ _ _ rfl Hlt (fun _ _ Hin => nomatch (Hin : _ ∈ ([] : List (Nat × Cell))))

theorem number_bindingname_pbounds : ∀ bn pv role b, pv < b → pbounds pv (number_bindingname (some pv) role b bn).1 := by
  intro bn pv role b Hlt
  exact pbounds_node _ _ _ _ rfl Hlt (fun _ _ Hin => nomatch (Hin : _ ∈ ([] : List (Nat × Cell))))

theorem number_opttype_pbounds : ∀ ot pv b, pv < b → pbounds pv (number_opttype (some pv) b ot).1 := by
  intro ot pv b Hlt
  cases ot with
  | some t => exact number_typeexpr_pbounds t pv RTypeUse b Hlt
  | none => intro pos cell Hin; exact nomatch (Hin : _ ∈ ([] : List (Nat × Cell)))

theorem number_constspec_pbounds : ∀ cs pv role b, pv < b → pbounds pv (number_constspec (some pv) role b cs).1 := by
  intro ⟨names, init⟩ pv role b Hlt
  have Hnc := number_list_pbounds (number_bindingname (some b) (RSpecName ConstSpecF)) b
    (fun bb x Hbb => number_bindingname_pbounds x b (RSpecName ConstSpecF) bb Hbb)
    (fun bb x => span_final_ge _ _ (number_bindingname_spans (some b) (RSpecName ConstSpecF) bb x))
    (b + 1) (Collections.ne_to_list names) (Nat.lt_succ_self b)
  have Hb1 := span_final_ge _ _ (number_list_span (number_bindingname (some b) (RSpecName ConstSpecF))
    (fun bb x => number_bindingname_spans (some b) (RSpecName ConstSpecF) bb x)
    (Collections.ne_to_list names) (b + 1))
  unfold number_constspec
  dsimp only
  rcases h1 : number_list (number_bindingname (some b) (RSpecName ConstSpecF)) (b + 1)
    (Collections.ne_to_list names) with ⟨nc, b1, nroots⟩
  rw [h1] at Hnc Hb1
  dsimp only at Hnc Hb1 ⊢
  cases init with
  | ExplicitConstInit ot vals =>
    dsimp only
    have Hb1lt : b < b1 := Hb1
    have Hoc := number_opttype_pbounds ot b b1 Hb1lt
    have Hb2 := span_final_ge _ _ (number_opttype_span (some b) b1 ot)
    rcases h2 : number_opttype (some b) b1 ot with ⟨oc, b2, oroots⟩
    rw [h2] at Hoc Hb2
    dsimp only at Hoc Hb2 ⊢
    have Hb2lt : b < b2 := Nat.lt_of_lt_of_le Hb1lt Hb2
    have Hvc := number_list_pbounds (number_expr (some b) RPlain) b
      (fun bb x Hbb => number_expr_pbounds x b RPlain bb Hbb)
      (fun bb x => span_final_ge _ _ (number_expr_spans x (some b) RPlain bb))
      b2 (Collections.ne_to_list vals) Hb2lt
    rcases h3 : number_list (number_expr (some b) RPlain) b2 (Collections.ne_to_list vals)
      with ⟨vc, b3, vroots⟩
    rw [h3] at Hvc
    dsimp only at Hvc ⊢
    exact pbounds_node _ _ _ _ rfl Hlt
      (pbounds_weaken pv b _ (Nat.le_of_lt Hlt) (pbounds_app _ _ _ Hnc (pbounds_app _ _ _ Hoc Hvc)))
  | InheritedConstInit =>
    dsimp only
    exact pbounds_node _ _ _ _ rfl Hlt
      (pbounds_weaken pv b _ (Nat.le_of_lt Hlt) (by rw [app_nil]; exact Hnc))

theorem number_varspec_pbounds : ∀ vs pv role b, pv < b → pbounds pv (number_varspec (some pv) role b vs).1 := by
  intro ⟨names, init⟩ pv role b Hlt
  have Hnc := number_list_pbounds (number_bindingname (some b) (RSpecName VarSpecF)) b
    (fun bb x Hbb => number_bindingname_pbounds x b (RSpecName VarSpecF) bb Hbb)
    (fun bb x => span_final_ge _ _ (number_bindingname_spans (some b) (RSpecName VarSpecF) bb x))
    (b + 1) (Collections.ne_to_list names) (Nat.lt_succ_self b)
  have Hb1 := span_final_ge _ _ (number_list_span (number_bindingname (some b) (RSpecName VarSpecF))
    (fun bb x => number_bindingname_spans (some b) (RSpecName VarSpecF) bb x)
    (Collections.ne_to_list names) (b + 1))
  unfold number_varspec
  dsimp only
  rcases h1 : number_list (number_bindingname (some b) (RSpecName VarSpecF)) (b + 1)
    (Collections.ne_to_list names) with ⟨nc, b1, nroots⟩
  rw [h1] at Hnc Hb1
  dsimp only at Hnc Hb1 ⊢
  cases init with
  | VarTypeOnly t =>
    dsimp only
    have Hb1lt : b < b1 := Hb1
    have Htc := number_typeexpr_pbounds t b RTypeUse b1 Hb1lt
    rcases h2 : number_typeexpr (some b) RTypeUse b1 t with ⟨tc, b2⟩
    rw [h2] at Htc
    dsimp only at Htc ⊢
    exact pbounds_node _ _ _ _ rfl Hlt
      (pbounds_weaken pv b _ (Nat.le_of_lt Hlt) (pbounds_app _ _ _ Hnc Htc))
  | VarValues ot vals =>
    dsimp only
    have Hb1lt : b < b1 := Hb1
    have Hoc := number_opttype_pbounds ot b b1 Hb1lt
    have Hb2 := span_final_ge _ _ (number_opttype_span (some b) b1 ot)
    rcases h2 : number_opttype (some b) b1 ot with ⟨oc, b2, oroots⟩
    rw [h2] at Hoc Hb2
    dsimp only at Hoc Hb2 ⊢
    have Hb2lt : b < b2 := Nat.lt_of_lt_of_le Hb1lt Hb2
    have Hvc := number_list_pbounds (number_expr (some b) RPlain) b
      (fun bb x Hbb => number_expr_pbounds x b RPlain bb Hbb)
      (fun bb x => span_final_ge _ _ (number_expr_spans x (some b) RPlain bb))
      b2 (Collections.ne_to_list vals) Hb2lt
    rcases h3 : number_list (number_expr (some b) RPlain) b2 (Collections.ne_to_list vals)
      with ⟨vc, b3, vroots⟩
    rw [h3] at Hvc
    dsimp only at Hvc ⊢
    exact pbounds_node _ _ _ _ rfl Hlt
      (pbounds_weaken pv b _ (Nat.le_of_lt Hlt) (pbounds_app _ _ _ Hnc (pbounds_app _ _ _ Hoc Hvc)))

theorem number_typespec_pbounds : ∀ ts pv role b, pv < b → pbounds pv (number_typespec (some pv) role b ts).1 := by
  intro ts pv role b Hlt
  cases ts with
  | AliasSpec bn t | DefSpec bn t =>
    unfold number_typespec
    dsimp only
    have Hbc := number_bindingname_pbounds bn b (RSpecName TypeSpecF) (b + 1) (Nat.lt_succ_self b)
    have Hb1 := span_final_ge _ _ (number_bindingname_spans (some b) (RSpecName TypeSpecF) (b + 1) bn)
    rcases h1 : number_bindingname (some b) (RSpecName TypeSpecF) (b + 1) bn with ⟨bc, b1⟩
    rw [h1] at Hbc Hb1
    dsimp only at Hbc Hb1
    have Hb1lt : b < b1 := Hb1
    have Htc := number_typeexpr_pbounds t b RTypeUse b1 Hb1lt
    rcases h2 : number_typeexpr (some b) RTypeUse b1 t with ⟨tc, bfin⟩
    rw [h2] at Htc
    dsimp only at Htc ⊢
    exact pbounds_node _ _ _ _ rfl Hlt
      (pbounds_weaken pv b _ (Nat.le_of_lt Hlt) (pbounds_app _ _ _ Hbc Htc))

theorem number_decl_pbounds : ∀ d pv role b, pv < b → pbounds pv (number_decl (some pv) role b d).1 := by
  intro d pv role b Hlt
  cases d with
  | ConstDecl cs =>
    unfold number_decl
    dsimp only
    have Hk := number_list_pbounds (number_constspec (some b) RPlain) b
      (fun bb x Hbb => number_constspec_pbounds x b RPlain bb Hbb)
      (fun bb x => span_final_ge _ _ (number_constspec_span (some b) RPlain bb x)) (b + 1) cs
      (Nat.lt_succ_self b)
    rcases h : number_list (number_constspec (some b) RPlain) (b + 1) cs with ⟨kc, bfin, roots⟩
    rw [h] at Hk
    dsimp only at Hk ⊢
    exact pbounds_node _ _ _ _ rfl Hlt (pbounds_weaken pv b _ (Nat.le_of_lt Hlt) Hk)
  | VarDecl vs =>
    unfold number_decl
    dsimp only
    have Hk := number_list_pbounds (number_varspec (some b) RPlain) b
      (fun bb x Hbb => number_varspec_pbounds x b RPlain bb Hbb)
      (fun bb x => span_final_ge _ _ (number_varspec_span (some b) RPlain bb x)) (b + 1) vs
      (Nat.lt_succ_self b)
    rcases h : number_list (number_varspec (some b) RPlain) (b + 1) vs with ⟨kc, bfin, roots⟩
    rw [h] at Hk
    dsimp only at Hk ⊢
    exact pbounds_node _ _ _ _ rfl Hlt (pbounds_weaken pv b _ (Nat.le_of_lt Hlt) Hk)
  | TypeDecl ts =>
    unfold number_decl
    dsimp only
    have Hk := number_list_pbounds (number_typespec (some b) RPlain) b
      (fun bb x Hbb => number_typespec_pbounds x b RPlain bb Hbb)
      (fun bb x => span_final_ge _ _ (number_typespec_span (some b) RPlain bb x)) (b + 1) ts
      (Nat.lt_succ_self b)
    rcases h : number_list (number_typespec (some b) RPlain) (b + 1) ts with ⟨kc, bfin, roots⟩
    rw [h] at Hk
    dsimp only at Hk ⊢
    exact pbounds_node _ _ _ _ rfl Hlt (pbounds_weaken pv b _ (Nat.le_of_lt Hlt) Hk)

theorem number_stmt_pbounds : ∀ s pv role b, pv < b → pbounds pv (number_stmt (some pv) role b s).1 := by
  intro s pv role b Hlt
  cases s with
  | ExprStmt e =>
    unfold number_stmt
    dsimp only
    have Hc := number_expr_pbounds e b RExprStatementExpr (b + 1) (Nat.lt_succ_self b)
    rcases h : number_expr (some b) RExprStatementExpr (b + 1) e with ⟨c, b'⟩
    rw [h] at Hc
    dsimp only at Hc ⊢
    exact pbounds_node _ _ _ _ rfl Hlt (pbounds_weaken pv b _ (Nat.le_of_lt Hlt) Hc)
  | DeclarationStmt d =>
    unfold number_stmt
    dsimp only
    have Hc := number_decl_pbounds d b RPlain (b + 1) (Nat.lt_succ_self b)
    rcases h : number_decl (some b) RPlain (b + 1) d with ⟨c, b'⟩
    rw [h] at Hc
    dsimp only at Hc ⊢
    exact pbounds_node _ _ _ _ rfl Hlt (pbounds_weaken pv b _ (Nat.le_of_lt Hlt) Hc)
  | ShortVarDecl names vals =>
    unfold number_stmt
    dsimp only
    have Hnc := number_list_pbounds (number_bindingname (some b) RShortLhs) b
      (fun bb x Hbb => number_bindingname_pbounds x b RShortLhs bb Hbb)
      (fun bb x => span_final_ge _ _ (number_bindingname_spans (some b) RShortLhs bb x))
      (b + 1) (Collections.ne_to_list names) (Nat.lt_succ_self b)
    have Hb1 := span_final_ge _ _ (number_list_span (number_bindingname (some b) RShortLhs)
      (fun bb x => number_bindingname_spans (some b) RShortLhs bb x) (Collections.ne_to_list names) (b + 1))
    rcases h1 : number_list (number_bindingname (some b) RShortLhs) (b + 1) (Collections.ne_to_list names)
      with ⟨nc, b1, nroots⟩
    rw [h1] at Hnc Hb1
    dsimp only at Hnc Hb1 ⊢
    have Hb1lt : b < b1 := Hb1
    have Hvc := number_list_pbounds (number_expr (some b) RPlain) b
      (fun bb x Hbb => number_expr_pbounds x b RPlain bb Hbb)
      (fun bb x => span_final_ge _ _ (number_expr_spans x (some b) RPlain bb))
      b1 (Collections.ne_to_list vals) Hb1lt
    rcases h2 : number_list (number_expr (some b) RPlain) b1 (Collections.ne_to_list vals)
      with ⟨vc, b2, vroots⟩
    rw [h2] at Hvc
    dsimp only at Hvc ⊢
    exact pbounds_node _ _ _ _ rfl Hlt
      (pbounds_weaken pv b _ (Nat.le_of_lt Hlt) (pbounds_app _ _ _ Hnc Hvc))

theorem number_block_pbounds : ∀ blk pv role b, pv < b → pbounds pv (number_block (some pv) role b blk).1 := by
  intro ⟨stmts⟩ pv role b Hlt
  unfold number_block
  dsimp only
  have Hk := number_list_pbounds (number_stmt (some b) RPlain) b
    (fun bb x Hbb => number_stmt_pbounds x b RPlain bb Hbb)
    (fun bb x => span_final_ge _ _ (number_stmt_span (some b) RPlain bb x)) (b + 1) stmts
    (Nat.lt_succ_self b)
  rcases h : number_list (number_stmt (some b) RPlain) (b + 1) stmts with ⟨kc, bfin, roots⟩
  rw [h] at Hk
  dsimp only at Hk ⊢
  exact pbounds_node _ _ _ _ rfl Hlt (pbounds_weaken pv b _ (Nat.le_of_lt Hlt) Hk)

theorem number_toplevel_pbounds : ∀ td pv role b, pv < b → pbounds pv (number_toplevel (some pv) role b td).1 := by
  intro td pv role b Hlt
  cases td with
  | TopDeclaration d =>
    unfold number_toplevel
    dsimp only
    have Hc := number_decl_pbounds d b RPlain (b + 1) (Nat.lt_succ_self b)
    rcases h : number_decl (some b) RPlain (b + 1) d with ⟨c, b'⟩
    rw [h] at Hc
    dsimp only at Hc ⊢
    exact pbounds_node _ _ _ _ rfl Hlt (pbounds_weaken pv b _ (Nat.le_of_lt Hlt) Hc)
  | Main blk =>
    unfold number_toplevel
    dsimp only
    have Hc := number_block_pbounds blk b RPlain (b + 1) (Nat.lt_succ_self b)
    rcases h : number_block (some b) RPlain (b + 1) blk with ⟨c, b'⟩
    rw [h] at Hc
    dsimp only at Hc ⊢
    exact pbounds_node _ _ _ _ rfl Hlt (pbounds_weaken pv b _ (Nat.le_of_lt Hlt) Hc)

/-! whole-file parent well-scoping: every parent edge points strictly earlier — the parent relation is
    acyclic -/
theorem number_file_pbounds : ∀ f, pbounds 0 (number_file f) := by
  intro f
  unfold number_file
  have Hd := number_list_pbounds (number_toplevel (some 0) RPlain) 0
    (fun bb x Hbb => number_toplevel_pbounds x 0 RPlain bb Hbb)
    (fun bb x => span_final_ge _ _ (number_toplevel_span (some 0) RPlain bb x))
    1 (Syntax.declarations f) Nat.zero_lt_one
  rcases h : number_list (number_toplevel (some 0) RPlain) 1 (Syntax.declarations f) with ⟨dc, bfin, droots⟩
  rw [h] at Hd
  dsimp only at Hd ⊢
  intro pos cell Hin pp Hpp
  cases Hin with
  | head => exact nomatch Hpp
  | tail _ Hin => exact Hd pos cell Hin pp Hpp

/-! [covered occs q]: position q is listed among the children of some member cell — it is nobody's
    orphan -/
def covered (occs : List (Nat × Cell)) (q : Nat) : Prop :=
  ∃ r rcell, (r, rcell) ∈ occs ∧ q ∈ c_children rcell

theorem covered_app_l : ∀ c1 c2 q, covered c1 q → covered (c1 ++ c2) q := by
  intro c1 c2 q ⟨r, rcell, Hin, Hq⟩
  exact ⟨r, rcell, List.mem_append_left c2 Hin, Hq⟩

theorem covered_app_r : ∀ c1 c2 q, covered c2 q → covered (c1 ++ c2) q := by
  intro c1 c2 q ⟨r, rcell, Hin, Hq⟩
  exact ⟨r, rcell, List.mem_append_right c1 Hin, Hq⟩

/-! every position a sublist fills is either one of its element roots or already covered inside an
    element -/
theorem number_list_cover {A : Type} (g : Nat → A → List (Nat × Cell) × Nat) :
    (∀ b x q, b < q ∧ q < (g b x).2 → covered (g b x).1 q) →
    (∀ b x, b ≤ (g b x).2) →
    ∀ b xs q, b ≤ q ∧ q < (number_list g b xs).2.1 →
      q ∈ (number_list g b xs).2.2 ∨ covered (number_list g b xs).1 q := by
  intro Hg Hmono b xs
  induction xs generalizing b with
  | nil =>
    intro q ⟨Hqlo, Hqhi⟩
    have Hqhi' : q < b := Hqhi
    exact absurd (Nat.lt_of_le_of_lt Hqlo Hqhi') (Nat.lt_irrefl b)
  | cons x rest IH =>
    intro q ⟨Hqlo, Hqhi⟩
    have Hgx := Hg b x
    rw [number_list_cons_next] at Hqhi
    rw [number_list_cons_roots, number_list_cons_fst]
    cases Nat.lt_or_ge q (g b x).2 with
    | inr Hge =>
      cases IH (g b x).2 q ⟨Hge, Hqhi⟩ with
      | inl Hin => exact Or.inl (List.Mem.tail _ Hin)
      | inr Hcov => exact Or.inr (covered_app_r _ _ _ Hcov)
    | inl Hqlt =>
      by_cases Heq : q = b
      · subst Heq; exact Or.inl (List.Mem.head _)
      · exact Or.inr (covered_app_l _ _ _ (Hgx q ⟨Nat.lt_of_le_of_ne Hqlo (fun h => Heq h.symm), Hqlt⟩))

theorem covered_cons : ∀ kv occs q, covered occs q → covered (kv :: occs) q := by
  intro kv occs q ⟨r, rcell, Hin, Hq⟩
  exact ⟨r, rcell, List.Mem.tail _ Hin, Hq⟩

theorem covered_here : ∀ b rcell occs q, q ∈ c_children rcell → covered ((b, rcell) :: occs) q :=
  fun b rcell _ _ Hq => ⟨b, rcell, List.Mem.head _, Hq⟩

-- the `.v`'s inner `assert (Hda : …)` of number_expr_cover, about `number_args`
private theorem number_args_cover_of (b : Nat) : ∀ es : List Syntax.Expr,
    (∀ a ∈ es, ∀ par role bb q,
      bb < q ∧ q < (number_expr par role bb a).2 → covered (number_expr par role bb a).1 q) →
    ∀ i0 bi q, bi ≤ q ∧ q < (number_args b i0 bi es).2.1 →
      q ∈ (number_args b i0 bi es).2.2 ∨ covered (number_args b i0 bi es).1 q := by
  intro es
  induction es with
  | nil =>
    intro _ i0 bi q ⟨Hqlo, Hqhi⟩
    have Hqhi' : q < bi := Hqhi
    exact absurd (Nat.lt_of_le_of_lt Hqlo Hqhi') (Nat.lt_irrefl bi)
  | cons a rest IH =>
    intro Hall i0 bi q ⟨Hqlo, Hqhi⟩
    have Ha := Hall a (List.Mem.head _) (some b) (RApplicationArg i0) bi
    have IHrest := IH (fun x hx => Hall x (List.Mem.tail _ hx)) (i0 + 1)
      (number_expr (some b) (RApplicationArg i0) bi a).2
    rw [number_args_cons_next] at Hqhi
    rw [number_args_cons_roots, number_args_cons_fst]
    cases Nat.lt_or_ge q (number_expr (some b) (RApplicationArg i0) bi a).2 with
    | inr Hge =>
      cases IHrest q ⟨Hge, Hqhi⟩ with
      | inl Hin => exact Or.inl (List.Mem.tail _ Hin)
      | inr Hcov => exact Or.inr (covered_app_r _ _ _ Hcov)
    | inl Hqlt =>
      by_cases Heq : q = bi
      · subst Heq; exact Or.inl (List.Mem.head _)
      · exact Or.inr (covered_app_l _ _ _ (Ha q ⟨Nat.lt_of_le_of_ne Hqlo (fun h => Heq h.symm), Hqlt⟩))

/-! every interior position of an expression's block is covered — its own root lists it, or a
    sub-expression does -/
theorem number_expr_cover : ∀ e par role b q,
    b < q ∧ q < (number_expr par role b e).2 → covered (number_expr par role b e).1 q := by
  intro e
  induction e using Syntax.Expr_ind' with
  | HName n =>
    intro par role b q ⟨Hqlo, Hqhi⟩
    have Hqhi' : q < b + 1 := Hqhi
    exact absurd (Nat.lt_of_lt_of_le Hqhi' Hqlo) (Nat.lt_irrefl q)
  | HLit l =>
    intro par role b q ⟨Hqlo, Hqhi⟩
    have Hqhi' : q < b + 1 := Hqhi
    exact absurd (Nat.lt_of_lt_of_le Hqhi' Hqlo) (Nat.lt_irrefl q)
  | HUnary op e' IH =>
    intro par role b q ⟨Hqlo, Hqhi⟩
    have IH' := IH (some b) RUnaryOperand (b + 1)
    rw [number_expr_unary_snd] at Hqhi
    rw [number_expr_unary_fst]
    by_cases Heq : q = b + 1
    · subst Heq; exact covered_here _ _ _ _ (List.Mem.head _)
    · exact covered_cons _ _ _ (IH' q ⟨Nat.lt_of_le_of_ne Hqlo (fun h => Heq h.symm), Hqhi⟩)
  | HApp head args IHh IHa =>
    intro par role b q ⟨Hqlo, Hqhi⟩
    have IHh' := IHh (some b) RApplicationHead (b + 1)
    have Hda := number_args_cover_of b args IHa 0 (number_expr (some b) RApplicationHead (b + 1) head).2
    rw [number_expr_app_snd] at Hqhi
    rw [number_expr_app_fst]
    cases Nat.lt_or_ge q (number_expr (some b) RApplicationHead (b + 1) head).2 with
    | inr Hge =>
      cases Hda q ⟨Hge, Hqhi⟩ with
      | inl Hin => exact covered_here _ _ _ _ (List.Mem.tail _ Hin)
      | inr Hcov => exact covered_cons _ _ _ (covered_app_r _ _ _ Hcov)
    | inl Hqlt =>
      by_cases Heq : q = b + 1
      · subst Heq; exact covered_here _ _ _ _ (List.Mem.head _)
      · exact covered_cons _ _ _
          (covered_app_l _ _ _ (IHh' q ⟨Nat.lt_of_le_of_ne Hqlo (fun h => Heq h.symm), Hqlt⟩))

theorem number_typeexpr_cover : ∀ t par role b q,
    b < q ∧ q < (number_typeexpr par role b t).2 → covered (number_typeexpr par role b t).1 q := by
  intro t par role b q ⟨Hqlo, Hqhi⟩
  have Hqhi' : q < b + 1 := Hqhi
  exact absurd (Nat.lt_of_lt_of_le Hqhi' Hqlo) (Nat.lt_irrefl q)

theorem number_bindingname_cover : ∀ bn par role b q,
    b < q ∧ q < (number_bindingname par role b bn).2 → covered (number_bindingname par role b bn).1 q := by
  intro bn par role b q ⟨Hqlo, Hqhi⟩
  have Hqhi' : q < b + 1 := Hqhi
  exact absurd (Nat.lt_of_lt_of_le Hqhi' Hqlo) (Nat.lt_irrefl q)

/-! the optional type slot fills exactly [b] (its type) or nothing: any position it covers is its one root -/
theorem number_opttype_cover : ∀ ot par b q,
    b ≤ q ∧ q < (number_opttype par b ot).2.1 →
      q ∈ (number_opttype par b ot).2.2 ∨ covered (number_opttype par b ot).1 q := by
  intro ot par b q ⟨Hqlo, Hqhi⟩
  cases ot with
  | some t =>
    have Hqhi' : q < b + 1 := Hqhi
    have Heq : q = b := Nat.le_antisymm (Nat.le_of_lt_succ Hqhi') Hqlo
    subst Heq
    exact Or.inl (List.Mem.head _)
  | none =>
    have Hqhi' : q < b := Hqhi
    exact absurd (Nat.lt_of_le_of_lt Hqlo Hqhi') (Nat.lt_irrefl b)

theorem number_constspec_cover : ∀ cs par role b q,
    b < q ∧ q < (number_constspec par role b cs).2 → covered (number_constspec par role b cs).1 q := by
  intro ⟨names, init⟩ par role b
  have Hnc := number_list_cover (number_bindingname (some b) (RSpecName ConstSpecF))
    (fun bb x q => number_bindingname_cover x (some b) (RSpecName ConstSpecF) bb q)
    (fun bb x => span_final_ge _ _ (number_bindingname_spans (some b) (RSpecName ConstSpecF) bb x))
    (b + 1) (Collections.ne_to_list names)
  unfold number_constspec
  dsimp only
  rcases h1 : number_list (number_bindingname (some b) (RSpecName ConstSpecF)) (b + 1)
    (Collections.ne_to_list names) with ⟨nc, b1, nroots⟩
  rw [h1] at Hnc
  dsimp only at Hnc ⊢
  cases init with
  | ExplicitConstInit ot vals =>
    dsimp only
    have Hoc := number_opttype_cover ot (some b) b1
    rcases h2 : number_opttype (some b) b1 ot with ⟨oc, b2, oroots⟩
    rw [h2] at Hoc
    dsimp only at Hoc ⊢
    have Hvc := number_list_cover (number_expr (some b) RPlain)
      (fun bb x q => number_expr_cover x (some b) RPlain bb q)
      (fun bb x => span_final_ge _ _ (number_expr_spans x (some b) RPlain bb))
      b2 (Collections.ne_to_list vals)
    rcases h3 : number_list (number_expr (some b) RPlain) b2 (Collections.ne_to_list vals)
      with ⟨vc, b3, vroots⟩
    rw [h3] at Hvc
    dsimp only at Hvc ⊢
    intro q ⟨Hqlo, Hqhi⟩
    cases Nat.lt_or_ge q b1 with
    | inr Hb1 =>
      cases Nat.lt_or_ge q b2 with
      | inr Hb2 =>
        cases Hvc q ⟨Hb2, Hqhi⟩ with
        | inl Hin => exact covered_here _ _ _ _ (List.mem_append_right _ (List.mem_append_right _ Hin))
        | inr Hcov => exact covered_cons _ _ _ (covered_app_r _ _ _ (covered_app_r _ _ _ Hcov))
      | inl Hb2 =>
        cases Hoc q ⟨Hb1, Hb2⟩ with
        | inl Hin => exact covered_here _ _ _ _ (List.mem_append_right _ (List.mem_append_left _ Hin))
        | inr Hcov => exact covered_cons _ _ _ (covered_app_r _ _ _ (covered_app_l _ _ _ Hcov))
    | inl Hb1 =>
      cases Hnc q ⟨Hqlo, Hb1⟩ with
      | inl Hin => exact covered_here _ _ _ _ (List.mem_append_left _ Hin)
      | inr Hcov => exact covered_cons _ _ _ (covered_app_l _ _ _ Hcov)
  | InheritedConstInit =>
    dsimp only
    intro q ⟨Hqlo, Hqhi⟩
    cases Hnc q ⟨Hqlo, Hqhi⟩ with
    | inl Hin => exact covered_here _ _ _ _ (by rw [app_nil]; exact Hin)
    | inr Hcov => exact covered_cons _ _ _ (by rw [app_nil]; exact Hcov)

theorem number_varspec_cover : ∀ vs par role b q,
    b < q ∧ q < (number_varspec par role b vs).2 → covered (number_varspec par role b vs).1 q := by
  intro ⟨names, init⟩ par role b
  have Hnc := number_list_cover (number_bindingname (some b) (RSpecName VarSpecF))
    (fun bb x q => number_bindingname_cover x (some b) (RSpecName VarSpecF) bb q)
    (fun bb x => span_final_ge _ _ (number_bindingname_spans (some b) (RSpecName VarSpecF) bb x))
    (b + 1) (Collections.ne_to_list names)
  unfold number_varspec
  dsimp only
  rcases h1 : number_list (number_bindingname (some b) (RSpecName VarSpecF)) (b + 1)
    (Collections.ne_to_list names) with ⟨nc, b1, nroots⟩
  rw [h1] at Hnc
  dsimp only at Hnc ⊢
  cases init with
  | VarTypeOnly t =>
    dsimp only [number_typeexpr, number_leaf]
    intro q ⟨Hqlo, Hqhi⟩
    cases Nat.lt_or_ge q b1 with
    | inr Hb1 =>
      have Heq : q = b1 := Nat.le_antisymm (Nat.le_of_lt_succ Hqhi) Hb1
      subst Heq
      exact covered_here _ _ _ _ (List.mem_append_right _ (List.Mem.head _))
    | inl Hb1 =>
      cases Hnc q ⟨Hqlo, Hb1⟩ with
      | inl Hin => exact covered_here _ _ _ _ (List.mem_append_left _ Hin)
      | inr Hcov => exact covered_cons _ _ _ (covered_app_l _ _ _ Hcov)
  | VarValues ot vals =>
    dsimp only
    have Hoc := number_opttype_cover ot (some b) b1
    rcases h2 : number_opttype (some b) b1 ot with ⟨oc, b2, oroots⟩
    rw [h2] at Hoc
    dsimp only at Hoc ⊢
    have Hvc := number_list_cover (number_expr (some b) RPlain)
      (fun bb x q => number_expr_cover x (some b) RPlain bb q)
      (fun bb x => span_final_ge _ _ (number_expr_spans x (some b) RPlain bb))
      b2 (Collections.ne_to_list vals)
    rcases h3 : number_list (number_expr (some b) RPlain) b2 (Collections.ne_to_list vals)
      with ⟨vc, b3, vroots⟩
    rw [h3] at Hvc
    dsimp only at Hvc ⊢
    intro q ⟨Hqlo, Hqhi⟩
    cases Nat.lt_or_ge q b1 with
    | inr Hb1 =>
      cases Nat.lt_or_ge q b2 with
      | inr Hb2 =>
        cases Hvc q ⟨Hb2, Hqhi⟩ with
        | inl Hin => exact covered_here _ _ _ _ (List.mem_append_right _ (List.mem_append_right _ Hin))
        | inr Hcov => exact covered_cons _ _ _ (covered_app_r _ _ _ (covered_app_r _ _ _ Hcov))
      | inl Hb2 =>
        cases Hoc q ⟨Hb1, Hb2⟩ with
        | inl Hin => exact covered_here _ _ _ _ (List.mem_append_right _ (List.mem_append_left _ Hin))
        | inr Hcov => exact covered_cons _ _ _ (covered_app_r _ _ _ (covered_app_l _ _ _ Hcov))
    | inl Hb1 =>
      cases Hnc q ⟨Hqlo, Hb1⟩ with
      | inl Hin => exact covered_here _ _ _ _ (List.mem_append_left _ Hin)
      | inr Hcov => exact covered_cons _ _ _ (covered_app_l _ _ _ Hcov)

theorem number_typespec_cover : ∀ ts par role b q,
    b < q ∧ q < (number_typespec par role b ts).2 → covered (number_typespec par role b ts).1 q := by
  intro ts par role b q ⟨Hqlo, Hqhi⟩
  cases ts with
  | AliasSpec bn t | DefSpec bn t =>
    have Hqhi' : q < b + 1 + 1 + 1 := Hqhi
    by_cases Heq : q = b + 1
    · subst Heq; exact covered_here _ _ _ _ (List.Mem.head _)
    · have Heq2 : q = b + 1 + 1 :=
        Nat.le_antisymm (Nat.le_of_lt_succ Hqhi') (Nat.lt_of_le_of_ne Hqlo (fun h => Heq h.symm))
      subst Heq2
      exact covered_here _ _ _ _ (List.Mem.tail _ (List.Mem.head _))

theorem number_decl_cover : ∀ d par role b q,
    b < q ∧ q < (number_decl par role b d).2 → covered (number_decl par role b d).1 q := by
  intro d par role b
  cases d with
  | ConstDecl cs =>
    unfold number_decl
    dsimp only
    have Hk := number_list_cover (number_constspec (some b) RPlain)
      (fun bb x q => number_constspec_cover x (some b) RPlain bb q)
      (fun bb x => span_final_ge _ _ (number_constspec_span (some b) RPlain bb x)) (b + 1) cs
    rcases h : number_list (number_constspec (some b) RPlain) (b + 1) cs with ⟨kc, bfin, roots⟩
    rw [h] at Hk
    dsimp only at Hk ⊢
    intro q ⟨Hqlo, Hqhi⟩
    cases Hk q ⟨Hqlo, Hqhi⟩ with
    | inl Hin => exact covered_here _ _ _ _ Hin
    | inr Hcov => exact covered_cons _ _ _ Hcov
  | VarDecl vs =>
    unfold number_decl
    dsimp only
    have Hk := number_list_cover (number_varspec (some b) RPlain)
      (fun bb x q => number_varspec_cover x (some b) RPlain bb q)
      (fun bb x => span_final_ge _ _ (number_varspec_span (some b) RPlain bb x)) (b + 1) vs
    rcases h : number_list (number_varspec (some b) RPlain) (b + 1) vs with ⟨kc, bfin, roots⟩
    rw [h] at Hk
    dsimp only at Hk ⊢
    intro q ⟨Hqlo, Hqhi⟩
    cases Hk q ⟨Hqlo, Hqhi⟩ with
    | inl Hin => exact covered_here _ _ _ _ Hin
    | inr Hcov => exact covered_cons _ _ _ Hcov
  | TypeDecl ts =>
    unfold number_decl
    dsimp only
    have Hk := number_list_cover (number_typespec (some b) RPlain)
      (fun bb x q => number_typespec_cover x (some b) RPlain bb q)
      (fun bb x => span_final_ge _ _ (number_typespec_span (some b) RPlain bb x)) (b + 1) ts
    rcases h : number_list (number_typespec (some b) RPlain) (b + 1) ts with ⟨kc, bfin, roots⟩
    rw [h] at Hk
    dsimp only at Hk ⊢
    intro q ⟨Hqlo, Hqhi⟩
    cases Hk q ⟨Hqlo, Hqhi⟩ with
    | inl Hin => exact covered_here _ _ _ _ Hin
    | inr Hcov => exact covered_cons _ _ _ Hcov

theorem number_stmt_cover : ∀ s par role b q,
    b < q ∧ q < (number_stmt par role b s).2 → covered (number_stmt par role b s).1 q := by
  intro s par role b
  cases s with
  | ExprStmt e =>
    unfold number_stmt
    dsimp only
    have Hc := number_expr_cover e (some b) RExprStatementExpr (b + 1)
    rcases h : number_expr (some b) RExprStatementExpr (b + 1) e with ⟨c, b'⟩
    rw [h] at Hc
    dsimp only at Hc ⊢
    intro q ⟨Hqlo, Hqhi⟩
    by_cases Heq : q = b + 1
    · subst Heq; exact covered_here _ _ _ _ (List.Mem.head _)
    · exact covered_cons _ _ _ (Hc q ⟨Nat.lt_of_le_of_ne Hqlo (fun h => Heq h.symm), Hqhi⟩)
  | DeclarationStmt d =>
    unfold number_stmt
    dsimp only
    have Hc := number_decl_cover d (some b) RPlain (b + 1)
    rcases h : number_decl (some b) RPlain (b + 1) d with ⟨c, b'⟩
    rw [h] at Hc
    dsimp only at Hc ⊢
    intro q ⟨Hqlo, Hqhi⟩
    by_cases Heq : q = b + 1
    · subst Heq; exact covered_here _ _ _ _ (List.Mem.head _)
    · exact covered_cons _ _ _ (Hc q ⟨Nat.lt_of_le_of_ne Hqlo (fun h => Heq h.symm), Hqhi⟩)
  | ShortVarDecl names vals =>
    unfold number_stmt
    dsimp only
    have Hnc := number_list_cover (number_bindingname (some b) RShortLhs)
      (fun bb x q => number_bindingname_cover x (some b) RShortLhs bb q)
      (fun bb x => span_final_ge _ _ (number_bindingname_spans (some b) RShortLhs bb x))
      (b + 1) (Collections.ne_to_list names)
    rcases h1 : number_list (number_bindingname (some b) RShortLhs) (b + 1) (Collections.ne_to_list names)
      with ⟨nc, b1, nroots⟩
    rw [h1] at Hnc
    dsimp only at Hnc ⊢
    have Hvc := number_list_cover (number_expr (some b) RPlain)
      (fun bb x q => number_expr_cover x (some b) RPlain bb q)
      (fun bb x => span_final_ge _ _ (number_expr_spans x (some b) RPlain bb))
      b1 (Collections.ne_to_list vals)
    rcases h2 : number_list (number_expr (some b) RPlain) b1 (Collections.ne_to_list vals)
      with ⟨vc, b2, vroots⟩
    rw [h2] at Hvc
    dsimp only at Hvc ⊢
    intro q ⟨Hqlo, Hqhi⟩
    cases Nat.lt_or_ge q b1 with
    | inr Hb1 =>
      cases Hvc q ⟨Hb1, Hqhi⟩ with
      | inl Hin => exact covered_here _ _ _ _ (List.mem_append_right _ Hin)
      | inr Hcov => exact covered_cons _ _ _ (covered_app_r _ _ _ Hcov)
    | inl Hb1 =>
      cases Hnc q ⟨Hqlo, Hb1⟩ with
      | inl Hin => exact covered_here _ _ _ _ (List.mem_append_left _ Hin)
      | inr Hcov => exact covered_cons _ _ _ (covered_app_l _ _ _ Hcov)

theorem number_block_cover : ∀ blk par role b q,
    b < q ∧ q < (number_block par role b blk).2 → covered (number_block par role b blk).1 q := by
  intro ⟨stmts⟩ par role b
  unfold number_block
  dsimp only
  have Hk := number_list_cover (number_stmt (some b) RPlain)
    (fun bb x q => number_stmt_cover x (some b) RPlain bb q)
    (fun bb x => span_final_ge _ _ (number_stmt_span (some b) RPlain bb x)) (b + 1) stmts
  rcases h : number_list (number_stmt (some b) RPlain) (b + 1) stmts with ⟨kc, bfin, roots⟩
  rw [h] at Hk
  dsimp only at Hk ⊢
  intro q ⟨Hqlo, Hqhi⟩
  cases Hk q ⟨Hqlo, Hqhi⟩ with
  | inl Hin => exact covered_here _ _ _ _ Hin
  | inr Hcov => exact covered_cons _ _ _ Hcov

theorem number_toplevel_cover : ∀ td par role b q,
    b < q ∧ q < (number_toplevel par role b td).2 → covered (number_toplevel par role b td).1 q := by
  intro td par role b
  cases td with
  | TopDeclaration d =>
    unfold number_toplevel
    dsimp only
    have Hc := number_decl_cover d (some b) RPlain (b + 1)
    rcases h : number_decl (some b) RPlain (b + 1) d with ⟨c, b'⟩
    rw [h] at Hc
    dsimp only at Hc ⊢
    intro q ⟨Hqlo, Hqhi⟩
    by_cases Heq : q = b + 1
    · subst Heq; exact covered_here _ _ _ _ (List.Mem.head _)
    · exact covered_cons _ _ _ (Hc q ⟨Nat.lt_of_le_of_ne Hqlo (fun h => Heq h.symm), Hqhi⟩)
  | Main blk =>
    unfold number_toplevel
    dsimp only
    have Hc := number_block_cover blk (some b) RPlain (b + 1)
    rcases h : number_block (some b) RPlain (b + 1) blk with ⟨c, b'⟩
    rw [h] at Hc
    dsimp only at Hc ⊢
    intro q ⟨Hqlo, Hqhi⟩
    by_cases Heq : q = b + 1
    · subst Heq; exact covered_here _ _ _ _ (List.Mem.head _)
    · exact covered_cons _ _ _ (Hc q ⟨Nat.lt_of_le_of_ne Hqlo (fun h => Heq h.symm), Hqhi⟩)

/-! every non-file position in the file is listed as some occurrence's child — the forest has no
    orphans -/
theorem number_file_cover : ∀ f q,
    0 < q ∧ q < List.length (number_file f) → covered (number_file f) q := by
  intro f q Hq
  unfold number_file at Hq ⊢
  have Hd := number_list_cover (number_toplevel (some 0) RPlain)
    (fun bb x q => number_toplevel_cover x (some 0) RPlain bb q)
    (fun bb x => span_final_ge _ _ (number_toplevel_span (some 0) RPlain bb x)) 1 (Syntax.declarations f)
  have Hsp := number_list_span (number_toplevel (some 0) RPlain)
    (fun bb x => number_toplevel_span (some 0) RPlain bb x) (Syntax.declarations f) 1
  rcases h : number_list (number_toplevel (some 0) RPlain) 1 (Syntax.declarations f) with ⟨dc, bfin, droots⟩
  rw [h] at Hd Hsp Hq
  dsimp only at Hd Hsp Hq ⊢
  obtain ⟨nd, Hmap, Hbfin⟩ := Hsp
  dsimp only at Hmap Hbfin
  obtain ⟨Hqlo, Hqhi⟩ := Hq
  have Hlen : List.length dc = nd := by
    have H := congrArg List.length Hmap
    rw [length_map, List.length_range'] at H
    exact H
  have Hqhi' : q < List.length dc + 1 := Hqhi
  have Hqb : q < bfin := by rw [Hbfin, Nat.add_comm 1 nd, ← Hlen]; exact Hqhi'
  cases Hd q ⟨Hqlo, Hqb⟩ with
  | inl Hin => exact covered_here _ _ _ _ Hin
  | inr Hcov => exact covered_cons _ _ _ Hcov

/-! distinct positions ⇒ one cell per position: two members sharing a position are the same cell -/
theorem occ_unique : ∀ (occs : List (Nat × Cell)) p c1 c2,
    List.Nodup (List.map Prod.fst occs) → (p, c1) ∈ occs → (p, c2) ∈ occs → c1 = c2 := by
  intro occs
  induction occs with
  | nil => intro p c1 c2 _ Hin1; exact nomatch Hin1
  | cons kc rest IH =>
    intro p c1 c2 Hnd Hin1 Hin2
    obtain ⟨k, c⟩ := kc
    have Hnd' : List.Pairwise (fun a b => a ≠ b) (k :: List.map Prod.fst rest) := Hnd
    cases Hnd' with
    | cons Hnotin Hnd'' =>
      cases Hin1 with
      | head =>
        cases Hin2 with
        | head => rfl
        | tail _ Hin2 => exact absurd rfl (Hnotin _ (mem_map_of_mem Prod.fst Hin2))
      | tail _ Hin1 =>
        cases Hin2 with
        | head => exact absurd rfl (Hnotin _ (mem_map_of_mem Prod.fst Hin1))
        | tail _ Hin2 => exact IH p c1 c2 Hnd'' Hin1 Hin2

/-! every represented source occurrence appears once: the ordinal positions of a file are pairwise
    distinct -/
theorem occurrences_distinct : ∀ f, List.Nodup (List.map Prod.fst (number_file f)) := by
  intro f
  obtain ⟨n, Hn⟩ := number_file_positions f
  rw [Hn, List.range_eq_range']
  exact nodup_range' n 0

/-! §4:252 completeness/inverse: any cell whose parent edge names pp is itself listed among pp's children -/
theorem number_file_complete : ∀ f cp ccell pp pcell,
    (cp, ccell) ∈ number_file f → (pp, pcell) ∈ number_file f →
    c_parent ccell = some pp → cp ∈ c_children pcell := by
  intro f cp ccell pp pcell Hinc Hinp Hpar
  have Hnd := occurrences_distinct f
  obtain ⟨Hpp, Hcplt⟩ := number_file_pbounds f cp ccell Hinc pp Hpar
  obtain ⟨count, Hpos⟩ := number_file_positions f
  have Hcpin : cp ∈ List.map Prod.fst (number_file f) := mem_map_of_mem Prod.fst Hinc
  rw [Hpos, List.range_eq_range'] at Hcpin
  obtain ⟨_, Hcpcount⟩ := mem_range'_bounds Hcpin
  have Hlen : List.length (number_file f) = count := by
    rw [← length_map Prod.fst (number_file f), Hpos, List.range_eq_range', List.length_range']
  obtain ⟨r, rcell, Hinr, Hchild⟩ := number_file_cover f cp
    ⟨Nat.lt_of_le_of_lt Hpp Hcplt,
     by rw [Hlen]; exact Nat.lt_of_lt_of_le Hcpcount (Nat.le_of_eq (Nat.zero_add count))⟩
  obtain ⟨ccell', Hinc', Hpar'⟩ := number_file_cpo f r rcell Hinr cp Hchild
  have Hcc : ccell' = ccell := occ_unique (number_file f) cp ccell' ccell Hnd Hinc' Hinc
  subst Hcc
  rw [Hpar] at Hpar'
  have Hrpp : pp = r := Option.some.inj Hpar'
  subst Hrpp
  have Hrc : rcell = pcell := occ_unique (number_file f) _ rcell pcell Hnd Hinr Hinp
  subst Hrc
  exact Hchild

/-! a listed child is a real position, so it falls below the block end that the span fixes -/
theorem child_lt : ∀ occs n b pos cell r,
    List.map Prod.fst occs = List.range' b n → child_parent_ok occs →
    (pos, cell) ∈ occs → r ∈ c_children cell → r < b + n := by
  intro occs n b pos cell r Hmap Hcpo Hin Hr
  obtain ⟨rc, Hinr, _⟩ := Hcpo pos cell Hin r Hr
  have Hinr' : r ∈ List.map Prod.fst occs := mem_map_of_mem Prod.fst Hinr
  rw [Hmap] at Hinr'
  exact (mem_range'_bounds Hinr').2

/-! ## Section 3 (`.v` lines 1601–2446) -/

/-! the extent field exactly delimits each cell's block: its own position at or below it, its children within
    it -/
def ext_ok (bnd : Nat) (occs : List (Nat × Cell)) : Prop :=
  ∀ kv ∈ occs, (kv.1 ≤ c_extent kv.2 ∧ c_extent kv.2 < bnd) ∧
               (∀ r ∈ c_children kv.2, r ≤ c_extent kv.2)

theorem ext_ok_weaken : ∀ bnd bnd' occs, bnd ≤ bnd' → ext_ok bnd occs → ext_ok bnd' occs := by
  intro bnd bnd' occs Hle H kv Hkv
  obtain ⟨⟨H1, H2⟩, H3⟩ := H kv Hkv
  exact ⟨⟨H1, Nat.lt_of_lt_of_le H2 Hle⟩, H3⟩

theorem ext_ok_app : ∀ bnd c1 c2, ext_ok bnd c1 → ext_ok bnd c2 → ext_ok bnd (c1 ++ c2) := by
  intro bnd c1 c2 H1 H2 kv Hkv
  cases mem_app_or Hkv with
  | inl H => exact H1 kv H
  | inr H => exact H2 kv H

-- Rocq's `Forall` constructors, for `ext_ok` (core has no `List.Forall`)
private theorem ext_ok_nil (bnd : Nat) : ext_ok bnd [] := fun _ H => nomatch H
private theorem ext_ok_cons (self : Nat) (cell : Cell) (kids : List (Nat × Cell)) (bnd : Nat)
    (H : (self ≤ c_extent cell ∧ c_extent cell < bnd) ∧ ∀ r ∈ c_children cell, r ≤ c_extent cell)
    (Hk : ext_ok bnd kids) : ext_ok bnd ((self, cell) :: kids) := by
  intro kv Hkv
  cases Hkv with
  | head => exact H
  | tail _ Hkv' => exact Hk kv Hkv'

-- the root cell's own clause, from the two facts every composite has: its block end is past its position
-- and past each listed child (the `.v` closes each with `lia` from `child_lt`)
private theorem ext_head (b bfin : Nat) (ch : List Nat) (Hb : b < bfin) (Hch : ∀ r ∈ ch, r < bfin) :
    (b ≤ bfin - 1 ∧ bfin - 1 < bfin) ∧ ∀ r ∈ ch, r ≤ bfin - 1 :=
  ⟨⟨Nat.le_sub_one_of_lt Hb, Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le b) Hb) Nat.zero_lt_one⟩,
   fun r Hr => Nat.le_sub_one_of_lt (Hch r Hr)⟩

-- the `.v`'s inner `assert (Hda : …)` of number_expr_ext, about `number_args`
private theorem number_args_ext_of (b : Nat) : ∀ es : List Syntax.Expr,
    (∀ a ∈ es, ∀ par role bb, ext_ok (number_expr par role bb a).2 (number_expr par role bb a).1) →
    ∀ i0 bi, ext_ok (number_args b i0 bi es).2.1 (number_args b i0 bi es).1
             ∧ bi ≤ (number_args b i0 bi es).2.1 := by
  intro es
  induction es with
  | nil => intro _ i0 bi; exact ⟨ext_ok_nil _, Nat.le_refl bi⟩
  | cons a rest IH =>
    intro Hall i0 bi
    obtain ⟨na, _, Hbi', _⟩ := number_expr_span a (some b) (RApplicationArg i0) bi
    have Ha := Hall a (List.Mem.head _) (some b) (RApplicationArg i0) bi
    obtain ⟨Hrc, Hle2⟩ := IH (fun x hx => Hall x (List.Mem.tail _ hx)) (i0 + 1)
      (number_expr (some b) (RApplicationArg i0) bi a).2
    rw [number_args_cons_fst, number_args_cons_next]
    exact ⟨ext_ok_app _ _ _ (ext_ok_weaken _ _ _ Hle2 Ha) Hrc,
           Nat.le_trans (by rw [Hbi']; exact Nat.le_add_right bi na) Hle2⟩

theorem number_expr_ext : ∀ e par role b,
    ext_ok (number_expr par role b e).2 (number_expr par role b e).1 := by
  intro e
  induction e using Syntax.Expr_ind' with
  | HName n =>
    intro par role b
    exact ext_ok_cons _ _ _ _ ⟨⟨Nat.le_refl b, Nat.lt_succ_self b⟩, fun _ Hr => nomatch Hr⟩ (ext_ok_nil _)
  | HLit l =>
    intro par role b
    exact ext_ok_cons _ _ _ _ ⟨⟨Nat.le_refl b, Nat.lt_succ_self b⟩, fun _ Hr => nomatch Hr⟩ (ext_ok_nil _)
  | HUnary op e' IH =>
    intro par role b
    have IH' := IH (some b) RUnaryOperand (b + 1)
    have Hcpo := number_expr_cpo (Syntax.Unary op e') par role b
    obtain ⟨n, Hmap, Hnxt⟩ := number_expr_spans (Syntax.Unary op e') par role b
    rw [number_expr_unary_fst] at Hcpo Hmap
    rw [number_expr_unary_snd] at Hnxt
    rw [number_expr_unary_fst, number_expr_unary_snd]
    have HSb : b + 1 < (number_expr (some b) RUnaryOperand (b + 1) e').2 := by
      rw [Hnxt]; exact child_lt _ n b b _ (b + 1) Hmap Hcpo (List.Mem.head _) (List.Mem.head _)
    exact ext_ok_cons _ _ _ _
      (ext_head b _ [b + 1] (Nat.lt_trans (Nat.lt_succ_self b) HSb)
        (fun r Hr => by
          cases Hr with
          | head => exact HSb
          | tail _ H => exact nomatch H))
      IH'
  | HApp head args IHh IHa =>
    intro par role b
    have IHh' := IHh (some b) RApplicationHead (b + 1)
    have Hcpo := number_expr_cpo (Syntax.Application head args) par role b
    obtain ⟨n, Hmap, Hbfin⟩ := number_expr_spans (Syntax.Application head args) par role b
    rw [number_expr_app_fst] at Hcpo Hmap
    rw [number_expr_app_snd] at Hbfin
    obtain ⟨Hext, Hble⟩ := number_args_ext_of b args IHa 0
      (number_expr (some b) RApplicationHead (b + 1) head).2
    rw [number_expr_app_fst, number_expr_app_snd]
    have Hchild : ∀ r ∈ (b + 1) :: (number_args b 0 (number_expr (some b) RApplicationHead (b + 1) head).2 args).2.2,
        r < (number_args b 0 (number_expr (some b) RApplicationHead (b + 1) head).2 args).2.1 :=
      fun r Hr => by rw [Hbfin]; exact child_lt _ n b b _ r Hmap Hcpo (List.Mem.head _) Hr
    exact ext_ok_cons _ _ _ _
      (ext_head b _ _ (Nat.lt_trans (Nat.lt_succ_self b) (Hchild (b + 1) (List.Mem.head _))) Hchild)
      (ext_ok_app _ _ _ (ext_ok_weaken _ _ _ Hble IHh') Hext)

theorem map_seq_pos : ∀ (occs : List (Nat × Cell)) n b,
    List.map Prod.fst occs = List.range' b n → occs ≠ [] → 0 < n := by
  intro occs n b Hmap Hne
  cases occs with
  | nil => exact absurd rfl Hne
  | cons x l =>
    cases n with
    | zero => exact nomatch Hmap
    | succ n => exact Nat.zero_lt_succ n

theorem number_typeexpr_ext : ∀ t par role b,
    ext_ok (number_typeexpr par role b t).2 (number_typeexpr par role b t).1 :=
  fun _ _ _ b => ext_ok_cons _ _ _ _ ⟨⟨Nat.le_refl b, Nat.lt_succ_self b⟩, fun _ Hr => nomatch Hr⟩ (ext_ok_nil _)

theorem number_bindingname_ext : ∀ bn par role b,
    ext_ok (number_bindingname par role b bn).2 (number_bindingname par role b bn).1 :=
  fun _ _ _ b => ext_ok_cons _ _ _ _ ⟨⟨Nat.le_refl b, Nat.lt_succ_self b⟩, fun _ Hr => nomatch Hr⟩ (ext_ok_nil _)

theorem number_opttype_ext : ∀ ot par b,
    ext_ok (number_opttype par b ot).2.1 (number_opttype par b ot).1 := by
  intro ot par b
  cases ot with
  | some t => exact number_typeexpr_ext t par RTypeUse b
  | none => exact ext_ok_nil _

theorem number_list_ext {A : Type} (g : Nat → A → List (Nat × Cell) × Nat) :
    (∀ b x, ext_ok (g b x).2 (g b x).1) →
    (∀ b x, b ≤ (g b x).2) →
    ∀ b xs, ext_ok (number_list g b xs).2.1 (number_list g b xs).1 ∧
            b ≤ (number_list g b xs).2.1 := by
  intro Hg Hmono b xs
  induction xs generalizing b with
  | nil => exact ⟨ext_ok_nil _, Nat.le_refl b⟩
  | cons x rest IH =>
    have Hgx := Hg b x
    have Hm := Hmono b x
    obtain ⟨Hrc, Hle⟩ := IH (g b x).2
    rw [number_list_cons_fst, number_list_cons_next]
    exact ⟨ext_ok_app _ _ _ (ext_ok_weaken _ _ _ Hle Hgx) Hrc, Nat.le_trans Hm Hle⟩

theorem number_constspec_ext : ∀ cs par role b,
    ext_ok (number_constspec par role b cs).2 (number_constspec par role b cs).1 := by
  intro ⟨names, init⟩ par role b
  have Hcpo := number_constspec_cpo par role b ⟨names, init⟩
  obtain ⟨n, Hmap, Hsnd⟩ := number_constspec_span par role b ⟨names, init⟩
  obtain ⟨Hnc, _⟩ := number_list_ext (number_bindingname (some b) (RSpecName ConstSpecF))
    (fun bb x => number_bindingname_ext x (some b) (RSpecName ConstSpecF) bb)
    (fun bb x => span_final_ge _ _ (number_bindingname_spans (some b) (RSpecName ConstSpecF) bb x))
    (b + 1) (Collections.ne_to_list names)
  unfold number_constspec at Hcpo Hmap Hsnd ⊢
  dsimp only at Hcpo Hmap Hsnd ⊢
  rcases h1 : number_list (number_bindingname (some b) (RSpecName ConstSpecF)) (b + 1)
    (Collections.ne_to_list names) with ⟨nc, b1, nroots⟩
  rw [h1] at Hnc Hcpo Hmap Hsnd
  dsimp only at Hnc Hcpo Hmap Hsnd ⊢
  cases init with
  | ExplicitConstInit ot vals =>
    dsimp only at Hcpo Hmap Hsnd ⊢
    have Hoc := number_opttype_ext ot (some b) b1
    have Hb2 := span_final_ge _ _ (number_opttype_span (some b) b1 ot)
    rcases h2 : number_opttype (some b) b1 ot with ⟨oc, b2, oroots⟩
    rw [h2] at Hoc Hb2 Hcpo Hmap Hsnd
    dsimp only at Hoc Hb2 Hcpo Hmap Hsnd ⊢
    obtain ⟨Hvc, Hvc_le⟩ := number_list_ext (number_expr (some b) RPlain)
      (fun bb x => number_expr_ext x (some b) RPlain bb)
      (fun bb x => span_final_ge _ _ (number_expr_spans x (some b) RPlain bb))
      b2 (Collections.ne_to_list vals)
    rcases h3 : number_list (number_expr (some b) RPlain) b2 (Collections.ne_to_list vals)
      with ⟨vc, b3, vroots⟩
    rw [h3] at Hvc Hvc_le Hcpo Hmap Hsnd
    dsimp only at Hvc Hvc_le Hcpo Hmap Hsnd ⊢
    have Hn : 0 < n := map_seq_pos _ n b Hmap (fun H => nomatch H)
    have Hb3 : b < b3 := by rw [Hsnd]; exact Nat.lt_add_of_pos_right Hn
    have Hchild : ∀ r ∈ nroots ++ (oroots ++ vroots), r < b3 :=
      fun r Hr => by rw [Hsnd]; exact child_lt _ n b b _ r Hmap Hcpo (List.Mem.head _) Hr
    exact ext_ok_cons _ _ _ _ (ext_head b b3 _ Hb3 Hchild)
      (ext_ok_app _ _ _ (ext_ok_weaken _ _ _ (Nat.le_trans Hb2 Hvc_le) Hnc)
        (ext_ok_app _ _ _ (ext_ok_weaken _ _ _ Hvc_le Hoc) Hvc))
  | InheritedConstInit =>
    dsimp only at Hcpo Hmap Hsnd ⊢
    have Hn : 0 < n := map_seq_pos _ n b Hmap (fun H => nomatch H)
    have Hb1 : b < b1 := by rw [Hsnd]; exact Nat.lt_add_of_pos_right Hn
    have Hchild : ∀ r ∈ nroots ++ [], r < b1 :=
      fun r Hr => by rw [Hsnd]; exact child_lt _ n b b _ r Hmap Hcpo (List.Mem.head _) Hr
    exact ext_ok_cons _ _ _ _ (ext_head b b1 _ Hb1 Hchild) (by rw [app_nil]; exact Hnc)

theorem number_varspec_ext : ∀ vs par role b,
    ext_ok (number_varspec par role b vs).2 (number_varspec par role b vs).1 := by
  intro ⟨names, init⟩ par role b
  have Hcpo := number_varspec_cpo par role b ⟨names, init⟩
  obtain ⟨n, Hmap, Hsnd⟩ := number_varspec_span par role b ⟨names, init⟩
  obtain ⟨Hnc, _⟩ := number_list_ext (number_bindingname (some b) (RSpecName VarSpecF))
    (fun bb x => number_bindingname_ext x (some b) (RSpecName VarSpecF) bb)
    (fun bb x => span_final_ge _ _ (number_bindingname_spans (some b) (RSpecName VarSpecF) bb x))
    (b + 1) (Collections.ne_to_list names)
  unfold number_varspec at Hcpo Hmap Hsnd ⊢
  dsimp only at Hcpo Hmap Hsnd ⊢
  rcases h1 : number_list (number_bindingname (some b) (RSpecName VarSpecF)) (b + 1)
    (Collections.ne_to_list names) with ⟨nc, b1, nroots⟩
  rw [h1] at Hnc Hcpo Hmap Hsnd
  dsimp only at Hnc Hcpo Hmap Hsnd ⊢
  cases init with
  | VarTypeOnly t =>
    dsimp only at Hcpo Hmap Hsnd ⊢
    have Htc := number_typeexpr_ext t (some b) RTypeUse b1
    have Hb2 := span_final_ge _ _ (number_typeexpr_spans (some b) RTypeUse b1 t)
    rcases h2 : number_typeexpr (some b) RTypeUse b1 t with ⟨tc, b2⟩
    rw [h2] at Htc Hb2 Hcpo Hmap Hsnd
    dsimp only at Htc Hb2 Hcpo Hmap Hsnd ⊢
    have Hn : 0 < n := map_seq_pos _ n b Hmap (fun H => nomatch H)
    have Hb2' : b < b2 := by rw [Hsnd]; exact Nat.lt_add_of_pos_right Hn
    have Hchild : ∀ r ∈ nroots ++ [b1], r < b2 :=
      fun r Hr => by rw [Hsnd]; exact child_lt _ n b b _ r Hmap Hcpo (List.Mem.head _) Hr
    exact ext_ok_cons _ _ _ _ (ext_head b b2 _ Hb2' Hchild)
      (ext_ok_app _ _ _ (ext_ok_weaken _ _ _ Hb2 Hnc) Htc)
  | VarValues ot vals =>
    dsimp only at Hcpo Hmap Hsnd ⊢
    have Hoc := number_opttype_ext ot (some b) b1
    have Hb2 := span_final_ge _ _ (number_opttype_span (some b) b1 ot)
    rcases h2 : number_opttype (some b) b1 ot with ⟨oc, b2, oroots⟩
    rw [h2] at Hoc Hb2 Hcpo Hmap Hsnd
    dsimp only at Hoc Hb2 Hcpo Hmap Hsnd ⊢
    obtain ⟨Hvc, Hvc_le⟩ := number_list_ext (number_expr (some b) RPlain)
      (fun bb x => number_expr_ext x (some b) RPlain bb)
      (fun bb x => span_final_ge _ _ (number_expr_spans x (some b) RPlain bb))
      b2 (Collections.ne_to_list vals)
    rcases h3 : number_list (number_expr (some b) RPlain) b2 (Collections.ne_to_list vals)
      with ⟨vc, b3, vroots⟩
    rw [h3] at Hvc Hvc_le Hcpo Hmap Hsnd
    dsimp only at Hvc Hvc_le Hcpo Hmap Hsnd ⊢
    have Hn : 0 < n := map_seq_pos _ n b Hmap (fun H => nomatch H)
    have Hb3 : b < b3 := by rw [Hsnd]; exact Nat.lt_add_of_pos_right Hn
    have Hchild : ∀ r ∈ nroots ++ (oroots ++ vroots), r < b3 :=
      fun r Hr => by rw [Hsnd]; exact child_lt _ n b b _ r Hmap Hcpo (List.Mem.head _) Hr
    exact ext_ok_cons _ _ _ _ (ext_head b b3 _ Hb3 Hchild)
      (ext_ok_app _ _ _ (ext_ok_weaken _ _ _ (Nat.le_trans Hb2 Hvc_le) Hnc)
        (ext_ok_app _ _ _ (ext_ok_weaken _ _ _ Hvc_le Hoc) Hvc))

theorem number_typespec_ext : ∀ ts par role b,
    ext_ok (number_typespec par role b ts).2 (number_typespec par role b ts).1 := by
  intro ts par role b
  have Hcpo := number_typespec_cpo par role b ts
  obtain ⟨n, Hmap, Hsnd⟩ := number_typespec_span par role b ts
  cases ts with
  | AliasSpec bn t | DefSpec bn t =>
    unfold number_typespec at Hcpo Hmap Hsnd ⊢
    dsimp only at Hcpo Hmap Hsnd ⊢
    have Hbc := number_bindingname_ext bn (some b) (RSpecName TypeSpecF) (b + 1)
    have Hb1 := span_final_ge _ _ (number_bindingname_spans (some b) (RSpecName TypeSpecF) (b + 1) bn)
    rcases h1 : number_bindingname (some b) (RSpecName TypeSpecF) (b + 1) bn with ⟨bc, b1⟩
    rw [h1] at Hbc Hb1 Hcpo Hmap Hsnd
    have Htc := number_typeexpr_ext t (some b) RTypeUse b1
    have Hbfin := span_final_ge _ _ (number_typeexpr_spans (some b) RTypeUse b1 t)
    rcases h2 : number_typeexpr (some b) RTypeUse b1 t with ⟨tc, bfin⟩
    rw [h2] at Htc Hbfin Hcpo Hmap Hsnd
    dsimp only at Hbc Hb1 Htc Hbfin Hcpo Hmap Hsnd ⊢
    have Hn : 0 < n := map_seq_pos _ n b Hmap (fun H => nomatch H)
    have Hbfin' : b < bfin := by rw [Hsnd]; exact Nat.lt_add_of_pos_right Hn
    have Hchild : ∀ r ∈ [b + 1, b1], r < bfin :=
      fun r Hr => by rw [Hsnd]; exact child_lt _ n b b _ r Hmap Hcpo (List.Mem.head _) Hr
    exact ext_ok_cons _ _ _ _ (ext_head b bfin _ Hbfin' Hchild)
      (ext_ok_app _ _ _ (ext_ok_weaken _ _ _ Hbfin Hbc) Htc)

theorem number_decl_ext : ∀ d par role b,
    ext_ok (number_decl par role b d).2 (number_decl par role b d).1 := by
  intro d par role b
  have Hcpo := number_decl_cpo par role b d
  obtain ⟨n, Hmap, Hsnd⟩ := number_decl_span par role b d
  cases d with
  | ConstDecl cs =>
    unfold number_decl at Hcpo Hmap Hsnd ⊢
    dsimp only at Hcpo Hmap Hsnd ⊢
    obtain ⟨Hk, _⟩ := number_list_ext (number_constspec (some b) RPlain)
      (fun bb x => number_constspec_ext x (some b) RPlain bb)
      (fun bb x => span_final_ge _ _ (number_constspec_span (some b) RPlain bb x)) (b + 1) cs
    rcases h : number_list (number_constspec (some b) RPlain) (b + 1) cs with ⟨kc, bfin, roots⟩
    rw [h] at Hk Hcpo Hmap Hsnd
    dsimp only at Hk Hcpo Hmap Hsnd ⊢
    have Hn : 0 < n := map_seq_pos _ n b Hmap (fun H => nomatch H)
    have Hbfin : b < bfin := by rw [Hsnd]; exact Nat.lt_add_of_pos_right Hn
    have Hchild : ∀ r ∈ roots, r < bfin :=
      fun r Hr => by rw [Hsnd]; exact child_lt _ n b b _ r Hmap Hcpo (List.Mem.head _) Hr
    exact ext_ok_cons _ _ _ _ (ext_head b bfin _ Hbfin Hchild) Hk
  | VarDecl vs =>
    unfold number_decl at Hcpo Hmap Hsnd ⊢
    dsimp only at Hcpo Hmap Hsnd ⊢
    obtain ⟨Hk, _⟩ := number_list_ext (number_varspec (some b) RPlain)
      (fun bb x => number_varspec_ext x (some b) RPlain bb)
      (fun bb x => span_final_ge _ _ (number_varspec_span (some b) RPlain bb x)) (b + 1) vs
    rcases h : number_list (number_varspec (some b) RPlain) (b + 1) vs with ⟨kc, bfin, roots⟩
    rw [h] at Hk Hcpo Hmap Hsnd
    dsimp only at Hk Hcpo Hmap Hsnd ⊢
    have Hn : 0 < n := map_seq_pos _ n b Hmap (fun H => nomatch H)
    have Hbfin : b < bfin := by rw [Hsnd]; exact Nat.lt_add_of_pos_right Hn
    have Hchild : ∀ r ∈ roots, r < bfin :=
      fun r Hr => by rw [Hsnd]; exact child_lt _ n b b _ r Hmap Hcpo (List.Mem.head _) Hr
    exact ext_ok_cons _ _ _ _ (ext_head b bfin _ Hbfin Hchild) Hk
  | TypeDecl ts =>
    unfold number_decl at Hcpo Hmap Hsnd ⊢
    dsimp only at Hcpo Hmap Hsnd ⊢
    obtain ⟨Hk, _⟩ := number_list_ext (number_typespec (some b) RPlain)
      (fun bb x => number_typespec_ext x (some b) RPlain bb)
      (fun bb x => span_final_ge _ _ (number_typespec_span (some b) RPlain bb x)) (b + 1) ts
    rcases h : number_list (number_typespec (some b) RPlain) (b + 1) ts with ⟨kc, bfin, roots⟩
    rw [h] at Hk Hcpo Hmap Hsnd
    dsimp only at Hk Hcpo Hmap Hsnd ⊢
    have Hn : 0 < n := map_seq_pos _ n b Hmap (fun H => nomatch H)
    have Hbfin : b < bfin := by rw [Hsnd]; exact Nat.lt_add_of_pos_right Hn
    have Hchild : ∀ r ∈ roots, r < bfin :=
      fun r Hr => by rw [Hsnd]; exact child_lt _ n b b _ r Hmap Hcpo (List.Mem.head _) Hr
    exact ext_ok_cons _ _ _ _ (ext_head b bfin _ Hbfin Hchild) Hk

theorem number_stmt_ext : ∀ s par role b,
    ext_ok (number_stmt par role b s).2 (number_stmt par role b s).1 := by
  intro s par role b
  have Hcpo := number_stmt_cpo par role b s
  obtain ⟨n, Hmap, Hsnd⟩ := number_stmt_span par role b s
  cases s with
  | ExprStmt e =>
    unfold number_stmt at Hcpo Hmap Hsnd ⊢
    dsimp only at Hcpo Hmap Hsnd ⊢
    have Hc := number_expr_ext e (some b) RExprStatementExpr (b + 1)
    rcases h : number_expr (some b) RExprStatementExpr (b + 1) e with ⟨c, b'⟩
    rw [h] at Hc Hcpo Hmap Hsnd
    dsimp only at Hc Hcpo Hmap Hsnd ⊢
    have Hn : 0 < n := map_seq_pos _ n b Hmap (fun H => nomatch H)
    have Hb' : b < b' := by rw [Hsnd]; exact Nat.lt_add_of_pos_right Hn
    have Hchild : ∀ r ∈ [b + 1], r < b' :=
      fun r Hr => by rw [Hsnd]; exact child_lt _ n b b _ r Hmap Hcpo (List.Mem.head _) Hr
    exact ext_ok_cons _ _ _ _ (ext_head b b' _ Hb' Hchild) Hc
  | DeclarationStmt d =>
    unfold number_stmt at Hcpo Hmap Hsnd ⊢
    dsimp only at Hcpo Hmap Hsnd ⊢
    have Hc := number_decl_ext d (some b) RPlain (b + 1)
    rcases h : number_decl (some b) RPlain (b + 1) d with ⟨c, b'⟩
    rw [h] at Hc Hcpo Hmap Hsnd
    dsimp only at Hc Hcpo Hmap Hsnd ⊢
    have Hn : 0 < n := map_seq_pos _ n b Hmap (fun H => nomatch H)
    have Hb' : b < b' := by rw [Hsnd]; exact Nat.lt_add_of_pos_right Hn
    have Hchild : ∀ r ∈ [b + 1], r < b' :=
      fun r Hr => by rw [Hsnd]; exact child_lt _ n b b _ r Hmap Hcpo (List.Mem.head _) Hr
    exact ext_ok_cons _ _ _ _ (ext_head b b' _ Hb' Hchild) Hc
  | ShortVarDecl names vals =>
    unfold number_stmt at Hcpo Hmap Hsnd ⊢
    dsimp only at Hcpo Hmap Hsnd ⊢
    obtain ⟨Hnc, _⟩ := number_list_ext (number_bindingname (some b) RShortLhs)
      (fun bb x => number_bindingname_ext x (some b) RShortLhs bb)
      (fun bb x => span_final_ge _ _ (number_bindingname_spans (some b) RShortLhs bb x))
      (b + 1) (Collections.ne_to_list names)
    rcases h1 : number_list (number_bindingname (some b) RShortLhs) (b + 1) (Collections.ne_to_list names)
      with ⟨nc, b1, nroots⟩
    rw [h1] at Hnc Hcpo Hmap Hsnd
    dsimp only at Hnc Hcpo Hmap Hsnd ⊢
    obtain ⟨Hvc, Hvc_le⟩ := number_list_ext (number_expr (some b) RPlain)
      (fun bb x => number_expr_ext x (some b) RPlain bb)
      (fun bb x => span_final_ge _ _ (number_expr_spans x (some b) RPlain bb))
      b1 (Collections.ne_to_list vals)
    rcases h2 : number_list (number_expr (some b) RPlain) b1 (Collections.ne_to_list vals)
      with ⟨vc, b2, vroots⟩
    rw [h2] at Hvc Hvc_le Hcpo Hmap Hsnd
    dsimp only at Hvc Hvc_le Hcpo Hmap Hsnd ⊢
    have Hn : 0 < n := map_seq_pos _ n b Hmap (fun H => nomatch H)
    have Hb2 : b < b2 := by rw [Hsnd]; exact Nat.lt_add_of_pos_right Hn
    have Hchild : ∀ r ∈ nroots ++ vroots, r < b2 :=
      fun r Hr => by rw [Hsnd]; exact child_lt _ n b b _ r Hmap Hcpo (List.Mem.head _) Hr
    exact ext_ok_cons _ _ _ _ (ext_head b b2 _ Hb2 Hchild)
      (ext_ok_app _ _ _ (ext_ok_weaken _ _ _ Hvc_le Hnc) Hvc)

theorem number_block_ext : ∀ blk par role b,
    ext_ok (number_block par role b blk).2 (number_block par role b blk).1 := by
  intro ⟨stmts⟩ par role b
  have Hcpo := number_block_cpo par role b ⟨stmts⟩
  obtain ⟨n, Hmap, Hsnd⟩ := number_block_span par role b ⟨stmts⟩
  unfold number_block at Hcpo Hmap Hsnd ⊢
  dsimp only at Hcpo Hmap Hsnd ⊢
  obtain ⟨Hk, _⟩ := number_list_ext (number_stmt (some b) RPlain)
    (fun bb x => number_stmt_ext x (some b) RPlain bb)
    (fun bb x => span_final_ge _ _ (number_stmt_span (some b) RPlain bb x)) (b + 1) stmts
  rcases h : number_list (number_stmt (some b) RPlain) (b + 1) stmts with ⟨kc, bfin, roots⟩
  rw [h] at Hk Hcpo Hmap Hsnd
  dsimp only at Hk Hcpo Hmap Hsnd ⊢
  have Hn : 0 < n := map_seq_pos _ n b Hmap (fun H => nomatch H)
  have Hbfin : b < bfin := by rw [Hsnd]; exact Nat.lt_add_of_pos_right Hn
  have Hchild : ∀ r ∈ roots, r < bfin :=
    fun r Hr => by rw [Hsnd]; exact child_lt _ n b b _ r Hmap Hcpo (List.Mem.head _) Hr
  exact ext_ok_cons _ _ _ _ (ext_head b bfin _ Hbfin Hchild) Hk

theorem number_toplevel_ext : ∀ td par role b,
    ext_ok (number_toplevel par role b td).2 (number_toplevel par role b td).1 := by
  intro td par role b
  have Hcpo := number_toplevel_cpo par role b td
  obtain ⟨n, Hmap, Hsnd⟩ := number_toplevel_span par role b td
  cases td with
  | TopDeclaration d =>
    unfold number_toplevel at Hcpo Hmap Hsnd ⊢
    dsimp only at Hcpo Hmap Hsnd ⊢
    have Hc := number_decl_ext d (some b) RPlain (b + 1)
    rcases h : number_decl (some b) RPlain (b + 1) d with ⟨c, b'⟩
    rw [h] at Hc Hcpo Hmap Hsnd
    dsimp only at Hc Hcpo Hmap Hsnd ⊢
    have Hn : 0 < n := map_seq_pos _ n b Hmap (fun H => nomatch H)
    have Hb' : b < b' := by rw [Hsnd]; exact Nat.lt_add_of_pos_right Hn
    have Hchild : ∀ r ∈ [b + 1], r < b' :=
      fun r Hr => by rw [Hsnd]; exact child_lt _ n b b _ r Hmap Hcpo (List.Mem.head _) Hr
    exact ext_ok_cons _ _ _ _ (ext_head b b' _ Hb' Hchild) Hc
  | Main blk =>
    unfold number_toplevel at Hcpo Hmap Hsnd ⊢
    dsimp only at Hcpo Hmap Hsnd ⊢
    have Hc := number_block_ext blk (some b) RPlain (b + 1)
    rcases h : number_block (some b) RPlain (b + 1) blk with ⟨c, b'⟩
    rw [h] at Hc Hcpo Hmap Hsnd
    dsimp only at Hc Hcpo Hmap Hsnd ⊢
    have Hn : 0 < n := map_seq_pos _ n b Hmap (fun H => nomatch H)
    have Hb' : b < b' := by rw [Hsnd]; exact Nat.lt_add_of_pos_right Hn
    have Hchild : ∀ r ∈ [b + 1], r < b' :=
      fun r Hr => by rw [Hsnd]; exact child_lt _ n b b _ r Hmap Hcpo (List.Mem.head _) Hr
    exact ext_ok_cons _ _ _ _ (ext_head b b' _ Hb' Hchild) Hc

theorem number_file_ext : ∀ f, ext_ok (List.length (number_file f)) (number_file f) := by
  intro f
  have Hcpo := number_file_cpo f
  obtain ⟨n, Hmap⟩ := number_file_positions f
  unfold number_file at Hcpo Hmap ⊢
  have Hsp := number_list_span (number_toplevel (some 0) RPlain)
    (fun bb x => number_toplevel_span (some 0) RPlain bb x) (Syntax.declarations f) 1
  obtain ⟨Hd, _⟩ := number_list_ext (number_toplevel (some 0) RPlain)
    (fun bb x => number_toplevel_ext x (some 0) RPlain bb)
    (fun bb x => span_final_ge _ _ (number_toplevel_span (some 0) RPlain bb x)) 1 (Syntax.declarations f)
  rcases h : number_list (number_toplevel (some 0) RPlain) 1 (Syntax.declarations f) with ⟨dc, bfin, droots⟩
  rw [h] at Hcpo Hmap Hsp Hd
  dsimp only at Hcpo Hmap Hsp Hd ⊢
  obtain ⟨nd, Hmapd, Hbfin⟩ := Hsp
  dsimp only at Hmapd Hbfin
  have Hlend : List.length dc = nd := by
    have H := congrArg List.length Hmapd
    rw [length_map, List.length_range'] at H
    exact H
  rw [List.range_eq_range'] at Hmap
  have Hnn : List.length dc + 1 = n := by
    have H : (List.map Prod.fst dc).length + 1 = (List.range' 0 n).length := congrArg List.length Hmap
    rw [length_map, List.length_range'] at H
    exact H
  have Hchild : ∀ r ∈ droots, r < List.length dc + 1 := fun r Hr => by
    rw [Hnn, ← Nat.zero_add n]
    exact child_lt _ n 0 0 _ r Hmap Hcpo (List.Mem.head _) Hr
  have Hbfin' : bfin = List.length dc + 1 := by rw [Hbfin, Hlend, Nat.add_comm]
  show ext_ok (List.length dc + 1) ((0, mkCell VFile RPlain none (bfin - 1) droots 0) :: dc)
  rw [Hbfin'] at Hd ⊢
  exact ext_ok_cons _ _ _ _ (ext_head 0 _ _ (Nat.zero_lt_succ _) Hchild) Hd

/-! extent is exact: in range, at least the node's own position, and at or above every direct child -/
theorem number_file_extent : ∀ f pos cell,
    (pos, cell) ∈ number_file f →
    (pos ≤ c_extent cell ∧ c_extent cell < List.length (number_file f)) ∧
    (∀ q qc, (q, qc) ∈ number_file f → c_parent qc = some pos → q ≤ c_extent cell) := by
  intro f pos cell Hin
  obtain ⟨Hrange, Hch⟩ := number_file_ext f (pos, cell) Hin
  exact ⟨Hrange, fun q qc Hinq Hpar => Hch q (number_file_complete f q qc pos cell Hinq Hin Hpar)⟩

/-! the kind a structural role commits its node to; the generic RPlain commits to none -/
def role_kind_of (r : Role) : Option Kind :=
  match r with
  | RApplicationHead | RApplicationArg _ | RUnaryOperand | RExprStatementExpr => some ExprKind
  | RSpecName _ | RShortLhs => some BindingNameKind
  | RTypeUse => some TypeExprKind
  | RPlain => none

def rv_ok (cell : Cell) : Prop :=
  match role_kind_of (c_role cell) with | some k => kind_of_view (c_view cell) = k | none => True

def role_ok_for (k : Kind) (r : Role) : Prop :=
  match role_kind_of r with | none => True | some k' => k' = k

def class_ok (occs : List (Nat × Cell)) : Prop := ∀ kv ∈ occs, rv_ok kv.2

theorem class_ok_app : ∀ c1 c2, class_ok c1 → class_ok c2 → class_ok (c1 ++ c2) := by
  intro c1 c2 H1 H2 kv Hkv
  cases mem_app_or Hkv with
  | inl H => exact H1 kv H
  | inr H => exact H2 kv H

-- Rocq's `Forall` constructors, for `class_ok`
private theorem class_ok_nil : class_ok [] := fun _ H => nomatch H
private theorem class_ok_cons (self : Nat) (cell : Cell) (kids : List (Nat × Cell))
    (H : rv_ok cell) (Hk : class_ok kids) : class_ok ((self, cell) :: kids) := by
  intro kv Hkv
  cases Hkv with
  | head => exact H
  | tail _ Hkv' => exact Hk kv Hkv'

theorem rv_ok_mk : ∀ v role par ext ch k sl,
    kind_of_view v = k → role_ok_for k role → rv_ok (mkCell v role par ext ch sl) := by
  intro v role par ext ch k sl Hk Hr
  cases role with
  | RPlain => exact True.intro
  | RApplicationHead => exact Hk.trans (Hr : ExprKind = k).symm
  | RApplicationArg i => exact Hk.trans (Hr : ExprKind = k).symm
  | RUnaryOperand => exact Hk.trans (Hr : ExprKind = k).symm
  | RExprStatementExpr => exact Hk.trans (Hr : ExprKind = k).symm
  | RSpecName fl => exact Hk.trans (Hr : BindingNameKind = k).symm
  | RShortLhs => exact Hk.trans (Hr : BindingNameKind = k).symm
  | RTypeUse => exact Hk.trans (Hr : TypeExprKind = k).symm

-- the `.v`'s inner `assert (Hda : …)` of number_expr_class, about `number_args`
private theorem number_args_class_of (b : Nat) : ∀ es : List Syntax.Expr,
    (∀ a ∈ es, ∀ par role bb, role_ok_for ExprKind role → class_ok (number_expr par role bb a).1) →
    ∀ i0 bi, class_ok (number_args b i0 bi es).1 := by
  intro es
  induction es with
  | nil => intro _ i0 bi; exact class_ok_nil
  | cons a rest IH =>
    intro Hall i0 bi
    have Ha := Hall a (List.Mem.head _) (some b) (RApplicationArg i0) bi rfl
    have IHrest := IH (fun x hx => Hall x (List.Mem.tail _ hx)) (i0 + 1)
      (number_expr (some b) (RApplicationArg i0) bi a).2
    rw [number_args_cons_fst]
    exact class_ok_app _ _ Ha IHrest

theorem number_expr_class : ∀ e par role b,
    role_ok_for ExprKind role → class_ok (number_expr par role b e).1 := by
  intro e
  induction e using Syntax.Expr_ind' with
  | HName n =>
    intro par role b Hr
    exact class_ok_cons _ _ _ (rv_ok_mk _ _ _ _ _ ExprKind _ rfl Hr) class_ok_nil
  | HLit l =>
    intro par role b Hr
    exact class_ok_cons _ _ _ (rv_ok_mk _ _ _ _ _ ExprKind _ rfl Hr) class_ok_nil
  | HUnary op e' IH =>
    intro par role b Hr
    have IH' := IH (some b) RUnaryOperand (b + 1) rfl
    rw [number_expr_unary_fst]
    exact class_ok_cons _ _ _ (rv_ok_mk _ _ _ _ _ ExprKind _ rfl Hr) IH'
  | HApp head args IHh IHa =>
    intro par role b Hr
    have IHh' := IHh (some b) RApplicationHead (b + 1) rfl
    have Hda := number_args_class_of b args IHa 0 (number_expr (some b) RApplicationHead (b + 1) head).2
    rw [number_expr_app_fst]
    exact class_ok_cons _ _ _ (rv_ok_mk _ _ _ _ _ ExprKind _ rfl Hr) (class_ok_app _ _ IHh' Hda)

theorem number_list_class {A : Type} (g : Nat → A → List (Nat × Cell) × Nat) :
    (∀ b x, class_ok (g b x).1) →
    ∀ b xs, class_ok (number_list g b xs).1 := by
  intro Hg b xs
  induction xs generalizing b with
  | nil => exact class_ok_nil
  | cons x rest IH =>
    have Hgx := Hg b x
    have IH' := IH (g b x).2
    rw [number_list_cons_fst]
    exact class_ok_app _ _ Hgx IH'

theorem number_bindingname_class : ∀ bn par role b,
    role_ok_for BindingNameKind role → class_ok (number_bindingname par role b bn).1 :=
  fun _ _ _ _ Hr => class_ok_cons _ _ _ (rv_ok_mk _ _ _ _ _ BindingNameKind _ rfl Hr) class_ok_nil

theorem number_typeexpr_class : ∀ t par role b,
    role_ok_for TypeExprKind role → class_ok (number_typeexpr par role b t).1 :=
  fun _ _ _ _ Hr => class_ok_cons _ _ _ (rv_ok_mk _ _ _ _ _ TypeExprKind _ rfl Hr) class_ok_nil

theorem number_opttype_class : ∀ ot par b, class_ok (number_opttype par b ot).1 := by
  intro ot par b
  cases ot with
  | some t => exact number_typeexpr_class t par RTypeUse b rfl
  | none => exact class_ok_nil

theorem number_constspec_class : ∀ cs par role b,
    role_ok_for (SpecKind ConstSpecF) role → class_ok (number_constspec par role b cs).1 := by
  intro ⟨names, init⟩ par role b Hr
  have Hnc := number_list_class (number_bindingname (some b) (RSpecName ConstSpecF))
    (fun bb x => number_bindingname_class x (some b) (RSpecName ConstSpecF) bb rfl)
    (b + 1) (Collections.ne_to_list names)
  unfold number_constspec
  dsimp only
  rcases h1 : number_list (number_bindingname (some b) (RSpecName ConstSpecF)) (b + 1)
    (Collections.ne_to_list names) with ⟨nc, b1, nroots⟩
  rw [h1] at Hnc
  dsimp only at Hnc ⊢
  cases init with
  | ExplicitConstInit ot vals =>
    dsimp only
    have Hoc := number_opttype_class ot (some b) b1
    rcases h2 : number_opttype (some b) b1 ot with ⟨oc, b2, oroots⟩
    rw [h2] at Hoc
    dsimp only at Hoc ⊢
    have Hvc := number_list_class (number_expr (some b) RPlain)
      (fun bb x => number_expr_class x (some b) RPlain bb True.intro) b2 (Collections.ne_to_list vals)
    rcases h3 : number_list (number_expr (some b) RPlain) b2 (Collections.ne_to_list vals)
      with ⟨vc, b3, vroots⟩
    rw [h3] at Hvc
    dsimp only at Hvc ⊢
    exact class_ok_cons _ _ _ (rv_ok_mk _ _ _ _ _ (SpecKind ConstSpecF) _ rfl Hr)
      (class_ok_app _ _ Hnc (class_ok_app _ _ Hoc Hvc))
  | InheritedConstInit =>
    dsimp only
    exact class_ok_cons _ _ _ (rv_ok_mk _ _ _ _ _ (SpecKind ConstSpecF) _ rfl Hr)
      (by rw [app_nil]; exact Hnc)

theorem number_varspec_class : ∀ vs par role b,
    role_ok_for (SpecKind VarSpecF) role → class_ok (number_varspec par role b vs).1 := by
  intro ⟨names, init⟩ par role b Hr
  have Hnc := number_list_class (number_bindingname (some b) (RSpecName VarSpecF))
    (fun bb x => number_bindingname_class x (some b) (RSpecName VarSpecF) bb rfl)
    (b + 1) (Collections.ne_to_list names)
  unfold number_varspec
  dsimp only
  rcases h1 : number_list (number_bindingname (some b) (RSpecName VarSpecF)) (b + 1)
    (Collections.ne_to_list names) with ⟨nc, b1, nroots⟩
  rw [h1] at Hnc
  dsimp only at Hnc ⊢
  cases init with
  | VarTypeOnly t =>
    dsimp only
    have Htc := number_typeexpr_class t (some b) RTypeUse b1 rfl
    rcases h2 : number_typeexpr (some b) RTypeUse b1 t with ⟨tc, b2⟩
    rw [h2] at Htc
    dsimp only at Htc ⊢
    exact class_ok_cons _ _ _ (rv_ok_mk _ _ _ _ _ (SpecKind VarSpecF) _ rfl Hr) (class_ok_app _ _ Hnc Htc)
  | VarValues ot vals =>
    dsimp only
    have Hoc := number_opttype_class ot (some b) b1
    rcases h2 : number_opttype (some b) b1 ot with ⟨oc, b2, oroots⟩
    rw [h2] at Hoc
    dsimp only at Hoc ⊢
    have Hvc := number_list_class (number_expr (some b) RPlain)
      (fun bb x => number_expr_class x (some b) RPlain bb True.intro) b2 (Collections.ne_to_list vals)
    rcases h3 : number_list (number_expr (some b) RPlain) b2 (Collections.ne_to_list vals)
      with ⟨vc, b3, vroots⟩
    rw [h3] at Hvc
    dsimp only at Hvc ⊢
    exact class_ok_cons _ _ _ (rv_ok_mk _ _ _ _ _ (SpecKind VarSpecF) _ rfl Hr)
      (class_ok_app _ _ Hnc (class_ok_app _ _ Hoc Hvc))

theorem number_typespec_class : ∀ ts par role b,
    role_ok_for (SpecKind TypeSpecF) role → class_ok (number_typespec par role b ts).1 := by
  intro ts par role b Hr
  cases ts with
  | AliasSpec bn t | DefSpec bn t =>
    unfold number_typespec
    dsimp only
    have Hbc := number_bindingname_class bn (some b) (RSpecName TypeSpecF) (b + 1) rfl
    rcases h1 : number_bindingname (some b) (RSpecName TypeSpecF) (b + 1) bn with ⟨bc, b1⟩
    rw [h1] at Hbc
    have Htc := number_typeexpr_class t (some b) RTypeUse b1 rfl
    rcases h2 : number_typeexpr (some b) RTypeUse b1 t with ⟨tc, bfin⟩
    rw [h2] at Htc
    dsimp only at Hbc Htc ⊢
    exact class_ok_cons _ _ _ (rv_ok_mk _ _ _ _ _ (SpecKind TypeSpecF) _ rfl Hr) (class_ok_app _ _ Hbc Htc)

theorem number_decl_class : ∀ d par role b,
    role_ok_for DeclKind role → class_ok (number_decl par role b d).1 := by
  intro d par role b Hr
  cases d with
  | ConstDecl cs =>
    unfold number_decl
    dsimp only
    have Hk := number_list_class (number_constspec (some b) RPlain)
      (fun bb x => number_constspec_class x (some b) RPlain bb True.intro) (b + 1) cs
    rcases h : number_list (number_constspec (some b) RPlain) (b + 1) cs with ⟨kc, bfin, roots⟩
    rw [h] at Hk
    dsimp only at Hk ⊢
    exact class_ok_cons _ _ _ (rv_ok_mk _ _ _ _ _ DeclKind _ rfl Hr) Hk
  | VarDecl vs =>
    unfold number_decl
    dsimp only
    have Hk := number_list_class (number_varspec (some b) RPlain)
      (fun bb x => number_varspec_class x (some b) RPlain bb True.intro) (b + 1) vs
    rcases h : number_list (number_varspec (some b) RPlain) (b + 1) vs with ⟨kc, bfin, roots⟩
    rw [h] at Hk
    dsimp only at Hk ⊢
    exact class_ok_cons _ _ _ (rv_ok_mk _ _ _ _ _ DeclKind _ rfl Hr) Hk
  | TypeDecl ts =>
    unfold number_decl
    dsimp only
    have Hk := number_list_class (number_typespec (some b) RPlain)
      (fun bb x => number_typespec_class x (some b) RPlain bb True.intro) (b + 1) ts
    rcases h : number_list (number_typespec (some b) RPlain) (b + 1) ts with ⟨kc, bfin, roots⟩
    rw [h] at Hk
    dsimp only at Hk ⊢
    exact class_ok_cons _ _ _ (rv_ok_mk _ _ _ _ _ DeclKind _ rfl Hr) Hk

theorem number_stmt_class : ∀ s par role b,
    role_ok_for StmtKind role → class_ok (number_stmt par role b s).1 := by
  intro s par role b Hr
  cases s with
  | ExprStmt e =>
    unfold number_stmt
    dsimp only
    have Hc := number_expr_class e (some b) RExprStatementExpr (b + 1) rfl
    rcases h : number_expr (some b) RExprStatementExpr (b + 1) e with ⟨c, b'⟩
    rw [h] at Hc
    dsimp only at Hc ⊢
    exact class_ok_cons _ _ _ (rv_ok_mk _ _ _ _ _ StmtKind _ rfl Hr) Hc
  | DeclarationStmt d =>
    unfold number_stmt
    dsimp only
    have Hc := number_decl_class d (some b) RPlain (b + 1) True.intro
    rcases h : number_decl (some b) RPlain (b + 1) d with ⟨c, b'⟩
    rw [h] at Hc
    dsimp only at Hc ⊢
    exact class_ok_cons _ _ _ (rv_ok_mk _ _ _ _ _ StmtKind _ rfl Hr) Hc
  | ShortVarDecl names vals =>
    unfold number_stmt
    dsimp only
    have Hnc := number_list_class (number_bindingname (some b) RShortLhs)
      (fun bb x => number_bindingname_class x (some b) RShortLhs bb rfl)
      (b + 1) (Collections.ne_to_list names)
    rcases h1 : number_list (number_bindingname (some b) RShortLhs) (b + 1) (Collections.ne_to_list names)
      with ⟨nc, b1, nroots⟩
    rw [h1] at Hnc
    dsimp only at Hnc ⊢
    have Hvc := number_list_class (number_expr (some b) RPlain)
      (fun bb x => number_expr_class x (some b) RPlain bb True.intro) b1 (Collections.ne_to_list vals)
    rcases h2 : number_list (number_expr (some b) RPlain) b1 (Collections.ne_to_list vals)
      with ⟨vc, b2, vroots⟩
    rw [h2] at Hvc
    dsimp only at Hvc ⊢
    exact class_ok_cons _ _ _ (rv_ok_mk _ _ _ _ _ StmtKind _ rfl Hr) (class_ok_app _ _ Hnc Hvc)

theorem number_block_class : ∀ blk par role b,
    role_ok_for BlockKind role → class_ok (number_block par role b blk).1 := by
  intro ⟨stmts⟩ par role b Hr
  unfold number_block
  dsimp only
  have Hk := number_list_class (number_stmt (some b) RPlain)
    (fun bb x => number_stmt_class x (some b) RPlain bb True.intro) (b + 1) stmts
  rcases h : number_list (number_stmt (some b) RPlain) (b + 1) stmts with ⟨kc, bfin, roots⟩
  rw [h] at Hk
  dsimp only at Hk ⊢
  exact class_ok_cons _ _ _ (rv_ok_mk _ _ _ _ _ BlockKind _ rfl Hr) Hk

theorem number_toplevel_class : ∀ td par role b,
    role_ok_for TopKind role → class_ok (number_toplevel par role b td).1 := by
  intro td par role b Hr
  cases td with
  | TopDeclaration d =>
    unfold number_toplevel
    dsimp only
    have Hc := number_decl_class d (some b) RPlain (b + 1) True.intro
    rcases h : number_decl (some b) RPlain (b + 1) d with ⟨c, b'⟩
    rw [h] at Hc
    dsimp only at Hc ⊢
    exact class_ok_cons _ _ _ (rv_ok_mk _ _ _ _ _ TopKind _ rfl Hr) Hc
  | Main blk =>
    unfold number_toplevel
    dsimp only
    have Hc := number_block_class blk (some b) RPlain (b + 1) True.intro
    rcases h : number_block (some b) RPlain (b + 1) blk with ⟨c, b'⟩
    rw [h] at Hc
    dsimp only at Hc ⊢
    exact class_ok_cons _ _ _ (rv_ok_mk _ _ _ _ _ TopKind _ rfl Hr) Hc

/-! §4:255 role/kind exact: every cell whose role commits to a kind carries a view of exactly that kind -/
theorem number_file_class : ∀ f, class_ok (number_file f) := by
  intro f
  unfold number_file
  have Hd := number_list_class (number_toplevel (some 0) RPlain)
    (fun bb x => number_toplevel_class x (some 0) RPlain bb True.intro) 1 (Syntax.declarations f)
  rcases h : number_list (number_toplevel (some 0) RPlain) 1 (Syntax.declarations f) with ⟨dc, bfin, droots⟩
  rw [h] at Hd
  dsimp only at Hd ⊢
  exact class_ok_cons _ _ _ (rv_ok_mk _ _ _ _ _ FileKind _ rfl True.intro) Hd

/-! round-trip (§4:251): each occurrence's tag is exactly its source construct's role and shallow view -/
theorem number_bindingname_view : ∀ par role b bn,
    ∃ cell rest, (number_bindingname par role b bn).1 = (b, cell) :: rest
                 ∧ c_role cell = role ∧ c_view cell = VBindingName bn :=
  fun _ _ _ _ => ⟨_, _, rfl, rfl, rfl⟩

theorem number_typeexpr_view : ∀ par role b t,
    ∃ cell rest, (number_typeexpr par role b t).1 = (b, cell) :: rest
                 ∧ c_role cell = role ∧ c_view cell = VTypeExpr t :=
  fun _ _ _ _ => ⟨_, _, rfl, rfl, rfl⟩

theorem number_constspec_view : ∀ par role b cs,
    ∃ cell rest, (number_constspec par role b cs).1 = (b, cell) :: rest
                 ∧ c_role cell = role ∧ c_view cell = VConstSpec (constspec_shape cs) := by
  intro par role b ⟨names, init⟩
  cases init with
  | ExplicitConstInit ot vals => exact ⟨_, _, rfl, rfl, rfl⟩
  | InheritedConstInit => exact ⟨_, _, rfl, rfl, rfl⟩

theorem number_varspec_view : ∀ par role b vs,
    ∃ cell rest, (number_varspec par role b vs).1 = (b, cell) :: rest
                 ∧ c_role cell = role ∧ c_view cell = VVarSpec (varspec_shape vs) := by
  intro par role b ⟨names, init⟩
  cases init with
  | VarTypeOnly t => exact ⟨_, _, rfl, rfl, rfl⟩
  | VarValues ot vals => exact ⟨_, _, rfl, rfl, rfl⟩

theorem number_typespec_view : ∀ par role b ts,
    ∃ cell rest, (number_typespec par role b ts).1 = (b, cell) :: rest
                 ∧ c_role cell = role ∧ c_view cell = VTypeSpec (typespec_shape ts) := by
  intro par role b ts
  cases ts with
  | AliasSpec bn t | DefSpec bn t => exact ⟨_, _, rfl, rfl, rfl⟩

theorem number_decl_view : ∀ par role b d,
    ∃ cell rest, (number_decl par role b d).1 = (b, cell) :: rest
                 ∧ c_role cell = role ∧ c_view cell = VDecl (decl_flavor d) := by
  intro par role b d
  cases d with
  | ConstDecl cs => exact ⟨_, _, rfl, rfl, rfl⟩
  | VarDecl vs => exact ⟨_, _, rfl, rfl, rfl⟩
  | TypeDecl ts => exact ⟨_, _, rfl, rfl, rfl⟩

theorem number_stmt_view : ∀ par role b s,
    ∃ cell rest, (number_stmt par role b s).1 = (b, cell) :: rest
                 ∧ c_role cell = role ∧ c_view cell = VStmt (stmt_shape s) := by
  intro par role b s
  cases s with
  | ExprStmt e => exact ⟨_, _, rfl, rfl, rfl⟩
  | DeclarationStmt d => exact ⟨_, _, rfl, rfl, rfl⟩
  | ShortVarDecl names vals => exact ⟨_, _, rfl, rfl, rfl⟩

theorem number_block_view : ∀ par role b blk,
    ∃ cell rest, (number_block par role b blk).1 = (b, cell) :: rest
                 ∧ c_role cell = role ∧ c_view cell = VBlock := by
  intro par role b ⟨stmts⟩
  exact ⟨_, _, rfl, rfl, rfl⟩

theorem number_toplevel_view : ∀ par role b td,
    ∃ cell rest, (number_toplevel par role b td).1 = (b, cell) :: rest
                 ∧ c_role cell = role ∧ c_view cell = VTop (top_shape td) := by
  intro par role b td
  cases td with
  | TopDeclaration d => exact ⟨_, _, rfl, rfl, rfl⟩
  | Main blk => exact ⟨_, _, rfl, rfl, rfl⟩

/-! main (§4:256): a Main top-level is tagged VTop TSMain and its one child is exactly the body block -/
theorem number_main : ∀ par role b blk,
    ∃ cell bcell rest,
      (number_toplevel par role b (Syntax.Main blk)).1 = (b, cell) :: rest ∧
      c_view cell = VTop TSMain ∧ c_children cell = [b + 1] ∧
      (b + 1, bcell) ∈ rest ∧ c_view bcell = VBlock := by
  intro par role b blk
  obtain ⟨bcell, brest, Hb, _, Hbv⟩ := number_block_view (some b) RPlain (b + 1) blk
  unfold number_toplevel
  dsimp only
  rcases h : number_block (some b) RPlain (b + 1) blk with ⟨bc, b'⟩
  rw [h] at Hb
  dsimp only at Hb ⊢
  exact ⟨_, bcell, bc, rfl, rfl, rfl, by rw [Hb]; exact List.Mem.head _, Hbv⟩

/-! strictly ascending child positions: the ordinal order IS the source order -/
def asc : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: t => a < b ∧ asc (b :: t)

theorem asc_cons : ∀ a l, (match l with | b :: _ => a < b | [] => True) → asc l → asc (a :: l) := by
  intro a l Hh Ht
  cases l with
  | nil => exact True.intro
  | cons b t => exact And.intro Hh Ht

theorem asc_app : ∀ l1 l2, asc l1 → asc l2 → (∀ x y, x ∈ l1 → y ∈ l2 → x < y) → asc (l1 ++ l2) := by
  intro l1
  induction l1 with
  | nil => intro l2 _ H2 _; exact H2
  | cons a t IH =>
    intro l2 H1 H2 Hlt
    show asc (a :: (t ++ l2))
    apply asc_cons
    · cases t with
      | nil =>
        cases l2 with
        | nil => exact True.intro
        | cons y l2' => exact Hlt a y (List.Mem.head _) (List.Mem.head _)
      | cons b t' => exact (H1 : a < b ∧ asc (b :: t')).1
    · apply IH
      · cases t with
        | nil => exact True.intro
        | cons b t' => exact (H1 : a < b ∧ asc (b :: t')).2
      · exact H2
      · intro x y Hx Hy; exact Hlt x y (List.Mem.tail _ Hx) Hy

theorem asc_head_lt : ∀ (t : List Nat) (a j y : Nat), asc (a :: t) → t[j]? = some y → a < y := by
  intro t
  induction t with
  | nil =>
    intro a j y _ Hy
    cases j with
    | zero => exact nomatch Hy
    | succ j => exact nomatch Hy
  | cons b t' IH =>
    intro a j y Ha Hy
    have Ha' : a < b ∧ asc (b :: t') := Ha
    cases j with
    | zero =>
      have Hby : b = y := Option.some.inj Hy
      rw [← Hby]
      exact Ha'.1
    | succ j' => exact Nat.lt_trans Ha'.1 (IH b j' y Ha'.2 Hy)

theorem asc_nth : ∀ (l : List Nat) (i j x y : Nat),
    asc l → i < j → l[i]? = some x → l[j]? = some y → x < y := by
  intro l
  induction l with
  | nil =>
    intro i j x y _ _ Hx _
    cases i with
    | zero => exact nomatch Hx
    | succ i => exact nomatch Hx
  | cons a t IH =>
    intro i j x y Ha Hij Hx Hy
    cases i with
    | zero =>
      have Hax : a = x := Option.some.inj Hx
      rw [← Hax]
      cases j with
      | zero => exact absurd Hij (Nat.lt_irrefl 0)
      | succ j' => exact asc_head_lt t a j' y Ha Hy
    | succ i' =>
      cases j with
      | zero => exact absurd Hij (Nat.not_lt_zero _)
      | succ j' =>
        have Htasc : asc t := by
          cases t with
          | nil => exact True.intro
          | cons b t' => exact (Ha : a < b ∧ asc (b :: t')).2
        exact IH i' j' x y Htasc (Nat.lt_of_succ_lt_succ Hij) Hx Hy

/-! the reverse layout clauses: a spec, statement, or declaration child pins its parent's exact view class -/
def reverse_clauses (pv cv : NodeView) : Prop :=
  (∀ fl, spec_view_of_flavor fl cv → pv = VDecl fl)
  ∧ (∀ sh, cv = VStmt sh → pv = VBlock)
  ∧ (∀ fl, cv = VDecl fl → pv = VStmt SSDecl ∨ pv = VTop TSTopDecl)

/-! a child view that is no spec, statement, or declaration discharges every reverse clause -/
def no_reverse (v : NodeView) : Prop :=
  match v with
  | VConstSpec _ | VVarSpec _ | VTypeSpec _ | VStmt _ | VDecl _ => False
  | VName _ | VLiteral _ | VUnary _ | VApplication | VTypeExpr _ | VBindingName _ | VBlock | VTop _ | VFile =>
      True

theorem no_reverse_clauses : ∀ pv cv, no_reverse cv → reverse_clauses pv cv := by
  intro pv cv H
  cases cv with
  | VConstSpec s | VVarSpec s | VTypeSpec s | VStmt s | VDecl s => exact False.elim H
  | VName n | VLiteral l | VUnary op | VApplication | VTypeExpr t | VBindingName bn | VBlock | VTop sh
  | VFile =>
    exact And.intro (fun fl Hs => by cases fl <;> exact False.elim Hs)
      (And.intro (fun _ He => nomatch He) (fun _ He => nomatch He))

theorem stmt_reverse_clauses : ∀ sh, reverse_clauses VBlock (VStmt sh) := by
  intro sh
  exact And.intro (fun fl Hs => by cases fl <;> exact False.elim Hs)
    (And.intro (fun _ _ => rfl) (fun _ He => nomatch He))

theorem spec_reverse_clauses : ∀ fl0 v, spec_view_of_flavor fl0 v → reverse_clauses (VDecl fl0) v := by
  intro fl0 v Hv
  cases fl0 <;> cases v <;> first
    | exact False.elim Hv
    | exact And.intro (fun fl Hs => by cases fl <;> first | rfl | exact False.elim Hs)
        (And.intro (fun _ He => nomatch He) (fun _ He => nomatch He))

theorem decl_stmt_reverse_clauses : ∀ fl, reverse_clauses (VStmt SSDecl) (VDecl fl) := by
  intro fl
  exact And.intro (fun fl0 Hs => by cases fl0 <;> exact False.elim Hs)
    (And.intro (fun _ He => nomatch He) (fun _ _ => Or.inl rfl))

theorem decl_top_reverse_clauses : ∀ fl, reverse_clauses (VTop TSTopDecl) (VDecl fl) := by
  intro fl
  exact And.intro (fun fl0 Hs => by cases fl0 <;> exact False.elim Hs)
    (And.intro (fun _ He => nomatch He) (fun _ _ => Or.inr rfl))

/-! per-parent layout: exact child roles; main, spec, statement and declaration adjacency in both directions -/
def child_layout_ok (occs : List (Nat × Cell)) : Prop :=
  ∀ pos cell, (pos, cell) ∈ occs →
    ∀ k cp, (c_children cell)[k]? = some cp →
      ∃ cc, (cp, cc) ∈ occs
            ∧ c_role cc = layout_role (c_view cell) k
            ∧ (c_view cell = VTop TSMain → c_view cc = VBlock)
            ∧ (∀ fl, c_view cell = VDecl fl → spec_view_of_flavor fl (c_view cc))
            ∧ reverse_clauses (c_view cell) (c_view cc)

theorem child_layout_ok_app : ∀ c1 c2,
    child_layout_ok c1 → child_layout_ok c2 → child_layout_ok (c1 ++ c2) := by
  intro c1 c2 H1 H2 pos cell Hin k cp Hcp
  cases mem_app_or Hin with
  | inl Hin =>
    obtain ⟨cc, Hc, Hp⟩ := H1 pos cell Hin k cp Hcp
    exact ⟨cc, List.mem_append_left c2 Hc, Hp⟩
  | inr Hin =>
    obtain ⟨cc, Hc, Hp⟩ := H2 pos cell Hin k cp Hcp
    exact ⟨cc, List.mem_append_right c1 Hc, Hp⟩

theorem child_layout_ok_node : ∀ self cell kids,
    (∀ k cp, (c_children cell)[k]? = some cp →
       ∃ cc, (cp, cc) ∈ (self, cell) :: kids
             ∧ c_role cc = layout_role (c_view cell) k
             ∧ (c_view cell = VTop TSMain → c_view cc = VBlock)
             ∧ (∀ fl, c_view cell = VDecl fl → spec_view_of_flavor fl (c_view cc))
             ∧ reverse_clauses (c_view cell) (c_view cc)) →
    child_layout_ok kids → child_layout_ok ((self, cell) :: kids) := by
  intro self cell kids Hself Hkids pos c Hin k cp Hcp
  cases Hin with
  | head => exact Hself k cp Hcp
  | tail _ Hin =>
    obtain ⟨cc, Hc, Hp⟩ := Hkids pos c Hin k cp Hcp
    exact ⟨cc, List.Mem.tail _ Hc, Hp⟩

/-! the per-cell shape law: children ascend in source order and match the count the shape fixes -/
def cell_shape_ok (cell : Cell) : Prop :=
  asc (c_children cell) ∧
  match layout_count (c_view cell) with | some n => List.length (c_children cell) = n | none => True
def shape_ok (occs : List (Nat × Cell)) : Prop := ∀ kv ∈ occs, cell_shape_ok kv.2

theorem shape_ok_app : ∀ c1 c2, shape_ok c1 → shape_ok c2 → shape_ok (c1 ++ c2) := by
  intro c1 c2 H1 H2 kv Hkv
  cases mem_app_or Hkv with
  | inl H => exact H1 kv H
  | inr H => exact H2 kv H

/-! ## Section 4 (`.v` lines 2447–3983) -/

/-! ### the `.v`'s stdlib facts this section adds (`length_app`, `nth_error_app1`, `nth_error_app2`), by hand -/

private theorem length_app {A : Type} : ∀ l1 l2 : List A, (l1 ++ l2).length = l1.length + l2.length
  | [], l2 => (Nat.zero_add l2.length).symm
  | _ :: xs, l2 => by
    show (xs ++ l2).length + 1 = xs.length + 1 + l2.length
    rw [length_app xs l2]
    exact Nat.add_right_comm _ _ _

-- Rocq: `nth_error_app1`, on `l[k]?`
private theorem getElem?_app_left {A : Type} : ∀ (l1 l2 : List A) (k : Nat),
    k < l1.length → (l1 ++ l2)[k]? = l1[k]?
  | [], _, k, H => absurd H (Nat.not_lt_zero k)
  | _ :: _, _, 0, _ => rfl
  | _ :: xs, l2, k + 1, H => getElem?_app_left xs l2 k (Nat.lt_of_succ_lt_succ H)

-- `S n - S m = n - m`, by hand (core's `Nat.add_sub_add_right` carries `propext`)
private theorem succ_sub_succ' : ∀ n m : Nat, n + 1 - (m + 1) = n - m
  | _, 0 => rfl
  | n, m + 1 => congrArg Nat.pred (succ_sub_succ' n m)

-- Rocq: `nth_error_app2`, on `l[k]?`
private theorem getElem?_app_right {A : Type} : ∀ (l1 l2 : List A) (k : Nat),
    l1.length ≤ k → (l1 ++ l2)[k]? = l2[k - l1.length]?
  | [], _, _, _ => rfl
  | _ :: _, _, 0, H => absurd H (Nat.not_succ_le_zero _)
  | _ :: xs, l2, k + 1, H => by
    show (xs ++ l2)[k]? = l2[k + 1 - (xs.length + 1)]?
    rw [succ_sub_succ']
    exact getElem?_app_right xs l2 k (Nat.le_of_succ_le_succ H)

-- Rocq's `Forall` constructors, for `shape_ok`
private theorem shape_ok_nil : shape_ok [] := fun _ H => nomatch H
private theorem shape_ok_cons (self : Nat) (cell : Cell) (kids : List (Nat × Cell))
    (H : cell_shape_ok cell) (Hk : shape_ok kids) : shape_ok ((self, cell) :: kids) := by
  intro kv Hkv
  cases Hkv with
  | head => exact H
  | tail _ Hkv' => exact Hk kv Hkv'

-- `asc_cons` with the head condition given against every element of the tail (the `.v` destructs the tail)
private theorem asc_cons_lt (a : Nat) (l : List Nat) (H : ∀ r ∈ l, a < r) (Hl : asc l) : asc (a :: l) := by
  apply asc_cons
  · cases l with
    | nil => exact True.intro
    | cons r _ => exact H r (List.Mem.head _)
  · exact Hl

-- Rocq's `Nat.ltb_lt` / `Nat.ltb_ge` / `Nat.eqb_eq` / `Nat.eqb_neq` rewrites under `bif decide …`
private theorem cond_decide_true {A : Type} (p : Prop) [inst : Decidable p] (h : p) (a b : A) :
    (bif decide p then a else b) = a := by
  cases inst with
  | isTrue _ => exact rfl
  | isFalse hn => exact absurd h hn
private theorem cond_decide_false {A : Type} (p : Prop) [inst : Decidable p] (h : ¬ p) (a b : A) :
    (bif decide p then a else b) = b := by
  cases inst with
  | isTrue hp => exact absurd hp h
  | isFalse _ => exact rfl

/-! one roots account for a numbered segment: count, ascent, bounds, and per-root cell resolution -/
theorem number_list_roots {A : Type} (g : Nat → A → List (Nat × Cell) × Nat) (P : Cell → Prop) :
    (∀ b x, spans (g b x) b) →
    (∀ b x, ∃ cell rest, (g b x).1 = (b, cell) :: rest ∧ P cell) →
    ∀ xs b,
      match number_list g b xs with
      | (c, b', roots) =>
        List.length roots = List.length xs
        ∧ asc roots
        ∧ (∀ r0, r0 ∈ roots → b ≤ r0 ∧ r0 < b')
        ∧ (∀ (k : Nat) r0, roots[k]? = some r0 → ∃ cell, (r0, cell) ∈ c ∧ P cell) := by
  intro Hspan Hroot xs
  induction xs with
  | nil =>
    intro b
    show List.length ([] : List Nat) = List.length ([] : List A) ∧ asc [] ∧ (∀ r0, r0 ∈ ([] : List Nat) → b ≤ r0 ∧ r0 < b)
      ∧ (∀ k r0, ([] : List Nat)[k]? = some r0 → ∃ cell, (r0, cell) ∈ ([] : List (Nat × Cell)) ∧ P cell)
    refine ⟨rfl, True.intro, (fun _ H => nomatch H), fun k r0 Hk => ?_⟩
    cases k with
    | zero => exact nomatch Hk
    | succ _ => exact nomatch Hk
  | cons x rest IH =>
    intro b
    obtain ⟨cell, crest, Hc, HP⟩ := Hroot b x
    obtain ⟨n1, Hmap, He⟩ := Hspan b x
    have Hn1 : 0 < n1 := by
      cases n1 with
      | zero => rw [Hc] at Hmap; exact nomatch Hmap
      | succ n => exact Nat.zero_lt_succ n
    have Hb1 : b < (g b x).2 := by rw [He]; exact Nat.lt_add_of_pos_right Hn1
    have Hsr := number_list_span g Hspan rest (g b x).2
    have IH' := IH (g b x).2
    show List.length (number_list g b (x :: rest)).2.2 = List.length (x :: rest)
      ∧ asc (number_list g b (x :: rest)).2.2
      ∧ (∀ r0, r0 ∈ (number_list g b (x :: rest)).2.2 → b ≤ r0 ∧ r0 < (number_list g b (x :: rest)).2.1)
      ∧ (∀ k r0, (number_list g b (x :: rest)).2.2[k]? = some r0 →
           ∃ cell, (r0, cell) ∈ (number_list g b (x :: rest)).1 ∧ P cell)
    rw [number_list_cons_fst, number_list_cons_next, number_list_cons_roots]
    rcases h : number_list g (g b x).2 rest with ⟨rc, b2, roots1⟩
    rw [h] at Hsr IH'
    dsimp only at Hsr IH' ⊢
    obtain ⟨Hlen, Hasc, Hbnd, Hnth⟩ := IH'
    obtain ⟨n2, _, Hb2⟩ := Hsr
    dsimp only at Hb2
    have Hb2' : (g b x).2 ≤ b2 := by rw [Hb2]; exact Nat.le_add_right _ n2
    refine ⟨?_, ?_, ?_, ?_⟩
    · show List.length roots1 + 1 = List.length rest + 1
      rw [Hlen]
    · exact asc_cons_lt b roots1 (fun r Hr => Nat.lt_of_lt_of_le Hb1 (Hbnd r Hr).1) Hasc
    · intro r0 Hr0
      cases Hr0 with
      | head => exact ⟨Nat.le_refl b, Nat.lt_of_lt_of_le Hb1 Hb2'⟩
      | tail _ Hr0 =>
        obtain ⟨H1, H2⟩ := Hbnd r0 Hr0
        exact ⟨Nat.le_trans (Nat.le_of_lt Hb1) H1, H2⟩
    · intro k r0 Hk
      cases k with
      | zero =>
        have H := Option.some.inj Hk
        subst H
        exact ⟨cell, List.mem_append_left _ (by rw [Hc]; exact List.Mem.head _), HP⟩
      | succ k' =>
        obtain ⟨cc, Hcc, HPc⟩ := Hnth k' r0 Hk
        exact ⟨cc, List.mem_append_right _ Hcc, HPc⟩

theorem number_list_shape {A : Type} (g : Nat → A → List (Nat × Cell) × Nat) :
    (∀ b x, shape_ok (g b x).1) →
    ∀ b xs, shape_ok (number_list g b xs).1 := by
  intro Hg b xs
  induction xs generalizing b with
  | nil => exact shape_ok_nil
  | cons x rest IH =>
    rw [number_list_cons_fst]
    exact shape_ok_app _ _ (Hg b x) (IH (g b x).2)

theorem number_list_layout {A : Type} (g : Nat → A → List (Nat × Cell) × Nat) :
    (∀ b x, child_layout_ok (g b x).1) →
    ∀ b xs, child_layout_ok (number_list g b xs).1 := by
  intro Hg b xs
  induction xs generalizing b with
  | nil => exact fun _ _ Hin => nomatch (Hin : _ ∈ ([] : List (Nat × Cell)))
  | cons x rest IH =>
    rw [number_list_cons_fst]
    exact child_layout_ok_app _ _ (Hg b x) (IH (g b x).2)

-- the `.v`'s inner `assert (Hda : …)` of number_expr_shape, about `number_args`
private theorem number_args_shape_of (b : Nat) : ∀ es : List Syntax.Expr,
    (∀ a ∈ es, ∀ par role bb, shape_ok (number_expr par role bb a).1) →
    ∀ i0 bi, shape_ok (number_args b i0 bi es).1 ∧ asc (number_args b i0 bi es).2.2
             ∧ bi ≤ (number_args b i0 bi es).2.1
             ∧ (∀ r, r ∈ (number_args b i0 bi es).2.2 → bi ≤ r ∧ r < (number_args b i0 bi es).2.1) := by
  intro es
  induction es with
  | nil =>
    intro _ i0 bi
    exact ⟨shape_ok_nil, True.intro, Nat.le_refl bi, fun _ Hr => nomatch (Hr : _ ∈ ([] : List Nat))⟩
  | cons a rest IH =>
    intro Hall i0 bi
    obtain ⟨na, _, Hbi', Hna⟩ := number_expr_span a (some b) (RApplicationArg i0) bi
    have Ha := Hall a (List.Mem.head _) (some b) (RApplicationArg i0) bi
    obtain ⟨Hrs, Hra, Hrb, Hrbnd⟩ := IH (fun x hx => Hall x (List.Mem.tail _ hx)) (i0 + 1)
      (number_expr (some b) (RApplicationArg i0) bi a).2
    have Hbi1 : bi < (number_expr (some b) (RApplicationArg i0) bi a).2 := by
      rw [Hbi']; exact Nat.lt_add_of_pos_right Hna
    rw [number_args_cons_fst, number_args_cons_next, number_args_cons_roots]
    refine ⟨shape_ok_app _ _ Ha Hrs, ?_, Nat.le_trans (Nat.le_of_lt Hbi1) Hrb, ?_⟩
    · exact asc_cons_lt bi _ (fun r Hr => Nat.lt_of_lt_of_le Hbi1 (Hrbnd r Hr).1) Hra
    · intro r Hr
      cases Hr with
      | head => exact ⟨Nat.le_refl bi, Nat.lt_of_lt_of_le Hbi1 Hrb⟩
      | tail _ Hr =>
        obtain ⟨H1, H2⟩ := Hrbnd r Hr
        exact ⟨Nat.le_trans (Nat.le_of_lt Hbi1) H1, H2⟩

theorem number_expr_shape : ∀ e par role b, shape_ok (number_expr par role b e).1 := by
  intro e
  induction e using Syntax.Expr_ind' with
  | HName n => intro par role b; exact shape_ok_cons _ _ _ (And.intro True.intro rfl) shape_ok_nil
  | HLit l => intro par role b; exact shape_ok_cons _ _ _ (And.intro True.intro rfl) shape_ok_nil
  | HUnary op e' IH =>
    intro par role b
    rw [number_expr_unary_fst]
    exact shape_ok_cons _ _ _ (And.intro True.intro rfl) (IH (some b) RUnaryOperand (b + 1))
  | HApp head args IHh IHa =>
    intro par role b
    have IHh' := IHh (some b) RApplicationHead (b + 1)
    obtain ⟨m1, _, Hb1, Hm1⟩ := number_expr_span head (some b) RApplicationHead (b + 1)
    obtain ⟨Hacs, Haca, _, Hacbnd⟩ := number_args_shape_of b args IHa 0
      (number_expr (some b) RApplicationHead (b + 1) head).2
    have HSb : b + 1 < (number_expr (some b) RApplicationHead (b + 1) head).2 := by
      rw [Hb1]; exact Nat.lt_add_of_pos_right Hm1
    rw [number_expr_app_fst]
    exact shape_ok_cons _ _ _
      (And.intro (asc_cons_lt (b + 1) _ (fun r Hr => Nat.lt_of_lt_of_le HSb (Hacbnd r Hr).1) Haca) True.intro)
      (shape_ok_app _ _ IHh' Hacs)

theorem number_typeexpr_shape : ∀ par role b t, shape_ok (number_typeexpr par role b t).1 :=
  fun _ _ _ _ => shape_ok_cons _ _ _ (And.intro True.intro rfl) shape_ok_nil
theorem number_bindingname_shape : ∀ par role b bn, shape_ok (number_bindingname par role b bn).1 :=
  fun _ _ _ _ => shape_ok_cons _ _ _ (And.intro True.intro rfl) shape_ok_nil

theorem number_opttype_shape : ∀ self b ot, shape_ok (number_opttype (some self) b ot).1 := by
  intro self b ot
  cases ot with
  | some t => exact number_typeexpr_shape (some self) RTypeUse b t
  | none => exact shape_ok_nil

/-! the opttype roots: exactly one RTypeUse root when the type is present, none otherwise -/
theorem number_opttype_roots : ∀ self b ot,
    match number_opttype (some self) b ot with
    | (c, b', roots) =>
      List.length roots = (match ot with | some _ => 1 | none => 0)
      ∧ asc roots ∧ b ≤ b' ∧ (∀ r, r ∈ roots → b ≤ r ∧ r < b')
      ∧ (∀ (k : Nat) r0, roots[k]? = some r0 →
           ∃ cell, (r0, cell) ∈ c ∧ c_role cell = RTypeUse
                   ∧ no_reverse (c_view cell)) := by
  intro self b ot
  cases ot with
  | some t =>
    show List.length [b] = 1 ∧ asc [b] ∧ b ≤ b + 1 ∧ (∀ r, r ∈ [b] → b ≤ r ∧ r < b + 1)
      ∧ (∀ k r0, [b][k]? = some r0 →
           ∃ cell, (r0, cell) ∈ [(b, mkCell (VTypeExpr t) RTypeUse (some self) b [] 0)]
                   ∧ c_role cell = RTypeUse ∧ no_reverse (c_view cell))
    refine ⟨rfl, True.intro, Nat.le_succ b, ?_, ?_⟩
    · intro r Hr
      cases Hr with
      | head => exact ⟨Nat.le_refl b, Nat.lt_succ_self b⟩
      | tail _ H => exact nomatch H
    · intro k r0 Hk
      cases k with
      | zero =>
        have H := Option.some.inj Hk
        subst H
        exact ⟨_, List.Mem.head _, rfl, True.intro⟩
      | succ k' =>
        cases k' with
        | zero => exact nomatch Hk
        | succ _ => exact nomatch Hk
  | none =>
    show List.length ([] : List Nat) = 0 ∧ asc [] ∧ b ≤ b ∧ (∀ r, r ∈ ([] : List Nat) → b ≤ r ∧ r < b)
      ∧ (∀ k r0, ([] : List Nat)[k]? = some r0 →
           ∃ cell, (r0, cell) ∈ ([] : List (Nat × Cell)) ∧ c_role cell = RTypeUse ∧ no_reverse (c_view cell))
    refine ⟨rfl, True.intro, Nat.le_refl b, (fun _ H => nomatch H), fun k r0 Hk => ?_⟩
    cases k with
    | zero => exact nomatch Hk
    | succ _ => exact nomatch Hk

-- the trivial per-root fact the shape lemmas thread through `number_list_roots`
private theorem root_true_of_view {A : Type} {g : Nat → A → List (Nat × Cell) × Nat} {r : Role}
    {v : A → NodeView}
    (Hv : ∀ bb x, ∃ cell rest, (g bb x).1 = (bb, cell) :: rest ∧ c_role cell = r ∧ c_view cell = v x) :
    ∀ bb x, ∃ cell rest, (g bb x).1 = (bb, cell) :: rest ∧ (fun _ => True) cell := by
  intro bb x
  obtain ⟨cell, rest, Hf, _, _⟩ := Hv bb x
  exact ⟨cell, rest, Hf, True.intro⟩

private theorem expr_root_true (par : Option Nat) (role : Role) :
    ∀ bb x, ∃ cell rest, (number_expr par role bb x).1 = (bb, cell) :: rest ∧ (fun _ => True) cell := by
  intro bb x
  obtain ⟨rest, rc, Hf, _, _, _⟩ := number_expr_root x par role bb
  exact ⟨rc, rest, Hf, True.intro⟩

theorem number_constspec_shape : ∀ par role b cs, shape_ok (number_constspec par role b cs).1 := by
  intro par role b ⟨names, init⟩
  have Hnr := number_list_roots (number_bindingname (some b) (RSpecName ConstSpecF)) (fun _ => True)
    (fun bb x => number_bindingname_spans (some b) (RSpecName ConstSpecF) bb x)
    (root_true_of_view (number_bindingname_view (some b) (RSpecName ConstSpecF)))
    (Collections.ne_to_list names) (b + 1)
  have Hns := number_list_shape (number_bindingname (some b) (RSpecName ConstSpecF))
    (fun bb x => number_bindingname_shape (some b) (RSpecName ConstSpecF) bb x)
    (b + 1) (Collections.ne_to_list names)
  unfold number_constspec
  dsimp only
  rcases h1 : number_list (number_bindingname (some b) (RSpecName ConstSpecF)) (b + 1)
    (Collections.ne_to_list names) with ⟨nc, b1, nroots⟩
  rw [h1] at Hnr Hns
  dsimp only at Hnr Hns ⊢
  obtain ⟨Hnlen, Hnasc, Hnbnd, _⟩ := Hnr
  cases init with
  | ExplicitConstInit ot vals =>
    dsimp only
    have Hor := number_opttype_roots b b1 ot
    have Hos := number_opttype_shape b b1 ot
    rcases h2 : number_opttype (some b) b1 ot with ⟨oc, b2, oroots⟩
    rw [h2] at Hor Hos
    dsimp only at Hor Hos ⊢
    obtain ⟨Holen, Hoasc, Hob, Hobnd, _⟩ := Hor
    have Hvr := number_list_roots (number_expr (some b) RPlain) (fun _ => True)
      (fun bb x => number_expr_spans x (some b) RPlain bb) (expr_root_true (some b) RPlain)
      (Collections.ne_to_list vals) b2
    have Hvs := number_list_shape (number_expr (some b) RPlain)
      (fun bb x => number_expr_shape x (some b) RPlain bb) b2 (Collections.ne_to_list vals)
    rcases h3 : number_list (number_expr (some b) RPlain) b2 (Collections.ne_to_list vals)
      with ⟨vc, b3, vroots⟩
    rw [h3] at Hvr Hvs
    dsimp only at Hvr Hvs ⊢
    obtain ⟨Hvlen, Hvasc, Hvbnd, _⟩ := Hvr
    apply shape_ok_cons
    · refine And.intro ?_ ?_
      · show asc (nroots ++ (oroots ++ vroots))
        apply asc_app _ _ Hnasc
          (asc_app _ _ Hoasc Hvasc (fun x y Hx Hy => Nat.lt_of_lt_of_le (Hobnd x Hx).2 (Hvbnd y Hy).1))
        intro x y Hx Hy
        cases mem_app_or Hy with
        | inl Hy => exact Nat.lt_of_lt_of_le (Hnbnd x Hx).2 (Hobnd y Hy).1
        | inr Hy => exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Hnbnd x Hx).2 Hob) (Hvbnd y Hy).1
      · show List.length (nroots ++ (oroots ++ vroots)) = _
        rw [length_app, length_app, Hnlen, Hvlen, Holen]
        cases ot with
        | some t => exact (Nat.add_assoc _ _ _).symm
        | none => exact (Nat.add_assoc _ _ _).symm
    · exact shape_ok_app _ _ Hns (shape_ok_app _ _ Hos Hvs)
  | InheritedConstInit =>
    dsimp only
    apply shape_ok_cons
    · refine And.intro ?_ ?_
      · show asc (nroots ++ [])
        rw [app_nil]
        exact Hnasc
      · show List.length (nroots ++ []) = List.length (Collections.ne_to_list names)
        rw [app_nil]
        exact Hnlen
    · rw [app_nil]
      exact Hns

theorem number_varspec_shape : ∀ par role b vs, shape_ok (number_varspec par role b vs).1 := by
  intro par role b ⟨names, init⟩
  have Hnr := number_list_roots (number_bindingname (some b) (RSpecName VarSpecF)) (fun _ => True)
    (fun bb x => number_bindingname_spans (some b) (RSpecName VarSpecF) bb x)
    (root_true_of_view (number_bindingname_view (some b) (RSpecName VarSpecF)))
    (Collections.ne_to_list names) (b + 1)
  have Hns := number_list_shape (number_bindingname (some b) (RSpecName VarSpecF))
    (fun bb x => number_bindingname_shape (some b) (RSpecName VarSpecF) bb x)
    (b + 1) (Collections.ne_to_list names)
  unfold number_varspec
  dsimp only
  rcases h1 : number_list (number_bindingname (some b) (RSpecName VarSpecF)) (b + 1)
    (Collections.ne_to_list names) with ⟨nc, b1, nroots⟩
  rw [h1] at Hnr Hns
  dsimp only at Hnr Hns ⊢
  obtain ⟨Hnlen, Hnasc, Hnbnd, _⟩ := Hnr
  cases init with
  | VarTypeOnly t =>
    dsimp only
    have Hts := number_typeexpr_shape (some b) RTypeUse b1 t
    rcases h2 : number_typeexpr (some b) RTypeUse b1 t with ⟨tc, b2⟩
    rw [h2] at Hts
    dsimp only at Hts ⊢
    apply shape_ok_cons
    · refine And.intro ?_ ?_
      · show asc (nroots ++ [b1])
        apply asc_app nroots [b1] Hnasc True.intro
        intro x y Hx Hy
        cases Hy with
        | head => exact (Hnbnd x Hx).2
        | tail _ H => exact nomatch H
      · show List.length (nroots ++ [b1]) = List.length (Collections.ne_to_list names) + 1
        rw [length_app, Hnlen]
        rfl
    · exact shape_ok_app _ _ Hns Hts
  | VarValues ot vals =>
    dsimp only
    have Hor := number_opttype_roots b b1 ot
    have Hos := number_opttype_shape b b1 ot
    rcases h2 : number_opttype (some b) b1 ot with ⟨oc, b2, oroots⟩
    rw [h2] at Hor Hos
    dsimp only at Hor Hos ⊢
    obtain ⟨Holen, Hoasc, Hob, Hobnd, _⟩ := Hor
    have Hvr := number_list_roots (number_expr (some b) RPlain) (fun _ => True)
      (fun bb x => number_expr_spans x (some b) RPlain bb) (expr_root_true (some b) RPlain)
      (Collections.ne_to_list vals) b2
    have Hvs := number_list_shape (number_expr (some b) RPlain)
      (fun bb x => number_expr_shape x (some b) RPlain bb) b2 (Collections.ne_to_list vals)
    rcases h3 : number_list (number_expr (some b) RPlain) b2 (Collections.ne_to_list vals)
      with ⟨vc, b3, vroots⟩
    rw [h3] at Hvr Hvs
    dsimp only at Hvr Hvs ⊢
    obtain ⟨Hvlen, Hvasc, Hvbnd, _⟩ := Hvr
    apply shape_ok_cons
    · refine And.intro ?_ ?_
      · show asc (nroots ++ (oroots ++ vroots))
        apply asc_app _ _ Hnasc
          (asc_app _ _ Hoasc Hvasc (fun x y Hx Hy => Nat.lt_of_lt_of_le (Hobnd x Hx).2 (Hvbnd y Hy).1))
        intro x y Hx Hy
        cases mem_app_or Hy with
        | inl Hy => exact Nat.lt_of_lt_of_le (Hnbnd x Hx).2 (Hobnd y Hy).1
        | inr Hy => exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Hnbnd x Hx).2 Hob) (Hvbnd y Hy).1
      · show List.length (nroots ++ (oroots ++ vroots)) = _
        rw [length_app, length_app, Hnlen, Hvlen, Holen]
        cases ot with
        | some t => exact (Nat.add_assoc _ _ _).symm
        | none => exact (Nat.add_assoc _ _ _).symm
    · exact shape_ok_app _ _ Hns (shape_ok_app _ _ Hos Hvs)

theorem number_typespec_shape : ∀ par role b ts, shape_ok (number_typespec par role b ts).1 := by
  intro par role b ts
  cases ts with
  | AliasSpec bn t | DefSpec bn t =>
    unfold number_typespec
    dsimp only [number_bindingname, number_typeexpr, number_leaf]
    exact shape_ok_cons _ _ _ (And.intro (And.intro (Nat.lt_succ_self (b + 1)) True.intro) rfl)
      (shape_ok_cons _ _ _ (And.intro True.intro rfl)
        (shape_ok_cons _ _ _ (And.intro True.intro rfl) shape_ok_nil))

theorem number_decl_shape : ∀ par role b d, shape_ok (number_decl par role b d).1 := by
  intro par role b d
  cases d with
  | ConstDecl cs =>
    unfold number_decl
    dsimp only
    have Hr := number_list_roots (number_constspec (some b) RPlain) (fun _ => True)
      (fun bb x => number_constspec_span (some b) RPlain bb x)
      (root_true_of_view (number_constspec_view (some b) RPlain)) cs (b + 1)
    have Hs := number_list_shape (number_constspec (some b) RPlain)
      (fun bb x => number_constspec_shape (some b) RPlain bb x) (b + 1) cs
    rcases h : number_list (number_constspec (some b) RPlain) (b + 1) cs with ⟨kc, bfin, roots⟩
    rw [h] at Hr Hs
    dsimp only at Hr Hs ⊢
    obtain ⟨_, Hasc, _, _⟩ := Hr
    exact shape_ok_cons _ _ _ (And.intro Hasc True.intro) Hs
  | VarDecl vs =>
    unfold number_decl
    dsimp only
    have Hr := number_list_roots (number_varspec (some b) RPlain) (fun _ => True)
      (fun bb x => number_varspec_span (some b) RPlain bb x)
      (root_true_of_view (number_varspec_view (some b) RPlain)) vs (b + 1)
    have Hs := number_list_shape (number_varspec (some b) RPlain)
      (fun bb x => number_varspec_shape (some b) RPlain bb x) (b + 1) vs
    rcases h : number_list (number_varspec (some b) RPlain) (b + 1) vs with ⟨kc, bfin, roots⟩
    rw [h] at Hr Hs
    dsimp only at Hr Hs ⊢
    obtain ⟨_, Hasc, _, _⟩ := Hr
    exact shape_ok_cons _ _ _ (And.intro Hasc True.intro) Hs
  | TypeDecl ts =>
    unfold number_decl
    dsimp only
    have Hr := number_list_roots (number_typespec (some b) RPlain) (fun _ => True)
      (fun bb x => number_typespec_span (some b) RPlain bb x)
      (root_true_of_view (number_typespec_view (some b) RPlain)) ts (b + 1)
    have Hs := number_list_shape (number_typespec (some b) RPlain)
      (fun bb x => number_typespec_shape (some b) RPlain bb x) (b + 1) ts
    rcases h : number_list (number_typespec (some b) RPlain) (b + 1) ts with ⟨kc, bfin, roots⟩
    rw [h] at Hr Hs
    dsimp only at Hr Hs ⊢
    obtain ⟨_, Hasc, _, _⟩ := Hr
    exact shape_ok_cons _ _ _ (And.intro Hasc True.intro) Hs

theorem number_stmt_shape : ∀ par role b s, shape_ok (number_stmt par role b s).1 := by
  intro par role b s
  cases s with
  | ExprStmt e =>
    unfold number_stmt
    dsimp only
    have Hs := number_expr_shape e (some b) RExprStatementExpr (b + 1)
    rcases h : number_expr (some b) RExprStatementExpr (b + 1) e with ⟨c, b'⟩
    rw [h] at Hs
    dsimp only at Hs ⊢
    exact shape_ok_cons _ _ _ (And.intro True.intro rfl) Hs
  | DeclarationStmt d =>
    unfold number_stmt
    dsimp only
    have Hs := number_decl_shape (some b) RPlain (b + 1) d
    rcases h : number_decl (some b) RPlain (b + 1) d with ⟨c, b'⟩
    rw [h] at Hs
    dsimp only at Hs ⊢
    exact shape_ok_cons _ _ _ (And.intro True.intro rfl) Hs
  | ShortVarDecl names vals =>
    unfold number_stmt
    dsimp only
    have Hnr := number_list_roots (number_bindingname (some b) RShortLhs) (fun _ => True)
      (fun bb x => number_bindingname_spans (some b) RShortLhs bb x)
      (root_true_of_view (number_bindingname_view (some b) RShortLhs))
      (Collections.ne_to_list names) (b + 1)
    have Hns := number_list_shape (number_bindingname (some b) RShortLhs)
      (fun bb x => number_bindingname_shape (some b) RShortLhs bb x) (b + 1) (Collections.ne_to_list names)
    rcases h1 : number_list (number_bindingname (some b) RShortLhs) (b + 1) (Collections.ne_to_list names)
      with ⟨nc, b1, nroots⟩
    rw [h1] at Hnr Hns
    dsimp only at Hnr Hns ⊢
    obtain ⟨Hnlen, Hnasc, Hnbnd, _⟩ := Hnr
    have Hvr := number_list_roots (number_expr (some b) RPlain) (fun _ => True)
      (fun bb x => number_expr_spans x (some b) RPlain bb) (expr_root_true (some b) RPlain)
      (Collections.ne_to_list vals) b1
    have Hvs := number_list_shape (number_expr (some b) RPlain)
      (fun bb x => number_expr_shape x (some b) RPlain bb) b1 (Collections.ne_to_list vals)
    rcases h2 : number_list (number_expr (some b) RPlain) b1 (Collections.ne_to_list vals)
      with ⟨vc, b2, vroots⟩
    rw [h2] at Hvr Hvs
    dsimp only at Hvr Hvs ⊢
    obtain ⟨Hvlen, Hvasc, Hvbnd, _⟩ := Hvr
    apply shape_ok_cons
    · refine And.intro ?_ ?_
      · show asc (nroots ++ vroots)
        exact asc_app _ _ Hnasc Hvasc (fun x y Hx Hy => Nat.lt_of_lt_of_le (Hnbnd x Hx).2 (Hvbnd y Hy).1)
      · show List.length (nroots ++ vroots)
          = List.length (Collections.ne_to_list names) + List.length (Collections.ne_to_list vals)
        rw [length_app, Hnlen, Hvlen]
    · exact shape_ok_app _ _ Hns Hvs

theorem number_block_shape : ∀ par role b blk, shape_ok (number_block par role b blk).1 := by
  intro par role b ⟨stmts⟩
  unfold number_block
  dsimp only
  have Hr := number_list_roots (number_stmt (some b) RPlain) (fun _ => True)
    (fun bb x => number_stmt_span (some b) RPlain bb x)
    (root_true_of_view (number_stmt_view (some b) RPlain)) stmts (b + 1)
  have Hs := number_list_shape (number_stmt (some b) RPlain)
    (fun bb x => number_stmt_shape (some b) RPlain bb x) (b + 1) stmts
  rcases h : number_list (number_stmt (some b) RPlain) (b + 1) stmts with ⟨kc, bfin, roots⟩
  rw [h] at Hr Hs
  dsimp only at Hr Hs ⊢
  obtain ⟨_, Hasc, _, _⟩ := Hr
  exact shape_ok_cons _ _ _ (And.intro Hasc True.intro) Hs

theorem number_toplevel_shape : ∀ par role b td, shape_ok (number_toplevel par role b td).1 := by
  intro par role b td
  cases td with
  | TopDeclaration d =>
    unfold number_toplevel
    dsimp only
    have Hs := number_decl_shape (some b) RPlain (b + 1) d
    rcases h : number_decl (some b) RPlain (b + 1) d with ⟨c, b'⟩
    rw [h] at Hs
    dsimp only at Hs ⊢
    exact shape_ok_cons _ _ _ (And.intro True.intro rfl) Hs
  | Main blk =>
    unfold number_toplevel
    dsimp only
    have Hs := number_block_shape (some b) RPlain (b + 1) blk
    rcases h : number_block (some b) RPlain (b + 1) blk with ⟨c, b'⟩
    rw [h] at Hs
    dsimp only at Hs ⊢
    exact shape_ok_cons _ _ _ (And.intro True.intro rfl) Hs

theorem number_file_shape : ∀ f, shape_ok (number_file f) := by
  intro f
  unfold number_file
  have Hr := number_list_roots (number_toplevel (some 0) RPlain) (fun _ => True)
    (fun bb x => number_toplevel_span (some 0) RPlain bb x)
    (root_true_of_view (number_toplevel_view (some 0) RPlain)) (Syntax.declarations f) 1
  have Hs := number_list_shape (number_toplevel (some 0) RPlain)
    (fun bb x => number_toplevel_shape (some 0) RPlain bb x) 1 (Syntax.declarations f)
  rcases h : number_list (number_toplevel (some 0) RPlain) 1 (Syntax.declarations f) with ⟨dc, bfin, droots⟩
  rw [h] at Hr Hs
  dsimp only at Hr Hs ⊢
  obtain ⟨_, Hasc, _, _⟩ := Hr
  exact shape_ok_cons _ _ _ (And.intro Hasc True.intro) Hs

theorem expr_view_not_const : ∀ e sh, expr_view e = VConstSpec sh → False := by
  intro e sh H
  cases e with
  | Name n => exact nomatch H
  | LiteralExpr l => exact nomatch H
  | Unary op e' => exact nomatch H
  | Application hd args => exact nomatch H

theorem expr_view_no_reverse : ∀ e, no_reverse (expr_view e) := by
  intro e
  cases e with
  | Name n => exact True.intro
  | LiteralExpr l => exact True.intro
  | Unary op e' => exact True.intro
  | Application hd args => exact True.intro

theorem number_leaf_layout : ∀ v par role b, child_layout_ok (number_leaf v par role b).1 := by
  intro v par role b pos c Hin k cp Hcp
  have Hin' : (pos, c) ∈ [(b, mkCell v role par b [] 0)] := Hin
  cases Hin' with
  | head =>
    cases k with
    | zero => exact nomatch Hcp
    | succ _ => exact nomatch Hcp
  | tail _ H => exact nomatch H

-- the `.v`'s inner `assert (Hda : …)` of number_expr_layout, about `number_args`
private theorem number_args_layout_of (b : Nat) : ∀ es : List Syntax.Expr,
    (∀ a ∈ es, ∀ par role bb, child_layout_ok (number_expr par role bb a).1) →
    ∀ i0 bi, child_layout_ok (number_args b i0 bi es).1
             ∧ (∀ (k : Nat) r0, (number_args b i0 bi es).2.2[k]? = some r0 →
                  ∃ cc, (r0, cc) ∈ (number_args b i0 bi es).1 ∧ c_role cc = RApplicationArg (i0 + k)
                        ∧ no_reverse (c_view cc)) := by
  intro es
  induction es with
  | nil =>
    intro _ i0 bi
    refine ⟨(fun _ _ Hin => nomatch (Hin : _ ∈ ([] : List (Nat × Cell)))), fun k r0 Hk => ?_⟩
    have Hk' : ([] : List Nat)[k]? = some r0 := Hk
    cases k with
    | zero => exact nomatch Hk'
    | succ _ => exact nomatch Hk'
  | cons a rest IH =>
    intro Hall i0 bi
    obtain ⟨arest, arc, Haroot, Harole, Haview, _⟩ := number_expr_root a (some b) (RApplicationArg i0) bi
    have Ha := Hall a (List.Mem.head _) (some b) (RApplicationArg i0) bi
    obtain ⟨Hrcok, Hroots⟩ := IH (fun x hx => Hall x (List.Mem.tail _ hx)) (i0 + 1)
      (number_expr (some b) (RApplicationArg i0) bi a).2
    rw [number_args_cons_fst, number_args_cons_roots]
    refine ⟨child_layout_ok_app _ _ Ha Hrcok, ?_⟩
    intro k r0 Hk
    cases k with
    | zero =>
      have H := Option.some.inj Hk
      subst H
      refine ⟨arc, List.mem_append_left _ (by rw [Haroot]; exact List.Mem.head _), Harole.trans rfl, ?_⟩
      rw [Haview]
      exact expr_view_no_reverse a
    | succ k' =>
      obtain ⟨cc, Hcc, Hccrole, Hccnc⟩ := Hroots k' r0 Hk
      exact ⟨cc, List.mem_append_right _ Hcc,
        Hccrole.trans (congrArg RApplicationArg (Nat.add_right_comm i0 1 k')), Hccnc⟩

theorem number_expr_layout : ∀ e par role b, child_layout_ok (number_expr par role b e).1 := by
  intro e
  induction e using Syntax.Expr_ind' with
  | HName n => intro par role b; exact number_leaf_layout (VName n) par role b
  | HLit l => intro par role b; exact number_leaf_layout (VLiteral l) par role b
  | HUnary op e' IH =>
    intro par role b
    have IH' := IH (some b) RUnaryOperand (b + 1)
    obtain ⟨urest, urc, Huroot, Hurole, Huview, _⟩ := number_expr_root e' (some b) RUnaryOperand (b + 1)
    rw [number_expr_unary_fst]
    apply child_layout_ok_node
    · intro k cp Hcp
      have Hcp' : [b + 1][k]? = some cp := Hcp
      cases k with
      | zero =>
        have H := Option.some.inj Hcp'
        subst H
        refine ⟨urc, List.Mem.tail _ (by rw [Huroot]; exact List.Mem.head _), Hurole,
          (fun He => nomatch He), (fun _ He => nomatch He), ?_⟩
        rw [Huview]
        exact no_reverse_clauses _ _ (expr_view_no_reverse e')
      | succ k' =>
        cases k' with
        | zero => exact nomatch Hcp'
        | succ _ => exact nomatch Hcp'
    · exact IH'
  | HApp head args IHh IHa =>
    intro par role b
    have IHh' := IHh (some b) RApplicationHead (b + 1)
    obtain ⟨hrest, hrc, Hhroot, Hhrole, Hhview, _⟩ := number_expr_root head (some b) RApplicationHead (b + 1)
    obtain ⟨Hacok, Haroots⟩ := number_args_layout_of b args IHa 0
      (number_expr (some b) RApplicationHead (b + 1) head).2
    rw [number_expr_app_fst]
    apply child_layout_ok_node
    · intro k cp Hcp
      have Hcp' : ((b + 1)
          :: (number_args b 0 (number_expr (some b) RApplicationHead (b + 1) head).2 args).2.2)[k]? = some cp := Hcp
      cases k with
      | zero =>
        have H := Option.some.inj Hcp'
        subst H
        refine ⟨hrc, List.Mem.tail _ (List.mem_append_left _ (by rw [Hhroot]; exact List.Mem.head _)), Hhrole,
          (fun He => nomatch He), (fun _ He => nomatch He), ?_⟩
        rw [Hhview]
        exact no_reverse_clauses _ _ (expr_view_no_reverse head)
      | succ i =>
        obtain ⟨cc, Hcc, Hccrole, Hccnc⟩ := Haroots i cp Hcp'
        exact ⟨cc, List.Mem.tail _ (List.mem_append_right _ Hcc),
          Hccrole.trans (congrArg RApplicationArg (Nat.zero_add i)),
          (fun He => nomatch He), (fun _ He => nomatch He), no_reverse_clauses _ _ Hccnc⟩
    · exact child_layout_ok_app _ _ IHh' Hacok

theorem number_typeexpr_layout : ∀ par role b t, child_layout_ok (number_typeexpr par role b t).1 :=
  fun par role b t => number_leaf_layout (VTypeExpr t) par role b
theorem number_bindingname_layout : ∀ par role b bn, child_layout_ok (number_bindingname par role b bn).1 :=
  fun par role b bn => number_leaf_layout (VBindingName bn) par role b

theorem number_opttype_layout : ∀ self b ot, child_layout_ok (number_opttype (some self) b ot).1 := by
  intro self b ot
  cases ot with
  | some t => exact number_typeexpr_layout (some self) RTypeUse b t
  | none => exact fun _ _ Hin => nomatch (Hin : _ ∈ ([] : List (Nat × Cell)))

-- the per-root fact the layout lemmas thread through `number_list_roots`: the role and no reverse clause
private theorem root_role_noreverse_of_view {A : Type} {g : Nat → A → List (Nat × Cell) × Nat} {r : Role}
    {v : A → NodeView}
    (Hv : ∀ bb x, ∃ cell rest, (g bb x).1 = (bb, cell) :: rest ∧ c_role cell = r ∧ c_view cell = v x)
    (Hnr : ∀ x, no_reverse (v x)) :
    ∀ bb x, ∃ cell rest, (g bb x).1 = (bb, cell) :: rest ∧ (c_role cell = r ∧ no_reverse (c_view cell)) := by
  intro bb x
  obtain ⟨cell, rest, Hf, Hr, Hview⟩ := Hv bb x
  exact ⟨cell, rest, Hf, Hr, Eq.mpr (congrArg no_reverse Hview) (Hnr x)⟩

private theorem expr_root_role_noreverse (par : Option Nat) (role : Role) :
    ∀ bb x, ∃ cell rest, (number_expr par role bb x).1 = (bb, cell) :: rest
                         ∧ (c_role cell = role ∧ no_reverse (c_view cell)) := by
  intro bb x
  obtain ⟨rest, rc, Hf, Hr, Hv, _⟩ := number_expr_root x par role bb
  exact ⟨rc, rest, Hf, Hr, Eq.mpr (congrArg no_reverse Hv) (expr_view_no_reverse x)⟩

-- `k` at or past the `nn` leading names: the `.v`'s `Nat.ltb_ge` step
private theorem not_lt_of_len_le {k nl nn : Nat} (Hk : nl ≤ k) (Hlen : nl = nn) : ¬ k < nn :=
  fun H => Nat.lt_irrefl k (Nat.lt_of_lt_of_le H (Nat.le_trans (Nat.le_of_eq Hlen.symm) Hk))

theorem number_constspec_layout : ∀ par role b cs, child_layout_ok (number_constspec par role b cs).1 := by
  intro par role b ⟨names, init⟩
  have Hnr := number_list_roots (number_bindingname (some b) (RSpecName ConstSpecF))
    (fun cell => c_role cell = RSpecName ConstSpecF ∧ no_reverse (c_view cell))
    (fun bb x => number_bindingname_spans (some b) (RSpecName ConstSpecF) bb x)
    (root_role_noreverse_of_view (number_bindingname_view (some b) (RSpecName ConstSpecF)) (fun _ => True.intro))
    (Collections.ne_to_list names) (b + 1)
  have Hnl := number_list_layout (number_bindingname (some b) (RSpecName ConstSpecF))
    (fun bb x => number_bindingname_layout (some b) (RSpecName ConstSpecF) bb x)
    (b + 1) (Collections.ne_to_list names)
  unfold number_constspec
  dsimp only
  rcases h1 : number_list (number_bindingname (some b) (RSpecName ConstSpecF)) (b + 1)
    (Collections.ne_to_list names) with ⟨nc, b1, nroots⟩
  rw [h1] at Hnr Hnl
  dsimp only at Hnr Hnl ⊢
  obtain ⟨Hnlen, _, _, Hnnth⟩ := Hnr
  cases init with
  | ExplicitConstInit ot vals =>
    dsimp only
    have Hor := number_opttype_roots b b1 ot
    have Hol := number_opttype_layout b b1 ot
    rcases h2 : number_opttype (some b) b1 ot with ⟨oc, b2, oroots⟩
    rw [h2] at Hor Hol
    dsimp only at Hor Hol ⊢
    obtain ⟨Holen, _, _, _, Honth⟩ := Hor
    have Hvr := number_list_roots (number_expr (some b) RPlain)
      (fun cell => c_role cell = RPlain ∧ no_reverse (c_view cell))
      (fun bb x => number_expr_spans x (some b) RPlain bb) (expr_root_role_noreverse (some b) RPlain)
      (Collections.ne_to_list vals) b2
    have Hvl := number_list_layout (number_expr (some b) RPlain)
      (fun bb x => number_expr_layout x (some b) RPlain bb) b2 (Collections.ne_to_list vals)
    rcases h3 : number_list (number_expr (some b) RPlain) b2 (Collections.ne_to_list vals)
      with ⟨vc, b3, vroots⟩
    rw [h3] at Hvr Hvl
    dsimp only at Hvr Hvl ⊢
    obtain ⟨Hvlen, _, _, Hvnth⟩ := Hvr
    apply child_layout_ok_node
    · intro k cp Hcp
      have Hcp' : (nroots ++ (oroots ++ vroots))[k]? = some cp := Hcp
      cases Nat.lt_or_ge k (List.length nroots) with
      | inl Hk =>
        rw [getElem?_app_left _ _ _ Hk] at Hcp'
        obtain ⟨cell, Hcell, Hrole, Hnc⟩ := Hnnth k cp Hcp'
        exact ⟨cell, List.Mem.tail _ (List.mem_append_left _ Hcell),
          Hrole.trans (cond_decide_true _ (Nat.lt_of_lt_of_eq Hk Hnlen) _ _).symm,
          (fun He => nomatch He), (fun _ He => nomatch He), no_reverse_clauses _ _ Hnc⟩
      | inr Hk =>
        rw [getElem?_app_right _ _ _ Hk] at Hcp'
        have Hnlt := not_lt_of_len_le Hk Hnlen
        cases Nat.lt_or_ge (k - List.length nroots) (List.length oroots) with
        | inl Hk2 =>
          rw [getElem?_app_left _ _ _ Hk2] at Hcp'
          obtain ⟨cell, Hcell, Hrole, Hnc⟩ := Honth _ cp Hcp'
          refine ⟨cell, List.Mem.tail _ (List.mem_append_right _ (List.mem_append_left _ Hcell)), ?_,
            (fun He => nomatch He), (fun _ He => nomatch He), no_reverse_clauses _ _ Hnc⟩
          cases ot with
          | some t0 =>
            have Hk2' : k - List.length nroots < 1 := Nat.lt_of_lt_of_eq Hk2 Holen
            have Hke : k = List.length (Collections.ne_to_list names) :=
              Nat.le_antisymm
                (Nat.le_trans (Nat.le_of_sub_eq_zero (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ Hk2')))
                  (Nat.le_of_eq Hnlen))
                (Nat.le_trans (Nat.le_of_eq Hnlen.symm) Hk)
            exact Hrole.trans
              ((cond_decide_true _ Hke RTypeUse RPlain).symm.trans (cond_decide_false _ Hnlt _ _).symm)
          | none => exact absurd (Nat.lt_of_lt_of_eq Hk2 Holen) (Nat.not_lt_zero _)
        | inr Hk2 =>
          rw [getElem?_app_right _ _ _ Hk2] at Hcp'
          obtain ⟨cell, Hcell, Hrole, Hnc⟩ := Hvnth _ cp Hcp'
          refine ⟨cell, List.Mem.tail _ (List.mem_append_right _ (List.mem_append_right _ Hcell)), ?_,
            (fun He => nomatch He), (fun _ He => nomatch He), no_reverse_clauses _ _ Hnc⟩
          cases ot with
          | some t0 =>
            have H1 : 1 ≤ k - List.length nroots := Nat.le_trans (Nat.le_of_eq Holen.symm) Hk2
            have Hne : ¬ k = List.length (Collections.ne_to_list names) := fun Heq => by
              rw [Heq, ← Hnlen, Nat.sub_self] at H1
              exact absurd H1 (Nat.not_succ_le_zero 0)
            exact Hrole.trans
              ((cond_decide_false _ Hne RTypeUse RPlain).symm.trans (cond_decide_false _ Hnlt _ _).symm)
          | none => exact Hrole.trans (cond_decide_false _ Hnlt _ _).symm
    · exact child_layout_ok_app _ _ Hnl (child_layout_ok_app _ _ Hol Hvl)
  | InheritedConstInit =>
    dsimp only
    apply child_layout_ok_node
    · intro k cp Hcp
      have Hcp' : (nroots ++ [])[k]? = some cp := Hcp
      rw [app_nil] at Hcp'
      obtain ⟨cell, Hcell, Hrole, Hnc⟩ := Hnnth k cp Hcp'
      exact ⟨cell, List.Mem.tail _ (by rw [app_nil]; exact Hcell), Hrole,
        (fun He => nomatch He), (fun _ He => nomatch He), no_reverse_clauses _ _ Hnc⟩
    · rw [app_nil]
      exact Hnl

theorem number_varspec_layout : ∀ par role b vs, child_layout_ok (number_varspec par role b vs).1 := by
  intro par role b ⟨names, init⟩
  have Hnr := number_list_roots (number_bindingname (some b) (RSpecName VarSpecF))
    (fun cell => c_role cell = RSpecName VarSpecF ∧ no_reverse (c_view cell))
    (fun bb x => number_bindingname_spans (some b) (RSpecName VarSpecF) bb x)
    (root_role_noreverse_of_view (number_bindingname_view (some b) (RSpecName VarSpecF)) (fun _ => True.intro))
    (Collections.ne_to_list names) (b + 1)
  have Hnl := number_list_layout (number_bindingname (some b) (RSpecName VarSpecF))
    (fun bb x => number_bindingname_layout (some b) (RSpecName VarSpecF) bb x)
    (b + 1) (Collections.ne_to_list names)
  unfold number_varspec
  dsimp only
  rcases h1 : number_list (number_bindingname (some b) (RSpecName VarSpecF)) (b + 1)
    (Collections.ne_to_list names) with ⟨nc, b1, nroots⟩
  rw [h1] at Hnr Hnl
  dsimp only at Hnr Hnl ⊢
  obtain ⟨Hnlen, _, _, Hnnth⟩ := Hnr
  cases init with
  | VarTypeOnly t =>
    dsimp only
    obtain ⟨tcell, trest, Htf, Htr, Htv⟩ := number_typeexpr_view (some b) RTypeUse b1 t
    have Htl := number_typeexpr_layout (some b) RTypeUse b1 t
    rcases h2 : number_typeexpr (some b) RTypeUse b1 t with ⟨tc, b2⟩
    rw [h2] at Htf Htl
    dsimp only at Htf Htl ⊢
    apply child_layout_ok_node
    · intro k cp Hcp
      have Hcp' : (nroots ++ [b1])[k]? = some cp := Hcp
      cases Nat.lt_or_ge k (List.length nroots) with
      | inl Hk =>
        rw [getElem?_app_left _ _ _ Hk] at Hcp'
        obtain ⟨cell, Hcell, Hrole, Hnc⟩ := Hnnth k cp Hcp'
        exact ⟨cell, List.Mem.tail _ (List.mem_append_left _ Hcell),
          Hrole.trans (cond_decide_true _ (Nat.lt_of_lt_of_eq Hk Hnlen) _ _).symm,
          (fun He => nomatch He), (fun _ He => nomatch He), no_reverse_clauses _ _ Hnc⟩
      | inr Hk =>
        rw [getElem?_app_right _ _ _ Hk] at Hcp'
        have Hnlt := not_lt_of_len_le Hk Hnlen
        cases Hk2 : k - List.length nroots with
        | zero =>
          rw [Hk2] at Hcp'
          have H := Option.some.inj Hcp'
          subst H
          refine ⟨tcell, List.Mem.tail _ (List.mem_append_right _ (by rw [Htf]; exact List.Mem.head _)),
            Htr.trans (cond_decide_false _ Hnlt _ _).symm,
            (fun He => nomatch He), (fun _ He => nomatch He), ?_⟩
          rw [Htv]
          exact no_reverse_clauses _ _ True.intro
        | succ k2 =>
          rw [Hk2] at Hcp'
          cases k2 with
          | zero => exact nomatch Hcp'
          | succ _ => exact nomatch Hcp'
    · exact child_layout_ok_app _ _ Hnl Htl
  | VarValues ot vals =>
    dsimp only
    have Hor := number_opttype_roots b b1 ot
    have Hol := number_opttype_layout b b1 ot
    rcases h2 : number_opttype (some b) b1 ot with ⟨oc, b2, oroots⟩
    rw [h2] at Hor Hol
    dsimp only at Hor Hol ⊢
    obtain ⟨Holen, _, _, _, Honth⟩ := Hor
    have Hvr := number_list_roots (number_expr (some b) RPlain)
      (fun cell => c_role cell = RPlain ∧ no_reverse (c_view cell))
      (fun bb x => number_expr_spans x (some b) RPlain bb) (expr_root_role_noreverse (some b) RPlain)
      (Collections.ne_to_list vals) b2
    have Hvl := number_list_layout (number_expr (some b) RPlain)
      (fun bb x => number_expr_layout x (some b) RPlain bb) b2 (Collections.ne_to_list vals)
    rcases h3 : number_list (number_expr (some b) RPlain) b2 (Collections.ne_to_list vals)
      with ⟨vc, b3, vroots⟩
    rw [h3] at Hvr Hvl
    dsimp only at Hvr Hvl ⊢
    obtain ⟨Hvlen, _, _, Hvnth⟩ := Hvr
    apply child_layout_ok_node
    · intro k cp Hcp
      have Hcp' : (nroots ++ (oroots ++ vroots))[k]? = some cp := Hcp
      cases Nat.lt_or_ge k (List.length nroots) with
      | inl Hk =>
        rw [getElem?_app_left _ _ _ Hk] at Hcp'
        obtain ⟨cell, Hcell, Hrole, Hnc⟩ := Hnnth k cp Hcp'
        exact ⟨cell, List.Mem.tail _ (List.mem_append_left _ Hcell),
          Hrole.trans (cond_decide_true _ (Nat.lt_of_lt_of_eq Hk Hnlen) _ _).symm,
          (fun He => nomatch He), (fun _ He => nomatch He), no_reverse_clauses _ _ Hnc⟩
      | inr Hk =>
        rw [getElem?_app_right _ _ _ Hk] at Hcp'
        have Hnlt := not_lt_of_len_le Hk Hnlen
        cases Nat.lt_or_ge (k - List.length nroots) (List.length oroots) with
        | inl Hk2 =>
          rw [getElem?_app_left _ _ _ Hk2] at Hcp'
          obtain ⟨cell, Hcell, Hrole, Hnc⟩ := Honth _ cp Hcp'
          refine ⟨cell, List.Mem.tail _ (List.mem_append_right _ (List.mem_append_left _ Hcell)), ?_,
            (fun He => nomatch He), (fun _ He => nomatch He), no_reverse_clauses _ _ Hnc⟩
          cases ot with
          | some t0 =>
            have Hk2' : k - List.length nroots < 1 := Nat.lt_of_lt_of_eq Hk2 Holen
            have Hke : k = List.length (Collections.ne_to_list names) :=
              Nat.le_antisymm
                (Nat.le_trans (Nat.le_of_sub_eq_zero (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ Hk2')))
                  (Nat.le_of_eq Hnlen))
                (Nat.le_trans (Nat.le_of_eq Hnlen.symm) Hk)
            exact Hrole.trans
              ((cond_decide_true _ Hke RTypeUse RPlain).symm.trans (cond_decide_false _ Hnlt _ _).symm)
          | none => exact absurd (Nat.lt_of_lt_of_eq Hk2 Holen) (Nat.not_lt_zero _)
        | inr Hk2 =>
          rw [getElem?_app_right _ _ _ Hk2] at Hcp'
          obtain ⟨cell, Hcell, Hrole, Hnc⟩ := Hvnth _ cp Hcp'
          refine ⟨cell, List.Mem.tail _ (List.mem_append_right _ (List.mem_append_right _ Hcell)), ?_,
            (fun He => nomatch He), (fun _ He => nomatch He), no_reverse_clauses _ _ Hnc⟩
          cases ot with
          | some t0 =>
            have H1 : 1 ≤ k - List.length nroots := Nat.le_trans (Nat.le_of_eq Holen.symm) Hk2
            have Hne : ¬ k = List.length (Collections.ne_to_list names) := fun Heq => by
              rw [Heq, ← Hnlen, Nat.sub_self] at H1
              exact absurd H1 (Nat.not_succ_le_zero 0)
            exact Hrole.trans
              ((cond_decide_false _ Hne RTypeUse RPlain).symm.trans (cond_decide_false _ Hnlt _ _).symm)
          | none => exact Hrole.trans (cond_decide_false _ Hnlt _ _).symm
    · exact child_layout_ok_app _ _ Hnl (child_layout_ok_app _ _ Hol Hvl)

theorem number_typespec_layout : ∀ par role b ts, child_layout_ok (number_typespec par role b ts).1 := by
  intro par role b ts
  cases ts with
  | AliasSpec bn t | DefSpec bn t =>
    unfold number_typespec
    dsimp only [number_bindingname, number_typeexpr, number_leaf]
    apply child_layout_ok_node
    · intro k cp Hcp
      have Hcp' : [b + 1, b + 1 + 1][k]? = some cp := Hcp
      cases k with
      | zero =>
        have H := Option.some.inj Hcp'
        subst H
        exact ⟨mkCell (VBindingName bn) (RSpecName TypeSpecF) (some b) (b + 1) [] 0,
          List.Mem.tail _ (List.Mem.head _), rfl, (fun He => nomatch He), (fun _ He => nomatch He),
          no_reverse_clauses _ _ True.intro⟩
      | succ k' =>
        cases k' with
        | zero =>
          have H := Option.some.inj Hcp'
          subst H
          exact ⟨mkCell (VTypeExpr t) RTypeUse (some b) (b + 1 + 1) [] 0,
            List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), rfl, (fun He => nomatch He),
            (fun _ He => nomatch He), no_reverse_clauses _ _ True.intro⟩
        | succ k'' =>
          cases k'' with
          | zero => exact nomatch Hcp'
          | succ _ => exact nomatch Hcp'
    · apply child_layout_ok_node
      · intro k cp Hcp
        cases k with
        | zero => exact nomatch Hcp
        | succ _ => exact nomatch Hcp
      · exact number_leaf_layout (VTypeExpr t) (some b) RTypeUse (b + 1 + 1)

theorem number_decl_layout : ∀ par role b d, child_layout_ok (number_decl par role b d).1 := by
  intro par role b d
  cases d with
  | ConstDecl cs =>
    unfold number_decl
    dsimp only
    have Hroot : ∀ bb x, ∃ cell rest, (number_constspec (some b) RPlain bb x).1 = (bb, cell) :: rest
        ∧ (c_role cell = RPlain ∧ ∃ sh0, c_view cell = VConstSpec sh0) := by
      intro bb x
      obtain ⟨cell, rest, Hf, Hr, Hv⟩ := number_constspec_view (some b) RPlain bb x
      exact ⟨cell, rest, Hf, Hr, constspec_shape x, Hv⟩
    have Hr := number_list_roots (number_constspec (some b) RPlain)
      (fun cell => c_role cell = RPlain ∧ ∃ sh0, c_view cell = VConstSpec sh0)
      (fun bb x => number_constspec_span (some b) RPlain bb x) Hroot cs (b + 1)
    have Hl := number_list_layout (number_constspec (some b) RPlain)
      (fun bb x => number_constspec_layout (some b) RPlain bb x) (b + 1) cs
    rcases h : number_list (number_constspec (some b) RPlain) (b + 1) cs with ⟨kc, bfin, roots⟩
    rw [h] at Hr Hl
    dsimp only at Hr Hl ⊢
    obtain ⟨_, _, _, Hnth⟩ := Hr
    apply child_layout_ok_node
    · intro k cp Hcp
      obtain ⟨cell, Hcell, Hrole, sh0, Hv⟩ := Hnth k cp Hcp
      refine ⟨cell, List.Mem.tail _ Hcell, Hrole, (fun He => nomatch He), ?_, ?_⟩
      · intro fl He
        have He' : VDecl ConstSpecF = VDecl fl := He
        cases He'
        rw [Hv]
        exact True.intro
      · rw [Hv]
        exact spec_reverse_clauses ConstSpecF (VConstSpec sh0) True.intro
    · exact Hl
  | VarDecl vs =>
    unfold number_decl
    dsimp only
    have Hroot : ∀ bb x, ∃ cell rest, (number_varspec (some b) RPlain bb x).1 = (bb, cell) :: rest
        ∧ (c_role cell = RPlain ∧ ∃ sh0, c_view cell = VVarSpec sh0) := by
      intro bb x
      obtain ⟨cell, rest, Hf, Hr, Hv⟩ := number_varspec_view (some b) RPlain bb x
      exact ⟨cell, rest, Hf, Hr, varspec_shape x, Hv⟩
    have Hr := number_list_roots (number_varspec (some b) RPlain)
      (fun cell => c_role cell = RPlain ∧ ∃ sh0, c_view cell = VVarSpec sh0)
      (fun bb x => number_varspec_span (some b) RPlain bb x) Hroot vs (b + 1)
    have Hl := number_list_layout (number_varspec (some b) RPlain)
      (fun bb x => number_varspec_layout (some b) RPlain bb x) (b + 1) vs
    rcases h : number_list (number_varspec (some b) RPlain) (b + 1) vs with ⟨kc, bfin, roots⟩
    rw [h] at Hr Hl
    dsimp only at Hr Hl ⊢
    obtain ⟨_, _, _, Hnth⟩ := Hr
    apply child_layout_ok_node
    · intro k cp Hcp
      obtain ⟨cell, Hcell, Hrole, sh0, Hv⟩ := Hnth k cp Hcp
      refine ⟨cell, List.Mem.tail _ Hcell, Hrole, (fun He => nomatch He), ?_, ?_⟩
      · intro fl He
        have He' : VDecl VarSpecF = VDecl fl := He
        cases He'
        rw [Hv]
        exact True.intro
      · rw [Hv]
        exact spec_reverse_clauses VarSpecF (VVarSpec sh0) True.intro
    · exact Hl
  | TypeDecl ts =>
    unfold number_decl
    dsimp only
    have Hroot : ∀ bb x, ∃ cell rest, (number_typespec (some b) RPlain bb x).1 = (bb, cell) :: rest
        ∧ (c_role cell = RPlain ∧ ∃ sh0, c_view cell = VTypeSpec sh0) := by
      intro bb x
      obtain ⟨cell, rest, Hf, Hr, Hv⟩ := number_typespec_view (some b) RPlain bb x
      exact ⟨cell, rest, Hf, Hr, typespec_shape x, Hv⟩
    have Hr := number_list_roots (number_typespec (some b) RPlain)
      (fun cell => c_role cell = RPlain ∧ ∃ sh0, c_view cell = VTypeSpec sh0)
      (fun bb x => number_typespec_span (some b) RPlain bb x) Hroot ts (b + 1)
    have Hl := number_list_layout (number_typespec (some b) RPlain)
      (fun bb x => number_typespec_layout (some b) RPlain bb x) (b + 1) ts
    rcases h : number_list (number_typespec (some b) RPlain) (b + 1) ts with ⟨kc, bfin, roots⟩
    rw [h] at Hr Hl
    dsimp only at Hr Hl ⊢
    obtain ⟨_, _, _, Hnth⟩ := Hr
    apply child_layout_ok_node
    · intro k cp Hcp
      obtain ⟨cell, Hcell, Hrole, sh0, Hv⟩ := Hnth k cp Hcp
      refine ⟨cell, List.Mem.tail _ Hcell, Hrole, (fun He => nomatch He), ?_, ?_⟩
      · intro fl He
        have He' : VDecl TypeSpecF = VDecl fl := He
        cases He'
        rw [Hv]
        exact True.intro
      · rw [Hv]
        exact spec_reverse_clauses TypeSpecF (VTypeSpec sh0) True.intro
    · exact Hl

theorem number_stmt_layout : ∀ par role b s, child_layout_ok (number_stmt par role b s).1 := by
  intro par role b s
  cases s with
  | ExprStmt e =>
    unfold number_stmt
    dsimp only
    obtain ⟨erest, erc, Heroot, Herole, Heview, _⟩ := number_expr_root e (some b) RExprStatementExpr (b + 1)
    have Hel := number_expr_layout e (some b) RExprStatementExpr (b + 1)
    rcases h : number_expr (some b) RExprStatementExpr (b + 1) e with ⟨c, b'⟩
    rw [h] at Heroot Hel
    dsimp only at Heroot Hel ⊢
    apply child_layout_ok_node
    · intro k cp Hcp
      have Hcp' : [b + 1][k]? = some cp := Hcp
      cases k with
      | zero =>
        have H := Option.some.inj Hcp'
        subst H
        refine ⟨erc, List.Mem.tail _ (by rw [Heroot]; exact List.Mem.head _), Herole,
          (fun He => nomatch He), (fun _ He => nomatch He), ?_⟩
        rw [Heview]
        exact no_reverse_clauses _ _ (expr_view_no_reverse e)
      | succ k' =>
        cases k' with
        | zero => exact nomatch Hcp'
        | succ _ => exact nomatch Hcp'
    · exact Hel
  | DeclarationStmt d =>
    unfold number_stmt
    dsimp only
    obtain ⟨dcell, drest, Hdf, Hdr, Hdv⟩ := number_decl_view (some b) RPlain (b + 1) d
    have Hdl := number_decl_layout (some b) RPlain (b + 1) d
    rcases h : number_decl (some b) RPlain (b + 1) d with ⟨c, b'⟩
    rw [h] at Hdf Hdl
    dsimp only at Hdf Hdl ⊢
    apply child_layout_ok_node
    · intro k cp Hcp
      have Hcp' : [b + 1][k]? = some cp := Hcp
      cases k with
      | zero =>
        have H := Option.some.inj Hcp'
        subst H
        refine ⟨dcell, List.Mem.tail _ (by rw [Hdf]; exact List.Mem.head _), Hdr,
          (fun He => nomatch He), (fun _ He => nomatch He), ?_⟩
        rw [Hdv]
        exact decl_stmt_reverse_clauses (decl_flavor d)
      | succ k' =>
        cases k' with
        | zero => exact nomatch Hcp'
        | succ _ => exact nomatch Hcp'
    · exact Hdl
  | ShortVarDecl names vals =>
    unfold number_stmt
    dsimp only
    have Hnr := number_list_roots (number_bindingname (some b) RShortLhs)
      (fun cell => c_role cell = RShortLhs ∧ no_reverse (c_view cell))
      (fun bb x => number_bindingname_spans (some b) RShortLhs bb x)
      (root_role_noreverse_of_view (number_bindingname_view (some b) RShortLhs) (fun _ => True.intro))
      (Collections.ne_to_list names) (b + 1)
    have Hnl := number_list_layout (number_bindingname (some b) RShortLhs)
      (fun bb x => number_bindingname_layout (some b) RShortLhs bb x) (b + 1) (Collections.ne_to_list names)
    rcases h1 : number_list (number_bindingname (some b) RShortLhs) (b + 1) (Collections.ne_to_list names)
      with ⟨nc, b1, nroots⟩
    rw [h1] at Hnr Hnl
    dsimp only at Hnr Hnl ⊢
    obtain ⟨Hnlen, _, _, Hnnth⟩ := Hnr
    have Hvr := number_list_roots (number_expr (some b) RPlain)
      (fun cell => c_role cell = RPlain ∧ no_reverse (c_view cell))
      (fun bb x => number_expr_spans x (some b) RPlain bb) (expr_root_role_noreverse (some b) RPlain)
      (Collections.ne_to_list vals) b1
    have Hvl := number_list_layout (number_expr (some b) RPlain)
      (fun bb x => number_expr_layout x (some b) RPlain bb) b1 (Collections.ne_to_list vals)
    rcases h2 : number_list (number_expr (some b) RPlain) b1 (Collections.ne_to_list vals)
      with ⟨vc, b2, vroots⟩
    rw [h2] at Hvr Hvl
    dsimp only at Hvr Hvl ⊢
    obtain ⟨_, _, _, Hvnth⟩ := Hvr
    apply child_layout_ok_node
    · intro k cp Hcp
      have Hcp' : (nroots ++ vroots)[k]? = some cp := Hcp
      cases Nat.lt_or_ge k (List.length nroots) with
      | inl Hk =>
        rw [getElem?_app_left _ _ _ Hk] at Hcp'
        obtain ⟨cell, Hcell, Hrole, Hnc⟩ := Hnnth k cp Hcp'
        exact ⟨cell, List.Mem.tail _ (List.mem_append_left _ Hcell),
          Hrole.trans (cond_decide_true _ (Nat.lt_of_lt_of_eq Hk Hnlen) _ _).symm,
          (fun He => nomatch He), (fun _ He => nomatch He), no_reverse_clauses _ _ Hnc⟩
      | inr Hk =>
        rw [getElem?_app_right _ _ _ Hk] at Hcp'
        obtain ⟨cell, Hcell, Hrole, Hnc⟩ := Hvnth _ cp Hcp'
        exact ⟨cell, List.Mem.tail _ (List.mem_append_right _ Hcell),
          Hrole.trans (cond_decide_false _ (not_lt_of_len_le Hk Hnlen) _ _).symm,
          (fun He => nomatch He), (fun _ He => nomatch He), no_reverse_clauses _ _ Hnc⟩
    · exact child_layout_ok_app _ _ Hnl Hvl

theorem number_block_layout : ∀ par role b blk, child_layout_ok (number_block par role b blk).1 := by
  intro par role b ⟨stmts⟩
  unfold number_block
  dsimp only
  have Hroot : ∀ bb x, ∃ cell rest, (number_stmt (some b) RPlain bb x).1 = (bb, cell) :: rest
      ∧ (c_role cell = RPlain ∧ ∃ sh, c_view cell = VStmt sh) := by
    intro bb x
    obtain ⟨cell, rest, Hf, Hr, Hv⟩ := number_stmt_view (some b) RPlain bb x
    exact ⟨cell, rest, Hf, Hr, stmt_shape x, Hv⟩
  have Hr := number_list_roots (number_stmt (some b) RPlain)
    (fun cell => c_role cell = RPlain ∧ ∃ sh, c_view cell = VStmt sh)
    (fun bb x => number_stmt_span (some b) RPlain bb x) Hroot stmts (b + 1)
  have Hl := number_list_layout (number_stmt (some b) RPlain)
    (fun bb x => number_stmt_layout (some b) RPlain bb x) (b + 1) stmts
  rcases h : number_list (number_stmt (some b) RPlain) (b + 1) stmts with ⟨kc, bfin, roots⟩
  rw [h] at Hr Hl
  dsimp only at Hr Hl ⊢
  obtain ⟨_, _, _, Hnth⟩ := Hr
  apply child_layout_ok_node
  · intro k cp Hcp
    obtain ⟨cell, Hcell, Hrole, sh0, Hv⟩ := Hnth k cp Hcp
    refine ⟨cell, List.Mem.tail _ Hcell, Hrole, (fun He => nomatch He), (fun _ He => nomatch He), ?_⟩
    rw [Hv]
    exact stmt_reverse_clauses sh0
  · exact Hl

theorem number_toplevel_layout : ∀ par role b td, child_layout_ok (number_toplevel par role b td).1 := by
  intro par role b td
  cases td with
  | TopDeclaration d =>
    unfold number_toplevel
    dsimp only
    obtain ⟨dcell, drest, Hdf, Hdr, Hdv⟩ := number_decl_view (some b) RPlain (b + 1) d
    have Hdl := number_decl_layout (some b) RPlain (b + 1) d
    rcases h : number_decl (some b) RPlain (b + 1) d with ⟨c, b'⟩
    rw [h] at Hdf Hdl
    dsimp only at Hdf Hdl ⊢
    apply child_layout_ok_node
    · intro k cp Hcp
      have Hcp' : [b + 1][k]? = some cp := Hcp
      cases k with
      | zero =>
        have H := Option.some.inj Hcp'
        subst H
        refine ⟨dcell, List.Mem.tail _ (by rw [Hdf]; exact List.Mem.head _), Hdr,
          (fun He => nomatch He), (fun _ He => nomatch He), ?_⟩
        rw [Hdv]
        exact decl_top_reverse_clauses (decl_flavor d)
      | succ k' =>
        cases k' with
        | zero => exact nomatch Hcp'
        | succ _ => exact nomatch Hcp'
    · exact Hdl
  | Main blk =>
    unfold number_toplevel
    dsimp only
    obtain ⟨bcell, brest, Hbf, Hbr, Hbv⟩ := number_block_view (some b) RPlain (b + 1) blk
    have Hbl := number_block_layout (some b) RPlain (b + 1) blk
    rcases h : number_block (some b) RPlain (b + 1) blk with ⟨c, b'⟩
    rw [h] at Hbf Hbl
    dsimp only at Hbf Hbl ⊢
    apply child_layout_ok_node
    · intro k cp Hcp
      have Hcp' : [b + 1][k]? = some cp := Hcp
      cases k with
      | zero =>
        have H := Option.some.inj Hcp'
        subst H
        refine ⟨bcell, List.Mem.tail _ (by rw [Hbf]; exact List.Mem.head _), Hbr,
          (fun _ => Hbv), (fun _ He => nomatch He), ?_⟩
        rw [Hbv]
        exact no_reverse_clauses _ _ True.intro
      | succ k' =>
        cases k' with
        | zero => exact nomatch Hcp'
        | succ _ => exact nomatch Hcp'
    · exact Hbl

theorem number_file_layout : ∀ f, child_layout_ok (number_file f) := by
  intro f
  unfold number_file
  have Hr := number_list_roots (number_toplevel (some 0) RPlain)
    (fun cell => c_role cell = RPlain ∧ no_reverse (c_view cell))
    (fun bb x => number_toplevel_span (some 0) RPlain bb x)
    (root_role_noreverse_of_view (number_toplevel_view (some 0) RPlain) (fun _ => True.intro))
    (Syntax.declarations f) 1
  have Hl := number_list_layout (number_toplevel (some 0) RPlain)
    (fun bb x => number_toplevel_layout (some 0) RPlain bb x) 1 (Syntax.declarations f)
  rcases h : number_list (number_toplevel (some 0) RPlain) 1 (Syntax.declarations f) with ⟨dc, bfin, droots⟩
  rw [h] at Hr Hl
  dsimp only at Hr Hl ⊢
  obtain ⟨_, _, _, Hnth⟩ := Hr
  apply child_layout_ok_node
  · intro k cp Hcp
    obtain ⟨cell, Hcell, Hrole, Hnc⟩ := Hnth k cp Hcp
    exact ⟨cell, List.Mem.tail _ Hcell, Hrole, (fun He => nomatch He), (fun _ He => nomatch He),
      no_reverse_clauses _ _ Hnc⟩
  · exact Hl

/-! the numbering's head is the file root cell at position zero -/
theorem number_file_root : ∀ f, ∃ ext ch, (0, mkCell VFile RPlain none ext ch 0) ∈ number_file f := by
  intro f
  unfold number_file
  rcases h : number_list (number_toplevel (some 0) RPlain) 1 (Syntax.declarations f) with ⟨dc, bfin, droots⟩
  dsimp only
  exact ⟨bfin - 1, droots, List.Mem.head _⟩

def child_kind_ok (occs : List (Nat × Cell)) : Prop :=
  ∀ pos cell, (pos, cell) ∈ occs →
    ∀ k cp, (c_children cell)[k]? = some cp →
      ∃ cc, (cp, cc) ∈ occs ∧ kind_of_view (c_view cc) = layout_kind (c_view cell) k

theorem child_kind_ok_app : ∀ c1 c2, child_kind_ok c1 → child_kind_ok c2 → child_kind_ok (c1 ++ c2) := by
  intro c1 c2 H1 H2 pos cell Hin k cp Hcp
  cases mem_app_or Hin with
  | inl Hin =>
    obtain ⟨cc, Hc, Hp⟩ := H1 pos cell Hin k cp Hcp
    exact ⟨cc, List.mem_append_left c2 Hc, Hp⟩
  | inr Hin =>
    obtain ⟨cc, Hc, Hp⟩ := H2 pos cell Hin k cp Hcp
    exact ⟨cc, List.mem_append_right c1 Hc, Hp⟩

theorem child_kind_ok_node : ∀ self cell kids,
    (∀ k cp, (c_children cell)[k]? = some cp →
       ∃ cc, (cp, cc) ∈ (self, cell) :: kids ∧ kind_of_view (c_view cc) = layout_kind (c_view cell) k) →
    child_kind_ok kids → child_kind_ok ((self, cell) :: kids) := by
  intro self cell kids Hself Hkids pos c Hin k cp Hcp
  cases Hin with
  | head => exact Hself k cp Hcp
  | tail _ Hin =>
    obtain ⟨cc, Hc, Hp⟩ := Hkids pos c Hin k cp Hcp
    exact ⟨cc, List.Mem.tail _ Hc, Hp⟩

theorem number_leaf_kind : ∀ v par role b, child_kind_ok (number_leaf v par role b).1 := by
  intro v par role b pos cell Hin k cp Hcp
  have Hin' : (pos, cell) ∈ [(b, mkCell v role par b [] 0)] := Hin
  cases Hin' with
  | head =>
    cases k with
    | zero => exact nomatch Hcp
    | succ _ => exact nomatch Hcp
  | tail _ H => exact nomatch H

theorem expr_view_kind : ∀ e, kind_of_view (expr_view e) = ExprKind := by
  intro e
  cases e with
  | Name n => exact rfl
  | LiteralExpr l => exact rfl
  | Unary op e' => exact rfl
  | Application hd args => exact rfl

theorem number_list_kind {A : Type} (g : Nat → A → List (Nat × Cell) × Nat) :
    (∀ b x, child_kind_ok (g b x).1) →
    ∀ b xs, child_kind_ok (number_list g b xs).1 := by
  intro Hg b xs
  induction xs generalizing b with
  | nil => exact fun _ _ Hin => nomatch (Hin : _ ∈ ([] : List (Nat × Cell)))
  | cons x rest IH =>
    rw [number_list_cons_fst]
    exact child_kind_ok_app _ _ (Hg b x) (IH (g b x).2)

-- the `.v`'s inner `assert (Hda : …)` of number_expr_kind, about `number_args`
private theorem number_args_kind_of (b : Nat) : ∀ es : List Syntax.Expr,
    (∀ a ∈ es, ∀ par role bb, child_kind_ok (number_expr par role bb a).1) →
    ∀ i0 bi, child_kind_ok (number_args b i0 bi es).1
             ∧ (∀ (k : Nat) r0, (number_args b i0 bi es).2.2[k]? = some r0 →
                  ∃ cc, (r0, cc) ∈ (number_args b i0 bi es).1 ∧ kind_of_view (c_view cc) = ExprKind) := by
  intro es
  induction es with
  | nil =>
    intro _ i0 bi
    refine ⟨(fun _ _ Hin => nomatch (Hin : _ ∈ ([] : List (Nat × Cell)))), fun k r0 Hk => ?_⟩
    have Hk' : ([] : List Nat)[k]? = some r0 := Hk
    cases k with
    | zero => exact nomatch Hk'
    | succ _ => exact nomatch Hk'
  | cons a rest IH =>
    intro Hall i0 bi
    obtain ⟨arest, arc, Haroot, _, Haview, _⟩ := number_expr_root a (some b) (RApplicationArg i0) bi
    have Ha := Hall a (List.Mem.head _) (some b) (RApplicationArg i0) bi
    obtain ⟨Hrcok, Hroots⟩ := IH (fun x hx => Hall x (List.Mem.tail _ hx)) (i0 + 1)
      (number_expr (some b) (RApplicationArg i0) bi a).2
    rw [number_args_cons_fst, number_args_cons_roots]
    refine ⟨child_kind_ok_app _ _ Ha Hrcok, ?_⟩
    intro k r0 Hk
    cases k with
    | zero =>
      have H := Option.some.inj Hk
      subst H
      exact ⟨arc, List.mem_append_left _ (by rw [Haroot]; exact List.Mem.head _),
        (congrArg kind_of_view Haview).trans (expr_view_kind a)⟩
    | succ k' =>
      obtain ⟨cc, Hcc, Hcck⟩ := Hroots k' r0 Hk
      exact ⟨cc, List.mem_append_right _ Hcc, Hcck⟩

theorem number_expr_kind : ∀ e par role b, child_kind_ok (number_expr par role b e).1 := by
  intro e
  induction e using Syntax.Expr_ind' with
  | HName n => intro par role b; exact number_leaf_kind (VName n) par role b
  | HLit l => intro par role b; exact number_leaf_kind (VLiteral l) par role b
  | HUnary op e' IH =>
    intro par role b
    have IH' := IH (some b) RUnaryOperand (b + 1)
    obtain ⟨urest, urc, Huroot, _, Huview, _⟩ := number_expr_root e' (some b) RUnaryOperand (b + 1)
    rw [number_expr_unary_fst]
    apply child_kind_ok_node
    · intro k cp Hcp
      have Hcp' : [b + 1][k]? = some cp := Hcp
      cases k with
      | zero =>
        have H := Option.some.inj Hcp'
        subst H
        exact ⟨urc, List.Mem.tail _ (by rw [Huroot]; exact List.Mem.head _),
          (congrArg kind_of_view Huview).trans (expr_view_kind e')⟩
      | succ k' =>
        cases k' with
        | zero => exact nomatch Hcp'
        | succ _ => exact nomatch Hcp'
    · exact IH'
  | HApp head args IHh IHa =>
    intro par role b
    have IHh' := IHh (some b) RApplicationHead (b + 1)
    obtain ⟨hrest, hrc, Hhroot, _, Hhview, _⟩ := number_expr_root head (some b) RApplicationHead (b + 1)
    obtain ⟨Hacok, Haroots⟩ := number_args_kind_of b args IHa 0
      (number_expr (some b) RApplicationHead (b + 1) head).2
    rw [number_expr_app_fst]
    apply child_kind_ok_node
    · intro k cp Hcp
      have Hcp' : ((b + 1)
          :: (number_args b 0 (number_expr (some b) RApplicationHead (b + 1) head).2 args).2.2)[k]? = some cp := Hcp
      cases k with
      | zero =>
        have H := Option.some.inj Hcp'
        subst H
        exact ⟨hrc, List.Mem.tail _ (List.mem_append_left _ (by rw [Hhroot]; exact List.Mem.head _)),
          (congrArg kind_of_view Hhview).trans (expr_view_kind head)⟩
      | succ i =>
        obtain ⟨cc, Hcc, Hcck⟩ := Haroots i cp Hcp'
        exact ⟨cc, List.Mem.tail _ (List.mem_append_right _ Hcc), Hcck⟩
    · exact child_kind_ok_app _ _ IHh' Hacok

theorem number_typeexpr_kind : ∀ par role b t, child_kind_ok (number_typeexpr par role b t).1 :=
  fun par role b t => number_leaf_kind (VTypeExpr t) par role b
theorem number_bindingname_kind : ∀ par role b bn, child_kind_ok (number_bindingname par role b bn).1 :=
  fun par role b bn => number_leaf_kind (VBindingName bn) par role b
theorem number_opttype_kind : ∀ self b ot, child_kind_ok (number_opttype (some self) b ot).1 := by
  intro self b ot
  cases ot with
  | some t => exact number_typeexpr_kind (some self) RTypeUse b t
  | none => exact fun _ _ Hin => nomatch (Hin : _ ∈ ([] : List (Nat × Cell)))

-- the per-root fact the kind lemmas thread through `number_list_roots`: the root view's kind
private theorem root_kind_of_view {A : Type} {g : Nat → A → List (Nat × Cell) × Nat} {r : Role}
    {v : A → NodeView} (kd : Kind)
    (Hv : ∀ bb x, ∃ cell rest, (g bb x).1 = (bb, cell) :: rest ∧ c_role cell = r ∧ c_view cell = v x)
    (Hk : ∀ x, kind_of_view (v x) = kd) :
    ∀ bb x, ∃ cell rest, (g bb x).1 = (bb, cell) :: rest ∧ kind_of_view (c_view cell) = kd := by
  intro bb x
  obtain ⟨cell, rest, Hf, _, Hview⟩ := Hv bb x
  exact ⟨cell, rest, Hf, (congrArg kind_of_view Hview).trans (Hk x)⟩

private theorem expr_root_kind (par : Option Nat) (role : Role) :
    ∀ bb x, ∃ cell rest, (number_expr par role bb x).1 = (bb, cell) :: rest
                         ∧ kind_of_view (c_view cell) = ExprKind := by
  intro bb x
  obtain ⟨rest, rc, Hf, _, Hv, _⟩ := number_expr_root x par role bb
  exact ⟨rc, rest, Hf, (congrArg kind_of_view Hv).trans (expr_view_kind x)⟩

theorem number_constspec_kind : ∀ par role b cs, child_kind_ok (number_constspec par role b cs).1 := by
  intro par role b ⟨names, init⟩
  have Hnr := number_list_roots (number_bindingname (some b) (RSpecName ConstSpecF))
    (fun cell => kind_of_view (c_view cell) = BindingNameKind)
    (fun bb x => number_bindingname_spans (some b) (RSpecName ConstSpecF) bb x)
    (root_kind_of_view BindingNameKind (number_bindingname_view (some b) (RSpecName ConstSpecF)) (fun _ => rfl))
    (Collections.ne_to_list names) (b + 1)
  have Hnl := number_list_kind (number_bindingname (some b) (RSpecName ConstSpecF))
    (fun bb x => number_bindingname_kind (some b) (RSpecName ConstSpecF) bb x)
    (b + 1) (Collections.ne_to_list names)
  unfold number_constspec
  dsimp only
  rcases h1 : number_list (number_bindingname (some b) (RSpecName ConstSpecF)) (b + 1)
    (Collections.ne_to_list names) with ⟨nc, b1, nroots⟩
  rw [h1] at Hnr Hnl
  dsimp only at Hnr Hnl ⊢
  obtain ⟨Hnlen, _, _, Hnnth⟩ := Hnr
  cases init with
  | ExplicitConstInit ot vals =>
    dsimp only
    have Hor := number_opttype_roots b b1 ot
    have Hol := number_opttype_kind b b1 ot
    have Hocls := number_opttype_class ot (some b) b1
    rcases h2 : number_opttype (some b) b1 ot with ⟨oc, b2, oroots⟩
    rw [h2] at Hor Hol Hocls
    dsimp only at Hor Hol Hocls ⊢
    obtain ⟨Holen, _, _, _, Honth⟩ := Hor
    have Hvr := number_list_roots (number_expr (some b) RPlain)
      (fun cell => kind_of_view (c_view cell) = ExprKind)
      (fun bb x => number_expr_spans x (some b) RPlain bb) (expr_root_kind (some b) RPlain)
      (Collections.ne_to_list vals) b2
    have Hvl := number_list_kind (number_expr (some b) RPlain)
      (fun bb x => number_expr_kind x (some b) RPlain bb) b2 (Collections.ne_to_list vals)
    rcases h3 : number_list (number_expr (some b) RPlain) b2 (Collections.ne_to_list vals)
      with ⟨vc, b3, vroots⟩
    rw [h3] at Hvr Hvl
    dsimp only at Hvr Hvl ⊢
    obtain ⟨Hvlen, _, _, Hvnth⟩ := Hvr
    apply child_kind_ok_node
    · intro k cp Hcp
      have Hcp' : (nroots ++ (oroots ++ vroots))[k]? = some cp := Hcp
      cases Nat.lt_or_ge k (List.length nroots) with
      | inl Hk =>
        rw [getElem?_app_left _ _ _ Hk] at Hcp'
        obtain ⟨cell, Hcell, Hkind⟩ := Hnnth k cp Hcp'
        exact ⟨cell, List.Mem.tail _ (List.mem_append_left _ Hcell),
          Hkind.trans (cond_decide_true _ (Nat.lt_of_lt_of_eq Hk Hnlen) _ _).symm⟩
      | inr Hk =>
        rw [getElem?_app_right _ _ _ Hk] at Hcp'
        have Hnlt := not_lt_of_len_le Hk Hnlen
        cases Nat.lt_or_ge (k - List.length nroots) (List.length oroots) with
        | inl Hk2 =>
          rw [getElem?_app_left _ _ _ Hk2] at Hcp'
          obtain ⟨cell, Hcell, Hrole, _⟩ := Honth _ cp Hcp'
          have Hkind : kind_of_view (c_view cell) = TypeExprKind := by
            have H : rv_ok cell := Hocls (cp, cell) Hcell
            unfold rv_ok at H
            rw [Hrole] at H
            exact H
          refine ⟨cell, List.Mem.tail _ (List.mem_append_right _ (List.mem_append_left _ Hcell)), ?_⟩
          cases ot with
          | some t0 =>
            have Hk2' : k - List.length nroots < 1 := Nat.lt_of_lt_of_eq Hk2 Holen
            have Hke : k = List.length (Collections.ne_to_list names) :=
              Nat.le_antisymm
                (Nat.le_trans (Nat.le_of_sub_eq_zero (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ Hk2')))
                  (Nat.le_of_eq Hnlen))
                (Nat.le_trans (Nat.le_of_eq Hnlen.symm) Hk)
            exact Hkind.trans
              ((cond_decide_true _ Hke TypeExprKind ExprKind).symm.trans (cond_decide_false _ Hnlt _ _).symm)
          | none => exact absurd (Nat.lt_of_lt_of_eq Hk2 Holen) (Nat.not_lt_zero _)
        | inr Hk2 =>
          rw [getElem?_app_right _ _ _ Hk2] at Hcp'
          obtain ⟨cell, Hcell, Hkind⟩ := Hvnth _ cp Hcp'
          refine ⟨cell, List.Mem.tail _ (List.mem_append_right _ (List.mem_append_right _ Hcell)), ?_⟩
          cases ot with
          | some t0 =>
            have H1 : 1 ≤ k - List.length nroots := Nat.le_trans (Nat.le_of_eq Holen.symm) Hk2
            have Hne : ¬ k = List.length (Collections.ne_to_list names) := fun Heq => by
              rw [Heq, ← Hnlen, Nat.sub_self] at H1
              exact absurd H1 (Nat.not_succ_le_zero 0)
            exact Hkind.trans
              ((cond_decide_false _ Hne TypeExprKind ExprKind).symm.trans (cond_decide_false _ Hnlt _ _).symm)
          | none => exact Hkind.trans (cond_decide_false _ Hnlt _ _).symm
    · exact child_kind_ok_app _ _ Hnl (child_kind_ok_app _ _ Hol Hvl)
  | InheritedConstInit =>
    dsimp only
    apply child_kind_ok_node
    · intro k cp Hcp
      have Hcp' : (nroots ++ [])[k]? = some cp := Hcp
      rw [app_nil] at Hcp'
      obtain ⟨cell, Hcell, Hkind⟩ := Hnnth k cp Hcp'
      exact ⟨cell, List.Mem.tail _ (by rw [app_nil]; exact Hcell), Hkind⟩
    · rw [app_nil]
      exact Hnl

theorem number_varspec_kind : ∀ par role b vs, child_kind_ok (number_varspec par role b vs).1 := by
  intro par role b ⟨names, init⟩
  have Hnr := number_list_roots (number_bindingname (some b) (RSpecName VarSpecF))
    (fun cell => kind_of_view (c_view cell) = BindingNameKind)
    (fun bb x => number_bindingname_spans (some b) (RSpecName VarSpecF) bb x)
    (root_kind_of_view BindingNameKind (number_bindingname_view (some b) (RSpecName VarSpecF)) (fun _ => rfl))
    (Collections.ne_to_list names) (b + 1)
  have Hnl := number_list_kind (number_bindingname (some b) (RSpecName VarSpecF))
    (fun bb x => number_bindingname_kind (some b) (RSpecName VarSpecF) bb x)
    (b + 1) (Collections.ne_to_list names)
  unfold number_varspec
  dsimp only
  rcases h1 : number_list (number_bindingname (some b) (RSpecName VarSpecF)) (b + 1)
    (Collections.ne_to_list names) with ⟨nc, b1, nroots⟩
  rw [h1] at Hnr Hnl
  dsimp only at Hnr Hnl ⊢
  obtain ⟨Hnlen, _, _, Hnnth⟩ := Hnr
  cases init with
  | VarTypeOnly t =>
    dsimp only
    obtain ⟨tcell, trest, Htf, _, Htv⟩ := number_typeexpr_view (some b) RTypeUse b1 t
    have Htl := number_typeexpr_kind (some b) RTypeUse b1 t
    rcases h2 : number_typeexpr (some b) RTypeUse b1 t with ⟨tc, b2⟩
    rw [h2] at Htf Htl
    dsimp only at Htf Htl ⊢
    apply child_kind_ok_node
    · intro k cp Hcp
      have Hcp' : (nroots ++ [b1])[k]? = some cp := Hcp
      cases Nat.lt_or_ge k (List.length nroots) with
      | inl Hk =>
        rw [getElem?_app_left _ _ _ Hk] at Hcp'
        obtain ⟨cell, Hcell, Hkind⟩ := Hnnth k cp Hcp'
        exact ⟨cell, List.Mem.tail _ (List.mem_append_left _ Hcell),
          Hkind.trans (cond_decide_true _ (Nat.lt_of_lt_of_eq Hk Hnlen) _ _).symm⟩
      | inr Hk =>
        rw [getElem?_app_right _ _ _ Hk] at Hcp'
        have Hnlt := not_lt_of_len_le Hk Hnlen
        cases Hk2 : k - List.length nroots with
        | zero =>
          rw [Hk2] at Hcp'
          have H := Option.some.inj Hcp'
          subst H
          exact ⟨tcell, List.Mem.tail _ (List.mem_append_right _ (by rw [Htf]; exact List.Mem.head _)),
            (congrArg kind_of_view Htv).trans (cond_decide_false _ Hnlt _ _).symm⟩
        | succ k2 =>
          rw [Hk2] at Hcp'
          cases k2 with
          | zero => exact nomatch Hcp'
          | succ _ => exact nomatch Hcp'
    · exact child_kind_ok_app _ _ Hnl Htl
  | VarValues ot vals =>
    dsimp only
    have Hor := number_opttype_roots b b1 ot
    have Hol := number_opttype_kind b b1 ot
    have Hocls := number_opttype_class ot (some b) b1
    rcases h2 : number_opttype (some b) b1 ot with ⟨oc, b2, oroots⟩
    rw [h2] at Hor Hol Hocls
    dsimp only at Hor Hol Hocls ⊢
    obtain ⟨Holen, _, _, _, Honth⟩ := Hor
    have Hvr := number_list_roots (number_expr (some b) RPlain)
      (fun cell => kind_of_view (c_view cell) = ExprKind)
      (fun bb x => number_expr_spans x (some b) RPlain bb) (expr_root_kind (some b) RPlain)
      (Collections.ne_to_list vals) b2
    have Hvl := number_list_kind (number_expr (some b) RPlain)
      (fun bb x => number_expr_kind x (some b) RPlain bb) b2 (Collections.ne_to_list vals)
    rcases h3 : number_list (number_expr (some b) RPlain) b2 (Collections.ne_to_list vals)
      with ⟨vc, b3, vroots⟩
    rw [h3] at Hvr Hvl
    dsimp only at Hvr Hvl ⊢
    obtain ⟨Hvlen, _, _, Hvnth⟩ := Hvr
    apply child_kind_ok_node
    · intro k cp Hcp
      have Hcp' : (nroots ++ (oroots ++ vroots))[k]? = some cp := Hcp
      cases Nat.lt_or_ge k (List.length nroots) with
      | inl Hk =>
        rw [getElem?_app_left _ _ _ Hk] at Hcp'
        obtain ⟨cell, Hcell, Hkind⟩ := Hnnth k cp Hcp'
        exact ⟨cell, List.Mem.tail _ (List.mem_append_left _ Hcell),
          Hkind.trans (cond_decide_true _ (Nat.lt_of_lt_of_eq Hk Hnlen) _ _).symm⟩
      | inr Hk =>
        rw [getElem?_app_right _ _ _ Hk] at Hcp'
        have Hnlt := not_lt_of_len_le Hk Hnlen
        cases Nat.lt_or_ge (k - List.length nroots) (List.length oroots) with
        | inl Hk2 =>
          rw [getElem?_app_left _ _ _ Hk2] at Hcp'
          obtain ⟨cell, Hcell, Hrole, _⟩ := Honth _ cp Hcp'
          have Hkind : kind_of_view (c_view cell) = TypeExprKind := by
            have H : rv_ok cell := Hocls (cp, cell) Hcell
            unfold rv_ok at H
            rw [Hrole] at H
            exact H
          refine ⟨cell, List.Mem.tail _ (List.mem_append_right _ (List.mem_append_left _ Hcell)), ?_⟩
          cases ot with
          | some t0 =>
            have Hk2' : k - List.length nroots < 1 := Nat.lt_of_lt_of_eq Hk2 Holen
            have Hke : k = List.length (Collections.ne_to_list names) :=
              Nat.le_antisymm
                (Nat.le_trans (Nat.le_of_sub_eq_zero (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ Hk2')))
                  (Nat.le_of_eq Hnlen))
                (Nat.le_trans (Nat.le_of_eq Hnlen.symm) Hk)
            exact Hkind.trans
              ((cond_decide_true _ Hke TypeExprKind ExprKind).symm.trans (cond_decide_false _ Hnlt _ _).symm)
          | none => exact absurd (Nat.lt_of_lt_of_eq Hk2 Holen) (Nat.not_lt_zero _)
        | inr Hk2 =>
          rw [getElem?_app_right _ _ _ Hk2] at Hcp'
          obtain ⟨cell, Hcell, Hkind⟩ := Hvnth _ cp Hcp'
          refine ⟨cell, List.Mem.tail _ (List.mem_append_right _ (List.mem_append_right _ Hcell)), ?_⟩
          cases ot with
          | some t0 =>
            have H1 : 1 ≤ k - List.length nroots := Nat.le_trans (Nat.le_of_eq Holen.symm) Hk2
            have Hne : ¬ k = List.length (Collections.ne_to_list names) := fun Heq => by
              rw [Heq, ← Hnlen, Nat.sub_self] at H1
              exact absurd H1 (Nat.not_succ_le_zero 0)
            exact Hkind.trans
              ((cond_decide_false _ Hne TypeExprKind ExprKind).symm.trans (cond_decide_false _ Hnlt _ _).symm)
          | none => exact Hkind.trans (cond_decide_false _ Hnlt _ _).symm
    · exact child_kind_ok_app _ _ Hnl (child_kind_ok_app _ _ Hol Hvl)

theorem number_typespec_kind : ∀ par role b ts, child_kind_ok (number_typespec par role b ts).1 := by
  intro par role b ts
  cases ts with
  | AliasSpec bn t | DefSpec bn t =>
    unfold number_typespec
    dsimp only [number_bindingname, number_typeexpr, number_leaf]
    apply child_kind_ok_node
    · intro k cp Hcp
      have Hcp' : [b + 1, b + 1 + 1][k]? = some cp := Hcp
      cases k with
      | zero =>
        have H := Option.some.inj Hcp'
        subst H
        exact ⟨mkCell (VBindingName bn) (RSpecName TypeSpecF) (some b) (b + 1) [] 0,
          List.Mem.tail _ (List.Mem.head _), rfl⟩
      | succ k' =>
        cases k' with
        | zero =>
          have H := Option.some.inj Hcp'
          subst H
          exact ⟨mkCell (VTypeExpr t) RTypeUse (some b) (b + 1 + 1) [] 0,
            List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)), rfl⟩
        | succ k'' =>
          cases k'' with
          | zero => exact nomatch Hcp'
          | succ _ => exact nomatch Hcp'
    · apply child_kind_ok_node
      · intro k cp Hcp
        cases k with
        | zero => exact nomatch Hcp
        | succ _ => exact nomatch Hcp
      · exact number_leaf_kind (VTypeExpr t) (some b) RTypeUse (b + 1 + 1)

theorem number_decl_kind : ∀ par role b d, child_kind_ok (number_decl par role b d).1 := by
  intro par role b d
  cases d with
  | ConstDecl cs =>
    unfold number_decl
    dsimp only
    have Hr := number_list_roots (number_constspec (some b) RPlain)
      (fun cell => kind_of_view (c_view cell) = SpecKind ConstSpecF)
      (fun bb x => number_constspec_span (some b) RPlain bb x)
      (root_kind_of_view (SpecKind ConstSpecF) (number_constspec_view (some b) RPlain) (fun _ => rfl)) cs (b + 1)
    have Hl := number_list_kind (number_constspec (some b) RPlain)
      (fun bb x => number_constspec_kind (some b) RPlain bb x) (b + 1) cs
    rcases h : number_list (number_constspec (some b) RPlain) (b + 1) cs with ⟨kc, bfin, roots⟩
    rw [h] at Hr Hl
    dsimp only at Hr Hl ⊢
    obtain ⟨_, _, _, Hnth⟩ := Hr
    apply child_kind_ok_node
    · intro k cp Hcp
      obtain ⟨cell, Hcell, Hkind⟩ := Hnth k cp Hcp
      exact ⟨cell, List.Mem.tail _ Hcell, Hkind⟩
    · exact Hl
  | VarDecl vs =>
    unfold number_decl
    dsimp only
    have Hr := number_list_roots (number_varspec (some b) RPlain)
      (fun cell => kind_of_view (c_view cell) = SpecKind VarSpecF)
      (fun bb x => number_varspec_span (some b) RPlain bb x)
      (root_kind_of_view (SpecKind VarSpecF) (number_varspec_view (some b) RPlain) (fun _ => rfl)) vs (b + 1)
    have Hl := number_list_kind (number_varspec (some b) RPlain)
      (fun bb x => number_varspec_kind (some b) RPlain bb x) (b + 1) vs
    rcases h : number_list (number_varspec (some b) RPlain) (b + 1) vs with ⟨kc, bfin, roots⟩
    rw [h] at Hr Hl
    dsimp only at Hr Hl ⊢
    obtain ⟨_, _, _, Hnth⟩ := Hr
    apply child_kind_ok_node
    · intro k cp Hcp
      obtain ⟨cell, Hcell, Hkind⟩ := Hnth k cp Hcp
      exact ⟨cell, List.Mem.tail _ Hcell, Hkind⟩
    · exact Hl
  | TypeDecl ts =>
    unfold number_decl
    dsimp only
    have Hr := number_list_roots (number_typespec (some b) RPlain)
      (fun cell => kind_of_view (c_view cell) = SpecKind TypeSpecF)
      (fun bb x => number_typespec_span (some b) RPlain bb x)
      (root_kind_of_view (SpecKind TypeSpecF) (number_typespec_view (some b) RPlain) (fun _ => rfl)) ts (b + 1)
    have Hl := number_list_kind (number_typespec (some b) RPlain)
      (fun bb x => number_typespec_kind (some b) RPlain bb x) (b + 1) ts
    rcases h : number_list (number_typespec (some b) RPlain) (b + 1) ts with ⟨kc, bfin, roots⟩
    rw [h] at Hr Hl
    dsimp only at Hr Hl ⊢
    obtain ⟨_, _, _, Hnth⟩ := Hr
    apply child_kind_ok_node
    · intro k cp Hcp
      obtain ⟨cell, Hcell, Hkind⟩ := Hnth k cp Hcp
      exact ⟨cell, List.Mem.tail _ Hcell, Hkind⟩
    · exact Hl

theorem number_stmt_kind : ∀ par role b s, child_kind_ok (number_stmt par role b s).1 := by
  intro par role b s
  cases s with
  | ExprStmt e =>
    unfold number_stmt
    dsimp only
    obtain ⟨erest, erc, Heroot, _, Heview, _⟩ := number_expr_root e (some b) RExprStatementExpr (b + 1)
    have Hel := number_expr_kind e (some b) RExprStatementExpr (b + 1)
    rcases h : number_expr (some b) RExprStatementExpr (b + 1) e with ⟨c, b'⟩
    rw [h] at Heroot Hel
    dsimp only at Heroot Hel ⊢
    apply child_kind_ok_node
    · intro k cp Hcp
      have Hcp' : [b + 1][k]? = some cp := Hcp
      cases k with
      | zero =>
        have H := Option.some.inj Hcp'
        subst H
        exact ⟨erc, List.Mem.tail _ (by rw [Heroot]; exact List.Mem.head _),
          (congrArg kind_of_view Heview).trans (expr_view_kind e)⟩
      | succ k' =>
        cases k' with
        | zero => exact nomatch Hcp'
        | succ _ => exact nomatch Hcp'
    · exact Hel
  | DeclarationStmt d =>
    unfold number_stmt
    dsimp only
    obtain ⟨dcell, drest, Hdf, _, Hdv⟩ := number_decl_view (some b) RPlain (b + 1) d
    have Hdl := number_decl_kind (some b) RPlain (b + 1) d
    rcases h : number_decl (some b) RPlain (b + 1) d with ⟨c, b'⟩
    rw [h] at Hdf Hdl
    dsimp only at Hdf Hdl ⊢
    apply child_kind_ok_node
    · intro k cp Hcp
      have Hcp' : [b + 1][k]? = some cp := Hcp
      cases k with
      | zero =>
        have H := Option.some.inj Hcp'
        subst H
        exact ⟨dcell, List.Mem.tail _ (by rw [Hdf]; exact List.Mem.head _), (congrArg kind_of_view Hdv).trans rfl⟩
      | succ k' =>
        cases k' with
        | zero => exact nomatch Hcp'
        | succ _ => exact nomatch Hcp'
    · exact Hdl
  | ShortVarDecl names vals =>
    unfold number_stmt
    dsimp only
    have Hnr := number_list_roots (number_bindingname (some b) RShortLhs)
      (fun cell => kind_of_view (c_view cell) = BindingNameKind)
      (fun bb x => number_bindingname_spans (some b) RShortLhs bb x)
      (root_kind_of_view BindingNameKind (number_bindingname_view (some b) RShortLhs) (fun _ => rfl))
      (Collections.ne_to_list names) (b + 1)
    have Hnl := number_list_kind (number_bindingname (some b) RShortLhs)
      (fun bb x => number_bindingname_kind (some b) RShortLhs bb x) (b + 1) (Collections.ne_to_list names)
    rcases h1 : number_list (number_bindingname (some b) RShortLhs) (b + 1) (Collections.ne_to_list names)
      with ⟨nc, b1, nroots⟩
    rw [h1] at Hnr Hnl
    dsimp only at Hnr Hnl ⊢
    obtain ⟨Hnlen, _, _, Hnnth⟩ := Hnr
    have Hvr := number_list_roots (number_expr (some b) RPlain)
      (fun cell => kind_of_view (c_view cell) = ExprKind)
      (fun bb x => number_expr_spans x (some b) RPlain bb) (expr_root_kind (some b) RPlain)
      (Collections.ne_to_list vals) b1
    have Hvl := number_list_kind (number_expr (some b) RPlain)
      (fun bb x => number_expr_kind x (some b) RPlain bb) b1 (Collections.ne_to_list vals)
    rcases h2 : number_list (number_expr (some b) RPlain) b1 (Collections.ne_to_list vals)
      with ⟨vc, b2, vroots⟩
    rw [h2] at Hvr Hvl
    dsimp only at Hvr Hvl ⊢
    obtain ⟨_, _, _, Hvnth⟩ := Hvr
    apply child_kind_ok_node
    · intro k cp Hcp
      have Hcp' : (nroots ++ vroots)[k]? = some cp := Hcp
      cases Nat.lt_or_ge k (List.length nroots) with
      | inl Hk =>
        rw [getElem?_app_left _ _ _ Hk] at Hcp'
        obtain ⟨cell, Hcell, Hkind⟩ := Hnnth k cp Hcp'
        exact ⟨cell, List.Mem.tail _ (List.mem_append_left _ Hcell),
          Hkind.trans (cond_decide_true _ (Nat.lt_of_lt_of_eq Hk Hnlen) _ _).symm⟩
      | inr Hk =>
        rw [getElem?_app_right _ _ _ Hk] at Hcp'
        obtain ⟨cell, Hcell, Hkind⟩ := Hvnth _ cp Hcp'
        exact ⟨cell, List.Mem.tail _ (List.mem_append_right _ Hcell),
          Hkind.trans (cond_decide_false _ (not_lt_of_len_le Hk Hnlen) _ _).symm⟩
    · exact child_kind_ok_app _ _ Hnl Hvl

theorem number_block_kind : ∀ par role b blk, child_kind_ok (number_block par role b blk).1 := by
  intro par role b ⟨stmts⟩
  unfold number_block
  dsimp only
  have Hr := number_list_roots (number_stmt (some b) RPlain)
    (fun cell => kind_of_view (c_view cell) = StmtKind)
    (fun bb x => number_stmt_span (some b) RPlain bb x)
    (root_kind_of_view StmtKind (number_stmt_view (some b) RPlain) (fun _ => rfl)) stmts (b + 1)
  have Hl := number_list_kind (number_stmt (some b) RPlain)
    (fun bb x => number_stmt_kind (some b) RPlain bb x) (b + 1) stmts
  rcases h : number_list (number_stmt (some b) RPlain) (b + 1) stmts with ⟨kc, bfin, roots⟩
  rw [h] at Hr Hl
  dsimp only at Hr Hl ⊢
  obtain ⟨_, _, _, Hnth⟩ := Hr
  apply child_kind_ok_node
  · intro k cp Hcp
    obtain ⟨cell, Hcell, Hkind⟩ := Hnth k cp Hcp
    exact ⟨cell, List.Mem.tail _ Hcell, Hkind⟩
  · exact Hl

theorem number_toplevel_kind : ∀ par role b td, child_kind_ok (number_toplevel par role b td).1 := by
  intro par role b td
  cases td with
  | TopDeclaration d =>
    unfold number_toplevel
    dsimp only
    obtain ⟨dcell, drest, Hdf, _, Hdv⟩ := number_decl_view (some b) RPlain (b + 1) d
    have Hdl := number_decl_kind (some b) RPlain (b + 1) d
    rcases h : number_decl (some b) RPlain (b + 1) d with ⟨c, b'⟩
    rw [h] at Hdf Hdl
    dsimp only at Hdf Hdl ⊢
    apply child_kind_ok_node
    · intro k cp Hcp
      have Hcp' : [b + 1][k]? = some cp := Hcp
      cases k with
      | zero =>
        have H := Option.some.inj Hcp'
        subst H
        exact ⟨dcell, List.Mem.tail _ (by rw [Hdf]; exact List.Mem.head _), (congrArg kind_of_view Hdv).trans rfl⟩
      | succ k' =>
        cases k' with
        | zero => exact nomatch Hcp'
        | succ _ => exact nomatch Hcp'
    · exact Hdl
  | Main blk =>
    unfold number_toplevel
    dsimp only
    obtain ⟨bcell, brest, Hbf, _, Hbv⟩ := number_block_view (some b) RPlain (b + 1) blk
    have Hbl := number_block_kind (some b) RPlain (b + 1) blk
    rcases h : number_block (some b) RPlain (b + 1) blk with ⟨c, b'⟩
    rw [h] at Hbf Hbl
    dsimp only at Hbf Hbl ⊢
    apply child_kind_ok_node
    · intro k cp Hcp
      have Hcp' : [b + 1][k]? = some cp := Hcp
      cases k with
      | zero =>
        have H := Option.some.inj Hcp'
        subst H
        exact ⟨bcell, List.Mem.tail _ (by rw [Hbf]; exact List.Mem.head _), (congrArg kind_of_view Hbv).trans rfl⟩
      | succ k' =>
        cases k' with
        | zero => exact nomatch Hcp'
        | succ _ => exact nomatch Hcp'
    · exact Hbl

theorem number_file_kind : ∀ f, child_kind_ok (number_file f) := by
  intro f
  unfold number_file
  have Hr := number_list_roots (number_toplevel (some 0) RPlain)
    (fun cell => kind_of_view (c_view cell) = TopKind)
    (fun bb x => number_toplevel_span (some 0) RPlain bb x)
    (root_kind_of_view TopKind (number_toplevel_view (some 0) RPlain) (fun _ => rfl)) (Syntax.declarations f) 1
  have Hl := number_list_kind (number_toplevel (some 0) RPlain)
    (fun bb x => number_toplevel_kind (some 0) RPlain bb x) 1 (Syntax.declarations f)
  rcases h : number_list (number_toplevel (some 0) RPlain) 1 (Syntax.declarations f) with ⟨dc, bfin, droots⟩
  rw [h] at Hr Hl
  dsimp only at Hr Hl ⊢
  obtain ⟨_, _, _, Hnth⟩ := Hr
  apply child_kind_ok_node
  · intro k cp Hcp
    obtain ⟨cell, Hcell, Hkind⟩ := Hnth k cp Hcp
    exact ⟨cell, List.Mem.tail _ Hcell, Hkind⟩
  · exact Hl

end Fido.Index.BuildLaws
