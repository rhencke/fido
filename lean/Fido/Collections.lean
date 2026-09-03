-- Port of Collections.v (lean/README.md).
import Std.Data.TreeMap
import Std.Data.TreeMap.Lemmas
import Fido.FilePath

/-! divergences:
  * Lean has no module functors.  `FMapAVL.Make X` / `FMapPositive.PositiveMap` and the `WFacts_fun` /
    `WProperties_fun` / `OrdProperties` instantiations are ONE generic body each (`FMap`, `WFacts`,
    `WProperties`, `OrdProperties`) over `Std.TreeMap key elt compare`, and `NodeMap`, `PackageMap`,
    `FileMap`, `PackageFacts`, `FileFacts`, … are namespaces that `export` exactly the names the theory
    consumes.  The `OrderedType` argument is the key's `Ord` instance with `TransOrd`/`LawfulEqOrd`
    (`FilePathOrder` supplies them for `FilePath.T`; `Nat` and `Str` have core's).
  * `MapsTo x e m` is `find x m = some e` (Rocq's is the abstract interface parameter, related to `find` by
    `find_mapsto_iff`, which is therefore `Iff.rfl` here); `Equal`/`In`/`Empty`/`Add` keep their definitions.
  * SetoidList predicates take their Leibniz rendering: `InA eq_key_elt (x, e) l` is `(x, e) ∈ l`,
    `NoDupA eq_key l` is `l.Pairwise (fun p q => ¬ eq_key p q)`, `equivlistA eq_key_elt l l'` is
    `∀ x, x ∈ l ↔ x ∈ l'`.  `Sorted`/`HdRel` (Sorting.Sorted) and `eqlistA` have no core counterpart and are
    ported as the stdlib inductives; `OrderedType.Compare` likewise (`FilePathOrder.compare` returns it).
  * `String_as_OT.lt a b` is `compare a b = .lt` — core's lexicographic `List.compareLex` on `Str` — rather
    than the stdlib `lts` inductive it decides; `{eq a b} + {~ eq a b}` is `Decidable (eq a b)`.
  * `NodeMap` keys are plain `Nat` (README: `positive` is `Nat`; the `0 < n` carrier is not part of the key
    type, so `0` is a key here where `PositiveMap` has none) ordered numerically, not by
    `PositiveOrderedTypeBits.lt`; `elements`/`fold`/`cardinal` therefore enumerate in numeric order (no
    consumer reads `NodeMap` order) and `NodeMap.E` exposes only `t`/`eq`/`eq_dec`, the part Index.v uses.
  * `S (cardinal m)` is `cardinal m + 1`.
  * CORE FINDING — every constant that touches a `Std.TreeMap` reaches `Classical.choice`, operations
    included (`Std.TreeMap.insert`/`empty`/`get?`/`toList`/… carry it: `Classical.propDecidable` inside the
    `_proof_n` auxiliaries of `Std.DTreeMap.Internal.Impl.insert`/`erase`/`link`/`balance` and
    `Classical.byContradiction` in `Impl.balance!_eq_balanceₘ`).  Core's `UInt8.instTransOrd`,
    `UInt8.instLawfulEqOrd`, `Nat.instTransOrd` and `Nat.instLawfulEqOrd` reach it too (a `Classical.not_not`
    `simp` artifact in `lt_iff_not_gt_and_ne_of_antisymm_of_total_of_not_le`), so the `FilePathOrder` order
    lemmas and instances, which rest on `Str`'s lexicographic order, inherit it as well.  No proof in this
    module can avoid either.  What stays constructive is exactly what never mentions a map operation:
    `HdRel`/`Sorted`/`eqlistA`/`OrderedType.Compare`, `String_as_OT.lt`, `eq_key`/`eq_key_elt`/`lt_key`,
    `OrdProperties.sort_equivlistA_eqlistA` (stated over instance variables), `NodeMap.E`,
    `FilePathOrder.eq*`/`eq_dec`/`instOrd`, `file_path_text_inj`, `equal_list_key_element_eq*`,
    `sorted_map_fst` and `NonEmpty`.
-/

namespace Fido.Collections
open Std (TransCmp LawfulEqCmp OrientedCmp ReflCmp TransOrd LawfulEqOrd OrientedOrd)

/-! ### Rocq stdlib notions the statements mention (`Sorting.Sorted`, `SetoidList`, `OrderedType`) -/

/-- `HdRel R a l`: `a` is `R`-below the head of `l`, if any. -/
inductive HdRel {A : Type} (R : A → A → Prop) (a : A) : List A → Prop
  | HdRel_nil : HdRel R a []
  | HdRel_cons (b : A) (l : List A) : R a b → HdRel R a (b :: l)

/-- Rocq's `Sorted` (locally sorted: each element is `R`-below its successor). -/
inductive Sorted {A : Type} (R : A → A → Prop) : List A → Prop
  | Sorted_nil : Sorted R []
  | Sorted_cons (a : A) (l : List A) : Sorted R l → HdRel R a l → Sorted R (a :: l)

/-- SetoidList `eqlistA`: pointwise `eqA`, same length. -/
inductive eqlistA {A : Type} (eqA : A → A → Prop) : List A → List A → Prop
  | eqlistA_nil : eqlistA eqA [] []
  | eqlistA_cons (x x' : A) (l l' : List A) : eqA x x' → eqlistA eqA l l' → eqlistA eqA (x :: l) (x' :: l')

namespace OrderedType
/-- `OrderedType.Compare lt eq x y`: the three-way comparison witness. -/
inductive Compare {A : Type} (lt eq : A → A → Prop) (x y : A) : Type
  | LT : lt x y → Compare lt eq x y
  | EQ : eq x y → Compare lt eq x y
  | GT : lt y x → Compare lt eq x y
end OrderedType

namespace String_as_OT
/-- `String_as_OT.lt`: strict lexicographic order on strings, as decided by core's `compare` on `Str`. -/
def lt (a b : Str) : Prop := compare a b = .lt
end String_as_OT

/-! ### `FMapInterface.Sfun` over `Std.TreeMap` — the body shared by every map instantiation -/

namespace FMap
variable {key : Type}

def eq_key {elt : Type} (p p' : key × elt) : Prop := p.1 = p'.1
def eq_key_elt {elt : Type} (p p' : key × elt) : Prop := p.1 = p'.1 ∧ p.2 = p'.2

-- `eqlistA eq_key_elt` is list equality: the one fact behind `equal_list_key_element_eq` and `…_str`
private theorem eqlistA_eq_key_elt_eq {elt : Type} :
    ∀ (l1 l2 : List (key × elt)), eqlistA eq_key_elt l1 l2 → l1 = l2 := by
  intro l1 l2 H
  induction H with
  | eqlistA_nil => rfl
  | eqlistA_cons x x' l l' Hxx' _ IH =>
    obtain ⟨k, e⟩ := x
    obtain ⟨k', e'⟩ := x'
    obtain ⟨Hk, He⟩ := Hxx'
    have Hk' : k = k' := Hk
    have He' : e = e' := He
    subst Hk' He'
    rw [IH]

variable [Ord key]

def empty (elt : Type) : Std.TreeMap key elt compare := ∅
def add {elt : Type} (x : key) (e : elt) (m : Std.TreeMap key elt compare) : Std.TreeMap key elt compare :=
  m.insert x e
def find {elt : Type} (x : key) (m : Std.TreeMap key elt compare) : Option elt := m[x]?
def remove {elt : Type} (x : key) (m : Std.TreeMap key elt compare) : Std.TreeMap key elt compare := m.erase x
def mem {elt : Type} (x : key) (m : Std.TreeMap key elt compare) : Bool := m.contains x
def map {elt elt' : Type} (f : elt → elt') (m : Std.TreeMap key elt compare) : Std.TreeMap key elt' compare :=
  Std.TreeMap.map (fun _ e => f e) m
def elements {elt : Type} (m : Std.TreeMap key elt compare) : List (key × elt) := m.toList
def cardinal {elt : Type} (m : Std.TreeMap key elt compare) : Nat := m.size
def fold {elt A : Type} (f : key → elt → A → A) (m : Std.TreeMap key elt compare) (i : A) : A :=
  m.foldl (fun a k e => f k e a) i

def MapsTo {elt : Type} (x : key) (e : elt) (m : Std.TreeMap key elt compare) : Prop := find x m = some e
def In {elt : Type} (x : key) (m : Std.TreeMap key elt compare) : Prop := ∃ e, MapsTo x e m
def Empty {elt : Type} (m : Std.TreeMap key elt compare) : Prop := ∀ a e, ¬ MapsTo a e m
def Equal {elt : Type} (m m' : Std.TreeMap key elt compare) : Prop := ∀ y, find y m = find y m'
def lt_key {elt : Type} (p p' : key × elt) : Prop := compare p.1 p'.1 = .lt

section laws
variable [TransOrd key] [LawfulEqOrd key] {elt : Type}
set_option linter.unusedSectionVars false

theorem cmp_eq_of_eq {x y : key} (H : x = y) : compare x y = .eq := H ▸ ReflCmp.compare_self
theorem eq_of_cmp_eq {x y : key} (H : compare x y = .eq) : x = y := LawfulEqCmp.eq_of_compare H
theorem ne_of_cmp_ne {x y : key} (H : compare x y ≠ .eq) : x ≠ y := fun Hxy => H (cmp_eq_of_eq Hxy)

theorem find_1 {m : Std.TreeMap key elt compare} {x : key} {e : elt} (H : MapsTo x e m) : find x m = some e := H
theorem find_2 {m : Std.TreeMap key elt compare} {x : key} {e : elt} (H : find x m = some e) : MapsTo x e m := H

theorem mem_1 {m : Std.TreeMap key elt compare} {x : key} : In x m → mem x m = true := by
  intro H
  obtain ⟨e, He⟩ := H
  have He' : m[x]? = some e := He
  unfold mem
  rw [Std.TreeMap.contains_eq_isSome_getElem?, He']
  rfl

theorem mem_2 {m : Std.TreeMap key elt compare} {x : key} : mem x m = true → In x m := by
  intro H
  unfold mem at H
  rw [Std.TreeMap.contains_eq_isSome_getElem?] at H
  cases h : m[x]? with
  | none => rw [h] at H; exact nomatch H
  | some e => exact ⟨e, h⟩

theorem empty_1 : Empty (empty elt : Std.TreeMap key elt compare) := by
  intro a e H
  have H' : (∅ : Std.TreeMap key elt compare)[a]? = some e := H
  rw [Std.TreeMap.getElem?_emptyc] at H'
  exact nomatch H'

theorem add_1 {m : Std.TreeMap key elt compare} {x y : key} {e : elt} : x = y → MapsTo y e (add x e m) := by
  intro H
  subst H
  show (m.insert x e)[x]? = some e
  exact Std.TreeMap.getElem?_insert_self

theorem add_2 {m : Std.TreeMap key elt compare} {x y : key} {e e' : elt} :
    x ≠ y → MapsTo y e m → MapsTo y e (add x e' m) := by
  intro Hne H
  show (m.insert x e')[y]? = some e
  rw [Std.TreeMap.getElem?_insert, if_neg (fun Hc => Hne (eq_of_cmp_eq Hc))]
  exact H

theorem add_3 {m : Std.TreeMap key elt compare} {x y : key} {e e' : elt} :
    x ≠ y → MapsTo y e (add x e' m) → MapsTo y e m := by
  intro Hne H
  have H' : (m.insert x e')[y]? = some e := H
  rw [Std.TreeMap.getElem?_insert, if_neg (fun Hc => Hne (eq_of_cmp_eq Hc))] at H'
  exact H'

theorem remove_1 {m : Std.TreeMap key elt compare} {x y : key} : x = y → ¬ In y (remove x m) := by
  intro H Hin
  subst H
  obtain ⟨e, He⟩ := Hin
  have He' : (m.erase x)[x]? = some e := He
  rw [Std.TreeMap.getElem?_erase, if_pos ReflCmp.compare_self] at He'
  exact nomatch He'

theorem remove_2 {m : Std.TreeMap key elt compare} {x y : key} {e : elt} :
    x ≠ y → MapsTo y e m → MapsTo y e (remove x m) := by
  intro Hne H
  show (m.erase x)[y]? = some e
  rw [Std.TreeMap.getElem?_erase, if_neg (fun Hc => Hne (eq_of_cmp_eq Hc))]
  exact H

theorem remove_3 {m : Std.TreeMap key elt compare} {x y : key} {e : elt} :
    MapsTo y e (remove x m) → MapsTo y e m := by
  intro H
  have H' : (m.erase x)[y]? = some e := H
  rw [Std.TreeMap.getElem?_erase] at H'
  cases Hc : compare x y with
  | lt => rw [Hc, if_neg nofun] at H'; exact H'
  | eq => rw [Hc, if_pos rfl] at H'; exact nomatch H'
  | gt => rw [Hc, if_neg nofun] at H'; exact H'

theorem elements_1 {m : Std.TreeMap key elt compare} {x : key} {e : elt} :
    MapsTo x e m → (x, e) ∈ elements m :=
  fun H => Std.TreeMap.mem_toList_iff_getElem?_eq_some.2 H

theorem elements_2 {m : Std.TreeMap key elt compare} {x : key} {e : elt} :
    (x, e) ∈ elements m → MapsTo x e m :=
  fun H => Std.TreeMap.mem_toList_iff_getElem?_eq_some.1 H

/-- Rocq: `NoDupA eq_key (elements m)` — no two bindings share a key. -/
theorem elements_3w (m : Std.TreeMap key elt compare) :
    (elements m).Pairwise (fun p p' => ¬ eq_key p p') :=
  Std.TreeMap.distinct_keys_toList.imp (fun H Hk => H (cmp_eq_of_eq Hk))

private theorem sorted_of_pairwise {A : Type} {R : A → A → Prop} : ∀ {l : List A}, List.Pairwise R l → Sorted R l := by
  intro l H
  induction H with
  | nil => exact Sorted.Sorted_nil
  | @cons a l H1 _ IH =>
    refine Sorted.Sorted_cons a l IH ?_
    cases l with
    | nil => exact HdRel.HdRel_nil
    | cons b l' => exact HdRel.HdRel_cons b l' (H1 b (List.Mem.head _))

theorem elements_3 (m : Std.TreeMap key elt compare) : Sorted lt_key (elements m) :=
  sorted_of_pairwise Std.TreeMap.ordered_keys_toList

theorem cardinal_1 (m : Std.TreeMap key elt compare) : cardinal m = (elements m).length :=
  Std.TreeMap.length_toList.symm

theorem fold_1 {A : Type} (m : Std.TreeMap key elt compare) (i : A) (f : key → elt → A → A) :
    fold f m i = List.foldl (fun a p => f p.1 p.2 a) i (elements m) :=
  Std.TreeMap.foldl_eq_foldl_toList

theorem map_1 {elt' : Type} {m : Std.TreeMap key elt compare} {x : key} {e : elt} (f : elt → elt') :
    MapsTo x e m → MapsTo x (f e) (map f m) := by
  intro H
  have H' : m[x]? = some e := H
  show (Std.TreeMap.map (fun _ e => f e) m)[x]? = some (f e)
  rw [Std.TreeMap.getElem?_map, H']
  rfl

theorem map_2 {elt' : Type} {m : Std.TreeMap key elt compare} {x : key} {f : elt → elt'} :
    In x (map f m) → In x m := by
  intro H
  obtain ⟨e', He'⟩ := H
  have H' : (Std.TreeMap.map (fun _ e => f e) m)[x]? = some e' := He'
  rw [Std.TreeMap.getElem?_map] at H'
  cases h : m[x]? with
  | none => rw [h] at H'; exact nomatch H'
  | some a => exact ⟨a, h⟩

end laws
end FMap

/-! ### `FMapFacts.OrdProperties` -/

namespace OrdProperties
open FMap
variable {key : Type} [Ord key] [TransOrd key] [LawfulEqOrd key] {elt : Type}
set_option linter.unusedSectionVars false

private theorem pairwise_of_sorted : ∀ {l : List (key × elt)}, Sorted lt_key l → List.Pairwise lt_key l := by
  intro l H
  induction H with
  | Sorted_nil => exact List.Pairwise.nil
  | Sorted_cons a l _ Hhd IH =>
    refine List.Pairwise.cons ?_ IH
    intro b Hb
    cases Hhd with
    | HdRel_nil => exact nomatch Hb
    | HdRel_cons b0 l'' Hab0 =>
      cases Hb with
      | head => exact Hab0
      | tail _ Hb' => exact TransCmp.lt_trans Hab0 (List.rel_of_pairwise_cons IH Hb')

private theorem lt_key_irrefl (p : key × elt) : ¬ lt_key p p :=
  fun H => nomatch (ReflCmp.compare_self (cmp := (compare : key → key → Ordering)) (a := p.1)).symm.trans H

private theorem sorted_tail {A : Type} {R : A → A → Prop} {a : A} {l : List A} : Sorted R (a :: l) → Sorted R l := by
  intro H
  cases H with
  | Sorted_cons _ _ Hs _ => exact Hs

/-- Two sorted, key-distinct enumerations of the same bindings are pointwise equal. -/
theorem sort_equivlistA_eqlistA : ∀ (l l' : List (key × elt)),
    Sorted lt_key l → Sorted lt_key l' → (∀ x, x ∈ l ↔ x ∈ l') → eqlistA eq_key_elt l l' := by
  intro l
  induction l with
  | nil =>
    intro l' _ _ Hequiv
    cases l' with
    | nil => exact eqlistA.eqlistA_nil
    | cons y l' => exact absurd ((Hequiv y).2 (List.Mem.head _)) nofun
  | cons x l IH =>
    intro l' Hs Hs' Hequiv
    cases l' with
    | nil => exact absurd ((Hequiv x).1 (List.Mem.head _)) nofun
    | cons y l' =>
      have Hp := pairwise_of_sorted Hs
      have Hp' := pairwise_of_sorted Hs'
      have Hxy : x = y := by
        have Hx : x ∈ y :: l' := (Hequiv x).1 (List.Mem.head _)
        have Hy : y ∈ x :: l := (Hequiv y).2 (List.Mem.head _)
        cases Hx with
        | head => rfl
        | tail _ Hx' =>
          cases Hy with
          | head => rfl
          | tail _ Hy' =>
            exact absurd (TransCmp.lt_trans (List.rel_of_pairwise_cons Hp' Hx') (List.rel_of_pairwise_cons Hp Hy'))
              (lt_key_irrefl y)
      subst Hxy
      refine eqlistA.eqlistA_cons x x l l' ⟨rfl, rfl⟩ (IH l' (sorted_tail Hs) (sorted_tail Hs') ?_)
      intro z
      constructor
      · intro Hz
        have Hz' : z ∈ x :: l' := (Hequiv z).1 (List.Mem.tail _ Hz)
        cases Hz' with
        | head => exact absurd (List.rel_of_pairwise_cons Hp Hz) (lt_key_irrefl x)
        | tail _ H => exact H
      · intro Hz
        have Hz' : z ∈ x :: l := (Hequiv z).2 (List.Mem.tail _ Hz)
        cases Hz' with
        | head => exact absurd (List.rel_of_pairwise_cons Hp' Hz) (lt_key_irrefl x)
        | tail _ H => exact H

end OrdProperties

/-! ### `FMapFacts.WFacts_fun` -/

namespace WFacts
open FMap
variable {key : Type} [Ord key] [TransOrd key] [LawfulEqOrd key] {elt : Type}
set_option linter.unusedSectionVars false

theorem find_mapsto_iff : ∀ (m : Std.TreeMap key elt compare) (x : key) (e : elt),
    MapsTo x e m ↔ find x m = some e := fun _ _ _ => Iff.rfl

theorem elements_mapsto_iff : ∀ (m : Std.TreeMap key elt compare) (x : key) (e : elt),
    MapsTo x e m ↔ (x, e) ∈ elements m := fun _ _ _ => ⟨elements_1, elements_2⟩

theorem mem_in_iff : ∀ (m : Std.TreeMap key elt compare) (x : key), In x m ↔ mem x m = true :=
  fun _ _ => ⟨mem_1, mem_2⟩

theorem in_find_iff : ∀ (m : Std.TreeMap key elt compare) (x : key), In x m ↔ find x m ≠ none := by
  intro m x
  constructor
  · intro H Hn
    obtain ⟨e, He⟩ := H
    have He' : find x m = some e := He
    rw [He'] at Hn
    exact nomatch Hn
  · intro H
    cases Hf : find x m with
    | none => exact absurd Hf H
    | some e => exact ⟨e, Hf⟩

theorem empty_o : ∀ (x : key), find x (empty elt) = none := fun _ => Std.TreeMap.getElem?_emptyc

theorem add_o [DecidableEq key] : ∀ (m : Std.TreeMap key elt compare) (x y : key) (e : elt),
    find y (add x e m) = if x = y then some e else find y m := by
  intro m x y e
  show (m.insert x e)[y]? = if x = y then some e else m[y]?
  rw [Std.TreeMap.getElem?_insert]
  obtain H | H := Decidable.em (x = y)
  · rw [if_pos (cmp_eq_of_eq H), if_pos H]
  · rw [if_neg (fun Hc => H (eq_of_cmp_eq Hc)), if_neg H]

theorem add_eq_o : ∀ (m : Std.TreeMap key elt compare) (x y : key) (e : elt),
    x = y → find y (add x e m) = some e :=
  fun _ _ _ _ H => add_1 H

theorem add_neq_o : ∀ (m : Std.TreeMap key elt compare) (x y : key) (e : elt),
    x ≠ y → find y (add x e m) = find y m := by
  intro m x y e Hne
  show (m.insert x e)[y]? = m[y]?
  rw [Std.TreeMap.getElem?_insert, if_neg (fun Hc => Hne (eq_of_cmp_eq Hc))]

theorem add_in_iff : ∀ (m : Std.TreeMap key elt compare) (x y : key) (e : elt),
    In y (add x e m) ↔ x = y ∨ In y m := by
  intro m x y e
  constructor
  · intro H
    obtain ⟨e', He'⟩ := H
    have H' : (m.insert x e)[y]? = some e' := He'
    rw [Std.TreeMap.getElem?_insert] at H'
    cases Hc : compare x y with
    | lt => rw [Hc, if_neg nofun] at H'; exact Or.inr ⟨e', H'⟩
    | eq => exact Or.inl (eq_of_cmp_eq Hc)
    | gt => rw [Hc, if_neg nofun] at H'; exact Or.inr ⟨e', H'⟩
  · intro H
    cases H with
    | inl H => exact ⟨e, add_1 H⟩
    | inr H =>
      obtain ⟨e', He'⟩ := H
      cases Hc : compare x y with
      | lt => exact ⟨e', add_2 (ne_of_cmp_ne (by rw [Hc]; exact nofun)) He'⟩
      | eq => exact ⟨e, add_1 (eq_of_cmp_eq Hc)⟩
      | gt => exact ⟨e', add_2 (ne_of_cmp_ne (by rw [Hc]; exact nofun)) He'⟩

theorem add_mapsto_iff : ∀ (m : Std.TreeMap key elt compare) (x y : key) (e e' : elt),
    MapsTo y e' (add x e m) ↔ (x = y ∧ e = e') ∨ (x ≠ y ∧ MapsTo y e' m) := by
  intro m x y e e'
  constructor
  · intro H
    have H' : (m.insert x e)[y]? = some e' := H
    rw [Std.TreeMap.getElem?_insert] at H'
    cases Hc : compare x y with
    | lt => rw [Hc, if_neg nofun] at H'; exact Or.inr ⟨ne_of_cmp_ne (by rw [Hc]; exact nofun), H'⟩
    | eq => rw [Hc, if_pos rfl] at H'; exact Or.inl ⟨eq_of_cmp_eq Hc, Option.some.inj H'⟩
    | gt => rw [Hc, if_neg nofun] at H'; exact Or.inr ⟨ne_of_cmp_ne (by rw [Hc]; exact nofun), H'⟩
  · intro H
    cases H with
    | inl H => obtain ⟨Hxy, Hee⟩ := H; subst Hee; exact add_1 Hxy
    | inr H => obtain ⟨Hne, H⟩ := H; exact add_2 Hne H

theorem remove_o [DecidableEq key] : ∀ (m : Std.TreeMap key elt compare) (x y : key),
    find y (remove x m) = if x = y then none else find y m := by
  intro m x y
  show (m.erase x)[y]? = if x = y then none else m[y]?
  rw [Std.TreeMap.getElem?_erase]
  obtain H | H := Decidable.em (x = y)
  · rw [if_pos (cmp_eq_of_eq H), if_pos H]
  · rw [if_neg (fun Hc => H (eq_of_cmp_eq Hc)), if_neg H]

theorem remove_eq_o : ∀ (m : Std.TreeMap key elt compare) (x y : key),
    x = y → find y (remove x m) = none := by
  intro m x y H
  subst H
  show (m.erase x)[x]? = none
  rw [Std.TreeMap.getElem?_erase, if_pos ReflCmp.compare_self]

theorem remove_neq_o : ∀ (m : Std.TreeMap key elt compare) (x y : key),
    x ≠ y → find y (remove x m) = find y m := by
  intro m x y Hne
  show (m.erase x)[y]? = m[y]?
  rw [Std.TreeMap.getElem?_erase, if_neg (fun Hc => Hne (eq_of_cmp_eq Hc))]

theorem map_o {elt' : Type} : ∀ (m : Std.TreeMap key elt compare) (x : key) (f : elt → elt'),
    find x (map f m) = Option.map f (find x m) :=
  fun _ _ _ => Std.TreeMap.getElem?_map

theorem map_mapsto_iff {elt' : Type} : ∀ (m : Std.TreeMap key elt compare) (x : key) (b : elt') (f : elt → elt'),
    MapsTo x b (map f m) ↔ ∃ a, b = f a ∧ MapsTo x a m := by
  intro m x b f
  show (Std.TreeMap.map (fun _ e => f e) m)[x]? = some b ↔ ∃ a, b = f a ∧ m[x]? = some a
  rw [Std.TreeMap.getElem?_map]
  cases m[x]? with
  | none =>
    constructor
    · intro H; exact nomatch H
    · intro H; obtain ⟨_, _, H⟩ := H; exact nomatch H
  | some a =>
    constructor
    · intro H; exact ⟨a, (Option.some.inj H).symm, rfl⟩
    · intro H
      obtain ⟨a', Hb, Ha⟩ := H
      have Ha' : a = a' := Option.some.inj Ha
      subst Ha'
      rw [Hb]
      rfl

end WFacts

/-! ### `FMapFacts.WProperties_fun` -/

namespace WProperties
open FMap
variable {key : Type} [Ord key] [TransOrd key] [LawfulEqOrd key] {elt : Type}
set_option linter.unusedSectionVars false

def Add (x : key) (e : elt) (m m' : Std.TreeMap key elt compare) : Prop := ∀ y, find y m' = find y (add x e m)

-- `Equal` maps enumerate identically: the one fact behind `cardinal_2` and every `*_elements_equal`
private theorem elements_Equal (m1 m2 : Std.TreeMap key elt compare) :
    Equal m1 m2 → elements m1 = elements m2 := by
  intro Heq
  apply FMap.eqlistA_eq_key_elt_eq
  apply OrdProperties.sort_equivlistA_eqlistA _ _ (elements_3 m1) (elements_3 m2)
  intro p
  obtain ⟨k, e⟩ := p
  constructor
  · intro H
    exact elements_1 (show find k m2 = some e by rw [← Heq k]; exact elements_2 H)
  · intro H
    exact elements_1 (show find k m1 = some e by rw [Heq k]; exact elements_2 H)

theorem cardinal_2 : ∀ (m m' : Std.TreeMap key elt compare) (x : key) (e : elt),
    ¬ In x m → Add x e m m' → cardinal m' = cardinal m + 1 := by
  intro m m' x e Hni Hadd
  rw [cardinal_1, elements_Equal m' (add x e m) Hadd, ← cardinal_1]
  show (m.insert x e).size = m.size + 1
  rw [Std.TreeMap.size_insert, if_neg]
  intro Hc
  exact Hni (mem_2 Hc)

end WProperties

/-! ### `Module NodeMap := FMapPositive.PositiveMap.` -/

namespace NodeMap
abbrev key : Type := Nat
abbrev t (A : Type) : Type := Std.TreeMap Nat A compare

namespace E
abbrev t : Type := Nat
def eq (a b : t) : Prop := a = b
def eq_dec (a b : t) : Decidable (eq a b) := decEq a b
end E

export FMap (empty add find remove mem map elements cardinal fold MapsTo In Empty Equal eq_key eq_key_elt lt_key
  find_1 find_2 mem_1 mem_2 empty_1 add_1 add_2 add_3 remove_1 remove_2 remove_3 elements_1 elements_2
  elements_3w elements_3 cardinal_1 fold_1 map_1 map_2)

theorem gss {A : Type} (i : Nat) (x : A) (m : t A) : find i (add i x m) = some x :=
  WFacts.add_eq_o m i i x rfl

theorem gso {A : Type} (i j : Nat) (x : A) (m : t A) : i ≠ j → find i (add j x m) = find i m :=
  fun H => WFacts.add_neq_o m j i x (Ne.symm H)
end NodeMap

/-! ### `Module PackageMap := FMapAVL.Make String_as_OT.` and its Facts/Properties -/

namespace PackageMap
abbrev key : Type := Str
abbrev t (A : Type) : Type := Std.TreeMap Str A compare
export FMap (empty add find remove mem map elements cardinal fold MapsTo In Empty Equal eq_key eq_key_elt lt_key
  find_1 find_2 mem_1 mem_2 empty_1 add_1 add_2 add_3 remove_1 remove_2 remove_3 elements_1 elements_2
  elements_3w elements_3 cardinal_1 fold_1 map_1 map_2)
end PackageMap

namespace PackageFacts
export WFacts (find_mapsto_iff elements_mapsto_iff mem_in_iff in_find_iff empty_o add_o add_eq_o add_neq_o
  add_in_iff add_mapsto_iff remove_o remove_eq_o remove_neq_o map_o map_mapsto_iff)
end PackageFacts

namespace PackageProperties
export WProperties (Add cardinal_2)
end PackageProperties

/-- Path equality is Leibniz, so a `FilePath.T` map key behaves as an identity rather than a setoid class. -/
theorem file_path_text_inj : ∀ a b : FilePath.T, FilePath.T.text a = FilePath.T.text b → a = b := by
  intro a b H
  apply (FilePath.equalb_spec a b).1
  unfold FilePath.equalb
  rw [H]
  exact decide_eq_true rfl

/-! ### `Module FilePathOrder <: OrderedType.OrderedType.` -/

namespace FilePathOrder
abbrev t : Type := FilePath.T
def eq (a b : t) : Prop := a = b
def lt (a b : t) : Prop := String_as_OT.lt (FilePath.T.text a) (FilePath.T.text b)

theorem eq_refl : ∀ x, eq x x := fun _ => rfl
theorem eq_sym : ∀ x y, eq x y → eq y x := by
  intro x y H
  unfold eq at *
  exact H.symm
theorem eq_trans : ∀ x y z, eq x y → eq y z → eq x z := by
  intro x y z Hxy Hyz
  unfold eq at *
  rw [Hxy]
  exact Hyz
theorem lt_trans : ∀ x y z, lt x y → lt y z → lt x z := by
  intro x y z Hxy Hyz
  unfold lt String_as_OT.lt at *
  exact TransCmp.lt_trans Hxy Hyz
theorem lt_not_eq : ∀ x y, lt x y → ¬ eq x y := by
  intro x y H Hxy
  unfold eq at Hxy
  subst Hxy
  unfold lt String_as_OT.lt at H
  exact nomatch (ReflCmp.compare_self (cmp := (compare : Str → Str → Ordering)) (a := FilePath.T.text x)).symm.trans H

def compare (a b : t) : OrderedType.Compare lt eq a b :=
  match H : Ord.compare (FilePath.T.text a) (FilePath.T.text b) with
  | .lt => .LT H
  | .eq => .EQ (file_path_text_inj a b (LawfulEqCmp.eq_of_compare H))
  | .gt => .GT (OrientedCmp.lt_of_gt H)

def eq_dec (a b : t) : Decidable (eq a b) :=
  match E : FilePath.equalb a b with
  | true => isTrue ((FilePath.equalb_spec a b).1 E)
  | false => isFalse (fun H => by rw [(FilePath.equalb_spec a b).2 H] at E; exact nomatch E)

-- the `OrderedType` structure, as the `Ord`-family instances `Std.TreeMap` reads it through
instance instOrd : Ord FilePath.T := ⟨fun a b => Ord.compare (FilePath.T.text a) (FilePath.T.text b)⟩
instance instDecidableEq : DecidableEq FilePath.T := eq_dec
instance instOrientedOrd : OrientedOrd FilePath.T :=
  ⟨fun {a b} => OrientedCmp.eq_swap (cmp := (Ord.compare : Str → Str → Ordering)) (a := FilePath.T.text a) (b := FilePath.T.text b)⟩
instance instTransOrd : TransOrd FilePath.T :=
  ⟨fun {a b c} H1 H2 => TransCmp.isLE_trans (cmp := (Ord.compare : Str → Str → Ordering))
    (a := FilePath.T.text a) (b := FilePath.T.text b) (c := FilePath.T.text c) H1 H2⟩
instance instReflCmp : ReflCmp (Ord.compare : FilePath.T → FilePath.T → Ordering) :=
  ⟨fun {a} => ReflCmp.compare_self (cmp := (Ord.compare : Str → Str → Ordering)) (a := FilePath.T.text a)⟩
instance instLawfulEqOrd : LawfulEqOrd FilePath.T :=
  ⟨fun {a b} H => file_path_text_inj a b (LawfulEqCmp.eq_of_compare H)⟩
end FilePathOrder

/-! ### `Module FileMap := FMapAVL.Make FilePathOrder.` and its Facts/Properties/OrdProperties -/

namespace FileMap
abbrev key : Type := FilePath.T
abbrev t (A : Type) : Type := Std.TreeMap FilePath.T A compare
export FMap (empty add find remove mem map elements cardinal fold MapsTo In Empty Equal eq_key eq_key_elt lt_key
  find_1 find_2 mem_1 mem_2 empty_1 add_1 add_2 add_3 remove_1 remove_2 remove_3 elements_1 elements_2
  elements_3w elements_3 cardinal_1 fold_1 map_1 map_2)
end FileMap

namespace FileFacts
export WFacts (find_mapsto_iff elements_mapsto_iff mem_in_iff in_find_iff empty_o add_o add_eq_o add_neq_o
  add_in_iff add_mapsto_iff remove_o remove_eq_o remove_neq_o map_o map_mapsto_iff)
end FileFacts

namespace FileProperties
export WProperties (Add cardinal_2)
end FileProperties

namespace FileOrder
export OrdProperties (sort_equivlistA_eqlistA)
end FileOrder

/-- `elements` is sorted by key, so equal maps enumerate identically — a function of meaning, not of balancing. -/
theorem equal_list_key_element_eq {A : Type} : ∀ (l1 l2 : List (FilePath.T × A)),
    eqlistA FileMap.eq_key_elt l1 l2 → l1 = l2 :=
  FMap.eqlistA_eq_key_elt_eq

theorem file_elements_equal {A : Type} : ∀ (m1 m2 : FileMap.t A),
    FileMap.Equal m1 m2 → FileMap.elements m1 = FileMap.elements m2 :=
  WProperties.elements_Equal

/-- `elements` has key-distinct bindings (`elements_3w`), so its projected key list is `Nodup`. -/
theorem file_map_elements_keys_nodup {A : Type} (m : FileMap.t A) :
    List.Nodup (List.map Prod.fst (FileMap.elements m)) := by
  unfold List.Nodup
  exact List.pairwise_map.2 ((FileMap.elements_3w m).imp (fun H => H))

namespace PackageOrder
export OrdProperties (sort_equivlistA_eqlistA)
end PackageOrder

theorem equal_list_key_element_eq_str {A : Type} : ∀ (l1 l2 : List (Str × A)),
    eqlistA PackageMap.eq_key_elt l1 l2 → l1 = l2 :=
  FMap.eqlistA_eq_key_elt_eq

theorem package_elements_equal {A : Type} : ∀ (m1 m2 : PackageMap.t A),
    PackageMap.Equal m1 m2 → PackageMap.elements m1 = PackageMap.elements m2 :=
  WProperties.elements_Equal

theorem sorted_map_fst {A B : Type} (f : A → B) : ∀ (l : List (Str × A)),
    Sorted PackageMap.lt_key l →
    Sorted PackageMap.lt_key (List.map (fun kv => (kv.1, f kv.2)) l) := by
  intro l Hs
  induction l with
  | nil => exact Sorted.Sorted_nil
  | cons a l IH =>
    cases Hs with
    | Sorted_cons _ _ Hs Hhd =>
      refine Sorted.Sorted_cons _ _ (IH Hs) ?_
      cases Hhd with
      | HdRel_nil => exact HdRel.HdRel_nil
      | HdRel_cons b l' Hab => exact HdRel.HdRel_cons _ _ Hab

theorem package_map_elements {A B : Type} (f : A → B) : ∀ (m : PackageMap.t A),
    PackageMap.elements (PackageMap.map f m)
    = List.map (fun kv => (kv.1, f kv.2)) (PackageMap.elements m) :=
  fun _ => Std.TreeMap.toList_map

theorem package_map_fst_elements {A B : Type} (f : A → B) (m : PackageMap.t A) :
    List.map Prod.fst (PackageMap.elements (PackageMap.map f m)) = List.map Prod.fst (PackageMap.elements m) := by
  rw [package_map_elements, List.map_map]
  rfl

theorem package_same_domain_keys {A B : Type} (m1 : PackageMap.t A) (m2 : PackageMap.t B) :
    (∀ k, PackageMap.In k m1 ↔ PackageMap.In k m2) →
    List.map Prod.fst (PackageMap.elements m1) = List.map Prod.fst (PackageMap.elements m2) := by
  intro Hdom
  rw [← package_map_fst_elements (fun _ => ()) m1, ← package_map_fst_elements (fun _ => ()) m2]
  apply congrArg
  apply package_elements_equal
  intro k
  rw [PackageFacts.map_o, PackageFacts.map_o]
  cases E1 : PackageMap.find k m1 with
  | some a =>
    cases E2 : PackageMap.find k m2 with
    | some b => rfl
    | none => exact absurd E2 ((PackageFacts.in_find_iff m2 k).1 ((Hdom k).1 ⟨a, E1⟩))
  | none =>
    cases E2 : PackageMap.find k m2 with
    | some b => exact absurd E1 ((PackageFacts.in_find_iff m1 k).1 ((Hdom k).2 ⟨b, E2⟩))
    | none => rfl

-- `genInjectivity false`: Rocq's `Record` generates no injectivity theorem, and the auto-generated `injEq`
-- would be the module's one `propext` use outside the map library.
set_option genInjectivity false in
/-- A thin one-or-more refinement of `list`: exactly the source positions the Go grammar requires nonempty. -/
structure NonEmpty (A : Type) : Type where
  MakeNonEmpty ::
  ne_first : A
  ne_rest : List A

open NonEmpty

def ne_to_list {A : Type} (ne : NonEmpty A) : List A := ne_first ne :: ne_rest ne
def ne_length {A : Type} (ne : NonEmpty A) : Nat := (ne_rest ne).length + 1
def ne_map {A B : Type} (f : A → B) (ne : NonEmpty A) : NonEmpty B :=
  MakeNonEmpty (f (ne_first ne)) (List.map f (ne_rest ne))

theorem ne_to_list_not_nil {A : Type} (ne : NonEmpty A) : ne_to_list ne ≠ [] := nofun
theorem ne_to_list_length {A : Type} (ne : NonEmpty A) : (ne_to_list ne).length = ne_length ne := rfl
theorem ne_map_to_list {A B : Type} (f : A → B) (ne : NonEmpty A) :
    ne_to_list (ne_map f ne) = List.map f (ne_to_list ne) := rfl

end Fido.Collections
