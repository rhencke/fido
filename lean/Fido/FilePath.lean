-- Port of FilePath.v (lean/README.md).
import Fido.Prelude

/-! divergences:
  * `ascii` is `Char` (README): `nat_of_ascii` is `Char.toNat`, whose range is the Unicode scalars, not
    `< 256`.  No proof here relies on the 8-bit bound — `is_lower`/`is_lower_digit` bound the code by the
    alphabet ranges and the slash lemmas evaluate `'/'` — so no bound is added anywhere.
  * The stdlib boolean tests are the mapped types' decision procedures: `String.eqb`/`Ascii.eqb` are
    `decide (_ = _)` on `Str`/`Char`, `Nat.leb` is `decide (_ ≤ _)`; `forallb`/`In`/`rev`/`String.length`
    are `List.all`/`∈`/`List.reverse`/`List.length`.
  * `String.substring` and `String.concat` have no core counterpart with the same recursion (`List.intercalate`
    recurses differently, so `concat_cons_empty`/`concat_map_head` would not be `rfl`): the two stdlib
    `Fixpoint`s are ported verbatim as `substring`/`concat`, same equations, same right-nested `++`.
  * `{a = b} + {a <> b}` is `Decidable (a = b)`: `pkgdir_eq_dec` matches on `decEq` over `List Str`
    (Rocq's `list_eq_dec string_dec`).
  * `UIP_dec Bool.bool_dec` is definitional proof irrelevance (`path_ok_pi`/`pkg_valid_pi` are `rfl`).
  * Rocq's named `Example`s are `theorem`s (a Lean `example` is anonymous).
-/

namespace Fido.FilePath

def is_lower (c : Char) : Bool :=
  let n := c.toNat
  decide (97 ≤ n) && decide (n ≤ 122)

def is_lower_digit (c : Char) : Bool :=
  let n := c.toNat
  (decide (97 ≤ n) && decide (n ≤ 122)) || (decide (48 ≤ n) && decide (n ≤ 57))

def tail_ok : Str → Bool
  | [] => true
  | c :: s' => is_lower_digit c && tail_ok s'

def component_ok (s : Str) : Bool :=
  match s with
  | [] => false
  | c :: s' => is_lower c && tail_ok s'

/-- A file beneath one of these directories would be certified and never built by `go build ./...`. -/
def reserved_dir (s : Str) : Bool := decide (s = str! "testdata") || decide (s = str! "vendor")

def dir_component_ok (s : Str) : Bool := component_ok s && !(reserved_dir s)

def split_slash : Str → List Str
  | [] => [[]]
  | c :: s' =>
      if c = '/' then [] :: split_slash s'
      else match split_slash s' with
           | h :: t => (c :: h) :: t
           | [] => [[c]]         -- unreachable: split_slash never returns []

/-- Rocq stdlib `String.substring`, verbatim: the `m` characters from position `n`, clipped to the string. -/
def substring : Nat → Nat → Str → Str
  | 0, 0, _ => []
  | 0, _ + 1, [] => []
  | 0, m + 1, c :: s' => c :: substring 0 m s'
  | _ + 1, _, [] => []
  | n + 1, m, _ :: s' => substring n m s'

/-- Rocq stdlib `String.concat`, verbatim (`x ++ sep ++ rest` is right-nested there). -/
def concat (sep : Str) : List Str → Str
  | [] => []
  | [x] => x
  | x :: y :: rest => x ++ (sep ++ concat sep (y :: rest))

def ends_go (s : Str) : Bool :=
  let n := s.length
  decide (3 ≤ n) && decide (substring (n - 3) 3 s = str! ".go")

def strip_go (s : Str) : Str := substring 0 (s.length - 3) s

def filename_ok (s : Str) : Bool := ends_go s && component_ok (strip_go s)

def path_ok (s : Str) : Bool :=
  match (split_slash s).reverse with
  | last :: rdirs => rdirs.all dir_component_ok && filename_ok last
  | [] => false

-- `genInjectivity false`: the auto-generated `injEq` would be the one `propext` use in the module, and
-- Rocq's `Record` generates no such theorem.
set_option genInjectivity false in
structure T : Type where
  Make ::
  text : Str
  valid : path_ok text = true

open T

/-- Validity proofs are unique (bool UIP), so equality reduces to the underlying string. -/
theorem path_ok_pi : ∀ s (p q : path_ok s = true), p = q := fun _ _ _ => rfl

theorem equal : ∀ a b, text a = text b → a = b := by
  intro ⟨sa, _⟩ ⟨sb, _⟩ H
  have H' : sa = sb := H
  subst H'
  rfl

def equalb (a b : T) : Bool := decide (text a = text b)

theorem equalb_spec : ∀ a b, equalb a b = true ↔ a = b := by
  intro a b
  constructor
  · intro H; exact equal a b (of_decide_eq_true H)
  · intro H; subst H; exact decide_eq_true rfl

def parent_of (s : Str) : Str :=
  match (split_slash s).reverse with
  | _ :: rdirs => concat (str! "/") rdirs.reverse
  | [] => []

/-- The parent directory of a file: files sharing one parent form one package. -/
def parent (p : T) : Str := parent_of (text p)

theorem split_slash_nonempty : ∀ s, split_slash s ≠ [] := by
  intro s
  cases s with
  | nil => exact nofun
  | cons c s' =>
    rw [split_slash]
    obtain E | E := Decidable.em (c = '/')
    · rw [if_pos E]; exact nofun
    · rw [if_neg E]
      cases split_slash s' with
      | nil => exact nofun
      | cons h t => exact nofun

theorem split_slash_app : ∀ a b,
    split_slash (a ++ '/' :: b) = split_slash a ++ split_slash b := by
  intro a b
  induction a with
  | nil =>
    show split_slash ('/' :: b) = [[]] ++ split_slash b
    rw [split_slash, if_pos rfl]
    rfl
  | cons c a' IH =>
    show split_slash (c :: (a' ++ '/' :: b)) = split_slash (c :: a') ++ split_slash b
    rw [split_slash, split_slash, IH]
    obtain E | E := Decidable.em (c = '/')
    · rw [if_pos E, if_pos E]
      rfl
    · rw [if_neg E, if_neg E]
      cases Ea : split_slash a' with
      | nil => exact absurd Ea (split_slash_nonempty a')
      | cons ha ta => rfl

theorem concat_cons_empty : ∀ (sep h : Str) (t : List Str),
    concat sep ([] :: h :: t) = sep ++ concat sep (h :: t) := fun _ _ _ => rfl

theorem concat_map_head : ∀ (sep : Str) (c : Char) (h : Str) (t : List Str),
    concat sep ((c :: h) :: t) = c :: concat sep (h :: t)
  | _, _, _, [] => rfl
  | _, _, _, _ :: _ => rfl

theorem split_slash_concat : ∀ s, concat (str! "/") (split_slash s) = s := by
  intro s
  induction s with
  | nil => rfl
  | cons c s IH =>
    rw [split_slash]
    obtain E | E := Decidable.em (c = '/')
    · subst E
      rw [if_pos rfl]
      cases Esp : split_slash s with
      | nil => exact absurd Esp (split_slash_nonempty s)
      | cons h t =>
        rw [concat_cons_empty, ← Esp, IH]
        rfl
    · rw [if_neg E]
      cases Esp : split_slash s with
      | nil => exact absurd Esp (split_slash_nonempty s)
      | cons h t =>
        show concat (str! "/") ((c :: h) :: t) = c :: s
        rw [concat_map_head, ← Esp, IH]

theorem split_concat_singles : ∀ comps : List Str,
    (∀ x, x ∈ comps → split_slash x = [x]) → comps ≠ [] →
    split_slash (concat (str! "/") comps) = comps := by
  intro comps
  induction comps with
  | nil => intro _ Hne; exact absurd rfl Hne
  | cons x rest IH =>
    intro Hs _
    cases rest with
    | nil => exact Hs x (List.Mem.head _)
    | cons y rest =>
      show split_slash (x ++ '/' :: concat (str! "/") (y :: rest)) = x :: y :: rest
      rw [split_slash_app, Hs x (List.Mem.head _),
        IH (fun z Hz => Hs z (List.Mem.tail _ Hz)) nofun]
      rfl

theorem is_lower_not_slash : ∀ c, is_lower c = true → decide (c = '/') = false := by
  intro c H
  obtain E | E := Decidable.em (c = '/')
  · subst E; exact absurd H (by decide)
  · exact decide_eq_false E

theorem is_lower_digit_not_slash : ∀ c, is_lower_digit c = true → decide (c = '/') = false := by
  intro c H
  obtain E | E := Decidable.em (c = '/')
  · subst E; exact absurd H (by decide)
  · exact decide_eq_false E

-- Rocq: `Bool.andb_true_iff`, the forward direction, by cases (no `propext`).
private theorem band_true : ∀ {a b : Bool}, (a && b) = true → a = true ∧ b = true
  | true, true, _ => ⟨rfl, rfl⟩
  | true, false, h => nomatch h
  | false, _, h => nomatch h

theorem tail_ok_single : ∀ s, tail_ok s = true → split_slash s = [s] := by
  intro s
  induction s with
  | nil => intro _; rfl
  | cons c s IH =>
    intro H
    obtain ⟨Hc, Hs⟩ := band_true H
    rw [split_slash, if_neg (of_decide_eq_false (is_lower_digit_not_slash c Hc)), IH Hs]

theorem component_ok_single : ∀ s, component_ok s = true → split_slash s = [s] := by
  intro s H
  cases s with
  | nil => exact nomatch H
  | cons c s' =>
    obtain ⟨Hc, Ht⟩ := band_true H
    rw [split_slash, if_neg (of_decide_eq_false (is_lower_not_slash c Hc)), tail_ok_single s' Ht]

theorem component_ok_nonempty : ∀ s, component_ok s = true → s ≠ [] := by
  intro s H
  cases s with
  | nil => exact nomatch H
  | cons _ _ => exact nofun

theorem dir_component_ok_single : ∀ s, dir_component_ok s = true → split_slash s = [s] := by
  intro s H
  exact component_ok_single s (band_true H).1

theorem dir_component_ok_nonempty : ∀ s, dir_component_ok s = true → s ≠ [] := by
  intro s H
  exact component_ok_nonempty s (band_true H).1

/-- the package DIRECTORY COMPONENTS of a key: the root key "" has none; else the split components. -/
def dir_components (dir : Str) : List Str :=
  if dir = [] then [] else split_slash dir

theorem dir_components_concat : ∀ dir, concat (str! "/") (dir_components dir) = dir := by
  intro dir
  unfold dir_components
  obtain E | E := Decidable.em (dir = [])
  · subst E
    rw [if_pos rfl]
    rfl
  · rw [if_neg E]
    exact split_slash_concat dir

-- Rocq: `forallb_forall`, one direction each, by induction (no `propext`).
private theorem all_forall {α : Type} (p : α → Bool) :
    ∀ (l : List α), l.all p = true → ∀ x, x ∈ l → p x = true := by
  intro l
  induction l with
  | nil => intro _ x hx; exact nomatch hx
  | cons y ys IH =>
    intro h x hx
    obtain ⟨hy, hys⟩ := band_true h
    cases hx with
    | head => exact hy
    | tail _ hx' => exact IH hys x hx'

private theorem forall_all {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∀ x, x ∈ l → p x = true) → l.all p = true := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons y ys IH =>
    intro h
    show (p y && ys.all p) = true
    rw [h y (List.Mem.head _), IH (fun x hx => h x (List.Mem.tail _ hx))]
    rfl

-- Rocq: `in_rev`, the `rev`-to-list direction, through `reverseAux` (no `propext`).
private theorem mem_of_mem_reverseAux {α : Type} :
    ∀ (l r : List α) (x : α), x ∈ List.reverseAux l r → x ∈ l ∨ x ∈ r := by
  intro l
  induction l with
  | nil => intro r x h; exact .inr h
  | cons y ys IH =>
    intro r x h
    rcases IH (y :: r) x h with h | h
    · exact .inl (List.Mem.tail _ h)
    · cases h with
      | head => exact .inl (List.Mem.head _)
      | tail _ h' => exact .inr h'

private theorem mem_of_mem_reverse {α : Type} {x : α} {l : List α} (h : x ∈ l.reverse) : x ∈ l :=
  match mem_of_mem_reverseAux l [] x h with
  | .inl h => h
  | .inr h => nomatch h

theorem parent_dir_components_nonempty : ∀ fp s,
    s ∈ dir_components (parent fp) → s ≠ [] := by
  intro fp s Hin
  unfold dir_components at Hin
  obtain E | E := Decidable.em (parent fp = [])
  · rw [if_pos E] at Hin; exact nomatch Hin
  · rw [if_neg E] at Hin
    have Hok := valid fp
    unfold path_ok at Hok
    revert Hok
    cases Erev : (split_slash (text fp)).reverse with
    | nil => intro Hok; exact nomatch Hok
    | cons lastc rdirs =>
      intro Hok
      have Hok' : (rdirs.all dir_component_ok && filename_ok lastc) = true := Hok
      have Hdirs := (band_true Hok').1
      have Hpar : parent fp = concat (str! "/") rdirs.reverse := by
        unfold parent parent_of
        rw [Erev]
      have Hsingle : ∀ x, x ∈ rdirs.reverse → split_slash x = [x] :=
        fun x Hx => dir_component_ok_single x (all_forall _ _ Hdirs x (mem_of_mem_reverse Hx))
      have Hrne : rdirs.reverse ≠ [] := fun Hc => E (by rw [Hpar, Hc]; rfl)
      rw [Hpar, split_concat_singles _ Hsingle Hrne] at Hin
      exact dir_component_ok_nonempty s (all_forall _ _ Hdirs s (mem_of_mem_reverse Hin))

/-- Every directory component of a file's parent is a valid directory component. -/
theorem file_dir_components_ok : ∀ p, (dir_components (parent p)).all dir_component_ok = true := by
  intro p
  unfold dir_components
  obtain E | E := Decidable.em (parent p = [])
  · rw [if_pos E]; rfl
  · rw [if_neg E]
    have Hok := valid p
    unfold path_ok at Hok
    revert Hok
    cases Erev : (split_slash (text p)).reverse with
    | nil => intro Hok; exact nomatch Hok
    | cons lastc rdirs =>
      intro Hok
      have Hok' : (rdirs.all dir_component_ok && filename_ok lastc) = true := Hok
      have Hdirs := (band_true Hok').1
      have Hpar : parent p = concat (str! "/") rdirs.reverse := by
        unfold parent parent_of
        rw [Erev]
      have Hsingle : ∀ x, x ∈ rdirs.reverse → split_slash x = [x] :=
        fun x Hx => dir_component_ok_single x (all_forall _ _ Hdirs x (mem_of_mem_reverse Hx))
      have Hrne : rdirs.reverse ≠ [] := fun Hc => E (by rw [Hpar, Hc]; rfl)
      rw [Hpar, split_concat_singles _ Hsingle Hrne]
      exact forall_all _ _ (fun x Hx => all_forall _ _ Hdirs x (mem_of_mem_reverse Hx))

set_option genInjectivity false in
/-- A package directory: a validated list of directory components (not a string); [] is the module-root package. -/
structure PkgDir : Type where
  MakePkgDir ::
  pkg_components : List Str
  pkg_valid : pkg_components.all dir_component_ok = true

open PkgDir

theorem pkg_valid_pi : ∀ (l : List Str) (p q : l.all dir_component_ok = true), p = q :=
  fun _ _ _ => rfl

theorem pkgdir_equal : ∀ a b, pkg_components a = pkg_components b → a = b := by
  intro ⟨la, _⟩ ⟨lb, _⟩ H
  have H' : la = lb := H
  subst H'
  rfl

def pkgdir_eq_dec (a b : PkgDir) : Decidable (a = b) :=
  match decEq (pkg_components a) (pkg_components b) with
  | isTrue E => isTrue (pkgdir_equal a b E)
  | isFalse NE => isFalse (fun H => NE (congrArg pkg_components H))

/-- The package-directory projection of a file: files sharing one PkgDir form one package. -/
def file_dir (p : T) : PkgDir := MakePkgDir (dir_components (parent p)) (file_dir_components_ok p)

theorem ok_main    : path_ok (str! "main.go") = true := by decide
theorem ok_a       : path_ok (str! "a.go") = true := by decide
theorem ok_pkg     : path_ok (str! "pkg/main.go") = true := by decide
theorem ok_nested  : path_ok (str! "cmd/x/app.go") = true := by decide

theorem no_empty     : path_ok (str! "") = false := by decide
theorem no_absolute  : path_ok (str! "/main.go") = false := by decide
theorem no_dotdot    : path_ok (str! "../x.go") = false := by decide
theorem no_mid_dotdot : path_ok (str! "a/../x.go") = false := by decide
theorem no_dot       : path_ok (str! "./x.go") = false := by decide
theorem no_double    : path_ok (str! "a//b.go") = false := by decide
theorem no_hidden    : path_ok (str! ".main.go") = false := by decide
theorem no_underscore : path_ok (str! "_main.go") = false := by decide
theorem no_test      : path_ok (str! "main_test.go") = false := by decide
theorem no_goos      : path_ok (str! "main_windows.go") = false := by decide
theorem no_ext       : path_ok (str! "main.txt") = false := by decide
theorem no_hidden_dir : path_ok (str! ".git/x.go") = false := by decide
theorem no_control   : path_ok (str! ".fido/x.go") = false := by decide
theorem no_trailing  : path_ok (str! "pkg/") = false := by decide
theorem no_bare_go   : path_ok (str! "go") = false := by decide
theorem no_testdata     : path_ok (str! "testdata/main.go") = false := by decide
theorem no_testdata_nest : path_ok (str! "a/testdata/x.go") = false := by decide
theorem no_vendor       : path_ok (str! "vendor/x.go") = false := by decide
theorem ok_testdata_file : path_ok (str! "testdata.go") = true := by decide

end Fido.FilePath
