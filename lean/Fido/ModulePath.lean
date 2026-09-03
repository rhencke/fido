-- Port of ModulePath.v (lean/README.md).
import Fido.Prelude

/-! divergences:
  - `Ascii.eqb a b` is `decide (a = b)` on `UInt8`, `String.eqb a b` is `decide (a = b)` on `Str`, and a
    Rocq `if` on `Ascii.eqb c x` is `if c = x then … else …` (its `Decidable` instance), so proofs case with
    `Decidable.em`, never on excluded middle.
  - `String.concat sep l` is `List.intercalate sep l` (`(intersperse sep l).flatten`): the same function
    pointwise, and `concat_cons_empty` / `concat_map_head` still hold by `rfl`; the one visible seam is
    `concat sep [x] = x` against `intercalate sep [x] = x ++ []` (one `append_nil` in
    `split_concat_singles`).  `String.get n s` is a private structural `get` (core's `s[n]?` instance
    carries `propext`; `List.get?` is gone in 4.33), `String.prefix p s` is `p.isPrefixOf s` (core's `BEq UInt8` is
    `instBEqOfDecidableEq`, so its `==` is the same `decide (_ = _)`), `forallb` is `List.all`, `List.last l d` is `l.getLastD d`,
    `In x l` is `x ∈ l`.
  - The `| _ => false` alternatives of `reserved_base` and `version_suffix_shape` are enumerated
    (`[] | [_] | …`): Lean 4.33 compiles a wildcard alternative through a `_sparseCasesOn` helper whose
    proofs depend on `propext`; the enumeration is the case tree Rocq's own pattern compiler builds.
  - `Record T := Make {…}` is `structure T where Make :: …` (with `genInjectivity` / `genSizeOfSpec` off,
    since the auto-generated lemmas would be the only `propext` users) plus `export T (Make text valid)`,
    so the projections read `text p` as in the `.v`.  `path_ok_pi` (Rocq: `UIP_dec`) is `rfl`: Lean's
    `Eq` is definitionally proof-irrelevant.
  - Rocq's named `Example`s are `theorem`s (a Lean `example` is anonymous). -/

namespace Fido.ModulePath

def is_lower (c : UInt8) : Bool :=
  let n := c.toNat; decide (97 ≤ n) && decide (n ≤ 122)

def is_lower_digit (c : UInt8) : Bool :=
  let n := c.toNat; (decide (97 ≤ n) && decide (n ≤ 122)) || (decide (48 ≤ n) && decide (n ≤ 57))

/-- A segment character: a..z, 0..9, or `.`, with no hyphen. -/
def seg_char (c : UInt8) : Bool := is_lower_digit c || decide (c = byte! '.')

def all_seg_chars : Str → Bool
  | [] => true
  | c :: s' => seg_char c && all_seg_chars s'

def no_double_dot : Str → Bool
  | a :: s0 =>
    match s0 with
    | b :: _ => !(decide (a = byte! '.') && decide (b = byte! '.')) && no_double_dot s0
    | [] => true
  | [] => true

/-- Rocq's `String.get`, structural on the string.  Core's `s[n]?` instance for lists carries `propext`
    and `List.get?` no longer exists in 4.33, so the stdlib Fixpoint is restated here. -/
private def get : Nat → Str → Option UInt8
  | _, [] => none
  | 0, c :: _ => some c
  | n + 1, _ :: s' => get n s'

def str_last (s : Str) : Option UInt8 := get (s.length - 1) s

def is_digit (c : UInt8) : Bool := let n := c.toNat; decide (48 ≤ n) && decide (n ≤ 57)

/-- A segment's base name is the part before its first `.`, which is what Go's device-name rejection reads. -/
def base_of : Str → Str
  | [] => []
  | c :: s' => if c = byte! '.' then [] else c :: base_of s'

def reserved_base (s : Str) : Bool :=
  let b := base_of s
  decide (b = str! "con") || decide (b = str! "prn") || decide (b = str! "aux") || decide (b = str! "nul")
  || match b with
     | [a, b1, c, d] =>
         ((decide (a = byte! 'c') && decide (b1 = byte! 'o') && decide (c = byte! 'm'))
          || (decide (a = byte! 'l') && decide (b1 = byte! 'p') && decide (c = byte! 't'))) && is_digit d
     | [] | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ :: _ => false

def segment_ok (s : Str) : Bool :=
  match s with
  | [] => false
  | c0 :: _ =>
      is_lower c0
      && all_seg_chars s
      && no_double_dot s
      && (match str_last s with | some cl => is_lower_digit cl | none => false)
      && !(reserved_base s)

def split_slash : Str → List Str
  | [] => [[]]
  | c :: s' =>
      if c = byte! '/' then [] :: split_slash s'
      else match split_slash s' with
           | h :: t => (c :: h) :: t
           | [] => [[c]]                                  -- unreachable: split_slash never returns []

/-- Rocq's `andb_true_iff`, by cases so the module stays axiom-free (`simp` would go through `propext`). -/
private theorem and_true_iff {a b : Bool} : (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

/-- Rocq's `orb_true_iff`, likewise. -/
private theorem or_true_iff {a b : Bool} : (a || b) = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem split_slash_nonempty : ∀ s, split_slash s ≠ [] := by
  intro s
  cases s with
  | nil => nofun
  | cons c s' =>
    rw [split_slash]
    obtain E | E := Decidable.em (c = byte! '/')
    · rw [if_pos E]; exact nofun
    · rw [if_neg E]
      cases split_slash s' with
      | nil => exact nofun
      | cons h t => exact nofun

theorem split_slash_app : ∀ a b,
    split_slash (a ++ byte! '/' :: b) = split_slash a ++ split_slash b := by
  intro a b
  induction a with
  | nil =>
    show split_slash (byte! '/' :: b) = [[]] ++ split_slash b
    rw [split_slash, if_pos rfl]
    rfl
  | cons c a' IH =>
    show split_slash (c :: (a' ++ byte! '/' :: b)) = split_slash (c :: a') ++ split_slash b
    rw [split_slash, split_slash, IH]
    obtain E | E := Decidable.em (c = byte! '/')
    · rw [if_pos E, if_pos E]
      rfl
    · rw [if_neg E, if_neg E]
      cases Ea : split_slash a' with
      | nil => exact absurd Ea (split_slash_nonempty a')
      | cons ha ta => rfl

def path_char (c : UInt8) : Bool := seg_char c || decide (c = byte! '/')

def all_path_chars : Str → Bool
  | [] => true
  | c :: s' => path_char c && all_path_chars s'

/-- Go reads a dotless first element as standard library, so a required dot keeps paths outside it. -/
def before_slash : Str → Str
  | [] => []
  | c :: s' => if c = byte! '/' then [] else c :: before_slash s'

def contains_dot : Str → Bool
  | [] => false
  | c :: s' => decide (c = byte! '.') || contains_dot s'

/-- Go's whole version-suffix shape is excluded rather than split into its accept and reject halves. -/
def is_dot_or_digit (c : UInt8) : Bool := is_digit c || decide (c = byte! '.')

def all_dot_or_digit : Str → Bool
  | [] => true
  | c :: s' => is_dot_or_digit c && all_dot_or_digit s'

def version_suffix_shape (seg : Str) : Bool :=
  match seg with
  | v :: c :: rest => decide (v = byte! 'v') && is_dot_or_digit c && all_dot_or_digit rest
  | [] | [_] => false

def last_segment (s : Str) : Str := (split_slash s).getLastD []

/-- The `gopkg.in/` host needs a `.vN` suffix grammar that is not modelled, so the whole prefix is excluded. -/
def is_gopkg_in (s : Str) : Bool := (str! "gopkg.in/").isPrefixOf s

def path_ok (s : Str) : Bool :=
  all_path_chars s
  && contains_dot (before_slash s)
  && !(is_gopkg_in s)
  && !(version_suffix_shape (last_segment s))
  && (split_slash s).all segment_ok

theorem path_ok_all_chars : ∀ s, path_ok s = true → all_path_chars s = true := by
  intro s H
  exact (and_true_iff.1 (and_true_iff.1 (and_true_iff.1 (and_true_iff.1 H).1).1).1).1

theorem path_char_lt_128 : ∀ c, path_char c = true → c.toNat < 128 := by
  intro c H
  obtain H | H := or_true_iff.1 H
  · obtain H | H := or_true_iff.1 H
    · obtain H | H := or_true_iff.1 H
      · exact Nat.lt_of_le_of_lt (of_decide_eq_true (and_true_iff.1 H).2) (by decide)
      · exact Nat.lt_of_le_of_lt (of_decide_eq_true (and_true_iff.1 H).2) (by decide)
    · have hc : c = byte! '.' := of_decide_eq_true H
      subst hc; decide
  · have hc : c = byte! '/' := of_decide_eq_true H
    subst hc; decide

-- Rocq's `Record` generates no injectivity or size lemmas; Lean's auto-generated `T.Make.injEq` and
-- `T.Make.sizeOf_spec` would be the module's only `propext` users, and nothing here needs them.
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure T : Type where
  Make ::
  text : Str
  valid : path_ok text = true

export T (Make text valid)

theorem path_ok_pi : ∀ s (p q : path_ok s = true), p = q := fun _ _ _ => rfl

theorem equal : ∀ a b, text a = text b → a = b := by
  intro a b H
  cases a with | Make sa pa =>
  cases b with | Make sb pb =>
  have H' : sa = sb := H
  subst H'
  rfl

def equalb (a b : T) : Bool := decide (text a = text b)

theorem equalb_spec : ∀ a b, equalb a b = true ↔ a = b := by
  intro a b
  exact ⟨fun H => equal a b (of_decide_eq_true H), fun H => by subst H; exact decide_eq_true rfl⟩

theorem concat_cons_empty : ∀ (sep h : Str) (t : List Str),
    List.intercalate sep ([] :: h :: t) = sep ++ List.intercalate sep (h :: t) := by
  intros; rfl

theorem concat_map_head : ∀ (sep : Str) (c : UInt8) (h : Str) (t : List Str),
    List.intercalate sep ((c :: h) :: t) = c :: List.intercalate sep (h :: t) := by
  intro sep c h t
  cases t with
  | nil => rfl
  | cons z t' => rfl

theorem split_slash_concat : ∀ s, List.intercalate (str! "/") (split_slash s) = s := by
  intro s
  induction s with
  | nil => rfl
  | cons c s IH =>
    rw [split_slash]
    obtain E | E := Decidable.em (c = byte! '/')
    · subst E
      rw [if_pos rfl]
      cases Esp : split_slash s with
      | nil => exact absurd Esp (split_slash_nonempty s)
      | cons h t =>
        rw [Esp] at IH
        show List.intercalate (str! "/") ([] :: h :: t) = byte! '/' :: s
        rw [concat_cons_empty (str! "/") h t, IH]
        rfl
    · rw [if_neg E]
      cases Esp : split_slash s with
      | nil => exact absurd Esp (split_slash_nonempty s)
      | cons h t =>
        rw [Esp] at IH
        show List.intercalate (str! "/") ((c :: h) :: t) = c :: s
        rw [concat_map_head (str! "/") c h t, IH]

/-- Rocq's `String.concat sep [x]` is `x` outright; `List.intercalate sep [x]` is `x ++ []`.  Core's
    `List.append_nil` is proved by `simp`, so this one is by hand to keep the closure axiom-free. -/
private theorem append_nil : ∀ (l : Str), l ++ [] = l
  | [] => rfl
  | c :: l => congrArg (c :: ·) (append_nil l)

theorem split_concat_singles : ∀ comps : List Str,
    (∀ x, x ∈ comps → split_slash x = [x]) → comps ≠ [] →
    split_slash (List.intercalate (str! "/") comps) = comps := by
  intro comps
  induction comps with
  | nil => intro _ Hne; exact absurd rfl Hne
  | cons x tl IH =>
    intro Hs _
    cases tl with
    | nil =>
      show split_slash (x ++ []) = [x]
      rw [append_nil]
      exact Hs x (List.Mem.head _)
    | cons y rest =>
      show split_slash (x ++ byte! '/' :: List.intercalate (str! "/") (y :: rest)) = x :: y :: rest
      rw [split_slash_app, Hs x (List.Mem.head _),
        IH (fun z Hz => Hs z (List.Mem.tail _ Hz)) nofun]
      rfl

theorem seg_char_not_slash : ∀ c, seg_char c = true → decide (c = byte! '/') = false := by
  intro c H
  obtain E | E := Decidable.em (c = byte! '/')
  · subst E; exact absurd H (by decide)
  · exact decide_eq_false E

theorem all_seg_chars_single : ∀ s, all_seg_chars s = true → split_slash s = [s] := by
  intro s
  induction s with
  | nil => intro _; rfl
  | cons c s IH =>
    intro H
    obtain ⟨Hc, Hs⟩ := and_true_iff.1 H
    rw [split_slash, if_neg (of_decide_eq_false (seg_char_not_slash c Hc)), IH Hs]

theorem segment_ok_single : ∀ s, segment_ok s = true → split_slash s = [s] := by
  intro s H
  apply all_seg_chars_single
  cases s with
  | nil => nomatch H
  | cons c s' =>
    exact (and_true_iff.1 (and_true_iff.1 (and_true_iff.1 (and_true_iff.1 H).1).1).1).2

theorem segment_ok_nonempty : ∀ s, segment_ok s = true → s ≠ [] := by
  intro s H
  cases s with
  | nil => nomatch H
  | cons c s' => nofun

def segments (p : T) : List Str := split_slash (text p)

theorem segments_nonempty : ∀ p, segments p ≠ [] := by
  intro p; exact split_slash_nonempty _

theorem text_concat : ∀ p, List.intercalate (str! "/") (segments p) = text p := by
  intro p; exact split_slash_concat _

/-- Rocq's `forallb_forall`, forward direction, by induction so the module stays axiom-free. -/
private theorem all_mem {p : Str → Bool} :
    ∀ (l : List Str), l.all p = true → ∀ x, x ∈ l → p x = true := by
  intro l
  induction l with
  | nil => intro _ x h; nomatch h
  | cons y t IH =>
    intro H x h
    cases h with
    | head _ => exact (and_true_iff.1 H).1
    | tail _ h' => exact IH (and_true_iff.1 H).2 x h'

theorem segments_segment_ok : ∀ p s, s ∈ segments p → segment_ok s = true := by
  intro p s Hin
  have Hok := valid p
  exact all_mem _ (and_true_iff.1 Hok).2 s Hin

theorem segments_single : ∀ p s, s ∈ segments p → split_slash s = [s] := by
  intro p s Hin; exact segment_ok_single s (segments_segment_ok p s Hin)

theorem segments_nonempty_elt : ∀ p s, s ∈ segments p → s ≠ [] := by
  intro p s Hin; exact segment_ok_nonempty s (segments_segment_ok p s Hin)

theorem ok_generated : path_ok (str! "fido.local/generated") = true := by decide
theorem ok_nested    : path_ok (str! "fido.local/generated/sub") = true := by decide
theorem ok_common    : path_ok (str! "fido.local/common") = true := by decide
theorem ok_dothost   : path_ok (str! "example.com") = true := by decide
theorem ok_digits    : path_ok (str! "fido2.dev/pkg9") = true := by decide

theorem no_empty          : path_ok (str! "") = false := by decide
theorem no_leading_slash  : path_ok (str! "/x") = false := by decide
theorem no_trailing_slash : path_ok (str! "x/") = false := by decide
theorem no_double_slash   : path_ok (str! "a//b") = false := by decide
theorem no_upper          : path_ok (str! "Fido.dev") = false := by decide
theorem no_dotdot         : path_ok (str! "a..b") = false := by decide
theorem no_leading_dot    : path_ok (str! ".fido") = false := by decide
theorem no_trailing_dot   : path_ok (str! "fido.") = false := by decide
theorem no_at             : path_ok (str! "fido.dev@v1") = false := by decide
theorem no_space          : path_ok (str! "fido dev.x") = false := by decide
theorem no_digit_start    : path_ok (str! "9fido.dev") = false := by decide
theorem no_dotless_go     : path_ok (str! "go") = false := by decide
theorem no_dotless_fmt    : path_ok (str! "fmt") = false := by decide
theorem no_dotless_bare   : path_ok (str! "fidoe2e") = false := by decide
theorem no_dotless_pkg    : path_ok (str! "fido2/pkg9") = false := by decide
theorem no_ver_v1     : path_ok (str! "example.com/pkg/v1") = false := by decide
theorem no_ver_v01    : path_ok (str! "example.com/pkg/v01") = false := by decide
theorem no_ver_v1dot2 : path_ok (str! "example.com/pkg/v1.2") = false := by decide
theorem no_ver_vdot   : path_ok (str! "example.com/pkg/v.2.3") = false := by decide  -- dot-led run
theorem no_ver_v2     : path_ok (str! "example.com/pkg/v2") = false := by decide  -- Go-valid, but out of scope
theorem ok_vlike_mid  : path_ok (str! "example.com/v2/pkg") = true := by decide   -- v2 NOT the last element
theorem ok_vword      : path_ok (str! "example.com/verify") = true := by decide
theorem no_gopkg_bare : path_ok (str! "gopkg.in/foo") = false := by decide
-- Go-valid, but out of scope
theorem no_gopkg_v2   : path_ok (str! "gopkg.in/yaml.v2") = false := by decide
-- Windows-reserved device names Go rejects as a path ELEMENT (even on Linux), with or without extension:
theorem no_reserved_con    : path_ok (str! "fido.local/con") = false := by decide
theorem no_reserved_nul    : path_ok (str! "fido.dev/nul") = false := by decide
theorem no_reserved_com1   : path_ok (str! "fido.dev/com1") = false := by decide
theorem no_reserved_lpt9   : path_ok (str! "fido.dev/lpt9") = false := by decide
theorem no_reserved_conext : path_ok (str! "con.js") = false := by decide  -- base "con" reserved

end Fido.ModulePath
