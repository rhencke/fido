(** ==================================================================================================
    GoString — Go strings over the model: the string ops ([str_len]/[str_concat]/…), [[]byte]/
    [string] conversions, the FAITHFUL UTF-8 rune view ([str_to_runes]/[runes_to_str] — exactly
    Go's DecodeRune incl. U+FFFD on invalid input, round-trip verified), string comparison and
    the total lexicographic order, and [range] over a string (the string expression switch
    lives in GoSwitch.v).
    Also HOME OF the sealed [ComparableW] witnesses for Go's generic [comparable] constraint
    (i64/u64/string): a witness CARRIES its decidability proof ([Squash]-sealed), and the string
    one is anchored on [str_eqb] defined here — one authority for both.
    ================================================================================================ *)

Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Coq.Lists.List.
From Stdlib Require Import ZArith.
From Stdlib Require Import StrictProp.
From Fido Require Import GoNumeric.
From Fido Require Import GoRuntimeTypes.
From Fido Require Import GoEffects.

(** ---- String operations (Go spec "String types") ----

    [str_len s] is the BYTE length (Go [len(s)]): a computable [int] that counts
    the [string]'s bytes, so [str_len "Go" = 2] is a THEOREM.  The plugin lowers
    it to Go [int64(len(s))] — the byte count in the [Z]-carried [GoInt] (int64) model.

    [str_at_ok] is the SAFE byte index (spec: "a string's bytes can be accessed
    by integer indices [0 <= i < len(s)]"; [s[i]] is of type [byte]).  CPS /
    comma-ok like [slice_at_ok]: it FORCES handling the out-of-range case, so it
    cannot panic.  In range ⇒ [b = s[i]] (the byte, a [GoByte] = [uint8]) and
    [ok = true]; else [b = 0], [ok = false].  [i : int] is SIGNED, so the bounds
    check covers BOTH ends.  Lowers to a bounds-checked [int64(s[i])] (the byte
    in the int64 carrier), mirroring [slice_at_ok].

    [str_concat] is Go's string [+] (spec "Operators": string concatenation) — a
    pure, total operation on immutable byte sequences, so [str_concat "ab" "cd" =
    "abcd"] is a THEOREM.  Defined by its OWN recursion (no [String.append]
    dependency to drag into extraction); suppressed in the plugin, lowered to Go
    [a + b]. *)
Fixpoint str_len (s : GoString) : GoInt :=
  match s with
  | EmptyString   => intwrap 0
  | String _ rest => intwrap (1 + intraw (str_len rest))
  end.

(** DEFINITION: the i'th BYTE of the string at the signed index,
    as a [GoByte] (= [GoU8]); out of range ⇒ [k 0 false].  Like the slice forms,
    the body must pull in NO external stdlib function, so it uses SELF-CONTAINED,
    suppressed helpers: [ascii_byte] decodes the 8 bits of an [ascii] to its 0–255
    [GoU8] carrier INLINE (no [nat_of_ascii], which drags in [N_of_digits]), and
    [go_str_byte] walks to the i'th byte ([int]-indexed, structural on the string,
    no [String.get]+[Z.to_nat]).  Lowered BY NAME to a bounds-checked [int64(s[i])]
    (body suppressed + NoInline), so this affects only proofs. *)
Definition ascii_byte (c : ascii) : GoByte :=
  match c with
  | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
      let v (b : bool) (k : Z) : Z := if b then k else 0%Z in
      u8wrap (v b0 1 + (v b1 2 + (v b2 4 + (v b3 8 +
             (v b4 16 + (v b5 32 + (v b6 64 + v b7 128)))))))%Z
  end.
Fixpoint go_str_byte (s : GoString) (i : nat) : GoByte :=
  match s with
  | EmptyString  => u8wrap 0
  | String c rest => if Nat.eqb i 0 then ascii_byte c
                     else go_str_byte rest (Nat.pred i)
  end.

(** ---- [[]byte] / [string] conversions (Go spec "Conversions to and from a string
    type") ----  [[]byte(s)] is the BYTE sequence of [s] (no UTF-8 decoding); [string(b)]
    reconstructs it.  [GoString] IS a byte sequence ([list ascii]), so these are faithful
    byte-for-byte.  [str_to_bytes] maps each char to its [GoByte] via the suppressed
    [ascii_byte]; [byte_ascii] is its inverse (reconstruct the 8 bits, again no
    [nat_of_ascii]).  Both lower BY NAME to the native [[]byte(s)] / [string(b)] (bodies
    suppressed + NoInline, so they affect only proofs).  [str_to_bytes_length] proves the
    byte count is preserved ([len([]byte(s)) == len(s)]); the value round-trip is golden. *)
Definition byte_ascii (b : GoByte) : ascii :=
  let n := u8raw b in
  let bit (k : Z) : bool := Z.testbit n k in
  Ascii (bit 0%Z) (bit 1%Z) (bit 2%Z) (bit 3%Z)
        (bit 4%Z) (bit 5%Z) (bit 6%Z) (bit 7%Z).
Fixpoint str_to_bytes (s : GoString) : list GoByte :=
  match s with
  | EmptyString   => nil
  | String c rest => ascii_byte c :: str_to_bytes rest
  end.
Fixpoint str_from_bytes (b : list GoByte) : GoString :=
  match b with
  | nil       => EmptyString
  | x :: rest => String (byte_ascii x) (str_from_bytes rest)
  end.
Lemma str_to_bytes_length : forall s, Datatypes.length (str_to_bytes s) = String.length s.
Proof. induction s as [|c rest IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.
Definition str_at_ok {B : Type}
  (s : GoString) (i : GoInt) (k : GoByte -> bool -> IO B) : IO B :=
  if (Z.leb 0 (intraw i) && Z.ltb (intraw i) (intraw (str_len s)))%bool
  then k (go_str_byte s (Z.to_nat (intraw i))) true
  else k (u8wrap 0) false.

Fixpoint str_concat (a b : GoString) : GoString :=
  match a with
  | EmptyString   => b
  | String c rest => String c (str_concat rest b)
  end.

(** String slicing [s[a:b]] (Go spec "Slice expressions": for a string, the result is the
    BYTE-substring [a, b)).  EVIDENCE-CARRYING / safe-by-construction: it DEMANDS a proof
    that [a <= b <= len(s)] (in bytes), so the emitted [s[a:b]] cannot panic — the bounds
    proof discharged Go's slice-bounds check (same discipline as [div_nz]).  Indices are
    [nat] (a string length/offset is non-negative).  The body [String.substring a (b-a) s] is recognized
    away to the native [s[a:b]] (decl + [substring] suppressed).  [eq_refl] discharges the
    proof for literal bounds. *)
Definition str_slice (s : GoString) (a b : nat)
  (_ : (Nat.leb a b && Nat.leb b (String.length s))%bool = true) : GoString :=
  String.substring a (b - a) s.

(** ---- Rune view: [[]rune(s)] / [string([]rune)] (Go spec "Conversions to and from a
    string type") ----  A [rune] is an int32 code point.  [[]rune(s)] UTF-8-DECODES the
    byte sequence to code points; [string(rs)] UTF-8-ENCODES them back.  Both lower BY NAME
    to the native Go [[]rune(s)] / [string(rs)] (the runtime does the real UTF-8, faithful);
    the Coq bodies below are the proof-side model (suppressed + NoInline), a full 1–4 byte
    UTF-8 codec.  [byte_chr] is a byte value → [ascii]; the codec is verified by the
    round-trip examples (ASCII and a 3-byte CJK code point). *)
Definition byte_chr (v : Z) : ascii := byte_ascii (u8wrap v).

(** [str_to_runes] is a FAITHFUL UTF-8 decoder — exactly Go's [utf8.DecodeRune] /
    range-over-string.  An invalid sequence yields [RuneError] (U+FFFD) and advances by exactly ONE byte
    (NOT the would-be width), rejecting: continuation bytes used as leads (0x80–0xBF), overlong 2-byte
    (0xC0/0xC1), missing/bad continuation bytes, overlong 3/4-byte (0xE0 with c1<0xA0; 0xF0 with c1<0x90),
    UTF-16 surrogates (0xED with c1≥0xA0), >MaxRune (0xF4 with c1≥0x90), and invalid leads ≥0xF5.  The body
    is proof-only (lowered by name to native [[]rune(s)], which does the same). *)
(** [str_to_runes_w] decodes AND records, per rune, the number of SOURCE bytes consumed (1 for an
    invalid byte — Go's [utf8.DecodeRune] advances exactly one — or the 2/3/4 of a valid multibyte).
    That CONSUMED width, not the decoded rune's would-be re-encoded width, is what [str_range]
    accumulates into byte offsets: for source [0x80 'A'] Go yields
    [(0,U+FFFD) (1,'A')], and so does the model (the FFFD consumed ONE byte, not
    [rune_width U+FFFD] = 3).  [str_to_runes] (rune-only) is [map fst] of this — one decoder. *)
Fixpoint str_to_runes_w (s : GoString) : list (GoI32 * Z) :=
  match s with
  | EmptyString => nil
  | String c0 r0 =>
      (* [rerr]/[isc] are LOCAL (not top-level Definitions): the whole body is suppressed and lowered by
         name to native [[]rune(s)], so the unsigned [ltb]/[leb] here are proof-only and never extracted. *)
      let rerr := i32wrap 65533%Z in              (* U+FFFD *)
      let isc  := fun v => andb (Z.leb 128%Z v) (Z.ltb v 192%Z) in  (* cont byte 0x80–0xBF *)
      let v0 := u8raw (ascii_byte c0) in
      if Z.ltb v0 128%Z then              (* 1-byte: ASCII 0x00–0x7F *)
        (i32wrap v0, 1%Z) :: str_to_runes_w r0
      else if Z.ltb v0 194%Z then         (* 0x80–0xC1: cont-as-lead OR overlong-2 → error *)
        (rerr, 1%Z) :: str_to_runes_w r0
      else if Z.ltb v0 224%Z then         (* 0xC2–0xDF: 2-byte (result ≥ 0x80, non-overlong) *)
        match r0 with
        | String c1 r1 =>
            let v1 := u8raw (ascii_byte c1) in
            if isc v1 then
              (i32wrap (Z.lor (Z.shiftl (Z.land v0 31%Z) 6%Z)
                                     (Z.land v1 63%Z)), 2%Z) :: str_to_runes_w r1
            else (rerr, 1%Z) :: str_to_runes_w r0   (* bad continuation → error, advance 1 *)
        | EmptyString => (rerr, 1%Z) :: nil         (* truncated → advance 1 (the lead) *)
        end
      else if Z.ltb v0 240%Z then         (* 0xE0–0xEF: 3-byte *)
        match r0 with
        | String c1 r1' =>
            let v1 := u8raw (ascii_byte c1) in
            let v1ok :=                                 (* accept-range: 0xE0→[0xA0,0xBF] (overlong); 0xED→[0x80,0x9F] (surrogate) *)
              if Z.eqb v0 224%Z then andb (Z.leb 160%Z v1) (Z.ltb v1 192%Z)
              else if Z.eqb v0 237%Z then andb (Z.leb 128%Z v1) (Z.ltb v1 160%Z)
              else isc v1 in
            match r1' with
            | String c2 r2 =>
                let v2 := u8raw (ascii_byte c2) in
                if andb v1ok (isc v2) then
                  (i32wrap (Z.lor (Z.lor
                           (Z.shiftl (Z.land v0 15%Z) 12%Z)
                           (Z.shiftl (Z.land v1 63%Z) 6%Z))
                           (Z.land v2 63%Z)), 3%Z) :: str_to_runes_w r2
                else (rerr, 1%Z) :: str_to_runes_w r0
            | EmptyString => (rerr, 1%Z) :: str_to_runes_w r0
            end
        | EmptyString => (rerr, 1%Z) :: nil
        end
      else if Z.ltb v0 245%Z then         (* 0xF0–0xF4: 4-byte *)
        match r0 with
        | String c1 r1' =>
            let v1 := u8raw (ascii_byte c1) in
            let v1ok :=                                 (* accept-range: 0xF0→[0x90,0xBF] (overlong); 0xF4→[0x80,0x8F] (>MaxRune) *)
              if Z.eqb v0 240%Z then andb (Z.leb 144%Z v1) (Z.ltb v1 192%Z)
              else if Z.eqb v0 244%Z then andb (Z.leb 128%Z v1) (Z.ltb v1 144%Z)
              else isc v1 in
            match r1' with
            | String c2 r2' =>
                let v2 := u8raw (ascii_byte c2) in
                match r2' with
                | String c3 r3 =>
                    let v3 := u8raw (ascii_byte c3) in
                    if andb v1ok (andb (isc v2) (isc v3)) then
                      (i32wrap (Z.lor (Z.lor (Z.lor
                               (Z.shiftl (Z.land v0 7%Z) 18%Z)
                               (Z.shiftl (Z.land v1 63%Z) 12%Z))
                               (Z.shiftl (Z.land v2 63%Z) 6%Z))
                               (Z.land v3 63%Z)), 4%Z) :: str_to_runes_w r3
                    else (rerr, 1%Z) :: str_to_runes_w r0
                | EmptyString => (rerr, 1%Z) :: str_to_runes_w r0
                end
            | EmptyString => (rerr, 1%Z) :: str_to_runes_w r0
            end
        | EmptyString => (rerr, 1%Z) :: nil
        end
      else                                             (* 0xF5–0xFF: invalid lead → error *)
        (rerr, 1%Z) :: str_to_runes_w r0
  end.
(* rune-only view = drop the consumed-width tags.  A manual fixpoint (not [List.map]) so the
   suppressed body pulls no generic [map] into the extraction closure. *)
Fixpoint str_runes_fst (rs : list (GoI32 * Z)) : list GoI32 :=
  match rs with
  | nil              => nil
  | cons (r, _) rest => cons r (str_runes_fst rest)
  end.
Definition str_to_runes (s : GoString) : list GoI32 := str_runes_fst (str_to_runes_w s).
Definition rune_bytes (r : GoI32) : GoString :=
  (* Go's [string(rune)] / [utf8.EncodeRune] replaces an out-of-range or surrogate rune with
     U+FFFD: Go tests [uint32(r) > MaxRune], so a NEGATIVE int32 is out of range —
     on our [Z] carrier that is simply [c0 < 0] (we guard [0 <= c0] below) — as is [r] in the
     UTF-16 surrogate range [0xD800,0xDFFF]. *)
  let c0 := i32raw r in
  (* out-of-range (incl. NEGATIVE — on the [Z] carrier that is [c0 < 0]) or UTF-16
     surrogate → U+FFFD. *)
  let c := if andb (andb (Z.leb 0 c0) (Z.leb c0 1114111))
                   (negb (andb (Z.leb 55296 c0) (Z.leb c0 57343)))
           then c0 else 65533%Z in
  if Z.ltb c 128 then
    String (byte_chr c) EmptyString
  else if Z.ltb c 2048 then
    String (byte_chr (Z.lor 192 (Z.shiftr c 6)))
   (String (byte_chr (Z.lor 128 (Z.land c 63))) EmptyString)
  else if Z.ltb c 65536 then
    String (byte_chr (Z.lor 224 (Z.shiftr c 12)))
   (String (byte_chr (Z.lor 128 (Z.land (Z.shiftr c 6) 63)))
   (String (byte_chr (Z.lor 128 (Z.land c 63))) EmptyString))
  else
    String (byte_chr (Z.lor 240 (Z.shiftr c 18)))
   (String (byte_chr (Z.lor 128 (Z.land (Z.shiftr c 12) 63)))
   (String (byte_chr (Z.lor 128 (Z.land (Z.shiftr c 6) 63)))
   (String (byte_chr (Z.lor 128 (Z.land c 63))) EmptyString))).
Fixpoint runes_to_str (rs : list GoI32) : GoString :=
  match rs with
  | nil => EmptyString
  | r :: rest => str_concat (rune_bytes r) (runes_to_str rest)
  end.

(** Codec verified by ROUND-TRIP: encode→decode is the identity for ASCII and for a 3-byte
    CJK code point (中 = U+4E2D = 20013, UTF-8 E4 B8 AD). *)
Example rune_roundtrip_ascii :
  str_to_runes (runes_to_str (i32wrap 65 :: i32wrap 66 :: nil))
    = i32wrap 65 :: i32wrap 66 :: nil.
Proof. vm_compute. reflexivity. Qed.
Example rune_roundtrip_cjk :
  str_to_runes (runes_to_str (i32wrap 20013 :: nil)) = i32wrap 20013 :: nil.
Proof. vm_compute. reflexivity. Qed.

(** Witnesses (machine-checked): INVALID UTF-8 decodes to U+FFFD (65533) per offending
    byte, advancing ONE byte — exactly Go's [utf8.DecodeRune].  [byte_chr v] is the byte
    with value [v]. *)
Example utf8_cont_as_lead :                  (* lone continuation 0x80 — not a valid lead → one U+FFFD *)
  str_to_runes (String (byte_chr 128) EmptyString) = i32wrap 65533 :: nil.
Proof. vm_compute. reflexivity. Qed.
Example utf8_overlong_2 :                     (* 0xC0 0x80 (overlong NUL): 0xC0 bad lead, 0x80 cont → two U+FFFD *)
  str_to_runes (String (byte_chr 192) (String (byte_chr 128) EmptyString))
    = i32wrap 65533 :: i32wrap 65533 :: nil.
Proof. vm_compute. reflexivity. Qed.
Example utf8_surrogate :                      (* 0xED 0xA0 0x80 (would be U+D800, a UTF-16 surrogate) → three U+FFFD *)
  str_to_runes (String (byte_chr 237) (String (byte_chr 160) (String (byte_chr 128) EmptyString)))
    = i32wrap 65533 :: i32wrap 65533 :: i32wrap 65533 :: nil.
Proof. vm_compute. reflexivity. Qed.
Example utf8_truncated_2 :                     (* 0xC2 with no continuation → one U+FFFD *)
  str_to_runes (String (byte_chr 194) EmptyString) = i32wrap 65533 :: nil.
Proof. vm_compute. reflexivity. Qed.
Example utf8_valid_2byte :                     (* 0xC2 0xA9 = U+00A9 (©) still decodes correctly *)
  str_to_runes (String (byte_chr 194) (String (byte_chr 169) EmptyString)) = i32wrap 169 :: nil.
Proof. vm_compute. reflexivity. Qed.

(** Single rune → string (Go's [string(rune)]): the 1-code-point UTF-8 string.  Reuses the
    [rune_bytes] encoder; lowers to the native [string(rune(r))] (the explicit [rune] cast
    keeps it out of the deprecated [string(int)] form). *)
Definition rune_to_str (r : GoI32) : GoString := rune_bytes r.
Example rune_to_str_ascii : rune_to_str (i32wrap 65) = "A"%string.
Proof. vm_compute. reflexivity. Qed.
(** An out-of-range or surrogate rune encodes to U+FFFD,
    exactly Go's [string(rune)].  Witnessed against the explicit FFFD encoding [EF BF BD]: a
    UTF-16 surrogate (0xD800), a code point past MaxRune (0x110000), and a NEGATIVE rune (-1,
    built by [i32_sub] so it is a genuine negative int32) all collapse to U+FFFD. *)
Example rune_to_str_surrogate : rune_to_str (i32wrap 55296) = rune_to_str (i32wrap 65533).
Proof. vm_compute. reflexivity. Qed.
Example rune_to_str_above_max : rune_to_str (i32wrap 1114112) = rune_to_str (i32wrap 65533).
Proof. vm_compute. reflexivity. Qed.
Example rune_to_str_negative :
  rune_to_str (i32_sub (i32wrap 0) (i32wrap 1)) = rune_to_str (i32wrap 65533).
Proof. vm_compute. reflexivity. Qed.

(** String COMPARISON (Go spec "Comparison operators": strings are comparable AND
    ordered).  [str_eqb] is Go [==] — byte-sequence equality (a THEOREM via
    [String.eqb]).  [str_ltb] is Go [<] — LEXICOGRAPHIC by BYTE VALUE, exactly Go's
    string ordering: compare byte-by-byte (unsigned 0..255), the first differing byte
    decides, and a proper prefix is [<] the longer string.  Both are pure, total
    operations on immutable byte sequences; the bodies are suppressed and each lowers
    to the bare Go operator ([a == b] / [a < b]).  [str_ltb] reuses the already-
    suppressed [ascii_byte] decoder (so it drags in no [nat_of_ascii]). *)
Definition str_eqb (a b : GoString) : bool := String.eqb a b.

(** Generic [comparable] CONSTRAINT (Go's [func F[K comparable](…)]).  A comparable type's
    equality is carried as a [ComparableW K] WITNESS — computational in Rocq (so [vm_compute] /
    proofs reduce), but the plugin ERASES it: a function with a [ComparableW (Tvar)] parameter
    drops that parameter at its declaration AND every call site, emits the corresponding type
    variable as [K comparable] (not [any]), and lowers the witness equality [cw_eqb] to native
    Go [==].  Faithful: on a Go-comparable type, [cw_eqb] decides the SAME equality [==] does, so
    erasing the dictionary to the native operator preserves meaning (the witness exists only so
    Rocq can compute/prove; Go's [comparable] supplies [==] structurally with no runtime dict). *)
(** Each comparison function DECIDES its type's equality — the evidence a sealed witness must carry. *)
Lemma i64_eqb_spec : forall x y, i64_eqb x y = true <-> x = y.
Proof.
  intros x y. unfold i64_eqb. split.
  - intro H. apply Z.eqb_eq in H. apply i64_ext; exact H.
  - intro H; subst; apply Z.eqb_refl.
Qed.
Lemma u64_eqb_spec : forall x y, u64_eqb x y = true <-> x = y.
Proof.
  intros x y. unfold u64_eqb. split.
  - intro H. apply Z.eqb_eq in H. apply u64_ext; exact H.
  - intro H; subst; apply Z.eqb_refl.
Qed.
Lemma str_eqb_spec : forall x y, str_eqb x y = true <-> x = y.
Proof. intros x y. unfold str_eqb. apply String.eqb_eq. Qed.

(** SEALED: [ComparableW] CARRIES the decidability proof
    [cw_ok] (SProp-erased, proof-irrelevant), so a bogus witness like [MkComparableW (fun _ _ => false) _]
    is UNCONSTRUCTABLE — its spec [forall x y, false = true <-> x = y] is false.  Hence erasing [cw_eqb] to
    native Go [==] is sound, not a forgeable claim.  The proof field erases (SProp), so extraction is
    unchanged: the whole witness is dropped by the plugin regardless of arity. *)
Record ComparableW (K : Type) : Type := MkComparableW {
  cw_eqb : K -> K -> bool ;
  cw_ok  : Squash (forall x y, cw_eqb x y = true <-> x = y) }.
Arguments MkComparableW {K} _ _.
Arguments cw_eqb {K} _.
Arguments cw_ok {K} _.
Definition ceqb {K} (w : ComparableW K) (a b : K) : bool := cw_eqb w a b.
(** Each instance is a [ComparableW]-typed Definition, suppressed by the plugin (the witness erases to
    native [==]); the [squash]ed spec is the seal that makes a bogus witness unconstructable. *)
Definition cw_i64 : ComparableW GoI64    := MkComparableW i64_eqb (squash i64_eqb_spec).
Definition cw_u64 : ComparableW GoU64    := MkComparableW u64_eqb (squash u64_eqb_spec).
Definition cw_str : ComparableW GoString := MkComparableW str_eqb (squash str_eqb_spec).

(** The seal is real (machine-checked): the always-[false] equality does NOT decide [GoI64] equality, so
    no [ComparableW GoI64] can wrap it — the forged witness [MkComparableW (fun _ _ => false) _] is
    unconstructable (its [cw_ok] obligation is the unprovable proposition below).  This is the safe-by-
    construction guarantee the erasure [cw_eqb w → Go ==] needs: a witness exists only when [cw_eqb]
    genuinely decides [=], hence agrees with Go's [==]. *)
Lemma bogus_eqb_undecidable :
  ~ (forall x y : GoI64, (fun _ _ : GoI64 => false) x y = true <-> x = y).
Proof. intro H. destruct (H (i64wrap 0%Z) (i64wrap 0%Z)) as [_ Hb]. discriminate (Hb eq_refl). Qed.

Fixpoint str_ltb (a b : GoString) : bool :=
  match a, b with
  | EmptyString,  EmptyString  => false   (* equal — not [<] *)
  | EmptyString,  String _ _   => true    (* "" < non-empty (prefix) *)
  | String _ _,   EmptyString  => false   (* non-empty not < "" *)
  | String ca ra, String cb rb =>
      let na := u8raw (ascii_byte ca) in  (* byte value 0..255 *)
      let nb := u8raw (ascii_byte cb) in
      if Z.ltb na nb then true
      else if Z.ltb nb na then false
      else str_ltb ra rb
  end.

(** Direct [>] / [>=] / [!=] for strings (total lexicographic order, no NaN, so
    [>=] is [¬(<)]).  Recognized by name and lowered to the direct Go operator. *)
Definition str_gtb  (a b : GoString) : bool := str_ltb b a.
Definition str_geb  (a b : GoString) : bool := negb (str_ltb a b).
Definition str_neqb (a b : GoString) : bool := negb (str_eqb a b).


(** ---- [range] over a string (Go spec "For statements: For range"): [for i, r := range s] ----
    Go ranges a STRING by UTF-8 code point: [i] is the BYTE offset of each code point's first
    byte, [r] the decoded rune.  Modeled faithfully on the rune view: [str_to_runes_w] decodes
    each rune WITH the number of source bytes it consumed, and the byte offsets are the running
    prefix sums of those CONSUMED widths — exactly Go's string-range index, even for invalid
    UTF-8 (machine-checked by [str_range_offsets] / [str_range_invalid_offsets] in main.v).
    ([rune_width] — utf8.RuneLen, a rune's ENCODED length — is a separate utility.)  [str_range] lowers
    to the NATIVE two-variable [for i, r := range s]; the [for_each_pairs]/[runes_with_offsets]
    model is proof-only (recognized by name, decl suppressed), so the emitted Go is the
    idiomatic range loop — never a [[]rune] materialisation.  The index is the Go [int]
    index type. *)
Definition rune_width (r : GoI32) : Z :=
  let c := i32raw r in
  if Z.ltb c 128   then 1    (* 1-byte (ASCII) *)
  else if Z.ltb c 2048  then 2    (* 2-byte *)
  else if Z.ltb c 65536 then 3    (* 3-byte *)
  else 4.                          (* 4-byte *)
(** Byte offsets are the running prefix sums of the CONSUMED SOURCE widths (the [int] tag from
    [str_to_runes_w]), so an invalid byte advances the offset by ONE — matching Go's range even
    for invalid UTF-8.  Re-encoding the decoded rune (via [rune_width]) would
    OVER-count: U+FFFD is 3 bytes encoded but a malformed byte consumes only 1. *)
Fixpoint runes_with_offsets (off : GoInt) (rs : list (GoI32 * Z)) : list (GoInt * GoI32) :=
  match rs with
  | nil              => nil
  | cons (r, w) rest => cons (off, r) (runes_with_offsets (int_add off (intwrap w)) rest)
  end.
Fixpoint for_each_pairs {A B : Type} (xs : list (A * B)) (body : A -> B -> IO unit) : IO unit :=
  match xs with
  | nil              => ret tt
  | cons (a, b) rest => bind (body a b) (fun _ => for_each_pairs rest body)
  end.
Definition str_range (s : GoString) (body : GoInt -> GoI32 -> IO unit) : IO unit :=
  for_each_pairs (runes_with_offsets (intwrap 0) (str_to_runes_w s)) body.
