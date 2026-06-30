(** ============================================================================
    GoSemAuthority.v — POST-IMPORT model-authority SEAL for GoSem.

    Compiled AFTER [Fido.GoSem] (a real dune module, in the build's [(modules …)] list), so it sees the module's
    FINAL contents — unlike a SAME-FILE [Fail Check], which only sees declarations BEFORE its own line and is
    therefore APPEND-bypassable (a later [Definition]/[Let] slips past it; Codex 2026-06-30).

    Invariant (SCOPED, honest): GoSem's string comparisons DELEGATE to the MODEL's Go string order
    ([builtins.v]'s [str_eqb] / [str_neqb] / [str_ltb] / [str_gtb] / [str_geb]); GoSem must define NONE of its
    own [str_*] order primitive.  Each [Fail Check] below FAILS THE BUILD iff [Fido.GoSem] exports that name —
    robust against ANY Rocq definition syntax ([Definition]/[Fixpoint]/[Program …]/[Let]/[Local]/[#[global]]/
    multiline attributes), because it consults Rocq's name resolution on the COMPILED module, not source text.
    A bare [str_ltb] inside GoSem keeps resolving to the imported MODEL constant; only a GoSem-OWN binding makes
    [Check Fido.GoSem.str_ltb] succeed, which trips the [Fail].

    SCOPE: this seals GoSem — the layer that computes string comparisons, and where the duplication occurred.
    It makes NO claim about other modules (they do not compute Go string comparisons).  The live delegation is
    additionally pinned in GoSem.v by [str_cmp_op]-branch reflexivity examples ([str_cmp_*_model]).
    ============================================================================ *)
From Fido Require GoSem.

Fail Check Fido.GoSem.str_eqb.
Fail Check Fido.GoSem.str_neqb.
Fail Check Fido.GoSem.str_ltb.
Fail Check Fido.GoSem.str_gtb.
Fail Check Fido.GoSem.str_geb.
Fail Check Fido.GoSem.str_leb.
