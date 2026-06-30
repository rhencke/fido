(** ============================================================================
    GoSemAuthority.v — a POST-IMPORT, TOP-LEVEL dead-name tripwire for GoSem.

    The AUTHORITY guarantee for the LIVE string-comparison path is NOT here — it is the [str_cmp_*_model]
    reflexivity pins in GoSem.v, which prove each [str_cmp_op] branch IS the fully qualified model constant
    [Fido.builtins.str_*] (shadow-immune; a fork that reroutes a branch breaks a pin).

    This module is only a SECONDARY tripwire: compiled AFTER [Fido.GoSem] (a real dune module), it [Fail Check]s
    that GoSem exports no TOP-LEVEL [str_*] of its own, FAILING THE BUILD on a direct top-level fork.  Being
    post-import it sees GoSem's FINAL contents (an append-after-the-check cannot slip past, unlike a same-file
    [Fail Check]).  LIMITS (honest): it only catches a TOP-LEVEL [Fido.GoSem.str_*] — a nested-module/[Import]
    shadow does NOT export that name, so this tripwire would miss it; that case is what the qualified-constant
    branch pins in GoSem.v rule out instead.  No claim about other modules.
    ============================================================================ *)
From Fido Require GoSem.

Fail Check Fido.GoSem.str_eqb.
Fail Check Fido.GoSem.str_neqb.
Fail Check Fido.GoSem.str_ltb.
Fail Check Fido.GoSem.str_gtb.
Fail Check Fido.GoSem.str_geb.
Fail Check Fido.GoSem.str_leb.
