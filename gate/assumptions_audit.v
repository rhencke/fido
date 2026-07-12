(** The SOUND zero-project-axiom gate: load every Fido module, then have the Fido Audit Assumptions
    command enumerate the compiled global environment and reject any Fido constant with an axiomatic
    body (Axiom/Parameter/Admitted — including UNUSED ones).  This replaces the source-text scanner (a
    lexer over text is fooled by control-command prefixes, no-space attributes, module aliases, etc.).
    gate/axiom_gate.v remains the complementary check: Print Assumptions on the public surfaces guards
    against EXTERNAL (non-Fido) axioms entering a proof closure. *)
From Fido Require Import digits Ints FilePath FMap GoAST GoCompile GoSafe GoRender GoEmit.
Declare ML Module "fido.emit".
Fido Audit Assumptions.
