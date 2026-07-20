(lang dune 3.21)
(name fido)

(using rocq 0.11)

; The findlib package for the certified materialization plugin (must match the project name).  The prover
; stage builds the theory WITHOUT the plugin dir, so the package may be empty there.
(package
 (name fido)
 (allow_empty)
 (synopsis "Fido — a proved Go generator; the certified materialization plugin"))
