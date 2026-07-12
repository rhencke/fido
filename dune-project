(lang dune 3.21)
(name fido)

(using rocq 0.11)

; The one tiny transport plugin (Fido Emit) — its findlib package (must match the project name).
(package
 (name fido)
 (allow_empty)   ; the prover stage builds the theory WITHOUT the plugin dir, leaving this package empty
 (synopsis "Fido — proved Go generator; the Fido Emit transport plugin"))
