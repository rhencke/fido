import Lean
import Fido
/-! The POC's assumption audit: the axiom closure of every `Fido.*` constant, and the two that are forbidden
    outright (`sorryAx` — an unfinished proof; `Lean.ofReduceBool` — `native_decide`, trusting the compiler).
    Run: `make lean-audit`.  Exit 1 on any forbidden axiom. -/
open Lean

def forbidden : List Name := [``sorryAx, ``Lean.ofReduceBool]

#eval show CoreM Unit from do
  let env ← getEnv
  -- FIDO_AUDIT_PREFIX narrows the audit to one module (`make lean-check MODULE=Fido.X`); default: all of Fido
  let pfx := ((← IO.getEnv "FIDO_AUDIT_PREFIX").getD "Fido").toName
  let mut used : NameSet := {}
  let mut bad : Array (Name × Name) := #[]
  let mut n := 0
  -- FIDO_AUDIT_VERBOSE=1 prints each constant that uses Classical.choice: the port tracks where classical
  -- reasoning enters, since the Rocq theory is constructive and axiom-free
  let verbose := (← IO.getEnv "FIDO_AUDIT_VERBOSE").isSome
  for (c, _) in env.constants.toList do
    if pfx.isPrefixOf c && !c.isInternal then
      n := n + 1
      let axs ← collectAxioms c
      if verbose && axs.contains ``Classical.choice then IO.println s!"  classical: {c}"
      for a in axs do
        used := used.insert a
        if forbidden.contains a then bad := bad.push (c, a)
  IO.println s!"fido-lean audit: {n} {pfx}.* constants; axioms used anywhere: {used.toList}"
  for (c, a) in bad do IO.println s!"  FORBIDDEN {a} in {c}"
  if !bad.isEmpty then throwError s!"fido-lean audit FAILED — {bad.size} forbidden axiom use(s)"
  IO.println "fido-lean audit OK — no sorryAx, no ofReduceBool"
