-- Port of Version.v (lean/README.md).  No divergences.
import Fido.Prelude

namespace Fido.Version

inductive Version : Type
  | Go1_23
  deriving DecidableEq, Repr

open Version

/-- The `go` directive value: no leading `v`, no patch component. -/
def render (v : Version) : Str :=
  match v with
  | Go1_23 => str! "1.23"

theorem render_go1_23 : render Go1_23 = str! "1.23" := rfl

def equalb (a b : Version) : Bool :=
  match a, b with
  | Go1_23, Go1_23 => true

theorem equalb_spec : ∀ a b, equalb a b = true ↔ a = b := by
  intro a b; cases a; cases b; simp [equalb]

end Fido.Version
