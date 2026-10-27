import QCryptLean.LOCC.SystemPresentation
import QCryptLean.QKD.Protocol

/-!
# Literal equality of protocol packages

This criterion compares the starting registers, designated key owners, and executable syntax.
It is stronger than equality of the denoted channels.
-/

namespace QKD.Protocol
open LOCC

variable {P : Type} [Fintype P] [DecidableEq P]

/-- Equal starting systems, designated parties, and programs give equal protocol packages. -/
theorem ext [SystemPresentation P] {p q : Protocol P} (hR : p.start = q.start)
    (hA : p.alice = q.alice) (hB : p.bob = q.bob) (hp : HEq p.program q.program) : p = q := by
  cases p
  cases q
  cases hR
  cases hA
  cases hB
  cases hp
  rfl

end QKD.Protocol
