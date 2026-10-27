import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Boundary.DirectSum
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.Quantum.Operators.Basic

/-!
# Operator blocks at complete public exits

Operator blocks at complete public exits.
-/

open scoped Matrix BigOperators
open LOCC LOCC.Boundary
variable {P : Type} [Fintype P] [DecidableEq P]

noncomputable section

/-- The operator block of one complete public exit, written as a Kraus sandwich. -/
def _root_.LOCC.Boundary.exitBlock (B : Boundary P) (e : B.Exit) (rho :
  Quantum.Operators.Op B.space) :
    Quantum.Operators.Op ((B.system e).total) :=
  (Boundary.exitKraus B e)ᴴ * rho * Boundary.exitKraus B e

@[simp] theorem _root_.LOCC.Boundary.exitBlock_apply (B : Boundary P) (e : B.Exit)
    (rho : Quantum.Operators.Op B.space) (a b : (B.system e).total) :
    LOCC.Boundary.exitBlock B e rho a b = rho ⟨e, a⟩ ⟨e, b⟩ := by
  simp [LOCC.Boundary.exitBlock, Matrix.mul_apply, Boundary.exitKraus, sigmaInclKraus]

end
