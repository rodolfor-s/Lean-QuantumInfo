import QCryptLean.Quantum.Operators.Tensor

/-! # Tensor Algebra -/


namespace Quantum.Operators

open Matrix
open scoped Kronecker

variable {X Y : Type*} {n m k : ℕ}

/-- Enumerate a dependent function register using its component enumerations. -/
def familyEquiv {D : Fin k → Type*} {a : Fin k → ℕ} (e : ∀ i, D i ≃ Fin (a i)) :
    ((i : Fin k) → D i) ≃ Fin (∏ i, a i) :=
  (Equiv.piCongrRight e).trans finPiFinEquiv

end Quantum.Operators
