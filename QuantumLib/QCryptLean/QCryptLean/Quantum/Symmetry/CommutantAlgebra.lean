import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Commutant
import QCryptLean.Quantum.Symmetry.Dimension
import QCryptLean.Quantum.Symmetry.TensorPowerSpan

/-! # Commutant Algebra -/


noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators

variable {X : Type*} [Fintype X] [DecidableEq X] {d k : ℕ}

/-- Schur--Weyl commutant identity on function registers. -/
theorem commutant_matrixTensorPow_eq_permSpan :
    commutant (Set.range fun A : Op X => Op.tensorPow A k) = permSpan (X := X) k := by
  rw [commutant_span, span_tensorPow_eq_permCommutant]
  let ρ : Equiv.Perm (Fin k) →* Op (Fin k → X) :=
    { toFun := permutationRepresentation
      map_one' := tensorPermutation_one
      map_mul' := fun σ τ => (tensorPermutation_mul σ τ).symm }
  exact finiteGroup_bicommutant ρ

end Quantum.Symmetry
