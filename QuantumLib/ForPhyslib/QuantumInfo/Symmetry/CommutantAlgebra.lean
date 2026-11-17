import QuantumLib.ForMathlib.LinearAlgebra.Matrix.TensorPermutation
import QuantumLib.ForPhyslib.QuantumInfo.Operators.Basic
import QuantumLib.ForPhyslib.QuantumInfo.Operators.Tensor
import QuantumLib.ForPhyslib.QuantumInfo.Symmetry.Basic
import QuantumLib.ForPhyslib.QuantumInfo.Symmetry.Commutant
import QuantumLib.ForPhyslib.QuantumInfo.Symmetry.Dimension
import QuantumLib.ForPhyslib.QuantumInfo.Symmetry.TensorPowerSpan

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
