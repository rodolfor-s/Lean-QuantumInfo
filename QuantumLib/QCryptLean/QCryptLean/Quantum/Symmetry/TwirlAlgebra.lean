import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.Inequality
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Dimension
import QCryptLean.Quantum.Symmetry.Twirl

/-! # Twirl Algebra -/


noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators Quantum.Metrics

variable {X : Type*} [Fintype X] [DecidableEq X] {d k : ℕ}

/-- Trace distance contracts under permutation symmetrization. -/
theorem symmetrize_contracts_distance (ρ σ : DensityOp (Fin k → X)) :
    traceDistance (symmetrize ρ).toOp (symmetrize σ).toOp ≤
      traceDistance ρ.toOp σ.toOp := by
  let := ρ.nonempty
  exact traceDistance_apply_le (symmetrizeChannel X k)
    (isChannel_twirl permutationUnitary) ρ.toOp σ.toOp

end Quantum.Symmetry
