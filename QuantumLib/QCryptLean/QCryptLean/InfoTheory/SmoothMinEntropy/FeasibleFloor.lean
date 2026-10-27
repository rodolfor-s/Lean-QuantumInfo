import Mathlib.Analysis.SpecialFunctions.Pow.Real
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.MinEntropy
import QCryptLean.Quantum.Operators.Basic

/-! # Exponential feasibility certifies extended min-entropy -/
namespace InfoTheory.SmoothMinEntropy
open Quantum.Operators
variable {C Q : Type*} [Fintype C] [Fintype Q]

/-- A feasible exponential coefficient certifies an entropy floor without a weight condition. -/
theorem ofReal_le_minEntropy_of_isFeasible (ρ : CQState C Q) (σ : SubDensityOp Q)
    (k : ℝ) (h : IsFeasible ρ σ (2 ^ (-k))) :
    ENNReal.ofReal k ≤ minEntropy ρ σ := by
  by_cases hp : 0 < minScale ρ σ
  · rw [minEntropy_eq_of_pos ρ σ hp]
    apply ENNReal.ofReal_le_ofReal
    apply (le_div_iff₀ (Real.log_pos one_lt_two)).mpr
    have hl := Real.log_le_log hp (minScale_le_of_isFeasible ρ σ h)
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hl
    change k * Real.log 2 ≤ -Real.log (minScale ρ σ)
    linarith
  · simp [minEntropy, hp, show HasScale ρ σ from ⟨_, h⟩]

end InfoTheory.SmoothMinEntropy
