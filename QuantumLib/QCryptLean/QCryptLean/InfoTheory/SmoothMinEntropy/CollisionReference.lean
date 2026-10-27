import QCryptLean.InfoTheory.Renyi.CQReference
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDBennett
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPBits
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPRates
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Normalized
import QCryptLean.Math.LinearAlgebra.Matrix.InverseTrace
import QCryptLean.Math.LinearAlgebra.Matrix.PositiveTrace
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.StateOperations

/-! # Native collision bounds at the quantum marginal

The support inverse uses real CFC power minus one and local matrix star order.
-/
noncomputable section
namespace InfoTheory.SmoothMinEntropy
open Matrix Quantum.Operators
open scoped MatrixOrder ComplexOrder
variable {C Q : Type*} [Fintype C] [Fintype Q]

/-- A normalized CQ state has a nonempty classical support. -/
theorem CQState.classicalRank_pos (ρ : CQState C Q)
    (hρ : ∑ c, (ρ.stateMap c).trace = 1) : 0 < ρ.classicalRank := by
  classical
  apply Finset.card_pos.mpr
  obtain ⟨c, _, hc⟩ := Finset.exists_lt_of_sum_lt
    (show ∑ _ : C, (0 : ℝ) < ∑ c, (ρ.stateMap c).trace by simp [hρ])
  exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩⟩

/-- Collision trace is nonnegative for every positive reference. -/
theorem CQState.tracedSquareTimesInvFactor_nonneg [DecidableEq Q]
    (ρ : CQState C Q) (σ : DensityOp Q) : 0 ≤ ρ.tracedSquareTimesInvFactor σ := by
  rw [CQState.tracedSquareTimesInvFactor, Complex.re_sum]
  apply Finset.sum_nonneg
  intro c _
  have hp : ((ρ.stateMap c).toOp * (ρ.stateMap c).toOp).PosSemidef := by
    simpa only [(ρ.stateMap c).isHermitian.eq] using
      posSemidef_conjTranspose_mul_self (ρ.stateMap c).toOp
  exact (Complex.nonneg_iff.mp (hp.trace_mul_nonneg
    (nonneg_iff_posSemidef.mp CFC.rpow_nonneg))).1

/-- At the normalized quantum marginal the collision trace is at most one. -/
theorem CQState.tracedSquareTimesInvFactor_quantumMarginal_le_one [DecidableEq Q]
    (ρ : CQState C Q) (hρ : ∑ c, (ρ.stateMap c).trace = 1) :
    ρ.tracedSquareTimesInvFactor (ρ.quantumMarginalDensityOp hρ) ≤ 1 := by
  rw [CQState.tracedSquareTimesInvFactor, Complex.re_sum]
  apply le_trans (b := ∑ c, (ρ.stateMap c).trace) _ hρ.le
  apply Finset.sum_le_sum
  intro c _
  exact (ρ.stateMap c).posSemidef.trace_sq_mul_rpow_neg_one_le
    (ρ.quantumMarginalDensityOp hρ).posSemidef (ρ.stateMap_le_quantumMarginal c)

/-- The marginal is a feasible reference with scale one. -/
theorem hasScale_quantumMarginalDensityOp (ρ : CQState C Q)
    (hρ : ∑ c, (ρ.stateMap c).trace = 1) :
    HasScale ρ (ρ.quantumMarginalDensityOp hρ).toSubDensityOp := by
  refine ⟨1, zero_le_one, fun c => ?_⟩
  rw [Complex.ofReal_one, one_smul]
  exact opLe_of_posSemidef_sub (Matrix.le_iff.mp (ρ.stateMap_le_quantumMarginal c))

/-- The exact Bennett correction is bounded by the classical rank plus three. -/
theorem AEP.IID.bennettPenalty_quantumMarginal_le [DecidableEq Q]
    (ρ : CQState C Q) (hρ : ∑ c, (ρ.stateMap c).trace = 1)
    (k : ℕ) (ε : ℝ) (r : ℕ) (hrank : ρ.classicalRank ≤ r) :
    bennettPenalty ρ (ρ.quantumMarginalDensityOp hρ) k ε ≤
      Real.logb 2 ((r : ℝ) + 3) * InfoTheory.SmoothMinEntropy.bennettTiltWidth k ε := by
  have hn := ρ.tracedSquareTimesInvFactor_nonneg (ρ.quantumMarginalDensityOp hρ)
  have hb := ρ.tracedSquareTimesInvFactor_quantumMarginal_le_one hρ
  have hr : (ρ.classicalRank : ℝ) ≤ r := by exact_mod_cast hrank
  apply mul_le_mul_of_nonneg_right _
    (InfoTheory.SmoothMinEntropy.bennettTiltWidth_nonneg k ε)
  apply Real.logb_le_logb_of_le (by norm_num)
  · dsimp [rtBoundBase]
    positivity
  · dsimp [rtBoundBase]
    linarith

end InfoTheory.SmoothMinEntropy
