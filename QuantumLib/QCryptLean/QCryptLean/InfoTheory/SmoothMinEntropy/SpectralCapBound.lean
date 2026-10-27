import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.FeasibleFloor
import QCryptLean.InfoTheory.SmoothMinEntropy.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.InfoTheory.SmoothMinEntropy.SpectralCapMoment
import QCryptLean.InfoTheory.SmoothMinEntropy.SpectralCapState
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.StateOperations

/-! # Smooth min-entropy from a spectral cap -/


namespace InfoTheory.SmoothMinEntropy.SpectralCap
open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder
variable {C Q : Type*} [Fintype C] [Fintype Q] [DecidableEq C] [DecidableEq Q]
  [Nonempty C] [Nonempty Q]

omit [Nonempty C] in
/-- A tilted-moment budget yields a fixed-reference smooth entropy floor on the full CQ ball. -/
theorem ofReal_le_smoothMinEntropy_of_moment_bound (ρ : CQState C Q)
    (hρ : ∑ c, (ρ.stateMap c).trace = 1) (σ : SubDensityOp Q) (hscale : HasScale ρ σ)
    (k : ℝ) {s ε : ℝ} (hs : 0 ≤ s) (hε : 0 ≤ ε)
    (hbudget : 2 * ((2 : ℝ) ^ (-k)) ^ (-s) *
      (∑ c, ((ρ.stateMap c).toOp ^ (1 + s) * σ.toOp ^ (-s)).trace.re) ≤ ε ^ 2) :
    ENNReal.ofReal k ≤ smoothMinEntropy ε ρ σ := by
  classical
  have hell : 0 < (2 : ℝ) ^ (-k) := Real.rpow_pos_of_pos (by norm_num) _
  let τ := cqState ρ σ (2 ^ (-k)) hell.le
  have htrace : 1 - τ.toJointDensity.trace ≤ (2 ^ (-k)) ^ (-s) *
      (∑ c, ((ρ.stateMap c).toOp ^ (1 + s) * σ.toOp ^ (-s)).trace.re) := by
    obtain ⟨t, ht⟩ := hscale
    rw [CQState.toJointDensity_trace]
    conv_lhs => lhs; rw [← hρ]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c _
    apply trace_sub_block_le_moment (ρ.stateMap c).toPosSemidefOp σ.toPosSemidefOp
      (t := t) _ hell hs
    exact Matrix.le_iff.mpr ((opLe_iff_posSemidef_sub (ρ.stateMap c).isHermitian
      (σ.posSemidef.smul (Complex.zero_le_real.mpr ht.1)).isHermitian).mp (ht.2 c))
  have hdist : ρ.purifiedDistance τ ≤ ε := by
    apply (cqState_purifiedDistance_le ρ hρ σ hell.le).trans
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hε, by linarith⟩
  exact (ofReal_le_minEntropy_of_isFeasible τ σ k
    (cqState_isFeasible ρ σ hell.le)).trans
      (minEntropy_le_smoothMinEntropy_of_purifiedDistance_le ρ τ σ hdist)

end InfoTheory.SmoothMinEntropy.SpectralCap
