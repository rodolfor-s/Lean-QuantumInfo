import QCryptLean.InfoTheory.Renyi.ConditionalVariance.CQReference
import QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPRates
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPWeights
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Normalized
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.StateOperations

/-! # The spectral exponential-moment budget of a CQ state -/
namespace InfoTheory.SmoothMinEntropy.AEP.Spectral
open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open private nsW nsL nsW_nonneg nsW_sum nsW_exp_neg_le
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
open private mulVec_eq_zero_of_le
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.CQReference
variable {C Q : Type*} [Fintype C] [Fintype Q] [DecidableEq Q]

/-- The inverse-likelihood moment counts only classical blocks of positive weight. -/
theorem sum_weight_mul_exp_neg_le (ρ : CQState C Q) (σ : DensityOp Q)
    (hscale : HasScale ρ σ.toSubDensityOp) :
    ∑ p, weight ρ σ p * Real.exp (-logRatio ρ σ p) ≤ (ρ.classicalRank : ℝ) := by
  classical
  obtain ⟨t, ht⟩ := hscale
  rw [Fintype.sum_prod_type]
  have he : (ρ.classicalRank : ℝ) =
      ∑ c : C, if 0 < (ρ.stateMap c).trace then (1 : ℝ) else 0 := by
    simp [CQState.classicalRank, Finset.sum_boole]
  rw [he]
  apply Finset.sum_le_sum
  intro c _
  by_cases hc : 0 < (ρ.stateMap c).trace
  · rw [ite_eq_left hc]
    have hle : (ρ.stateMap c).toOp ≤ (t : ℂ) • σ.toOp := Matrix.le_iff.mpr
      ((opLe_iff_posSemidef_sub (ρ.stateMap c).isHermitian
        (σ.posSemidef.smul (Complex.zero_le_real.mpr ht.1)).isHermitian).mp (ht.2 c))
    have hsup (v : Q → ℂ) (hv : σ.toOp *ᵥ v = 0) : (ρ.stateMap c).toOp *ᵥ v = 0 :=
      mulVec_eq_zero_of_le (ρ.stateMap c).posSemidef.nonneg hle
        (by simp [Matrix.smul_mulVec, hv])
    have h := nsW_exp_neg_le (ρ.stateMap c).isHermitian σ.isHermitian
      (ρ.stateMap c).posSemidef.nonneg σ.posSemidef.nonneg hsup
    simpa only [weight, logRatio, σ.trace_one, Complex.one_re] using h
  · rw [ite_eq_right hc]
    have hz : (ρ.stateMap c).trace = 0 :=
      le_antisymm (le_of_not_gt hc) (ρ.stateMap c).trace_nonneg
    have hw : ∀ p : Q × Q, weight ρ σ (c, p) = 0 := by
      intro p
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => weight_nonneg ρ σ (c, p))).mp
        ((nsW_sum (ρ.stateMap c).isHermitian σ.isHermitian).trans hz) p (Finset.mem_univ p)
    simp only [hw, zero_mul, Finset.sum_const_zero, le_refl]

/-- The positive unit-tilt moment is the exact collision factor against the support inverse. -/
theorem sum_weight_mul_exp_one (ρ : CQState C Q) (σ : DensityOp Q)
    (hscale : HasScale ρ σ.toSubDensityOp) :
    ∑ p, weight ρ σ p * Real.exp (logRatio ρ σ p) = ρ.tracedSquareTimesInvFactor σ := by
  have h := sum_weight_mul_exp ρ σ hscale (s := 1) zero_le_one
  rw [CQState.tracedSquareTimesInvFactor, Complex.re_sum]
  simp only [one_mul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro c _
  rw [show (1 : ℝ) + 1 = (2 : ℕ) by norm_num,
    CFC.rpow_natCast _ 2 (ρ.stateMap c).posSemidef.nonneg, pow_two]

/-- The symmetric likelihood budget is bounded by the unchanged Renner base. -/
theorem sum_weight_mul_exp_add_exp_neg_add_two_le (ρ : CQState C Q)
    (hρ : ∑ c, (ρ.stateMap c).trace = 1) (σ : DensityOp Q)
    (hscale : HasScale ρ σ.toSubDensityOp) :
    ∑ p, weight ρ σ p *
      (Real.exp (logRatio ρ σ p) + Real.exp (-logRatio ρ σ p) + 2) ≤
        IID.rtBoundBase ρ σ := by
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_weight, hρ,
    one_mul, sum_weight_mul_exp_one ρ σ hscale]
  have h := sum_weight_mul_exp_neg_le ρ σ hscale
  unfold IID.rtBoundBase
  linarith

end InfoTheory.SmoothMinEntropy.AEP.Spectral
