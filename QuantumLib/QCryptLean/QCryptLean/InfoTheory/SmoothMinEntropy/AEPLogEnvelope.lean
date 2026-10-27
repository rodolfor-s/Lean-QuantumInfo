import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.RtFunction
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPBits
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPEnvelope
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPRates
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPWeightBudget
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPWeights
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.CollisionReference
import QCryptLean.InfoTheory.SmoothMinEntropy.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Normalized
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-! # Logarithmic spectral envelopes and the reference entropy bound -/
namespace InfoTheory.SmoothMinEntropy.AEP.Spectral
open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder
variable {C Q : Type*} [Fintype C] [Fintype Q] [DecidableEq C] [DecidableEq Q]

omit [DecidableEq C] in
/-- Every nonnegative tilted moment of a normalized feasible CQ state is positive. -/
theorem moment_pos (ρ : CQState C Q) (hρ : ∑ c, (ρ.stateMap c).trace = 1)
    (σ : DensityOp Q) (hscale : HasScale ρ σ.toSubDensityOp) {s : ℝ} (hs : 0 ≤ s) :
    0 < ∑ c, ((ρ.stateMap c).toOp ^ (1 + s) * σ.toOp ^ (-s)).trace.re := by
  rw [← sum_weight_mul_exp ρ σ hscale hs]
  obtain ⟨p, hp, hw⟩ := (Finset.sum_pos_iff_of_nonneg (fun p _ => weight_nonneg ρ σ p)).mp
    (show 0 < ∑ p, weight ρ σ p by rw [sum_weight, hρ]; norm_num)
  exact (Finset.sum_pos_iff_of_nonneg (fun p _ =>
    mul_nonneg (weight_nonneg ρ σ p) (Real.exp_pos _).le)).mpr
      ⟨p, hp, mul_pos hw (Real.exp_pos _)⟩

/-- The exact cumulant bound keeps the exponential remainder at the Bennett tilt. -/
theorem logb_moment_le (ρ : CQState C Q) (hρ : ∑ c, (ρ.stateMap c).trace = 1)
    (σ : DensityOp Q) (hscale : HasScale ρ σ.toSubDensityOp) {s : ℝ} (hs : 0 ≤ s)
    (hrange : s * Real.log (IID.rtBoundBase ρ σ) ≤ Real.log 2) :
    Real.logb 2 (∑ c, ((ρ.stateMap c).toOp ^ (1 + s) * σ.toOp ^ (-s)).trace.re) ≤
      -s * referenceCondVonNeumannBits ρ hρ σ +
        (Real.exp (s * Real.log (IID.rtBoundBase ρ σ)) -
          s * Real.log (IID.rtBoundBase ρ σ) - 1) / Real.log 2 := by
  have henv := moment_le_rennerRt_sub_add_one ρ hρ σ hscale hs hrange
  have hlog := Real.log_le_sub_one_of_pos (moment_pos ρ hρ σ hscale hs)
  have hμ : 0 < IID.rtBoundBase ρ σ := by
    unfold IID.rtBoundBase
    linarith [ρ.tracedSquareTimesInvFactor_nonneg σ, Nat.cast_nonneg (α := ℝ) ρ.classicalRank]
  unfold InfoTheory.SmoothMinEntropy.rennerRt at henv
  rw [Real.rpow_def_of_pos hμ, mul_comm (Real.log _) s] at henv
  rw [Real.logb, div_le_iff₀ (Real.log_pos one_lt_two)]
  have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  field_simp
  nlinarith

/-- The reference conditional bit entropy is at most the logarithm of the Renner base. -/
theorem referenceCondVonNeumannBits_le_logb_rtBoundBase (ρ : CQState C Q)
    (hρ : ∑ c, (ρ.stateMap c).trace = 1) (σ : DensityOp Q)
    (hscale : HasScale ρ σ.toSubDensityOp) :
    referenceCondVonNeumannBits ρ hρ σ ≤ Real.logb 2 (IID.rtBoundBase ρ σ) := by
  have hw := (sum_weight ρ σ).trans hρ
  have hJ := convexOn_exp.map_sum_le (t := Finset.univ) (w := weight ρ σ)
    (p := fun p => -logRatio ρ σ p) (fun p _ => weight_nonneg ρ σ p) hw
    (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul, mul_neg, Finset.sum_neg_distrib,
    sum_weight_mul_logRatio ρ hρ σ, neg_mul, neg_neg] at hJ
  have hb : (ρ.classicalRank : ℝ) ≤ IID.rtBoundBase ρ σ := by
    unfold IID.rtBoundBase
    linarith [ρ.tracedSquareTimesInvFactor_nonneg σ]
  have hlog := Real.log_le_log (Real.exp_pos _)
    (hJ.trans ((sum_weight_mul_exp_neg_le ρ σ hscale).trans hb))
  rw [Real.log_exp] at hlog
  rw [Real.logb, le_div_iff₀ (Real.log_pos one_lt_two)]
  nlinarith

end InfoTheory.SmoothMinEntropy.AEP.Spectral
