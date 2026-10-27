import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.Purified
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.StateOperations

/-! # Weight bounds for real-valued smooth entropy optimization -/

noncomputable section
namespace InfoTheory.SmoothMinEntropy
open Matrix Quantum.Operators Quantum.Metrics
open scoped ComplexOrder
variable {C Q : Type*} [Fintype C] [Fintype Q] [Nonempty C]

/-- A feasible reference bounds the average classical weight by the optimal scale. -/
theorem weight_div_card_le_minScale_of_hasScale (ρ : CQState C Q) (σ : SubDensityOp Q)
    (h : HasScale ρ σ) :
    (∑ c, (ρ.stateMap c).trace) / Fintype.card C ≤ minScale ρ σ := by
  have hc : (0 : ℝ) < Fintype.card C := Nat.cast_pos.mpr Fintype.card_pos
  apply le_csInf h
  intro t ht
  apply (div_le_iff₀ hc).mpr
  have hh (c : C) : (ρ.stateMap c).trace ≤ t := by
    have hp := (opLe_iff_posSemidef_sub (ρ.stateMap c).isHermitian
      (σ.posSemidef.smul (Complex.zero_le_real.mpr ht.1)).isHermitian).mp (ht.2 c)
    have hp' := (Complex.nonneg_iff.mp hp.trace_nonneg).1
    simp only [trace_sub, trace_smul, Complex.sub_re, smul_eq_mul,
      Complex.re_ofReal_mul, sub_nonneg] at hp'
    exact hp'.trans ((mul_le_mul_of_nonneg_left σ.trace_le_one ht.1).trans_eq (mul_one _))
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using
    Finset.sum_le_sum (s := Finset.univ) (fun c _ => hh c)

variable [DecidableEq C] [Nonempty Q]
/-- A CQ smoothing witness loses at most twice its purified-distance radius in total weight. -/
theorem CQState.weight_sub_two_mul_le_of_purifiedDistance_le (ρ τ : CQState C Q)
    {ε : ℝ} (h : ρ.purifiedDistance τ ≤ ε) :
    (∑ c, (ρ.stateMap c).trace) - 2 * ε ≤ ∑ c, (τ.stateMap c).trace := by
  have hd := (traceDistanceGen_le_purifiedDistance ρ.toJointDensity τ.toJointDensity).trans h
  have hn := traceNorm_nonneg (ρ.toJointDensity.toOp - τ.toJointDensity.toOp)
  have ha := le_abs_self (ρ.toJointDensity.trace - τ.toJointDensity.trace)
  change (1 / 2) * traceNorm _ + (1 / 2) * |(ρ.toJointDensity.toOp.trace -
    τ.toJointDensity.toOp.trace).re| ≤ ε at hd
  rw [Complex.sub_re] at hd
  change _ ≤ ε at hd
  simp only [CQState.toJointDensity_trace] at ha
  change (1 / 2) * traceNorm _ + (1 / 2) * |ρ.toJointDensity.trace -
    τ.toJointDensity.trace| ≤ ε at hd
  rw [CQState.toJointDensity_trace, CQState.toJointDensity_trace] at hd
  linarith

/-- A strictly positive weight floor bounds the signed smooth optimization domain above. -/
theorem smoothMinEntropyReal_bddAbove_of_weight (ε : ℝ) (ρ : CQState C Q)
    (hweight : 2 * ε < ∑ c, (ρ.stateMap c).trace) (σ : SubDensityOp Q) :
    BddAbove (Set.ofPred (IsInSmoothedSetReal ε ρ σ)) := by
  let w := ((∑ c, (ρ.stateMap c).trace) - 2 * ε) / Fintype.card C
  have hw : 0 < w := div_pos (sub_pos.mpr hweight) (Nat.cast_pos.mpr Fintype.card_pos)
  refine ⟨max 0 (-Real.log w / Real.log 2), ?_⟩
  rintro t ⟨τ, rfl, hd⟩
  by_cases hf : HasScale τ σ
  · have hb : w ≤ minScale τ σ :=
      (div_le_div_of_nonneg_right (ρ.weight_sub_two_mul_le_of_purifiedDistance_le τ hd)
        (Nat.cast_nonneg _)).trans (weight_div_card_le_minScale_of_hasScale τ σ hf)
    exact (div_le_div_of_nonneg_right (neg_le_neg (Real.log_le_log hw hb))
      (Real.log_pos one_lt_two).le).trans (le_max_right _ _)
  · simp only [minEntropyReal, minScale_eq_zero_of_not_hasScale τ σ hf,
      Real.log_zero, neg_zero, zero_div]
    exact le_max_left _ _
end InfoTheory.SmoothMinEntropy
