import QCryptLean.InfoTheory.RelativeEntropy.Inequalities
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.BennettScalar
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IID.TensorPower
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDBennett
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPBits
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPBitsBounds
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPLogEnvelope
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPRates
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.CollisionReference
import QCryptLean.InfoTheory.SmoothMinEntropy.Normalized
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.InfoTheory.VonNeumannEntropy.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-! # The exact rank-capped Renner IID bound on natural registers -/

noncomputable section

namespace InfoTheory.SmoothMinEntropy.AEP.IID

open Quantum.Operators InfoTheory.VonNeumannEntropy

/-- Rank-capped Renner AEP, retaining the `2 log₂(r + 3)` correction and every positive radius.
The Bennett bound controls its correction inside the tilt regime; outside that regime
the proposed floor is nonpositive. -/
theorem ofReal_mul_sub_le_smoothMinEntropy_of_classicalRank_le
    {C Q : Type*} [Fintype C] [DecidableEq C] [Fintype Q]
    (ρ : CQState C Q) (hρ : ∑ c, (ρ.stateMap c).trace = 1)
    (n : ℕ) [NeZero n] (ε : ℝ) (hε : 0 < ε) (r : ℕ) (hrank : ρ.classicalRank ≤ r) :
    ENNReal.ofReal ((n : ℝ) *
      ((vonNeumannEntropy (ρ.toJointDensityOp hρ) -
        vonNeumannEntropy (ρ.quantumMarginalDensityOp hρ)) / Real.log 2 -
        2 * Real.logb 2 ((r : ℝ) + 3) * noiseFactor n ε)) ≤
      smoothMinEntropy ε (ρ.tensorPower n) (tensorReference (ρ.quantumMarginalDensityOp hρ) n) := by
  classical
  have hl : 0 ≤ Real.logb 2 ((r : ℝ) + 3) :=
    Real.logb_nonneg (by norm_num) (by have := Nat.cast_nonneg (α := ℝ) r; linarith)
  by_cases hg : InfoTheory.SmoothMinEntropy.AEP.IID.BennettRegime n ε
  · have hw : bennettTiltWidth n ε ≤ 2 * noiseFactor n ε :=
      bennettFactor_le_two_mul_of_eq_four_mul_log_two_mul_sq
        (Real.sqrt_nonneg _) rfl (bennettTiltWidth_le_one hg)
    apply (ENNReal.ofReal_le_ofReal ?_).trans
      (Bennett.ofReal_mul_sub_le_smoothMinEntropy ρ hρ n ε hε r hrank)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
    have hh := mul_le_mul_of_nonneg_left hw hl
    nlinarith only [hh]
  · have hnf : 1 ≤ 2 * noiseFactor n ε := by
      have hh : 3 / 4 < 4 * Real.log 2 * noiseFactor n ε ^ 2 := lt_of_not_ge hg
      have hl2 : Real.log 2 < 3 / 4 := by
        linarith [Real.log_two_lt_d9]
      have hn : 0 ≤ noiseFactor n ε := Real.sqrt_nonneg _
      by_contra h
      have hs : noiseFactor n ε ^ 2 < 1 / 4 := by nlinarith
      have hp := mul_lt_mul_of_pos_left hs (by positivity : 0 < 4 * Real.log 2)
      nlinarith
    have he := Spectral.referenceCondVonNeumannBits_le_logb_rtBoundBase ρ hρ
      (ρ.quantumMarginalDensityOp hρ) (hasScale_quantumMarginalDensityOp ρ hρ)
    have hr : Real.logb 2 (rtBoundBase ρ (ρ.quantumMarginalDensityOp hρ)) ≤
        Real.logb 2 ((r : ℝ) + 3) := by
      apply Real.logb_le_logb_of_le (by norm_num)
      · unfold rtBoundBase
        have := ρ.tracedSquareTimesInvFactor_nonneg (ρ.quantumMarginalDensityOp hρ)
        positivity
      · unfold rtBoundBase
        have := ρ.tracedSquareTimesInvFactor_quantumMarginal_le_one hρ
        have hh : (ρ.classicalRank : ℝ) ≤ (r : ℝ) := by exact_mod_cast hrank
        linarith
    unfold referenceCondVonNeumannBits at he
    rw [InfoTheory.RelativeEntropy.relativeEntropyReal_self, sub_zero] at he
    have hh := mul_le_mul_of_nonneg_left hnf hl
    rw [ENNReal.ofReal_eq_zero.mpr (mul_nonpos_of_nonneg_of_nonpos
      (Nat.cast_nonneg n) (by nlinarith [he.trans hr]))]
    exact zero_le

end InfoTheory.SmoothMinEntropy.AEP.IID
