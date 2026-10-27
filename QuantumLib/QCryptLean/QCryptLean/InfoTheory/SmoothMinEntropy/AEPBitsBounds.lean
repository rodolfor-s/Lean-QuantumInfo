import QCryptLean.InfoTheory.RelativeEntropy.Inequalities
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDBennett
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPBennettBudget
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPBits
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPLogEnvelope
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPRates
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.CQTensor
import QCryptLean.InfoTheory.SmoothMinEntropy.CollisionReference
import QCryptLean.InfoTheory.SmoothMinEntropy.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Normalized
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.InfoTheory.SmoothMinEntropy.SpectralCapBound
import QCryptLean.InfoTheory.VonNeumannEntropy.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor

/-! # AEPBits Bounds -/


noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators InfoTheory.VonNeumannEntropy
open InfoTheory.RelativeEntropy
open scoped MatrixOrder

variable {C Q : Type*} [Fintype C] [Fintype Q] [DecidableEq C] [DecidableEq Q] {n : ℕ}

namespace AEP.IID

/-- Bennett's fixed-reference AEP bound for every positive radius.
The feasible-scale condition retains the original support restriction. -/
theorem ofReal_bitBennettEntropyFloor_le_smoothRate
    (ρ : CQState C Q) (hρ : ∑ c, (ρ.stateMap c).trace = 1) (σ : DensityOp Q)
    (k : ℕ) [NeZero k] (ε : ℝ) (hε : 0 < ε) (hfeas : HasScale ρ σ.toSubDensityOp) :
    ENNReal.ofReal (bitBennettEntropyFloor ρ hρ σ k ε) ≤ smoothRate ρ σ k ε := by
  let : Nonempty Q := σ.nonempty
  by_cases hε1 : ε < 1
  swap
  · apply (ofReal_le_smoothRate_iff ρ σ k ε _).mpr
    rw [smoothMinEntropy_eq_top_of_weight_le_eps_sq hε.le]
    · exact le_top
    · have hw := (ρ.tensorPower k).weight_le_one
      nlinarith [le_of_not_gt hε1]
  by_cases hregime : InfoTheory.SmoothMinEntropy.AEP.IID.BennettRegime k ε
  swap
  · have hH := Spectral.referenceCondVonNeumannBits_le_logb_rtBoundBase ρ hρ σ hfeas
    have hμ : 1 ≤ rtBoundBase ρ σ := by
      unfold rtBoundBase
      linarith [ρ.tracedSquareTimesInvFactor_nonneg σ, Nat.cast_nonneg (α := ℝ) ρ.classicalRank]
    have hw := mul_le_mul_of_nonneg_left
      (InfoTheory.SmoothMinEntropy.one_le_bennettTiltWidth hregime)
      (Real.logb_nonneg one_lt_two hμ)
    have hf : bitBennettEntropyFloor ρ hρ σ k ε ≤ 0 := by
      unfold bitBennettEntropyFloor bennettPenalty
      rw [mul_one] at hw
      linarith
    rw [ENNReal.ofReal_eq_zero.mpr hf]
    exact zero_le
  obtain ⟨s, hs, hb⟩ := exists_bennett_moment_budget ρ hρ σ hfeas k ε hε hε1 hregime
  apply (ofReal_le_smoothRate_iff ρ σ k ε _).mpr
  have hscale : HasScale (ρ.tensorPower k) (tensorReference σ k) := by
    obtain ⟨t, ht⟩ := hfeas
    exact ⟨t ^ k, ht.tensorPower k⟩
  apply SpectralCap.ofReal_le_smoothMinEntropy_of_moment_bound
    (ρ.tensorPower k) (ρ.tensorPower_sum_trace hρ k) (tensorReference σ k) hscale
    ((k : ℝ) * bitBennettEntropyFloor ρ hρ σ k ε) hs hε.le
  change 2 * ((2 : ℝ) ^ (-bitBennettBlockEntropyFloor ρ hρ σ k ε)) ^ (-s) *
    (∑ cs, (((ρ.tensorPower k).stateMap cs).toOp ^ (1 + s) *
      (σ.toSubDensityOp.tensorPow k).toOp ^ (-s)).trace.re) ≤ ε ^ 2
  rw [CQState.sum_trace_rpow_tensorPower]
  exact hb

omit [DecidableEq Q] in
/-- Rank-capped Bennett AEP in bits with the `rank + 3` constant,
from collision domination. -/
theorem ofReal_sub_logb_mul_bennettTiltWidth_le_smoothRate
    (ρ : CQState C Q) (hρ : ∑ c, (ρ.stateMap c).trace = 1)
    (k : ℕ) [NeZero k] (ε : ℝ) (hε : 0 < ε) (r : ℕ) (hrank : ρ.classicalRank ≤ r) :
    ENNReal.ofReal
      (((vonNeumannEntropy (ρ.toJointDensityOp hρ) -
        vonNeumannEntropy (ρ.quantumMarginalDensityOp hρ)) / Real.log 2) -
        Real.logb 2 ((r : ℝ) + 3) * InfoTheory.SmoothMinEntropy.bennettTiltWidth k ε) ≤
      smoothRate ρ (ρ.quantumMarginalDensityOp hρ) k ε := by
  classical
  have hδ := bennettPenalty_quantumMarginal_le ρ hρ k ε r hrank
  have hAEP := ofReal_bitBennettEntropyFloor_le_smoothRate ρ hρ
    (ρ.quantumMarginalDensityOp hρ) k ε hε (hasScale_quantumMarginalDensityOp ρ hρ)
  refine (ENNReal.ofReal_le_ofReal ?_).trans hAEP
  unfold bitBennettEntropyFloor referenceCondVonNeumannBits
  rw [InfoTheory.RelativeEntropy.relativeEntropyReal_self]
  simp only [sub_zero]
  exact sub_le_sub_left hδ _

omit [DecidableEq Q] in
/-- Native conversion of the Bennett per-copy bound to its completed block floor. -/
theorem Bennett.ofReal_mul_sub_le_smoothMinEntropy
    (ρ : CQState C Q) (hρ : ∑ c, (ρ.stateMap c).trace = 1)
    (k : ℕ) [NeZero k] (ε : ℝ) (hε : 0 < ε) (r : ℕ) (hrank : ρ.classicalRank ≤ r) :
    ENNReal.ofReal ((k : ℝ) *
      (((vonNeumannEntropy (ρ.toJointDensityOp hρ) -
        vonNeumannEntropy (ρ.quantumMarginalDensityOp hρ)) / Real.log 2) -
        Real.logb 2 ((r : ℝ) + 3) * InfoTheory.SmoothMinEntropy.bennettTiltWidth k ε)) ≤
      smoothMinEntropy ε (ρ.tensorPower k) (tensorReference (ρ.quantumMarginalDensityOp hρ) k) :=
  (ofReal_le_smoothRate_iff ρ (ρ.quantumMarginalDensityOp hρ) k ε _).mp
    (ofReal_sub_logb_mul_bennettTiltWidth_le_smoothRate ρ hρ k ε hε r hrank)

end AEP.IID
end InfoTheory.SmoothMinEntropy
