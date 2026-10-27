import QCryptLean.InfoTheory.Renyi.ConditionalVariance.Continuity
import QCryptLean.InfoTheory.Renyi.SecondOrderConstants
import QCryptLean.InfoTheory.Renyi.Basic
import QCryptLean.InfoTheory.Renyi.Continuity
import QCryptLean.InfoTheory.Renyi.Bounds
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.Quantum.Operators.StateOperations

/-! # Conditional variance for a two-element classical alphabet -/

noncomputable section

namespace InfoTheory.Renyi

open InfoTheory.SmoothMinEntropy

/-- The generic classical variance cap specializes to the exact qubit constant. -/
theorem condVariance_le_logb_sq_of_card_eq_two
    {C Q : Type*} [Fintype C] [DecidableEq C] [Fintype Q] [DecidableEq Q]
    (ρ : CQState C Q) (hρ : ∑ c, (ρ.stateMap c).trace = 1) (hC : Fintype.card C = 2) :
    condVariance ρ ≤ Real.logb 2 (Real.sqrt 2 + 1) ^ 2 := by
  simpa only [hC, Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, Real.sqrt_one] using
    condVariance_le_logb_sq ρ hρ

/-- `K(1 + β) ≤ K_β` for `0 < β < 1` at a normalized binary classical register.

The conditional von Neumann entropy is at most `log₂ 2 = 1`, and the conditional Petz-down
Rényi entropies at orders `1 + β` and `2` are nonnegative. Thus both entropy differences in
Dupuis–Fawzi's Corollary IV.2 remainder are at most `1`. -/
theorem secondOrderK_le_binarySecondOrderRemainderBound
    {C Q : Type*} [Fintype C] [DecidableEq C] [Fintype Q] [DecidableEq Q]
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    (ρ : CQState C Q) (hnorm : ∑ x : C, (ρ.stateMap x).trace = 1)
    (hcard : Fintype.card C = 2) :
    secondOrderK (1 + β) ρ ≤ binarySecondOrderRemainderBound β := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hα1 : 1 < 1 + β := by linarith
  have hα2 : 1 + β ≤ 2 := by linarith
  have hH1 : CQState.condVonNeumannBits ρ ≤ 1 := by
    have hHd := CQState.condVonNeumannBits_le_logb_card ρ hnorm
    simpa [hcard, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using hHd
  have hRα : 0 ≤ condPetzRenyiDown (1 + β) ρ :=
    condPetzRenyiDown_nonneg (1 + β) hα1 hα2 ρ hnorm
  have hR2 : 0 ≤ condPetzRenyiDown 2 ρ :=
    condPetzRenyiDown_nonneg 2 (by norm_num) (by norm_num) ρ hnorm
  have hEα : CQState.condVonNeumannBits ρ - condPetzRenyiDown (1 + β) ρ
    ≤ 1 :=
    (sub_le_self _ hRα).trans hH1
  have hE2 : CQState.condVonNeumannBits ρ - condPetzRenyiDown 2 ρ ≤ 1 :=
    (sub_le_self _ hR2).trans hH1
  have hdenβ : 0 < 1 - β := sub_pos.mpr hβ1
  have hB2 : (2 : ℝ) ^ (β * (CQState.condVonNeumannBits ρ -
    condPetzRenyiDown (1 + β) ρ))
      ≤ (2 : ℝ) ^ β := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    simpa using mul_le_mul_of_nonneg_left hEα hβpos.le
  have harg_pos : (0 : ℝ) < (2 : ℝ) ^ (CQState.condVonNeumannBits ρ -
    condPetzRenyiDown 2 ρ)
      + Real.exp 2 := by positivity
  have harg_le : (2 : ℝ) ^ (CQState.condVonNeumannBits ρ -
    condPetzRenyiDown 2 ρ) + Real.exp 2
      ≤ 2 + Real.exp 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hE2
    rw [Real.rpow_one] at h
    exact add_le_add h le_rfl
  have hlog_nn : 0 ≤ Real.log ((2 : ℝ) ^ (CQState.condVonNeumannBits ρ
    - condPetzRenyiDown 2 ρ)
      + Real.exp 2) :=
    Real.log_nonneg (le_add_of_nonneg_of_le (Real.rpow_pos_of_pos (by norm_num) _).le
      (Real.one_le_exp (by norm_num)))
  have hB3 : Real.log ((2 : ℝ) ^ (CQState.condVonNeumannBits ρ -
    condPetzRenyiDown 2 ρ) + Real.exp 2) ^ 3
      ≤ Real.log (2 + Real.exp 2) ^ 3 :=
    pow_le_pow_left₀ hlog_nn (Real.log_le_log harg_pos harg_le) 3
  simp only [secondOrderK, continuityRemainderScale, condPetzEntropyGap]
  rw [ show 1 + β - 1 = β by ring, show 2 - (1 + β) = 1 - β by ring]
  calc (1 / (6 * (1 - β) ^ 3 * Real.log 2))
        * (2 : ℝ) ^ (β * (CQState.condVonNeumannBits ρ -
          condPetzRenyiDown (1 + β) ρ))
        * Real.log ((2 : ℝ) ^ (CQState.condVonNeumannBits ρ -
          condPetzRenyiDown 2 ρ) + Real.exp 2) ^ 3
      ≤ (1 / (6 * (1 - β) ^ 3 * Real.log 2)) * (2 : ℝ) ^ β
          * Real.log (2 + Real.exp 2) ^ 3 := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hB2 (by positivity)) hB3
          (by positivity) (by positivity)
    _ = binarySecondOrderRemainderBound β := by
        unfold binarySecondOrderRemainderBound binarySecondOrderRemainderBase
        field_simp


end InfoTheory.Renyi
