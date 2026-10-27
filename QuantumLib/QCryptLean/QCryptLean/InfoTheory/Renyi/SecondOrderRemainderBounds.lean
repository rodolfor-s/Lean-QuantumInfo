import QCryptLean.InfoTheory.Renyi.SecondOrderConstants
import QCryptLean.Math.Analysis.LogBounds

/-! # Second Order Remainder Bounds -/


noncomputable section

namespace InfoTheory.Renyi

/-- The binary remainder base is at least `5/2`. -/
lemma five_halves_le_binarySecondOrderRemainderBase :
    (5 : ℝ) / 2 ≤ binarySecondOrderRemainderBase := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : (219 : ℝ) / 100 ≤ Real.log (2 + Real.exp 2) := by
    have harg : (9 : ℝ) ≤ 2 + Real.exp 2 := by linarith [Real.exp_two_ge_d6]
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 9) harg
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith [Real.log_three_gt_d4]
  have hcube := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 219 / 100) hlog 3
  rw [binarySecondOrderRemainderBase, le_div_iff₀ (by positivity : 0 < 6 * Real.log 2)]
  nlinarith [Real.log_two_lt_d9]

/-- The binary Dupuis–Fawzi remainder is at most `7/2` for `β ≤ 1/16`. -/
lemma binarySecondOrderRemainderBound_le_seven_halves (β : ℝ) (hβ : β ≤ 1 / 16) :
    binarySecondOrderRemainderBound β ≤ 7 / 2 := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl2lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hdenβ : (15 : ℝ) / 16 ≤ 1 - β := by linarith
  have hdenβpos : (0 : ℝ) < 1 - β := by linarith
  have hden : (0 : ℝ) < 6 * (1 - β) ^ 3 * Real.log 2 := by positivity
  have hcube : (3375 : ℝ) / 4096 ≤ (1 - β) ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 15 / 16) hdenβ 3
    norm_num at this ⊢
    exact this
  have hprod : ((3375 : ℝ) / 4096) * 0.6931471803 ≤ (1 - β) ^ 3 * Real.log 2 :=
    mul_le_mul hcube hl2lo.le (by norm_num) (by positivity)
  have hB1 : 1 / (6 * (1 - β) ^ 3 * Real.log 2) ≤ 2919 / 10000 := by
    rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 10000)]
    calc 1 * 10000 ≤ (2919 * 6 : ℝ) * (((3375 : ℝ) / 4096) * 0.6931471803) := by norm_num
      _ ≤ (2919 * 6 : ℝ) * ((1 - β) ^ 3 * Real.log 2) :=
          mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = 2919 * (6 * (1 - β) ^ 3 * Real.log 2) := by ring
  have hB2 : (2 : ℝ) ^ β ≤ 10443 / 10000 :=
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ).trans Real.two_rpow_one_sixteenth_le
  have hlog : 0 ≤ Real.log (2 + Real.exp 2) := Real.log_nonneg (by
    have := Real.exp_pos (2 : ℝ)
    linarith)
  have hB3 : Real.log (2 + Real.exp 2) ^ 3 ≤ (2245 / 1000 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hlog Real.log_two_add_exp_two_le 3
  calc binarySecondOrderRemainderBound β
      = (1 / (6 * (1 - β) ^ 3 * Real.log 2)) * (2 : ℝ) ^ β
          * Real.log (2 + Real.exp 2) ^ 3 := by
        unfold binarySecondOrderRemainderBound binarySecondOrderRemainderBase
        field_simp
    _ ≤ (2919 / 10000 : ℝ) * (10443 / 10000 : ℝ) * (2245 / 1000 : ℝ) ^ 3 := by
        exact mul_le_mul (mul_le_mul hB1 hB2 (by positivity) (by norm_num)) hB3
          (by positivity) (by positivity)
    _ ≤ 7 / 2 := by norm_num

end InfoTheory.Renyi

end
