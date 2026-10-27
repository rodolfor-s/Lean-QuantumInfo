import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import QCryptLean.Math.Concentration.BernoulliKL

/-!
# Logarithm Bounds — log powers, log-eight lower bound, and log(89) series estimate

Certified numerical bounds on logarithms. This file provides small reusable
logarithm identities and lower bounds, together with the Taylor-series proof of
`Real.log 89 > 4.4886` using `Real.abs_log_sub_add_sum_range_le`.

## Main statements
- `Real.log_eight`: `Real.log 8 = 3 * Real.log 2`.
- `Real.three_mul_d9_lt_log_eight`: decimal lower bound for `Real.log 8`.
- `Real.log_eighty_nine_gt_d4`: `log 89 > 4.4886`
- `Real.log_ten_gt_d5`: `log 10 > 2.30257`
- `Real.log_five_gt_d5`: `log 5 > 1.60943`
- `Real.log_one_point_two_five_lt_d5`, `Real.log_one_point_one_gt_d4`,
`Real.log_one_point_one_two_lt_d3`, `Real.log_one_point_one_one_lt_d3`: series bounds on logarithms
near one,
  used for the binary-entropy threshold values `h(0.11) < 1/2 < h(0.112)`
-/

namespace Real

/-- `Real.log 8 = 3 * Real.log 2`, since `8 = 2 ^ 3`. -/
lemma log_eight : Real.log 8 = 3 * Real.log 2 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  ring

/-- Numeric lower bound for `log 8` obtained from Mathlib's lower bound on `log 2`. -/
lemma three_mul_d9_lt_log_eight : (3 * 0.6931471803 : ℝ) < Real.log 8 := by
  rw [Real.log_eight]
  linarith [Real.log_two_gt_d9]

/-- `exp(−x) ≤ 2^(−m)` whenever `m·log 2 ≤ x`. -/
lemma exp_neg_le_inv_two_pow {x : ℝ} {m : ℕ}
    (h : (m : ℝ) * Real.log 2 ≤ x) : Real.exp (-x) ≤ ((2 : ℝ) ^ m)⁻¹ := by
  have h2 : ((2 : ℝ) ^ m) = Real.exp ((m : ℝ) * Real.log 2) := by
    rw [← Real.rpow_natCast (2 : ℝ) m, Real.rpow_def_of_pos (by norm_num), mul_comm]
  rw [h2, ← Real.exp_neg]
  exact Real.exp_le_exp.mpr (by linarith)

/-- The logarithm to a positive base different from one of a natural power of that base. -/
lemma logb_self_pow {b : ℝ} (hb : 0 < b) (hb1 : b ≠ 1) (k : ℕ) :
    Real.logb b (b ^ k) = k := by
  rw [Real.logb_pow, Real.logb_self_eq_one_iff.mpr ⟨hb.ne', hb1, by linarith⟩, mul_one]

/-- The base-two logarithm of twice the inverse square of an inverse power of two. -/
lemma logb_two_div_sq_inv_two_pow (k : ℕ) :
    Real.logb 2 (2 / (((2 : ℝ) ^ k)⁻¹) ^ 2) = 2 * (k : ℝ) + 1 := by
  rw [inv_pow, div_eq_mul_inv, inv_inv, ← pow_mul, ← pow_succ',
    logb_self_pow (by norm_num) (by norm_num)]
  push_cast
  ring

/-- A decimal lower bound for `log 3`, from the lower bound for `log (9/8)`. -/
lemma log_three_gt_d4 : 1.0952 < Real.log 3 := by
  have h98 : 2 * Real.log 3 = 3 * Real.log 2 + Real.log ((9 : ℝ) / 8) := by
    rw [Real.log_div (by norm_num) (by norm_num), show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num,
      show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hlo := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 9 / 8 by norm_num)
  norm_num at hlo
  linarith [Real.log_two_gt_d9]

/-- `log 3 < 1.09861233` (true value `1.0986122886681…`).  From `3^12 = 2^19·(531441/524288)`,
`12 log 3 = 19 log 2 + log (531441/524288)`, with `log 2 < 0.6931471808`
(`Real.log_two_lt_d9`) and the Padé `[2,1]` upper bound at `t = 7153/524288`. -/
lemma log_three_lt_d8 : Real.log 3 < 1.09861233 := by
  have hp := Math.Concentration.BernoulliKL.log_one_add_le_mul_add_div (7153 / 524288 : ℝ) (by
    norm_num)
  rw [show (1 : ℝ) + 7153 / 524288 = 531441 / 524288 by norm_num] at hp
  have hid : 12 * Real.log 3 = 19 * Real.log 2 + Real.log (531441 / 524288) := by
    have h1 : Real.log ((3 : ℝ) ^ (12 : ℕ)) = 12 * Real.log 3 := by
      rw [Real.log_pow]
      push_cast
      ring
    rw [show ((3 : ℝ) ^ (12 : ℕ)) = 2 ^ (19 : ℕ) * (531441 / 524288) by norm_num,
      Real.log_mul (by positivity) (by norm_num), Real.log_pow] at h1
    push_cast at h1 ⊢
    linarith [h1]
  have h2 := Real.log_two_lt_d9
  rw [show (7153 : ℝ) / 524288 * (7153 / 524288 + 2) / (2 * (7153 / 524288 + 1))
      = 7551629537 / 557256278016 by norm_num] at hp
  linarith [hp, hid, h2]

/-- A certified interval for the base-two logarithm of three. -/
lemma logb_two_three_mem_Icc : Real.logb 2 3 ∈ Set.Icc (1.58 : ℝ) 1.591 := by
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlo := Real.log_two_gt_d9
  have hhi := Real.log_two_lt_d9
  have h3lo := Real.log_three_gt_d4
  have h3hi := Real.log_three_lt_d8
  change 1.58 ≤ Real.log 3 / Real.log 2 ∧ Real.log 3 / Real.log 2 ≤ 1.591
  constructor
  · rw [le_div_iff₀ hL]
    linarith
  · rw [div_le_iff₀ hL]
    linarith

/-- A certified interval for the logarithm of the silver ratio `1 + √2`. -/
lemma log_one_add_sqrt_two_mem_Icc :
    Real.log (1 + Real.sqrt 2) ∈ Set.Icc (0.88093 : ℝ) 0.88184 := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hslo : (1.4142135 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have hshi : Real.sqrt 2 ≤ (1.4142136 : ℝ) := by nlinarith
  have hX : (1 + Real.sqrt 2) ^ 4 = 17 + 12 * Real.sqrt 2 := by nlinarith [hs2]
  have hXpos : (0 : ℝ) < 17 + 12 * Real.sqrt 2 := by linarith
  have hlogX : Real.log ((1 + Real.sqrt 2) ^ 4) = 4 * Real.log (1 + Real.sqrt 2) := by
    rw [Real.log_pow]
    norm_num
  have hlog32 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hsplit : Real.log ((1 + Real.sqrt 2) ^ 4)
      = Real.log ((17 + 12 * Real.sqrt 2) / 32) + Real.log (32 : ℝ) := by
    rw [hX, Real.log_div (ne_of_gt hXpos) (by norm_num : (32 : ℝ) ≠ 0)]
    ring
  have ht : (0 : ℝ) < (17 + 12 * Real.sqrt 2) / 32 := by positivity
  have hbrlo := Real.one_sub_inv_le_log_of_pos ht
  have hbrhi := Real.log_le_sub_one_of_pos ht
  -- `1 − 32/33.970562 ≤ log((17+12√2)/32)`, from `√2 ≥ 1.4142135`
  have hinv : ((17 + 12 * Real.sqrt 2) / 32)⁻¹ ≤ (32 : ℝ) / 33.970562 := by
    rw [inv_div, div_le_div_iff₀ hXpos (by norm_num : (0 : ℝ) < 33.970562)]
    linarith
  constructor
  · -- `4·Δ ≥ 1 − 32/33.970562 + 5·log 2`
    have hlog2lo := Real.log_two_gt_d9
    linarith
  · -- `4·Δ ≤ (12·√2 − 15)/32 + 5·log 2`
    have hlog2hi := Real.log_two_lt_d9
    linarith

end Real

open Real Finset

noncomputable section

namespace Real

/-! ## Step 1: Bound on log(1.25) -/

theorem log_one_point_two_five_gt_d5 : log 1.25 > 0.22314 := by
  -- Use series: log(1.25) = log(1 - (-1/4)), so x = -1/4
  have h := Real.abs_log_sub_add_sum_range_le (x := -1/4) (by norm_num : |(-1:ℝ)/4| < 1) 10
  have h_eq : (1 : ℝ) - (-1/4) = 5/4 := by norm_num
  have h_eq2 : (5:ℝ)/4 = 1.25 := by norm_num
  rw [h_eq, h_eq2] at h
  -- Series sum: -147409261/660602880 ≈ -0.2231435337
  have h_sum : (∑ i ∈ range 10, (-1/4 : ℝ)^(i+1) / (i+1)) = -147409261/660602880 := by
    simp only [sum_range_succ, range_zero, sum_empty, Nat.cast_zero, Nat.cast_one,
               Nat.cast_ofNat, pow_succ]
    norm_num
  rw [h_sum] at h
  -- Error: (1/4)^11 / (3/4) < 3.2e-7 < 0.0000004
  have h_err : |(-1:ℝ)/4|^11 / (1 - |(-1:ℝ)/4|) < 0.0000004 := by norm_num
  have h_bound : |(-147409261:ℝ)/660602880 + log 1.25| < 0.0000004 := lt_of_le_of_lt h h_err
  have h_abs := abs_lt.mp h_bound
  -- 147409261/660602880 ≈ 0.2231435, so log 1.25 > 0.2231435 - 0.0000004 > 0.22314
  have h_val : (147409261:ℝ)/660602880 - 0.0000004 > 0.22314 := by norm_num
  linarith

/-- `log 1.25 < 0.22317`: seven terms of the series of `log (1 - x)` at `x = -1/4`, whose
remainder is below `2.1·10⁻⁵`. -/
theorem log_one_point_two_five_lt_d5 : log 1.25 < 0.22317 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -1/4) (by norm_num) 7
  rw [show (1 : ℝ) - -1/4 = 1.25 by norm_num] at h
  have h_sum : (∑ i ∈ range 7, (-1/4 : ℝ) ^ (i + 1) / (i + 1)) = -383881/1720320 := by
    simp only [sum_range_succ, range_zero, sum_empty, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, pow_succ]
    norm_num
  have h_err : |(-1/4 : ℝ)| ^ (7 + 1) / (1 - |(-1/4 : ℝ)|) < 0.000021 := by norm_num
  rw [h_sum] at h
  linarith only [(abs_lt.mp (h.trans_lt h_err)).2]

/-! ## Step 2: log(5) > 1.60943 -/

theorem log_five_gt_d5 : log 5 > 1.60943 := by
  have h1 : log 5 = 2 * log 2 + log 1.25 := by
    have h4 : (4 : ℝ) = 2^2 := by norm_num
    have h5 : (5 : ℝ) = 4 * 1.25 := by norm_num
    rw [h5, log_mul (by norm_num) (by norm_num), h4, log_pow]
    ring
  rw [h1]
  have h2 := Real.log_two_gt_d9  -- 0.6931471803 < log 2
  have h3 := Real.log_one_point_two_five_gt_d5         -- log 1.25 > 0.22314
  linarith

/-! ## Step 3: log(10) > 2.30257 -/

theorem log_ten_gt_d5 : log 10 > 2.30257 := by
  have h1 : log 10 = log 2 + log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, log_mul (by norm_num) (by norm_num)]
  rw [h1]
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_five_gt_d5
  linarith

/-! ## Step 4: Bound on log(100/89) -/

theorem log_hundred_div_eighty_nine_lt_d5 : log (100/89) < 0.11654 := by
  -- Use series: log(100/89) = log(1 - (-11/89)), so x = -11/89
  have h := Real.abs_log_sub_add_sum_range_le (x := (-11:ℝ)/89) (by norm_num : |(-11:ℝ)/89| < 1) 6
  have h_eq : (1 : ℝ) - (-11/89) = 100/89 := by norm_num
  rw [h_eq] at h
  -- Series sum with 6 terms: -3474905892733/29818877457660 ≈ -0.116533759
  have h_sum : (∑ i ∈ range 6, ((-11:ℝ)/89)^(i+1) / (i+1)) =
               -3474905892733/29818877457660 := by
    simp only [sum_range_succ, range_zero, sum_empty, Nat.cast_zero, Nat.cast_one,
               Nat.cast_ofNat, pow_succ]
    norm_num
  rw [h_sum] at h
  -- Error bound: (11/89)^7 / (78/89) < 5.1e-7 < 0.0000006
  have h_err : |(-11:ℝ)/89|^7 / (1 - |(-11:ℝ)/89|) < 0.0000006 := by norm_num
  have h_bound : |(-3474905892733:ℝ)/29818877457660 + log (100/89)| < 0.0000006 :=
    lt_of_le_of_lt h h_err
  have h_abs := abs_lt.mp h_bound
  -- 3474905892733/29818877457660 ≈ 0.116533759, so log(100/89) < 0.116533759 + 0.0000006 < 0.11654
  have h_val : (3474905892733:ℝ)/29818877457660 + 0.0000006 < 0.11654 := by norm_num
  linarith

/-! ## Bounds near one for the binary-entropy threshold values -/

/-- `log 1.1 > 0.0953`: five terms of the series of `log (1 - x)` at `x = -1/10`, whose remainder
is below `1.2·10⁻⁶`. -/
theorem log_one_point_one_gt_d4 : log 1.1 > 0.0953 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -1/10) (by norm_num) 5
  rw [show (1 : ℝ) - -1/10 = 1.1 by norm_num] at h
  have h_sum : (∑ i ∈ range 5, (-1/10 : ℝ) ^ (i + 1) / (i + 1)) = -285931/3000000 := by
    simp only [sum_range_succ, range_zero, sum_empty, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, pow_succ]
    norm_num
  have h_err : |(-1/10 : ℝ)| ^ (5 + 1) / (1 - |(-1/10 : ℝ)|) < 0.0000012 := by norm_num
  rw [h_sum] at h
  linarith only [(abs_lt.mp (h.trans_lt h_err)).1]

/-- `log 1.12 < 0.114`: three terms of the series of `log (1 - x)` at `x = -0.12`, whose
remainder is below `2.4·10⁻⁴`. -/
theorem log_one_point_one_two_lt_d3 : log 1.12 < 0.114 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -0.12) (by norm_num) 3
  rw [show (1 : ℝ) - -0.12 = 1.12 by norm_num] at h
  have h_sum : (∑ i ∈ range 3, (-0.12 : ℝ) ^ (i + 1) / (i + 1)) = -3543/31250 := by
    simp only [sum_range_succ, range_zero, sum_empty, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, pow_succ]
    norm_num
  have h_err : |(-0.12 : ℝ)| ^ (3 + 1) / (1 - |(-0.12 : ℝ)|) < 0.00024 := by norm_num
  rw [h_sum] at h
  linarith only [(abs_lt.mp (h.trans_lt h_err)).2]

/-- `log 1.11 < 0.105`: three terms of the series of `log (1 - x)` at `x = -0.11`, whose
remainder is below `1.7·10⁻⁴`. -/
theorem log_one_point_one_one_lt_d3 : log 1.11 < 0.105 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -0.11) (by norm_num) 3
  rw [show (1 : ℝ) - -0.11 = 1.11 by norm_num] at h
  have h_sum : (∑ i ∈ range 3, (-0.11 : ℝ) ^ (i + 1) / (i + 1)) = -313181/3000000 := by
    simp only [sum_range_succ, range_zero, sum_empty, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, pow_succ]
    norm_num
  have h_err : |(-0.11 : ℝ)| ^ (3 + 1) / (1 - |(-0.11 : ℝ)|) < 0.00017 := by norm_num
  rw [h_sum] at h
  linarith only [(abs_lt.mp (h.trans_lt h_err)).2]

/-! ## Step 5: log(89) > 4.4886 -/

theorem log_eighty_nine_gt_d4 : log 89 > 4.4886 := by
  have h1 : log 89 = 2 * log 10 - log (100/89) := by
    have h_eq : (89 : ℝ) = 100 / (100/89) := by norm_num
    rw [h_eq, log_div (by norm_num) (by norm_num)]
    rw [show (100 : ℝ) = 10^2 by norm_num, log_pow]
    ring_nf
  rw [h1]
  have h2 := Real.log_ten_gt_d5       -- log 10 > 2.30258
  have h3 := Real.log_hundred_div_eighty_nine_lt_d5   -- log(100/89) < 0.11654
  linarith

end Real

namespace Real

/-- `e² ≥ 7.389056`, from `Real.exp_one_gt_d9`. -/
lemma exp_two_ge_d6 : (7389056 : ℝ) / 1000000 ≤ Real.exp 2 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hsq : Real.exp 1 * Real.exp 1 = Real.exp 2 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [h1, h0, hsq]

/-- `exp(49/200) ≥ 1272932/1000000`, from `1 + x ≤ exp x` at `x = 49/1600` and three squarings.

The eighth-power form is what is needed: the first-order bound `1 + x ≤ exp x` gives only
`1.245`, which is too weak for `log(2 + e²) ≤ 2245/1000`. -/
lemma exp_forty_nine_div_two_hundred_ge : (1272932 : ℝ) / 1000000 ≤ Real.exp (49 / 200) := by
  have hb : (1 : ℝ) + 49 / 1600 ≤ Real.exp (49 / 1600) := by
    have := Real.add_one_le_exp ((49 : ℝ) / 1600)
    linarith
  have hb0 : (0 : ℝ) ≤ 1 + 49 / 1600 := by norm_num
  have h2 : ((1 : ℝ) + 49 / 1600) ^ 2 ≤ (Real.exp (49 / 1600)) ^ 2 :=
    pow_le_pow_left₀ hb0 hb 2
  have he2 : (Real.exp (49 / 1600)) ^ 2 = Real.exp (49 / 800) := by
    rw [sq, ← Real.exp_add]; norm_num
  rw [he2] at h2
  have h20 : (0 : ℝ) ≤ ((1 : ℝ) + 49 / 1600) ^ 2 := by positivity
  have h4 : (((1 : ℝ) + 49 / 1600) ^ 2) ^ 2 ≤ (Real.exp (49 / 800)) ^ 2 :=
    pow_le_pow_left₀ h20 h2 2
  have he4 : (Real.exp (49 / 800)) ^ 2 = Real.exp (49 / 400) := by
    rw [sq, ← Real.exp_add]; norm_num
  rw [he4] at h4
  have h40 : (0 : ℝ) ≤ (((1 : ℝ) + 49 / 1600) ^ 2) ^ 2 := by positivity
  have h8 : ((((1 : ℝ) + 49 / 1600) ^ 2) ^ 2) ^ 2 ≤ (Real.exp (49 / 400)) ^ 2 :=
    pow_le_pow_left₀ h40 h4 2
  have he8 : (Real.exp (49 / 400)) ^ 2 = Real.exp (49 / 200) := by
    rw [sq, ← Real.exp_add]; norm_num
  rw [he8] at h8
  have hnum : (1272932 : ℝ) / 1000000 ≤ ((((1 : ℝ) + 49 / 1600) ^ 2) ^ 2) ^ 2 := by norm_num
  linarith

/-- **`log(2 + e²) ≤ 2245/1000`** (true value `2.2395448`).

`2 + e² ≤ exp(2 + 49/200)` because `exp(49/200) − 1 ≥ 0.272932 ≥ 2/e²`. -/
lemma log_two_add_exp_two_le : Real.log (2 + Real.exp 2) ≤ 2245 / 1000 := by
  have he2 := exp_two_ge_d6
  have hs := exp_forty_nine_div_two_hundred_ge
  have hexp_pos : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  have hsplit : Real.exp ((2245 : ℝ) / 1000) = Real.exp 2 * Real.exp (49 / 200) := by
    rw [← Real.exp_add]; norm_num
  have hle : 2 + Real.exp 2 ≤ Real.exp ((2245 : ℝ) / 1000) := by
    rw [hsplit]
    nlinarith [he2, hs, hexp_pos]
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 + Real.exp 2) hle
  rwa [Real.log_exp] at h

/-- **`2^(1/16) ≤ 10443/10000`** (true value `1.0442738`), from `(10443/10000)^16 ≥ 2`. -/
lemma two_rpow_one_sixteenth_le : (2 : ℝ) ^ ((1 : ℝ) / 16) ≤ 10443 / 10000 := by
  have hc : (0 : ℝ) < 10443 / 10000 := by norm_num
  have hpow : (2 : ℝ) ≤ ((10443 : ℝ) / 10000) ^ (16 : ℕ) := by norm_num
  have hstep : (2 : ℝ) ^ ((1 : ℝ) / 16)
      ≤ (((10443 : ℝ) / 10000) ^ (16 : ℕ)) ^ ((1 : ℝ) / 16) :=
    Real.rpow_le_rpow (by norm_num) hpow (by norm_num)
  have hid : (((10443 : ℝ) / 10000) ^ (16 : ℕ)) ^ ((1 : ℝ) / 16) = (10443 : ℝ) / 10000 := by
    rw [← Real.rpow_natCast ((10443 : ℝ) / 10000) 16, ← Real.rpow_mul hc.le]
    norm_num
  rwa [hid] at hstep

end Real
