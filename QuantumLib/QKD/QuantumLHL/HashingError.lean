import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Basic.ENNReal.Real

/-!
# Hashing error at extended entropy

The scalar leftover-hashing error is zero at infinite entropy and has its usual exponential
value at finite entropy. Uniform budgets pass to entropy infima, and shortening the key
compensates for additive entropy penalties.
-/

namespace InfoTheory.QuantumLHL

/-- The leftover-hashing error for an extended entropy and a real key length.
Infinite entropy has zero hashing error; finite entropy uses the usual exponential. -/
noncomputable def hashingError (l : ℝ) (H : ENNReal) : ℝ :=
  if H = ⊤ then 0 else (1 / 2) * Real.rpow 2 (-(1 / 2) * (H.toReal - l))

/-- Infinite entropy removes the hashing error. -/
@[simp] theorem hashingError_top (l : ℝ) : hashingError l ⊤ = 0 := by
  simp [hashingError]

/-- A zero entropy floor gives the trivial hashing term for the key length. -/
@[simp] theorem hashingError_zero (l : ℝ) :
    hashingError l 0 = (1 / 2) * Real.rpow 2 ((1 / 2) * l) := by
  simp [hashingError]

/-- At finite entropy the hashing error is the usual real exponential. -/
theorem hashingError_of_ne_top (l : ℝ) {H : ENNReal} (hH : H ≠ ⊤) :
    hashingError l H = (1 / 2) * Real.rpow 2 (-(1 / 2) * (H.toReal - l)) := by
  simp [hashingError, hH]

/-- The hashing error is nonnegative for every extended entropy. -/
theorem hashingError_nonneg (l : ℝ) (H : ENNReal) : 0 ≤ hashingError l H := by
  unfold hashingError
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)

/-- A zero hashing budget is equivalent to infinite entropy. -/
theorem hashingError_le_zero_iff (l : ℝ) (H : ENNReal) :
    hashingError l H ≤ 0 ↔ H = ⊤ := by
  by_cases hH : H = ⊤
  · simp [hH]
  · rw [hashingError_of_ne_top l hH]
    have hp : 0 < (1 / 2 : ℝ) * Real.rpow 2 (-(1 / 2) * (H.toReal - l)) := by
      exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)
    exact iff_of_false (not_le_of_gt hp) hH

/-- A positive hashing budget is equivalent to the completed, clipped real entropy floor. -/
theorem hashingError_le_iff (l : ℝ) (H : ENNReal) {ε : ℝ} (hε : 0 < ε) :
    hashingError l H ≤ ε ↔
      ENNReal.ofReal (l - 2 * Real.logb 2 (2 * ε)) ≤ H := by
  by_cases hH : H = ⊤
  · simp [hH, hε.le]
  rw [hashingError_of_ne_top l hH, ENNReal.ofReal_le_iff_le_toReal hH]
  have hlog : Real.rpow 2 (Real.logb 2 (2 * ε)) = 2 * ε :=
    Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
  have hpow : Real.rpow 2 (-(1 / 2 : ℝ) * (H.toReal - l)) ≤
      Real.rpow 2 (Real.logb 2 (2 * ε)) ↔
        -(1 / 2 : ℝ) * (H.toReal - l) ≤ Real.logb 2 (2 * ε) :=
    Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)
  rw [hlog] at hpow
  constructor <;> intro h
  · have hh := hpow.mp (show Real.rpow 2 (-(1 / 2 : ℝ) * (H.toReal - l)) ≤
        2 * ε by linarith)
    linarith
  · have hh := hpow.mpr (show -(1 / 2 : ℝ) * (H.toReal - l) ≤
        Real.logb 2 (2 * ε) by linarith)
    linarith

/-- A uniform hashing budget passes to an extended entropy infimum, including an empty family
and a zero budget. -/
theorem hashingError_iInf_le {ι : Sort*} (l : ℝ) (H : ι → ENNReal)
    {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ i, hashingError l (H i) ≤ ε) :
    hashingError l (⨅ i, H i) ≤ ε := by
  rcases eq_or_lt_of_le hε with hzero | hpos
  · subst ε
    apply (hashingError_le_zero_iff l _).2
    apply top_unique
    exact le_iInf fun i => (hashingError_le_zero_iff l (H i)).1 (h i) ▸ le_rfl
  · apply (hashingError_le_iff l _ hpos).2
    exact le_iInf fun i => (hashingError_le_iff l (H i) hpos).1 (h i)

/-- Shortening the key by a nonnegative entropy penalty preserves the hashing error bound.
The additive entropy inequality retains its meaning when either entropy is infinite. -/
theorem hashingError_le_of_le_add (l l' p : ℝ) (H H' : ENNReal)
    (hp : 0 ≤ p) (hH : H ≤ H' + ENNReal.ofReal p) (hl : l' ≤ l - p) :
    hashingError l' H' ≤ hashingError l H := by
  by_cases hH' : H' = ⊤
  · rw [hH', hashingError_top]
    exact hashingError_nonneg l H
  have hfinite : H ≠ ⊤ := ne_top_of_le_ne_top (by simp [hH']) hH
  rw [hashingError_of_ne_top l' hH', hashingError_of_ne_top l hfinite]
  have hreal := ENNReal.toReal_mono (by simp [hH']) hH
  rw [ENNReal.toReal_add hH' ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp] at hreal
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  linarith

/-- Increasing extended entropy decreases the hashing error. -/
theorem hashingError_antitone (l : ℝ) : Antitone (hashingError l) := by
  intro H H' h
  exact hashingError_le_of_le_add l l 0 H H' le_rfl (by simpa using h) (by simp)

/-- Clipping a signed rate at zero can only decrease the usual real hashing term. -/
theorem hashingError_ofReal_le (l k : ℝ) :
    hashingError l (ENNReal.ofReal k) ≤ (1 / 2) * Real.rpow 2 (-(1 / 2) * (k - l)) := by
  rw [hashingError_of_ne_top l ENNReal.ofReal_ne_top]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  have hk : k ≤ (ENNReal.ofReal k).toReal := by
    rw [ENNReal.toReal_ofReal']
    exact le_max_left _ _
  linarith

end InfoTheory.QuantumLHL
