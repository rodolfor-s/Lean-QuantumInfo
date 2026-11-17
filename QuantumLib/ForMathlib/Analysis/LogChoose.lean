import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Logarithmic bounds for binomial coefficients

For positive `n`, twice the base-two logarithm of `C(n + 3, 3)` is at least four.
-/

namespace Real

/-- For positive `n`, the logarithmic quantity `2 log₂ C(n + 3, 3)` is at least four. -/
lemma four_le_two_mul_log_choose_add_three_div_log_two {n : ℕ} (hn : 0 < n) :
    4 ≤ 2 * Real.log (Nat.choose (n + 3) 3 : ℝ) / Real.log 2 := by
  have hg4 : (4 : ℝ) ≤ (Nat.choose (n + 3) 3 : ℝ) := by
    exact_mod_cast (show 4 ≤ Nat.choose (n + 3) 3 from
      (by norm_num : 4 = Nat.choose 4 3) ▸ Nat.choose_le_choose 3 (by omega))
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hg4
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow] at hlog
  norm_num at hlog
  rw [le_div_iff₀ hL]
  nlinarith

end Real
