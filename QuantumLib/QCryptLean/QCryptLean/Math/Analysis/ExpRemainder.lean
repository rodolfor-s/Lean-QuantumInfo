import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# An exponential remainder inequality

An exponential remainder inequality.
-/

noncomputable section

/-- For `t ≥ 0`, `exp(t) - 1 ≤ t * exp(t)`.
    Follows from `1 - exp(-t) ≤ t` and multiplication by `exp(t)`. -/
lemma _root_.Real.exp_sub_one_le_mul_exp {t : ℝ} (_ht : 0 ≤ t) :
    Real.exp t - 1 ≤ t * Real.exp t := by
  have h : 1 - Real.exp (-t) ≤ t := by
    have := Real.one_sub_le_exp_neg t
    calc 1 - Real.exp (-t) = -(Real.exp (-t) - 1 + t) + t := by ring
      _ ≤ -0 + t := by linarith
      _ = t := by ring
  calc Real.exp t - 1
      = Real.exp t * (1 - Real.exp (-t)) := by
          rw [mul_sub, mul_one, ← Real.exp_add]
          simp
    _ ≤ Real.exp t * t := mul_le_mul_of_nonneg_left h (Real.exp_pos t).le
    _ = t * Real.exp t := by ring

end
