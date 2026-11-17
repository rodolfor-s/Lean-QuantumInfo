import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Bounds on sums involving square roots

A nonnegative affine square-root budget is at least one when any error term crosses its threshold.
-/

namespace Real

/-- A nonnegative affine square-root expression exceeds one when its scale is at least four
and one of its nonnegative error terms exceeds the indicated threshold. -/
theorem one_le_add_mul_add_sqrt_of_large {g c E e p : ℝ}
    (hg : 4 ≤ g) (hc : 0 ≤ c) (he : 0 ≤ e) (hp : 0 ≤ p)
    (hlarge : 3 / 16 < e ∨ 1 / 8 ≤ E ∨ 1 / 2 ≤ p) :
    1 ≤ c + g * (p + 2 * (e + sqrt (2 * E))) := by
  have hsqrt := sqrt_nonneg (2 * E)
  have hinner : 1 / 4 ≤ p + 2 * (e + sqrt (2 * E)) := by
    rcases hlarge with hlarge | hlarge | hlarge
    · linarith
    · have hsq := sq_sqrt (show 0 ≤ 2 * E by linarith)
      have : 1 / 2 ≤ sqrt (2 * E) := by nlinarith
      linarith
    · linarith
  have hprod := mul_le_mul hg hinner (by norm_num) (by linarith : 0 ≤ g)
  linarith

end Real
