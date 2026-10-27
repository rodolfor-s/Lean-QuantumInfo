import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# Inverse square root of two

Inverse square root of two.
-/


noncomputable section

/-- Helper: (√2)⁻¹ * (√2)⁻¹ = 1/2 -/
lemma _root_.Complex.inv_sqrt_two_mul_self :
    ((Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹) = (1/2 : ℂ) := by
  rw [← mul_inv]
  have h : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    norm_cast
    rw [← sq]
    exact Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)
  rw [h]
  norm_num

/-!
## Normalization
-/

/-- Helper: (1 / √2) * conj(1 / √2) = 1/2 -/
lemma _root_.Complex.one_div_sqrt_two_mul_conj :
    (1 / Real.sqrt 2 : ℂ) * (starRingEnd ℂ) (1 / Real.sqrt 2 : ℂ) = (1 / 2 : ℂ) := by
  norm_num
  have : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)
  field_simp
  ring_nf
  norm_cast
  linarith [sq_nonneg (Real.sqrt 2)]

end
