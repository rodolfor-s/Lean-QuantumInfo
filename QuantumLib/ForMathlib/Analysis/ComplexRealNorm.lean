import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Norm of a nonnegative real complex number

Norm of a nonnegative real complex number.
-/


noncomputable section

/-- For a complex number with zero imaginary part and nonnegative real part, `‖c‖ = c.re`. -/
lemma _root_.Complex.norm_eq_re_of_nonneg_re_of_im_eq_zero {c : ℂ} (hre : 0 ≤ c.re) (him : c.im =
    0) :
    ‖c‖ = c.re := by
  rw [show ‖c‖ = Real.sqrt (c.normSq) from rfl,
    show c.normSq = c.re ^ 2 from by
      rw [Complex.normSq_apply, him, mul_zero, add_zero, sq],
    Real.sqrt_sq hre]

end
