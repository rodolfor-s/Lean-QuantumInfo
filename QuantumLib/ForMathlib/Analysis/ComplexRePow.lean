import Mathlib.Analysis.Complex.Basic

/-!
# Real parts of powers of real complex numbers

Real parts of powers of real complex numbers.
-/


noncomputable section

/-- A complex number with zero imaginary part has real part compatible with
natural powers. -/
lemma _root_.Complex.re_pow_of_im_eq_zero (z : ℂ) (hz : z.im = 0) (n : ℕ) :
    (z ^ n).re = z.re ^ n := by
  have hz_eq : z = (z.re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hz]
  conv_lhs => rw [hz_eq]
  have h := congrArg Complex.re (Complex.ofReal_pow z.re n)
  rw [Complex.ofReal_re] at h
  exact h.symm

end
