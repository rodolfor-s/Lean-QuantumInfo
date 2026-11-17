import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Tactic

/-!
# Infinitude of the complex unit circle

Infinitude of the complex unit circle.
-/


noncomputable section

/-- The unit circle in ℂ is infinite (needed for polynomial root arguments). -/
lemma _root_.Complex.infinite_setOf_norm_eq_one : Set.Infinite (Set.ofPred (fun z : ℂ => ‖z‖ = 1))
    := by
  apply (Set.infinite_range_of_injective
    (f := fun n : ℕ => Complex.exp (↑(n : ℝ) * Complex.I))
    (fun a b hab => ?_)).mono
  · rintro _ ⟨n, rfl⟩; exact Complex.norm_exp_ofReal_mul_I n
  · rw [Complex.exp_eq_exp_iff_exists_int] at hab
    obtain ⟨k, hk⟩ := hab
    -- Take imaginary parts: ↑a = ↑b + k * (2 * π), so (a - b : ℝ) = 2πk
    have him : (a : ℝ) = (b : ℝ) + ↑k * (2 * Real.pi) := by
      have := congr_arg Complex.im hk
      simp [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
            Complex.add_im, Complex.mul_im] at this
      linarith
    -- Since π is irrational, k = 0
    have hk0 : k = 0 := by
      by_contra hk_ne
      exact irrational_pi ⟨((a : ℚ) - b) / (2 * k), by push_cast; field_simp; linarith⟩
    subst hk0; simp only [Int.cast_zero, zero_mul, add_zero] at him; exact_mod_cast him

end
