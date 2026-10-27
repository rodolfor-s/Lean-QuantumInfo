import QCryptLean.Math.SpectralTheory.Matrix

/-!
# Positive matrix square roots and real scalars

The square root uses the matrix star order, installed only by the local scope.
No norm instance is needed for the finite-dimensional Hermitian calculus.
-/

namespace Matrix

open scoped ComplexOrder MatrixOrder

variable {X : Type*} [Fintype X]

open scoped Classical in
/-- A positive matrix square root pulls out a nonnegative real scalar. -/
theorem PosSemidef.sqrt_ofReal_smul {A : Matrix X X ℂ} (hA : A.PosSemidef)
    {c : ℝ} (hc : 0 ≤ c) :
    CFC.sqrt ((c : ℂ) • A) = (Real.sqrt c : ℂ) • CFC.sqrt A := by
  have hcC : (0 : ℂ) ≤ (c : ℂ) := by simpa using hc
  have hsC : (0 : ℂ) ≤ (Real.sqrt c : ℂ) := by simp
  have hL := hA.smul hcC
  have hR := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).smul hsC
  rw [CFC.sqrt_eq_iff _ _ hL.nonneg hR.nonneg]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, CFC.sqrt_mul_sqrt_self A hA.nonneg,
    ← Complex.ofReal_mul, Real.mul_self_sqrt hc]

open scoped Classical in
/-- A square root commutes with every operator commuting with its argument. -/
theorem sqrt_commute {A B : Matrix X X ℂ} (h : Commute A B) : Commute (CFC.sqrt A) B := by
  exact h.cfcₙ_nnreal NNReal.sqrt

end Matrix
