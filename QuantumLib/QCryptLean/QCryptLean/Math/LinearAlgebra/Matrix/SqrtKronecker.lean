import Mathlib.LinearAlgebra.Matrix.Kronecker
import QCryptLean.Math.SpectralTheory.Matrix

/-!
# Square roots of positive Kronecker products

The CFC square root uses the local matrix star order. No matrix norm instance is
selected: uniqueness among positive square roots is entirely algebraic here.
-/

namespace Matrix

open scoped Kronecker ComplexOrder MatrixOrder

variable {X Y : Type*} [Fintype X] [Fintype Y]

open scoped Classical in
/-- Positive square roots commute with Kronecker products on product registers. -/
theorem PosSemidef.sqrt_kronecker {A : Matrix X X ℂ} {B : Matrix Y Y ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    CFC.sqrt (A ⊗ₖ B) = CFC.sqrt A ⊗ₖ CFC.sqrt B := by
  classical
  apply CFC.sqrt_unique
  · rw [← mul_kronecker_mul, CFC.sqrt_mul_sqrt_self A (nonneg_iff_posSemidef.mpr hA),
      CFC.sqrt_mul_sqrt_self B (nonneg_iff_posSemidef.mpr hB)]
  · exact nonneg_iff_posSemidef.mpr
      ((nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).kronecker
        (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)))

end Matrix
