import Mathlib.Data.Matrix.ColumnRowPartitioned
import QCryptLean.Math.LinearAlgebra.Matrix.UnitaryGram
import QCryptLean.Math.SpectralTheory.Matrix

/-!
# Rectangular factors of dominated Gram matrices

Complete the smaller Gram matrix by its positive deficit, use the native Gram
isometry, and discard its auxiliary columns. The conclusion uses positivity,
without any matrix norm instance.
-/

namespace Matrix
noncomputable section
open scoped MatrixOrder ComplexOrder

open Classical in
/-- Gram domination admits a right factor whose row Gram is at most the identity. -/
theorem exists_mul_eq_of_posSemidef_rowGram_sub
    {X Y Z : Type*} [Finite X] [Fintype Y] [Fintype Z]
    (A : Matrix X Y ℂ) (B : Matrix X Z ℂ) (h : (A * Aᴴ - B * Bᴴ).PosSemidef) :
    ∃ W : Matrix Y Z ℂ, B = A * W ∧ (1 - W * Wᴴ).PosSemidef := by
  classical
  let := Fintype.ofFinite X
  let D := CFC.sqrt (A * Aᴴ - B * Bᴴ)
  have hd : D * Dᴴ = A * Aᴴ - B * Bᴴ := h.eq_cfcSqrt_mul_conjTranspose.symm
  let C : Matrix X (Z ⊕ X ⊕ Y) ℂ := fromCols B (fromCols D 0)
  have hc : A * Aᴴ = C * Cᴴ := by
    simp only [C, conjTranspose_fromCols_eq_fromRows_conjTranspose,
      fromCols_mul_fromRows, conjTranspose_zero, Matrix.mul_zero, add_zero, hd]
    abel
  have hn : Fintype.card Y ≤ Fintype.card (Z ⊕ X ⊕ Y) := by
    simp only [Fintype.card_sum]
    omega
  obtain ⟨U, hu, he⟩ := exists_coisometry_of_rowGram_eq A C hc hn
  let W := U.submatrix id Sum.inl
  let V := U.submatrix id Sum.inr
  have hsplit : W * Wᴴ + V * Vᴴ = 1 := by
    rw [← hu]
    ext i j
    simp only [W, V, Matrix.mul_apply, conjTranspose_apply, submatrix_apply, id_eq,
      Matrix.add_apply, Fintype.sum_sum_type]
  refine ⟨W, ?_, ?_⟩
  · ext i j
    have hh := congrFun (congrFun he i) (Sum.inl j)
    simpa only [C, fromCols_apply_inl, W, Matrix.mul_apply, submatrix_apply, id_eq] using hh
  · have hv : 1 - W * Wᴴ = V * Vᴴ := by rw [← hsplit]; abel
    rw [hv]
    exact posSemidef_self_mul_conjTranspose V

end
end Matrix
