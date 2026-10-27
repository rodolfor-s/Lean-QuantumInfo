import Mathlib.Analysis.Matrix.Order
import QCryptLean.Math.LinearAlgebra.Matrix.Transport

/-! # Partial transposition on product indices -/

namespace Matrix

variable {X Y Z W R : Type*}

/-- Transpose the right register of a rectangular product-indexed matrix. -/
def partialTransposeRight (A : Matrix (X × Y) (Z × W) R) : Matrix (X × W) (Z × Y) R :=
  of fun x y => A (x.1, y.2) (y.1, x.2)

/-- Partial transposition distributes over finite sums. -/
theorem partialTransposeRight_sum [AddCommMonoid R] {I : Type*} (s : Finset I)
    (A : I → Matrix (X × Y) (Z × W) R) :
    partialTransposeRight (∑ i ∈ s, A i) = ∑ i ∈ s, partialTransposeRight (A i) := by
  ext x y
  simp only [partialTransposeRight, of_apply, sum_apply]

open scoped Kronecker in
/-- Partial transposition transposes the right Kronecker factor. -/
theorem partialTransposeRight_kronecker [Mul R] (A : Matrix X Z R) (B : Matrix Y W R) :
    partialTransposeRight (A ⊗ₖ B) = A ⊗ₖ Bᵀ := rfl

open scoped ComplexOrder Kronecker in
/-- A sum of positive product matrices is positive after transposing the right register. -/
theorem posSemidef_partialTransposeRight_sum_kronecker {I : Type*} (s : Finset I)
    [Finite X] [Finite Y] (A : I → Matrix X X ℂ) (B : I → Matrix Y Y ℂ)
    (hA : ∀ i ∈ s, (A i).PosSemidef) (hB : ∀ i ∈ s, (B i).PosSemidef) :
    (partialTransposeRight (∑ i ∈ s, A i ⊗ₖ B i)).PosSemidef := by
  let := Fintype.ofFinite X
  let := Fintype.ofFinite Y
  rw [partialTransposeRight_sum]
  exact posSemidef_sum s fun i hi => (hA i hi).kronecker (hB i hi).transpose

end Matrix
