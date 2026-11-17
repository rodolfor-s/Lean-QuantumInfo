import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Completeness of sandwiched matrix families

An isometry on the output of a complete matrix family leaves its input Gram sum unchanged.
-/

open scoped Matrix BigOperators

noncomputable section

namespace Matrix

/-- **A complete Kraus family, sandwiched, has completeness sum `Rᴴ R`.** If `∑ᵢ Tᵢᴴ Tᵢ = 1` and
`L` is an isometry, then `∑ᵢ (L Tᵢ R)ᴴ (L Tᵢ R) = Rᴴ R`. -/
theorem sum_conjTranspose_mul_self_sandwich {k l m n ι S : Type*}
    [Semiring S] [StarRing S] [Fintype k] [Fintype l]
    [DecidableEq l] [Fintype m] [DecidableEq m] [Fintype ι]
    (L : Matrix k l S) (T : ι → Matrix l m S) (R : Matrix m n S)
    (hL : Lᴴ * L = 1) (hT : ∑ i, (T i)ᴴ * T i = 1) :
    ∑ i, (L * T i * R)ᴴ * (L * T i * R) = Rᴴ * R := by
  have h : ∀ i, (L * T i * R)ᴴ * (L * T i * R) = Rᴴ * ((T i)ᴴ * T i) * R := fun i => by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Lᴴ L, hL, Matrix.one_mul]
  rw [Fintype.sum_congr _ _ h, ← Matrix.sum_mul, ← Matrix.mul_sum, hT, Matrix.mul_one]

end Matrix
