import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Transport between isometric matrix encodings

`Matrix.exists_conj_eq_conj_of_isometry` relates two isometric encodings of the same matrix.
The explicit transport `J * Eᴴ` preserves the support of the first encoding and conjugates it
into the second, including for the zero matrix.
`Matrix.isometry_dim_le` bounds the input dimension of an isometry by its output dimension.
-/

open scoped Matrix ComplexOrder

namespace Matrix

/-- Decode one isometric encoding of an operator into another. The decoder is
an isometry on the encoded operator's support, including when that operator is zero. -/
lemma exists_conj_eq_conj_of_isometry {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α]
    (E : Matrix β α ℂ) (J : Matrix γ α ℂ)
    (hE : Eᴴ * E = 1) (hJ : Jᴴ * J = 1) (A : Matrix α α ℂ) :
    ∃ V : Matrix γ β ℂ,
      Vᴴ * V * (E * A * Eᴴ) = E * A * Eᴴ ∧
      J * A * Jᴴ = V * (E * A * Eᴴ) * Vᴴ := by
  refine ⟨J * Eᴴ, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [Matrix.mul_assoc E Jᴴ, ← Matrix.mul_assoc Jᴴ J Eᴴ, hJ, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Eᴴ E, hE, Matrix.one_mul]
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Eᴴ E, hE, Matrix.one_mul,
      ← Matrix.mul_assoc Eᴴ E, hE, Matrix.one_mul]

/-- An isometry over a nontrivial commutative ring cannot decrease dimension. -/
theorem isometry_dim_le {α β R : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [CommRing R] [Nontrivial R] [Star R] (K : Matrix β α R) (hK : Kᴴ * K = 1) :
    Fintype.card α ≤ Fintype.card β := by
  calc
    Fintype.card α = (Kᴴ * K).rank := by rw [hK, Matrix.rank_one]
    _ ≤ K.rank := Matrix.rank_mul_le_right _ _
    _ ≤ Fintype.card β := Matrix.rank_le_card_height K

end Matrix
