import Mathlib.LinearAlgebra.Matrix.Permutation

/-! # Permutation Matrix -/


open Matrix
open scoped ComplexConjugate

namespace Equiv.Perm

/-- Conjugating a coordinate projector by a permutation matrix relabels its coordinate. -/
lemma permMatrix_conj_single {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Equiv.Perm α) (i : α) :
    Equiv.Perm.permMatrix ℂ σ.symm * Matrix.single i i (1 : ℂ) *
        (Equiv.Perm.permMatrix ℂ σ.symm)ᴴ =
      Matrix.single (σ i) (σ i) (1 : ℂ) := by
  rw [Matrix.conjTranspose_permMatrix]
  rw [PEquiv.toMatrix_toPEquiv_mul]
  rw [PEquiv.mul_toMatrix_toPEquiv]
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.single_apply, Equiv.Perm.inv_def,
    Equiv.eq_symm_apply, Equiv.symm_symm, id_eq]

/-- Permutation matrices are unitary: their conjugate transpose is a left inverse. -/
lemma permMatrix_conjTranspose_mul_self {α : Type*} [DecidableEq α]
    [Fintype α] (σ : Equiv.Perm α) :
    (Equiv.Perm.permMatrix ℂ σ)ᴴ * Equiv.Perm.permMatrix ℂ σ = 1 := by
  rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

/-- Multiplying a matrix unit by a permutation matrix relabels its row. -/
theorem permMatrix_mul_single {β γ R : Type*} [Semiring R] [Fintype β]
    [DecidableEq β] [DecidableEq γ]
    (σ : Equiv.Perm β) (out : β) (col : γ) (v : R) :
    Equiv.Perm.permMatrix R σ * (Matrix.single out col v) =
      Matrix.single (σ.symm out) col v := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  ext p q
  rw [Matrix.submatrix_apply, id_eq, Matrix.single_apply, Matrix.single_apply]
  have hcond : (out = σ p) ↔ (σ.symm out = p) := by
    constructor
    · intro h; rw [h, Equiv.symm_apply_apply]
    · intro h; rw [← h, Equiv.apply_symm_apply]
  by_cases hq : col = q
  · by_cases hp : σ.symm out = p
    · rw [ite_eq_left ⟨hcond.mpr hp, hq⟩, ite_eq_left ⟨hp, hq⟩]
    · rw [ite_eq_right (fun h => hp (hcond.mp h.1)), ite_eq_right (fun h => hp h.1)]
  · rw [ite_eq_right (fun h => hq h.2), ite_eq_right (fun h => hq h.2)]

end Equiv.Perm
