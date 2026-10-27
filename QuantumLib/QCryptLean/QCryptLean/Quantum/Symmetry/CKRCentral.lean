import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Paired

/-! # The CKR marginal as a central permutation average -/
noncomputable section
namespace Quantum.Symmetry
open Matrix Quantum.Operators
open scoped Kronecker
variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {k : ℕ}

/-- The CKR marginal is the character-weighted permutation average. -/
theorem ckrDeFinettiState_eq_sum :
    (ckrDeFinettiState X k).toOp =
      (symmetricProjector (X × X) k).trace⁻¹ • ((1 / (k.factorial : ℂ)) •
        ∑ σ : Equiv.Perm (Fin k), (permutationRepresentation (X := X) σ).trace •
          permutationRepresentation (X := X) σ) := by
  change partialTraceRight ((symmetricProjector (X × X) k).trace⁻¹ •
    pairedProjector X k) = _
  rw [partialTraceRight_smul]
  rw [pairedProjector_eq_sum, partialTraceRight_smul, partialTraceRight_sum]
  simp only [partialTraceRight_kronecker]

/-- Commuting with every site permutation suffices to commute with the CKR marginal. -/
theorem commute_ckrDeFinettiState_of_commute (A : Op (Fin k → X))
    (hA : ∀ σ : Equiv.Perm (Fin k), Commute A (permutationRepresentation σ)) :
    Commute A (ckrDeFinettiState X k).toOp := by
  change A * _ = _ * A
  rw [ckrDeFinettiState_eq_sum]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro σ _
  rw [(hA σ).eq]

/-- The CKR marginal is unchanged by transposition in the product basis. -/
theorem transpose_ckrDeFinettiState : (ckrDeFinettiState X k).toOpᵀ =
    (ckrDeFinettiState X k).toOp := by
  rw [ckrDeFinettiState_eq_sum]
  simp only [transpose_smul, transpose_sum]
  congr 2
  have ht (σ : Equiv.Perm (Fin k)) :
      (permutationRepresentation (X := X) σ)ᵀ = permutationRepresentation σ⁻¹ :=
    tensorPermutation_transpose σ
  have htr (σ : Equiv.Perm (Fin k)) :
      (permutationRepresentation (X := X) σ).trace =
        (permutationRepresentation (X := X) σ⁻¹).trace := by
    rw [← ht, trace_transpose]
  simp only [ht]
  apply Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin k)))
  intro σ
  rw [htr σ]
  rfl

/-- A nonempty local register makes every site-permutation character nonzero. -/
theorem trace_permutationRepresentation_ne_zero (σ : Equiv.Perm (Fin k)) :
    (permutationRepresentation (X := X) σ).trace ≠ 0 := by
  have h : (permutationRepresentation (X := X) σ).trace =
      ((Finset.univ.filter (fun x : Fin k → X => x = x ∘ σ.symm)).card : ℂ) := by
    simp only [Matrix.trace, Matrix.diag_apply, permutationRepresentation, tensorPermutation,
      Matrix.of_apply, Finset.sum_boole]
  rw [h]
  apply Nat.cast_ne_zero.mpr
  apply ne_of_gt
  apply Finset.card_pos.mpr
  exact ⟨fun _ => Classical.choice ‹Nonempty X›, by simp [Function.comp_def]⟩

end Quantum.Symmetry
