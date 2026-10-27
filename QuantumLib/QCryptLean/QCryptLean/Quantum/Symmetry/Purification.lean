import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Paired
import QCryptLean.Quantum.Symmetry.PairedAlgebra

/-! # Purification -/


noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators
open scoped Kronecker MatrixOrder ComplexOrder

variable {X : Type*} [Fintype X] [DecidableEq X] {d k : ℕ}

/-- The canonical purification vector is fixed by simultaneous site permutations. -/
theorem permutationRepresentation_kronecker_mulVec_purificationKet
    (ρ : DensityOp (Fin k → X)) (hρ : IsPermutationInvariant ρ) (σ : Equiv.Perm (Fin k)) :
    (permutationRepresentation σ ⊗ₖ permutationRepresentation σ) *ᵥ
      ρ.purificationKet.toKet.vec = ρ.purificationKet.toKet.vec := by
  classical
  let e := Equiv.arrowCongr σ (Equiv.refl X)
  have he : reindex e e ρ.toOp = ρ.toOp := by
    ext x y
    exact (isPermutationInvariant_iff ρ).mp hρ σ x y
  have hs := Matrix.reindex_cfcSqrt ρ.posSemidef e
  rw [he] at hs
  ext p
  change ((permutationRepresentation σ ⊗ₖ permutationRepresentation σ) *ᵥ
    (fun q => CFC.sqrt ρ.toOp q.1 q.2)) p = CFC.sqrt ρ.toOp p.1 p.2
  simp only [mulVec, dotProduct, kroneckerMap_apply, permutationRepresentation,
    tensorPermutation, Matrix.of_apply, eq_comp_symm_iff, Fintype.sum_prod_type,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Fintype.sum_ite_eq]
  exact congrArg (fun M => M p.1 p.2) hs

/-- Canonical purification of an invariant state is invariant under the paired action.
The vectorized square root is fixed by every paired permutation. -/
theorem isPairedPermInvariant_purification (ρ : DensityOp (Fin k → X))
    (hρ : IsPermutationInvariant ρ) : IsPairedPermInvariant ρ.purification := by
  intro σ
  let v := ρ.purificationKet.toKet.vec
  have hv := permutationRepresentation_kronecker_mulVec_purificationKet ρ hρ σ
  have hl : (permutationRepresentation σ ⊗ₖ permutationRepresentation σ) *
      ρ.purification.toOp = ρ.purification.toOp := by
    change _ * vecMulVec v (star v) = vecMulVec v (star v)
    rw [mul_vecMulVec, hv]
  rw [hl]
  have hr := congrArg Matrix.conjTranspose hl
  simpa only [conjTranspose_mul, ρ.purification.isHermitian.eq] using hr

/-- Canonical purification of an invariant state is supported on the paired symmetric subspace.
The averaged paired action fixes the purification vector and hence its projector. -/
theorem purification_in_paired_symmetric_subspace (ρ : DensityOp (Fin k → X))
    (hρ : IsPermutationInvariant ρ) :
    pairedProjector X k * ρ.purification.toOp * pairedProjector X k = ρ.purification.toOp := by
  let v := ρ.purificationKet.toKet.vec
  have hv : pairedProjector X k *ᵥ v = v := by
    dsimp only [v]
    rw [pairedProjector_eq_sum, Matrix.smul_mulVec, Matrix.sum_mulVec]
    simp only [permutationRepresentation_kronecker_mulVec_purificationKet ρ hρ,
      Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    rw [one_div_mul_cancel (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)), one_smul]
  have hl : pairedProjector X k * ρ.purification.toOp = ρ.purification.toOp := by
    change _ * vecMulVec v (star v) = vecMulVec v (star v)
    rw [mul_vecMulVec, hv]
  rw [hl]
  have hr := congrArg Matrix.conjTranspose hl
  simpa only [conjTranspose_mul, ρ.purification.isHermitian.eq,
    pairedProjector_posSemidef.isHermitian.eq] using hr

/-- An invariant state has a pure, paired-invariant symmetric extension with its exact marginal. -/
theorem symmetric_purification_with_pure (ρ : DensityOp (Fin k → X))
    (hρ : IsPermutationInvariant ρ) :
    ∃ ψ : DensityOp ((Fin k → X) × (Fin k → X)), ψ.IsPure ∧
      IsPairedPermInvariant ψ ∧
      pairedProjector X k * ψ.toOp * pairedProjector X k = ψ.toOp ∧
      ψ.partialTraceRight = ρ :=
  ⟨ρ.purification, ρ.isPure_purification, isPairedPermInvariant_purification ρ hρ,
    purification_in_paired_symmetric_subspace ρ hρ, ρ.partialTraceRight_purification⟩

end Quantum.Symmetry
