import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Cyclic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Paired
import QCryptLean.Quantum.Symmetry.Twirl

/-! # Symmetrization commutes with the roundwise system marginal -/
noncomputable section
namespace Quantum.Symmetry
open Matrix Quantum.Operators
open scoped Kronecker
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] {k : ℕ}

/-- Discarding one component of every round commutes with permutation averaging. -/
theorem partialTraceRight_reindex_symmetrize (ρ : DensityOp (Fin k → A × B)) :
    ((symmetrize ρ).reindex (pairFunctions A B k)).partialTraceRight =
      symmetrize (ρ.reindex (pairFunctions A B k)).partialTraceRight := by
  let f := reindexAlgEquiv ℂ ℂ (pairFunctions A B k)
  let L := (partialTraceRightLinearMap (S := ℂ)).comp f.toLinearMap
  apply DensityOp.ext
  change L (symmetrize ρ).toOp = (symmetrize _).toOp
  rw [symmetrize_toOp, map_smul, map_sum, symmetrize_toOp]
  apply congrArg ((1 / (k.factorial : ℂ)) • ·)
  apply Finset.sum_congr rfl
  intro σ _
  change partialTraceRight (f (permutationRepresentation σ * ρ.toOp *
    (permutationRepresentation σ)ᴴ)) = _
  rw [map_mul, map_mul]
  change partialTraceRight (reindex _ _ _ * reindex _ _ _ * reindex _ _ _ᴴ) = _
  rw [← conjTranspose_reindex, reindex_permutationRepresentation_pair,
    conjTranspose_kronecker]
  have hu : (permutationRepresentation (X := B) σ)ᴴ * permutationRepresentation σ = 1 :=
    (tensorPermutation_unitary σ).1
  exact partialTraceRight_kronecker_sandwich_of_mul_eq_one _ _ _ _ _ hu

end Quantum.Symmetry
