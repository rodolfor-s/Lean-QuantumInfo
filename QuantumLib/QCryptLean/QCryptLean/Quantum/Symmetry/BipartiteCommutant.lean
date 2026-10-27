import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Sandwich
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Paired
import QCryptLean.Quantum.Symmetry.SymmetricMarginal
import QCryptLean.Quantum.Symmetry.TensorUnitaryCommutant

/-! # Commutation and permutation transfer for bipartite symmetric projectors -/
noncomputable section
namespace Quantum.Symmetry
open Matrix Quantum.Operators
open scoped Kronecker
variable {X Y A : Type*} [Fintype X] [Fintype Y] [Fintype A]
  [DecidableEq X] [DecidableEq Y] [DecidableEq A] {k : ℕ}

/-- A simultaneous site permutation fixes the bipartite symmetric projector. -/
theorem kronecker_permutation_mul_pairedProjectorOf (σ : Equiv.Perm (Fin k)) :
    (permutationRepresentation (X := X) σ ⊗ₖ permutationRepresentation (X := Y) σ) *
      pairedProjectorOf X Y k = pairedProjectorOf X Y k := by
  rw [← reindex_permutationRepresentation_pair]
  change (reindexAlgEquiv ℂ ℂ (pairFunctions X Y k)) _ *
    (reindexAlgEquiv ℂ ℂ (pairFunctions X Y k)) _ = (reindexAlgEquiv ℂ ℂ (pairFunctions X Y k)) _
  rw [← map_mul, permutationRepresentation_mul_symmetricProjector]

/-- A commuting first-register operator commutes with the joint symmetric projector. -/
theorem commute_kronecker_one_pairedProjectorOf (C : Op (Fin k → X))
    (hC : ∀ σ : Equiv.Perm (Fin k), Commute C (permutationRepresentation σ)) :
    Commute (C ⊗ₖ (1 : Op (Fin k → Y))) (pairedProjectorOf X Y k) := by
  rw [pairedProjectorOf_eq_sum]
  apply Commute.smul_right
  apply Commute.sum_right
  intro σ _
  unfold Commute SemiconjBy
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, (hC σ).eq]

/-- Tensor permutations commute with uniform tensor powers on the second register. -/
theorem tensorUnitaryRepresentation_commute_generator (D : Op A)
    (σ : Equiv.Perm (Fin k)) (U : unitaryGroup Y ℂ) :
    Commute (tensorUnitaryRepresentation A Y k U).val
      (D ⊗ₖ permutationRepresentation (X := Y) σ) := by
  change ((1 : Op A) ⊗ₖ Op.tensorPow U.val k) * _ = _ * ((1 : Op A) ⊗ₖ Op.tensorPow U.val k)
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  exact congrArg (D ⊗ₖ ·) (tensorPermutation_mul_piTensorProduct_const σ U.val).symm

/-- The bipartite symmetric projector commutes with uniform second-register unitaries. -/
theorem tensorUnitaryRepresentation_commute_pairedProjectorOf (U : unitaryGroup Y ℂ) :
    Commute (tensorUnitaryRepresentation (Fin k → X) Y k U).val (pairedProjectorOf X Y k) := by
  rw [pairedProjectorOf_eq_sum]
  exact (Commute.sum_right _ _ _ (fun σ _ =>
    tensorUnitaryRepresentation_commute_generator (permutationRepresentation σ) σ U)).smul_right _

/-- A second-register permutation transfers to the first in the symmetric marginal. -/
theorem partialTraceRight_kronecker_permutation_mul_pairedProjectorOf
    (D : Op (Fin k → X)) (σ : Equiv.Perm (Fin k)) :
    partialTraceRight ((D ⊗ₖ permutationRepresentation (X := Y) σ) *
      pairedProjectorOf X Y k) =
      D * permutationRepresentation (X := X) σ⁻¹ *
        partialTraceRight (pairedProjectorOf X Y k) := by
  have hs : ((1 : Op (Fin k → X)) ⊗ₖ permutationRepresentation (X := Y) σ) *
      pairedProjectorOf X Y k =
      (permutationRepresentation (X := X) σ⁻¹ ⊗ₖ (1 : Op (Fin k → Y))) *
        pairedProjectorOf X Y k := by
    calc
      _ = (permutationRepresentation (X := X) σ⁻¹ ⊗ₖ (1 : Op (Fin k → Y))) *
          ((permutationRepresentation (X := X) σ ⊗ₖ permutationRepresentation (X := Y) σ) *
            pairedProjectorOf X Y k) := by
        rw [← Matrix.mul_assoc, ← mul_kronecker_mul, Matrix.one_mul]
        simp only [permutationRepresentation, tensorPermutation_mul, inv_mul_cancel,
          tensorPermutation_one]
      _ = _ := by rw [kronecker_permutation_mul_pairedProjectorOf]
  have he : D ⊗ₖ permutationRepresentation (X := Y) σ =
      (D ⊗ₖ (1 : Op (Fin k → Y))) *
        ((1 : Op (Fin k → X)) ⊗ₖ permutationRepresentation (X := Y) σ) := by
    rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [he, Matrix.mul_assoc, hs, ← Matrix.mul_assoc, ← mul_kronecker_mul,
    Matrix.one_mul, partialTraceRight_kronecker_one_mul]

end Quantum.Symmetry
