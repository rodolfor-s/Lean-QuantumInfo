import Mathlib.LinearAlgebra.Trace
import QCryptLean.Math.LinearAlgebra.Matrix.EntryIntegral
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.PurificationMixture
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.RankPurificationBounds
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Dimension
import QCryptLean.Quantum.Symmetry.Paired
import QCryptLean.Quantum.Symmetry.Purification

/-! # Purification Mixture Bounds -/


noncomputable section

namespace Quantum.DeFinetti

open scoped ComplexOrder

open Matrix Quantum.Operators Quantum.Symmetry MeasureTheory

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

private local instance {Z : Type*} [Fintype Z] : ContinuousENorm (Op Z) :=
  SeminormedAddGroup.toContinuousENorm

variable {X : Type*} [Fintype X] [DecidableEq X] {d k : ℕ}

/-- The canonical joint mixture is supported on paired symmetric vectors
by entrywise integration. -/
theorem purificationMixture_supported (k : ℕ) (μ : DensityMeasure X) :
    pairedProjector X k * (purificationMixture k μ).toOp * pairedProjector X k =
      (purificationMixture k μ).toOp := by
  have hi := Matrix.sandwich_entryIntegral (pairedProjector X k)
    (integrable_purificationTensorPow_entry μ k)
  simpa only [purificationMixture, purificationMixtureOp, pairedProjector_posSemidef.isHermitian.eq,
    purification_in_paired_symmetric_subspace _ (isPermutationInvariant_tensorPow _)] using hi

omit [DecidableEq X] in
/-- The canonical joint mixture has rank bounded by the symmetric dimension. -/
theorem rank_purificationMixture_le [Nonempty X] (k : ℕ) (μ : DensityMeasure X) :
    (purificationMixture k μ).toOp.rank ≤
      (k + Fintype.card X ^ 2 - 1).choose (Fintype.card X ^ 2 - 1) := by
  classical
  let P := symmetricProjector (X × X) k
  have hr : P.rank = (k + Fintype.card X ^ 2 - 1).choose (Fintype.card X ^ 2 - 1) := by
    simpa only [Fintype.card_prod, ← pow_two] using
      rank_symmetricProjector (X := X × X) (k := k)
  calc
    _ = (pairedProjector X k * (purificationMixture k μ).toOp * pairedProjector X k).rank :=
      congrArg Matrix.rank (purificationMixture_supported k μ).symm
    _ ≤ (pairedProjector X k).rank := Matrix.rank_mul_le_right _ _
    _ = P.rank := Matrix.rank_reindex _ _ _
    _ = _ := hr

omit [DecidableEq X] in
/-- Any reference large enough for the polynomial rank supports a pure extension of the mixture. -/
theorem exists_isPure_partialTraceRight_eq_purificationMixture [Nonempty X]
    {R : Type*} [Fintype R] (k : ℕ) (μ : DensityMeasure X)
    (hR : (k + Fintype.card X ^ 2 - 1).choose (Fintype.card X ^ 2 - 1) ≤ Fintype.card R) :
    ∃ ψ : DensityOp (((Fin k → X) × (Fin k → X)) × R), ψ.IsPure ∧
      ψ.partialTraceRight = purificationMixture k μ :=
  (purificationMixture k μ).exists_isPure_partialTraceRight_eq_of_rank_le
    ((rank_purificationMixture_le k μ).trans hR)

end Quantum.DeFinetti
