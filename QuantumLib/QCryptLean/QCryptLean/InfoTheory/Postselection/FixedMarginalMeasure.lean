import QCryptLean.InfoTheory.Postselection.Protocol
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.Probability.UnitaryHaar
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.CKRMixture
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.EmbeddedPurification
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Topology

/-! # Haar measures on states with a prescribed marginal

The reference is the actual product `B × E`. An embedding specifies the
entangled basis; no dimension comparison or enumeration is needed.
-/
noncomputable section
namespace InfoTheory.Postselection
open Matrix Quantum.Operators Quantum.DeFinetti MeasureTheory
variable {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
  [DecidableEq A] [DecidableEq B] [DecidableEq E]

/-- A state distribution is supported almost everywhere on the prescribed marginal. -/
def IsFixedMarginalMeasure (σA : DensityOp A) (μ : DensityMeasure (A × B)) : Prop :=
  ∀ᵐ σ ∂μ.measure, σ ∈ fixedMarginalSet σA

/-- Discard the environment of an embedded purification, retaining the two system registers. -/
def fixedMarginalSingleRoundState (σA : DensityOp A) (e : A ↪ B × E)
    (U : unitaryGroup (B × E) ℂ) : DensityOp (A × B) :=
  ((σA.embeddedPurification e U).reindex (Equiv.prodAssoc A B E).symm).partialTraceRight

/-- Every single-round Haar sample has exactly the prescribed Alice marginal. -/
theorem partialTraceRight_fixedMarginalSingleRoundState (σA : DensityOp A)
    (e : A ↪ B × E) (U : unitaryGroup (B × E) ℂ) :
    (fixedMarginalSingleRoundState σA e U).partialTraceRight = σA := by
  apply DensityOp.ext
  change Matrix.partialTraceRight (Matrix.partialTraceRight
    (reindex (Equiv.prodAssoc A B E).symm (Equiv.prodAssoc A B E).symm
      (σA.embeddedPurification e U).toOp)) = _
  rw [partialTraceRight_partialTraceRight]
  simp only [Matrix.reindex_apply, Matrix.submatrix_submatrix, Equiv.symm_symm]
  change Matrix.partialTraceRight (σA.embeddedPurification e U).toOp = _
  exact congrArg DensityOp.toOp (σA.partialTraceRight_embeddedPurification e U)

/-- The single-round state depends continuously on the Haar unitary. -/
theorem continuous_fixedMarginalSingleRoundState (σA : DensityOp A) (e : A ↪ B × E) :
    Continuous (fixedMarginalSingleRoundState σA e) :=
  continuous_partialTraceRight.comp
    ((DensityOp.continuous_reindex (Equiv.prodAssoc A B E).symm).comp
      (σA.continuous_embeddedPurification e))

/-- Push normalized Haar measure forward through the fixed-marginal state construction. -/
def fixedMarginalHaarMeasure (σA : DensityOp A) (e : A ↪ B × E) :
    DensityMeasure (A × B) where
  measure := Measure.map (fixedMarginalSingleRoundState σA e)
    (UnitaryGroup.haarProbUnitary (B × E))
  isProbability := by
    let := UnitaryGroup.isProbabilityMeasure_haarProbUnitary (B × E)
    exact (Measure.isProbabilityMeasure_map_iff
      (continuous_fixedMarginalSingleRoundState σA e).measurable.aemeasurable).mpr inferInstance

/-- The Haar pushforward is supported on extensions of the prescribed marginal. -/
theorem isFixedMarginalMeasure_fixedMarginalHaarMeasure (σA : DensityOp A)
    (e : A ↪ B × E) : IsFixedMarginalMeasure σA (fixedMarginalHaarMeasure σA e) := by
  apply (ae_map_iff (continuous_fixedMarginalSingleRoundState σA e).measurable.aemeasurable
    ?_).mpr
  · exact Filter.Eventually.of_forall fun U =>
      partialTraceRight_fixedMarginalSingleRoundState σA e U
  · exact (isClosed_eq continuous_partialTraceRight continuous_const).measurableSet

end InfoTheory.Postselection
