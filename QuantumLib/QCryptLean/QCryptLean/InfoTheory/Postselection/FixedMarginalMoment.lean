import QCryptLean.InfoTheory.Postselection.FixedMarginalMeasure
import QCryptLean.Math.Analysis.CompactSpaceIntegrable
import QCryptLean.Math.LinearAlgebra.Matrix.EntryIntegral
import QCryptLean.Math.LinearAlgebra.Matrix.TensorFamilyTrace
import QCryptLean.Math.LinearAlgebra.Matrix.TensorSqrt
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.RankOne
import QCryptLean.Math.Probability.MatrixHaarAverage
import QCryptLean.Math.Probability.UnitaryHaar
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.EmbeddedPurification
import QCryptLean.Quantum.Operators.EmbeddedPurificationTensor
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Operators.Topology
import QCryptLean.Quantum.Symmetry.EmbeddedEntanglement
import QCryptLean.Quantum.Symmetry.Paired
import QCryptLean.Quantum.Symmetry.RegisterRegroup
import QCryptLean.Quantum.Symmetry.TensorUnitaryCommutant

/-! # The purified Haar reference and its fixed-marginal tensor mixture -/
noncomputable section
namespace InfoTheory.Postselection
open Matrix Quantum.Operators Quantum.DeFinetti
  Quantum.Symmetry MeasureTheory
open scoped Kronecker ComplexOrder MatrixOrder
variable {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
  [DecidableEq A] [DecidableEq B] [DecidableEq E]

/-- Tensor powers of embedded purifications, with all environment sites grouped at the right. -/
def fixedMarginalPureTensor (σA : DensityOp A) (e : A ↪ B × E) (k : ℕ)
    (U : unitaryGroup (B × E) ℂ) : DensityOp ((Fin k → A × B) × (Fin k → E)) :=
  ((((σA.embeddedPurification e U).reindex (Equiv.prodAssoc A B E).symm).tensorPow k).reindex
    (pairFunctions (A × B) E k))

/-- Every entry of the purified tensor sample is continuous in the Haar unitary. -/
theorem continuous_fixedMarginalPureTensor_entry (σA : DensityOp A) (e : A ↪ B × E)
    (k : ℕ) (i j : (Fin k → A × B) × (Fin k → E)) :
    Continuous (fun U => (fixedMarginalPureTensor σA e k U).toOp i j) :=
  (DensityOp.continuous_tensorPow_entry k _ _).comp
    ((DensityOp.continuous_reindex (Equiv.prodAssoc A B E).symm).comp
      (σA.continuous_embeddedPurification e))

/-- The purified Haar reference, defined by entrywise integration on its natural registers. -/
def fixedMarginalReference (σA : DensityOp A) (e : A ↪ B × E) (k : ℕ) :
    Op ((Fin k → A × B) × (Fin k → E)) :=
  of fun i j => ∫ U, (fixedMarginalPureTensor σA e k U).toOp i j
    ∂UnitaryGroup.haarProbUnitary (B × E)

/-- The purified Haar reference is positive semidefinite. -/
theorem fixedMarginalReference_posSemidef (σA : DensityOp A) (e : A ↪ B × E) (k : ℕ) :
    (fixedMarginalReference σA e k).PosSemidef := by
  let := UnitaryGroup.isProbabilityMeasure_haarProbUnitary (B × E)
  exact posSemidef_entryIntegral (fun U => (fixedMarginalPureTensor σA e k U).posSemidef)
    (fun i j => (continuous_fixedMarginalPureTensor_entry σA e k i j).integrable_of_compactSpace)

/-- Discarding the purification environments gives the fixed-marginal tensor-power mixture. -/
theorem partialTraceRight_fixedMarginalReference (σA : DensityOp A) (e : A ↪ B × E)
    (k : ℕ) : partialTraceRight (fixedMarginalReference σA e k) =
      integralTensorPower k (fixedMarginalHaarMeasure σA e) := by
  let := UnitaryGroup.isProbabilityMeasure_haarProbUnitary (B × E)
  rw [fixedMarginalReference, partialTraceRight_entryIntegral
    (fun i j => (continuous_fixedMarginalPureTensor_entry σA e k i j).integrable_of_compactSpace)]
  ext i j
  change (∫ U, partialTraceRight (fixedMarginalPureTensor σA e k U).toOp i j
    ∂UnitaryGroup.haarProbUnitary (B × E)) =
      ∫ σ, (σ.tensorPow k).toOp i j ∂Measure.map (fixedMarginalSingleRoundState σA e)
        (UnitaryGroup.haarProbUnitary (B × E))
  rw [integral_map (continuous_fixedMarginalSingleRoundState σA e).measurable.aemeasurable
    (DensityOp.continuous_tensorPow_entry k i j).measurable.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with U
  exact congrFun (congrFun (partialTraceRight_reindex_piTensorProduct
    (fun _ : Fin k => ((σA.embeddedPurification e U).reindex
      (Equiv.prodAssoc A B E).symm).toOp)) i) j

/-- Regrouping the purified reference exhibits its square-root-filtered Haar twirl. -/
theorem reindex_fixedMarginalReference (σA : DensityOp A) (e : A ↪ B × E) (k : ℕ) :
    reindex (regroupTriple A B E k) (regroupTriple A B E k)
      (fixedMarginalReference σA e k) =
      (CFC.sqrt (σA.tensorPow k).toOp ⊗ₖ (1 : Op (Fin k → B × E))) *
        unitaryHaarAverage (tensorUnitaryRepresentation (Fin k → A) (B × E) k)
          (embeddedMaxEntangled
            (e.arrowCongrRight : (Fin k → A) ↪ (Fin k → B × E))).projector *
        (CFC.sqrt (σA.tensorPow k).toOp ⊗ₖ (1 : Op (Fin k → B × E)))ᴴ := by
  have hs : CFC.sqrt (σA.tensorPow k).toOp = Op.tensorPow (CFC.sqrt σA.toOp) k :=
    PosSemidef.sqrt_piTensorProduct (fun _ : Fin k => σA.toOp) (fun _ => σA.posSemidef)
  rw [hs, ← σA.integral_tensorPow_embeddedPurification e k]
  rfl

end InfoTheory.Postselection
