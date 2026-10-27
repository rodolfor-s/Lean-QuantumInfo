import QCryptLean.InfoTheory.Postselection.MeasureThenHash
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.InstrumentReference
import QCryptLean.Math.LinearAlgebra.Matrix.EntryIntegral
import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.PurificationMixture
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Operators.Topology

/-! # Accepted mixtures and correlated raw-key extensions

All mixtures and instrument maps use the actual finite registers. Matrix norms
are local Frobenius instances for continuity; integrals are defined entrywise.
-/
noncomputable section
namespace InfoTheory.Postselection
open Matrix Quantum.Operators Quantum.Channels
  Quantum.DeFinetti MeasureTheory InfoTheory.SmoothMinEntropy
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
variable {A B K C CE CP Raw E Public Seed Key R : Type*}
  [Fintype A] [Fintype B] [Fintype K] [Fintype C] [Fintype CE] [Fintype CP]
  [Fintype Raw] [Fintype E] [Fintype Public] [Fintype Seed] [Fintype Key] [Fintype R]
  [Nonempty Seed] [Nonempty Key] [DecidableEq Seed] [DecidableEq Key] [DecidableEq Public]
  {k l' : ℕ} {M : RawKeyMeasurement A B K C CE CP Raw E k}

/-- The accepted CQ state of the mixture of canonical IID purifications. -/
def MeasureThenHash.acceptMixture (H : MeasureThenHash M Public Seed Key l')
    (μ : DensityMeasure (A × B)) : CQState Raw E :=
  (CQState.ofInstrumentWithReference H.instrument H.instrument_isCompletelyPositive
    H.instrument_weight_le_one (purificationMixture k μ)).reindex H.condEquiv

/-- Every stored IID raw-key block is continuous in the single-round state. -/
theorem MeasureThenHash.continuous_rawKeyCQ (H : MeasureThenHash M Public Seed Key l')
    (x : Raw) : Continuous (fun σ : DensityOp (A × B) => ((M.rawKeyCQ σ).stateMap x).toOp) := by
  let L := (Matrix.reindexLinearEquiv ℂ ℂ H.condEquiv H.condEquiv).toLinearMap.comp
    (mapTensorId (H.instrument x) (Fin k → A × B))
  have ht : Continuous (fun σ : DensityOp (A × B) => σ.tensorPow k) :=
    continuous_induced_rng.mpr (continuous_pi fun i => continuous_pi fun j =>
      DensityOp.continuous_tensorPow_entry k i j)
  have he : (fun σ : DensityOp (A × B) => ((M.rawKeyCQ σ).stateMap x).toOp) =
      fun σ => L (σ.tensorPow k).purification.toOp := funext fun σ => H.rawKeyCQ_stateMap_toOp σ x
  rw [he]
  exact L.toContinuousLinearMap.continuous.comp
    (DensityOp.continuous_toOp.comp (continuous_purification.comp ht))

/-- Applying the instrument to the purification mixture integrates the actual IID raw-key blocks. -/
theorem MeasureThenHash.acceptMixture_block_integral (H : MeasureThenHash M Public Seed Key l')
    (μ : DensityMeasure (A × B)) (x : Raw) :
    ((H.acceptMixture μ).stateMap x).toOp =
      Matrix.of (fun i j => ∫ σ, ((M.rawKeyCQ σ).stateMap x).toOp i j ∂μ.measure) := by
  let L := (Matrix.reindexLinearEquiv ℂ ℂ H.condEquiv H.condEquiv).toLinearMap.comp
    (mapTensorId (H.instrument x) (Fin k → A × B))
  change L (purificationMixtureOp k μ) = _
  rw [purificationMixtureOp, Matrix.linearMap_entryIntegral L _
    (integrable_purificationTensorPow_entry μ k)]
  ext i j
  exact integral_congr_ae (Filter.Eventually.of_forall fun σ =>
    congrArg (fun D : Op E => D i j) (H.rawKeyCQ_stateMap_toOp σ x).symm)

/-- Apply the raw-key instrument while retaining a further correlated reference. -/
def MeasureThenHash.extendedRawKeyCQ (H : MeasureThenHash M Public Seed Key l')
    (ρ : DensityOp (((Fin k → A × B) × (Fin k → A × B)) × R)) : CQState Raw (E × R) :=
  ((CQState.ofInstrumentWithReference H.instrument H.instrument_isCompletelyPositive
    H.instrument_weight_le_one (ρ.reindex (Equiv.prodAssoc _ _ _))).reindex
      (Equiv.prodAssoc Public (Fin k → A × B) R).symm).reindex
        (H.condEquiv.prodCongr (Equiv.refl R))

/-- The correlated raw-key extension has precisely the accepted mixture as its marginal. -/
theorem MeasureThenHash.partialTraceRight_extendedRawKeyCQ
    (H : MeasureThenHash M Public Seed Key l') (μ : DensityMeasure (A × B))
    (ρ : DensityOp (((Fin k → A × B) × (Fin k → A × B)) × R))
    (hρ : ρ.partialTraceRight = purificationMixture k μ) :
    (H.extendedRawKeyCQ ρ).partialTraceRight = H.acceptMixture μ := by
  have he := CQState.partialTraceRight_ofInstrumentWithReference_assoc H.instrument
    H.instrument_isCompletelyPositive H.instrument_weight_le_one ρ
  rw [hρ] at he
  apply CQState.ext
  funext x
  apply SubDensityOp.ext
  change Matrix.partialTraceRight (Matrix.reindex (H.condEquiv.prodCongr (Equiv.refl R))
    (H.condEquiv.prodCongr (Equiv.refl R)) _) = _
  rw [Matrix.partialTraceRight_reindex]
  exact congrArg (fun τ : CQState Raw (Public × (Fin k → A × B)) =>
    Matrix.reindex H.condEquiv H.condEquiv (τ.stateMap x).toOp) he

end InfoTheory.Postselection
