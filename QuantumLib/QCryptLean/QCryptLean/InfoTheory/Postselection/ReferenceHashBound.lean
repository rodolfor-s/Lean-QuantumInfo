import QCryptLean.InfoTheory.Postselection.ExtendedHashing
import QCryptLean.InfoTheory.Postselection.HashFactorization
import QCryptLean.InfoTheory.Postselection.InstrumentMixture
import QCryptLean.InfoTheory.Postselection.MeasureThenHash
import QCryptLean.InfoTheory.Postselection.Protocol
import QCryptLean.InfoTheory.QuantumLHL.HashingError
import QCryptLean.InfoTheory.QuantumLHL.Extractor
import QCryptLean.InfoTheory.QuantumLHL.HashOperation
import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.InstrumentReference
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.Math.Combinatorics.DeFinettiPrefactor
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Channels.Ancilla
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.Integral
import QCryptLean.Quantum.DeFinetti.PurificationMixture
import QCryptLean.Quantum.DeFinetti.PurificationMixtureBounds
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.StateOperations

/-! # Native reference secrecy from accepted IID hashing

The polynomial reference comes from the native rank bound. The pure-extension
trace-norm inequality replaces an unnecessary isometry-decoding witness.
-/
noncomputable section
namespace InfoTheory.Postselection
open Matrix Quantum.Operators Quantum.DeFinetti Quantum.Metrics
  Quantum.Channels InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL
  MeasureTheory Math.Combinatorics
open scoped ComplexOrder
variable {A B K C CE CP Raw E Public Seed Key R : Type*}
  [Fintype A] [Fintype B] [Fintype K] [Fintype C] [Fintype CE] [Fintype CP]
  [Fintype Raw] [Fintype E] [Fintype Public] [Fintype Seed] [Fintype Key] [Fintype R]
  [Nonempty Seed] [Nonempty Key] [DecidableEq Seed] [DecidableEq Key] [DecidableEq Public]
  {k l' : ℕ} {M : RawKeyMeasurement A B K C CE CP Raw E k}

/-- The extended hash distance bounds the corresponding amplified protocol difference. -/
theorem MeasureThenHash.half_traceNorm_le_extended_hashDistance
    (H : MeasureThenHash M Public Seed Key l')
    (ρ : DensityOp (((Fin k → A × B) × (Fin k → A × B)) × R)) :
    (1 / 2 : ℝ) * traceNorm (mapTensorId (M.toProtocol.roundDifferenceMap l')
      ((Fin k → A × B) × R) (ρ.reindex (Equiv.prodAssoc _ _ _)).toOp) ≤
        traceDistanceGen
          (InfoTheory.QuantumLHL.SeedKey.output H.hash
            (H.extendedRawKeyCQ ρ)).toJointDensity.toOp
          (uniformCQState (C := Seed × Key)
            (H.extendedRawKeyCQ ρ).quantumMarginal).toJointDensity.toOp := by
  let τ := ρ.reindex (Equiv.prodAssoc _ _ _)
  let q := CQState.ofInstrumentWithReference H.instrument H.instrument_isCompletelyPositive
    H.instrument_weight_le_one τ
  have hn : traceNorm
      ((InfoTheory.QuantumLHL.SeedKey.output H.hash
        (H.extendedRawKeyCQ ρ)).toJointDensity.toOp -
        (uniformCQState (C := Seed × Key)
          (H.extendedRawKeyCQ ρ).quantumMarginal).toJointDensity.toOp) =
      traceNorm (mapTensorId
        (InfoTheory.QuantumLHL.SeedKey.hashDifferenceOperation H.hash H.instrument)
        ((Fin k → A × B) × R) τ.toOp) := by
    unfold MeasureThenHash.extendedRawKeyCQ
    rw [InfoTheory.QuantumLHL.SeedKey.hashDifference_reindex, traceNorm_reindex,
      InfoTheory.QuantumLHL.SeedKey.hashDifference_reindex, traceNorm_reindex]
    rw [← InfoTheory.QuantumLHL.SeedKey.hashDifferenceOperation_apply H.hash
      (fun x => mapTensorId (H.instrument x) ((Fin k → A × B) × R)) τ.toOp q (fun _ => rfl),
      InfoTheory.QuantumLHL.SeedKey.hashDifferenceOperation_mapTensorId,
      traceNorm_reindex]
  rw [H.traceNorm_mapTensorId_eq_hashDifference]
  change (1 / 2 : ℝ) * traceNorm _ ≤ (1 / 2) * traceNorm _ + _
  rw [hn]
  exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (abs_nonneg _))

/-- Exact polynomial key shortening bounds the purified mixture's protocol difference. -/
theorem MeasureThenHash.referenceBound_of_component_hashing
    [Nonempty A] [Nonempty B]
    [Nonempty Raw] [Nonempty E] [DecidableEq Raw]
    (H : MeasureThenHash M Public Seed Key l') (μ : DensityMeasure (A × B))
    (S P : Set (DensityOp (A × B))) (hS : IsClosed S) (hP : IsClosed P)
    (hμ : ∀ᵐ σ ∂μ.measure, σ ∈ P)
    (εAT εPA εbar : ℝ) (hεPA : 0 ≤ εPA) (hεbar : 0 ≤ εbar)
    (hbad : ∑ x, (Matrix.of fun i j => ∫ σ in Sᶜ,
      ((M.rawKeyCQ σ).stateMap x).toOp i j ∂μ.measure).trace.re ≤ εAT)
    (hcomp : ∀ σ ∈ S ∩ P,
      hashingError M.toProtocol.l (smoothMinEntropy εbar (M.rawKeyCQ σ) M.sigmaE) ≤ εPA)
    (hl : (l' : ℝ) ≤ (M.toProtocol.l : ℝ) - 2 * Real.logb 2
      (deFinettiPrefactor (Fintype.card A ^ 2 * Fintype.card B ^ 2) k : ℝ)) :
    (1 / 2 : ℝ) * traceNorm (mapTensorId (M.toProtocol.roundDifferenceMap l')
      (Fin k → A × B) (integralTensorPowerDensity k μ).purification.toOp) ≤
        εPA + 2 * (εbar + Real.sqrt (2 * εAT)) := by
  classical
  let g := deFinettiPrefactor (Fintype.card A ^ 2 * Fintype.card B ^ 2) k
  have hg : 0 < g := deFinettiPrefactor_pos _ _
  let : NeZero g := ⟨hg.ne'⟩
  obtain ⟨ψ, hψ, hm⟩ := exists_isPure_partialTraceRight_eq_purificationMixture
    (R := Fin g) k μ (by simp [g, deFinettiPrefactor, Fintype.card_prod, mul_pow])
  let τ := ψ.reindex (Equiv.prodAssoc _ _ _)
  have ht : τ.IsPure := by
    change Matrix.reindex _ _ ψ.toOp * Matrix.reindex _ _ ψ.toOp = Matrix.reindex _ _ ψ.toOp
    exact ((Matrix.reindexAlgEquiv ℂ ℂ (Equiv.prodAssoc _ _ _)).map_mul _ _).symm.trans
      (congrArg (Matrix.reindex (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)) hψ)
  have htm : τ.partialTraceRight = integralTensorPowerDensity k μ := by
    apply DensityOp.ext
    change Matrix.partialTraceRight (Matrix.reindex (Equiv.prodAssoc _ _ _)
      (Equiv.prodAssoc _ _ _) ψ.toOp) = _
    rw [← Matrix.partialTraceRight_partialTraceRight]
    change ψ.partialTraceRight.partialTraceRight.toOp = _
    rw [hm, partialTraceRight_purificationMixture]
  have hn := traceNorm_mapTensorId_substate_bound (M.toProtocol.roundDifferenceMap l')
    (integralTensorPowerDensity k μ).purification.toOp
    (integralTensorPowerDensity k μ).purification.posSemidef τ ht 1 one_pos (by
      rw [htm, Complex.ofReal_one, one_smul]
      change ((integralTensorPowerDensity k μ).toOp -
        (integralTensorPowerDensity k μ).purification.partialTraceRight.toOp).PosSemidef
      rw [DensityOp.partialTraceRight_purification, sub_self]
      exact Matrix.PosSemidef.zero)
  rw [one_mul] at hn
  apply (mul_le_mul_of_nonneg_left hn (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans
  apply (H.half_traceNorm_le_extended_hashDistance ψ).trans
  apply H.extended_hashing_bound μ S P hS hP hμ εAT εPA εbar hεPA hεbar hbad hcomp
    (H.extendedRawKeyCQ ψ) (H.partialTraceRight_extendedRawKeyCQ μ ψ hm)
  simpa only [Fintype.card_fin] using hl

end InfoTheory.Postselection
