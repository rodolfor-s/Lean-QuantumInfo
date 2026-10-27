import QCryptLean.InfoTheory.Postselection.IIDProof
import QCryptLean.InfoTheory.Postselection.Lift
import QCryptLean.InfoTheory.Postselection.FixedMarginalChannelBound
import QCryptLean.InfoTheory.Postselection.FixedMarginalMeasure
import QCryptLean.InfoTheory.Postselection.InstrumentMixture
import QCryptLean.InfoTheory.Postselection.MeasureThenHash
import QCryptLean.InfoTheory.Postselection.Protocol
import QCryptLean.InfoTheory.Postselection.ReferenceHashBound
import QCryptLean.InfoTheory.QuantumLHL.HashingError
import QCryptLean.InfoTheory.Security.FiniteKey
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.MixtureWeight
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.Math.Combinatorics.DeFinettiPrefactor
import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.CKRMixture
import QCryptLean.Quantum.DeFinetti.Integral
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Symmetry.Paired

/-! # Coherent -/


noncomputable section

universe u s

namespace InfoTheory.Postselection

open Quantum.Operators Quantum.Channels
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL
open Math.Combinatorics
open MeasureTheory
open scoped ComplexOrder

variable {A B : Type*} [Fintype A] [Fintype B]

variable {K C CE CP Raw E Public : Type*} {Seed Key : Type u}
  [Fintype K] [Fintype C] [Fintype CE] [Fintype CP] [Fintype Raw] [Fintype E]
  [Fintype Public] [Fintype Seed] [Fintype Key]
  [Nonempty A] [Nonempty B] [Nonempty K] [Nonempty C] [Nonempty CE] [Nonempty CP]
  [Nonempty Raw] [Nonempty E] [Nonempty Public] [Nonempty Seed] [Nonempty Key]
  [DecidableEq A] [DecidableEq B] [DecidableEq Raw] [DecidableEq Public]
  [DecidableEq Seed] [DecidableEq Key] {k : ℕ}

omit [Nonempty Public] in
omit [Nonempty K] [Nonempty C] [Nonempty CE] [Nonempty CP] in
/-- Extended IID entropy implies coherent security with the CKR prefactor.
The proof retains registers throughout the native Haar, smoothing, and hashing reductions. -/
theorem isSecretAt_of_measureThenHash
    (M : RawKeyMeasurement A B K C CE CP Raw E k) (σA : DensityOp A)
    (hσA : σA.toOp.PosDef) (εAT εPA εbar : ℝ) (l' : ℕ)
    (goodSet : Set (DensityOp (A × B)))
    (hcondS : InfoTheory.Postselection.SatisfiesAcceptTestBound (fixedMarginalSet σA)
      (goodSet ∩ fixedMarginalSet σA) M.pAcc εAT)
    (hcondLHL : ∀ σ ∈ goodSet ∩ fixedMarginalSet σA,
      hashingError M.toProtocol.l (smoothMinEntropy εbar (M.rawKeyCQ σ) M.sigmaE) ≤ εPA)
    (hεPA : 0 ≤ εPA) (hεbar : 0 ≤ εbar)
    (H : MeasureThenHash M Public Seed Key l')
    (hl' : (l' : ℝ) ≤ (M.toProtocol.l : ℝ) - 2 * Real.logb 2
      (deFinettiPrefactor (Fintype.card A ^ 2 * Fintype.card B ^ 2) k))
    (hperm : PermutationCovariant (M.toProtocol.roundDifferenceMap l'))
    (hClosed : IsClosed goodSet) :
    M.toProtocol.IsSecretAt.{_, _, _, _, _, _, _, s} l' σA
      ((deFinettiPrefactor (Fintype.card A ^ 2 * Fintype.card B ^ 2) k : ℝ) *
        InfoTheory.Postselection.coherentIIDSecrecy εAT εPA εbar) := by
  classical
  let b : B := Classical.choice inferInstance
  let e : A ↪ B × (A × B) := ⟨fun a => (b, (a, b)), fun _ _ h =>
    congrArg (fun p => p.2.1) h⟩
  let μ := fixedMarginalHaarMeasure σA e
  have hμ := isFixedMarginalMeasure_fixedMarginalHaarMeasure σA e
  have hP : IsClosed (fixedMarginalSet (B := B) σA) :=
    isClosed_eq Quantum.DeFinetti.continuous_partialTraceRight continuous_const
  have hbad : ∑ x, (Matrix.of fun i j => ∫ σ in goodSetᶜ,
      ((M.rawKeyCQ σ).stateMap x).toOp i j ∂μ.measure).trace.re ≤ εAT := by
    apply CQState.sum_trace_entryIntegral_le μ M.rawKeyCQ H.continuous_rawKeyCQ goodSetᶜ
      hcondS.1.1
    filter_upwards [MeasureTheory.ae_restrict_mem hClosed.measurableSet.compl,
      MeasureTheory.ae_restrict_of_ae hμ] with σ hσg hσP
    exact hcondS.2.2 σ ⟨hσP, fun h => hσg h.1⟩
  have href := H.referenceBound_of_component_hashing μ goodSet (fixedMarginalSet σA)
    hClosed hP hμ εAT εPA εbar hεPA hεbar hbad hcondLHL hl'
  have href' : (1 / 2 : ℝ) * Quantum.Metrics.traceNorm
      (mapTensorId (M.toProtocol.roundDifferenceMap l') (Fin k → A × B)
        (Quantum.DeFinetti.integralTensorPowerDensity k μ).purification.toOp) ≤
      InfoTheory.Postselection.coherentIIDSecrecy εAT εPA εbar := by
    convert href using 1
    unfold InfoTheory.Postselection.coherentIIDSecrecy InfoTheory.Security.smoothingError
      InfoTheory.Security.acceptanceError
    ring
  intro R _ _ ρ hmarg
  let f := Quantum.Symmetry.pairFunctions A B k
  let ρ' := ρ.reindex (f.symm.prodCongr (Equiv.refl R))
  have hm : Matrix.reindex f f (Matrix.partialTraceRight ρ'.toOp) =
      Matrix.partialTraceRight ρ.toOp := by
    change Matrix.reindex f f (Matrix.partialTraceRight (Matrix.reindex
      (f.symm.prodCongr (Equiv.refl R)) (f.symm.prodCongr (Equiv.refl R)) ρ.toOp)) = _
    rw [Matrix.partialTraceRight_reindex]
    ext i j
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]
  have hb := traceNorm_mapTensorId_le_fixedMarginal σA hσA e k
    (M.toProtocol.roundDifferenceMap l') hperm ρ' (by rw [hm]; exact hmarg)
  have he : mapTensorId (M.toProtocol.roundDifferenceMap l') R ρ'.toOp =
      mapTensorId (M.toProtocol.differenceMap l') R ρ.toOp := by
    ext p q
    change M.toProtocol.differenceMap l' (Matrix.reindex f f
      (Matrix.of fun i j => ρ'.toOp (i, p.2) (j, q.2))) p.1 q.1 =
        M.toProtocol.differenceMap l' (Matrix.of fun i j => ρ.toOp (i, p.2) (j, q.2)) p.1 q.1
    congr 1
  rw [he] at hb
  calc
    _ ≤ (1 / 2 : ℝ) * ((deFinettiPrefactor (Fintype.card A ^ 2 * Fintype.card B ^ 2) k : ℝ) *
        Quantum.Metrics.traceNorm (mapTensorId (M.toProtocol.roundDifferenceMap l')
          (Fin k → A × B)
          (Quantum.DeFinetti.integralTensorPowerDensity k μ).purification.toOp)) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = (deFinettiPrefactor (Fintype.card A ^ 2 * Fintype.card B ^ 2) k : ℝ) *
        ((1 / 2 : ℝ) * Quantum.Metrics.traceNorm
          (mapTensorId (M.toProtocol.roundDifferenceMap l') (Fin k → A × B)
            (Quantum.DeFinetti.integralTensorPowerDensity k μ).purification.toOp)) := by
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left href' (Nat.cast_nonneg _)

end InfoTheory.Postselection
