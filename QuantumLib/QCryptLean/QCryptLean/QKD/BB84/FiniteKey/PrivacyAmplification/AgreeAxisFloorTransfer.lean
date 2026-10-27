import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelInterchange
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelProjection
import QCryptLean.InfoTheory.SmoothMinEntropy.Normalized
import QCryptLean.InfoTheory.SmoothMinEntropy.Penalty
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.AnnounceConditioningCQ
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.ClassicalAnnounceKernel
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.KeyHashEC
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.SiftedPassSupport
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.AgreeBlock.Input
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.StateOperations

/-! # Agreement filtering on the classical axis

The PE and agreement inputs share the complete announcement and reference register.
Agreement filters the fine classical outcomes before coarsening to Alice's key;
it therefore costs no entropy and assumes no decoding property.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators Quantum.Channels
open InfoTheory.SmoothMinEntropy QKD.BB84.Model QKD.BB84.Measurement

/-- The PE-filtered labelled hashing input, retaining all announcements. -/
def peLabelledLHLInput {n m : ℕ} (ℓEV : ℕ)
    (E : Type*) [Fintype E] [DecidableEq E]
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {R : Type*} [Fintype R]
    (τ : DensityOp (Signals n × R)) :
    CQState (KeyBitString n peSel)
      ((Bits leakEC × (KeyHashSeed n ℓEV peSel × Bits ℓEV)) ×
        (Signals (min n m) × (E × R))) :=
  (aliceKeyAnnounceCQ peSel (fun ω => (partEquiv (m := m) peSel ω).2)
      (postMeasurementCQSiftedLocalPEPassFilter _ peSel xSel Q δ
        (siftedTauPostMeasurementNormalizedCQState E pre hpre peSel xSel
          τ).toCQState)).tensorLeftKernel
    (announceKernel ℓEV peSel ec)

/-- The common fine classical ancestor before Alice's key coarsening. -/
def peLabelledLHLFineInput {n m : ℕ} (ℓEV : ℕ)
    (E : Type*) [Fintype E] [DecidableEq E]
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {R : Type*} [Fintype R]
    (τ : DensityOp (Signals n × R)) :
    CQState (Signals n)
      ((Bits leakEC × (KeyHashSeed n ℓEV peSel × Bits ℓEV)) ×
        (Signals (min n m) × (E × R))) :=
  ((CQState.filterKeep (siftedLocalPETestPassed peSel xSel δ Q)
        (siftedTauPostMeasurementNormalizedCQState E pre hpre peSel xSel
            τ).toCQState).tensorLeftKernel
      (fun ω =>
        (stdNormKet ((partEquiv (m := m) peSel ω).2)).toDensityOp.toSubDensityOp)).tensorLeftKernel
    (fun ω => announceKernel ℓEV peSel ec (aliceKeyString peSel ω))

/-- The PE-labelled input is the Alice-key coarsening of its fine ancestor. -/
theorem peLabelledLHLInput_eq_coarsen {n m : ℕ} (ℓEV : ℕ)
    (E : Type*) [Fintype E] [DecidableEq E]
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {R : Type*} [Fintype R]
    (τ : DensityOp (Signals n × R)) :
    peLabelledLHLInput (m := m) ℓEV E pre hpre peSel xSel ec Q δ τ =
      CQState.coarsen (aliceKeyString peSel)
        (peLabelledLHLFineInput (m := m) ℓEV E pre hpre peSel xSel ec Q δ τ) := by
  rw [peLabelledLHLInput, peLabelledLHLFineInput, aliceKeyAnnounceCQ,
    announceCoarsenCQ, postMeasurementCQSiftedLocalPEPassFilter]
  exact (CQState.coarsen_tensorLeftKernel_factor
    _ (aliceKeyString peSel) (announceKernel ℓEV peSel ec)).symm

/-- Agreement is a second classical filter on the same fine ancestor. -/
theorem peAnnounceAgreeLHLInput_eq_coarsen_filterKeep {n m : ℕ}
    (ℓEV : ℕ) (E : Type*) [Fintype E] [DecidableEq E]
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {R : Type*} [Fintype R]
    (τ : DensityOp (Signals n × R)) :
    peAnnounceAgreeLHLInput (m := m) E ℓEV pre hpre peSel xSel ec Q δ τ =
      CQState.coarsen (aliceKeyString peSel)
        (CQState.filterKeep (fun ω => !siftedKeyStringsDiffer peSel ec ω)
          (peLabelledLHLFineInput (m := m) ℓEV E pre hpre peSel xSel ec Q δ τ)) := by
  rw [peAnnounceAgreeLHLInput, aliceKeyAnnounceCQ, announceCoarsenCQ,
    siftedAgreeAcceptCQState]
  rw [show (CQState.filterKeep (siftedAgreeAcceptKeep peSel xSel ec δ Q)
        (siftedTauPostMeasurementNormalizedCQState E pre hpre peSel xSel τ).toCQState) =
      CQState.filterKeep (fun ω => !siftedKeyStringsDiffer peSel ec ω)
        (CQState.filterKeep (siftedLocalPETestPassed peSel xSel δ Q)
          (siftedTauPostMeasurementNormalizedCQState E pre hpre peSel xSel τ).toCQState)
              from
    (CQState.filterKeep_filterKeep _ _ _).symm]
  rw [peLabelledLHLFineInput]
  conv_lhs => rw [CQState.tensorLeftKernel_filterKeep]
  conv_rhs => rw [← CQState.tensorLeftKernel_filterKeep]
  exact (CQState.coarsen_tensorLeftKernel_factor
    _ (aliceKeyString peSel) (announceKernel ℓEV peSel ec)).symm

/-- The agreement filter can only remove weight. -/
theorem peAnnounceAgreeLHLInput_weight_le_peLabelled {n m : ℕ}
    (ℓEV : ℕ) (E : Type*) [Fintype E] [DecidableEq E]
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {R : Type*} [Fintype R]
    (τ : DensityOp (Signals n × R)) :
    ∑ x : KeyBitString n peSel,
        ((peAnnounceAgreeLHLInput (m := m) E ℓEV pre hpre peSel xSel ec Q δ
          τ).stateMap x).trace ≤
      ∑ x : KeyBitString n peSel,
        ((peLabelledLHLInput (m := m) ℓEV E pre hpre peSel xSel ec Q δ
          τ).stateMap x).trace := by
  rw [peAnnounceAgreeLHLInput_eq_coarsen_filterKeep, peLabelledLHLInput_eq_coarsen]
  simp only [← CQState.quantumMarginal_trace, CQState.quantumMarginal_coarsen]
  simpa only [CQState.quantumMarginal_trace] using
    CQState.filterKeep_weight_le
      (peLabelledLHLFineInput (m := m) ℓEV E pre hpre peSel xSel ec Q δ τ)
      (fun ω => !siftedKeyStringsDiffer peSel ec ω)

/-- Filtering on agreement preserves every floor for the PE-labelled input. -/
theorem le_smoothMinEntropy_agreeInput_of_labelled
    {n m : ℕ} (ℓEV : ℕ)
    (E : Type*) [Fintype E] [DecidableEq E] [Nonempty E]
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    {R : Type*} [Fintype R]
    (τ : DensityOp (Signals n × R))
    (ε : ℝ)
    (σ : SubDensityOp ((Bits leakEC × (KeyHashSeed n ℓEV peSel × Bits ℓEV)) ×
        (Signals (min n m) × (E × R))))
    (k : ℝ)
    (hFloor : ENNReal.ofReal k ≤ smoothMinEntropy ε
      (peLabelledLHLInput (m := m) ℓEV E pre hpre peSel xSel ec Q δ τ) σ) :
    ENNReal.ofReal k ≤ smoothMinEntropy ε
      (peAnnounceAgreeLHLInput (m := m) E ℓEV pre hpre peSel xSel ec Q δ τ) σ := by
  let : Nonempty R := τ.nonempty.map Prod.snd
  rw [peAnnounceAgreeLHLInput_eq_coarsen_filterKeep]
  rw [peLabelledLHLInput_eq_coarsen] at hFloor
  refine le_trans hFloor
    (smoothMinEntropy_coarsen_filterKeep_ge ε
      (aliceKeyString peSel) (fun ω => !siftedKeyStringsDiffer peSel ec ω)
      (peLabelledLHLFineInput (m := m) ℓEV E pre hpre peSel xSel ec Q δ τ) σ)


end QKD.BB84.FiniteKey
