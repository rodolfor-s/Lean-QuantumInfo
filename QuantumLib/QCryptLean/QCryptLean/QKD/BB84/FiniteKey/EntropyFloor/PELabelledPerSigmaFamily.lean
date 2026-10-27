import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelAnalysis
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PerSigmaFamily
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.AcceptSplit
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.CKRMixture
import QCryptLean.Quantum.DeFinetti.Haar
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.StateOperations

/-! # The test-labelled component family and mixture

The announced test string remains a normalized classical projector in the
conditioning register. Attaching this fixed kernel preserves continuity,
integrability, the component integral and the total accepted weight.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators Quantum.Channels Quantum.DeFinetti
open InfoTheory.SmoothMinEntropy QKD.BB84.Model QKD.BB84.Measurement

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

private local instance {X : Type*} [Fintype X] : ContinuousENorm (Op X) :=
  SeminormedAddGroup.toContinuousENorm

/-- The announced sorted test outcomes, retained as a computational-basis state. -/
def peLabelKernel {n m : ℕ} (peSel : Fin n → Bool) (ω : Signals n) :
    SubDensityOp (Signals (min n m)) :=
  (stdNormKet ((partEquiv (m := m) peSel ω).2)).toDensityOp.toSubDensityOp

/-- Announcing a test string preserves its probability weight. -/
@[simp] lemma peLabelKernel_trace {n m : ℕ} (peSel : Fin n → Bool) (ω : Signals n) :
    (peLabelKernel (m := m) peSel ω).trace = 1 :=
  congrArg Complex.re (DensityOp.trace_one _)

/-- The test-label matrix has complex trace one. -/
lemma peLabelKernel_matrix_trace {n m : ℕ} (peSel : Fin n → Bool) (ω : Signals n) :
    (peLabelKernel (m := m) peSel ω).toOp.trace = 1 :=
  DensityOp.trace_one _

variable (E : Type*) [Fintype E] [DecidableEq E]

/-- The accepted paired reference with the complete test string announced. -/
def peLabelledEnVRhoEtilde {n m : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    CQState (Signals n) (Signals (min n m) × (E × Signals n)) :=
  (enVRhoEtilde E pre hpre peSel xSel Q δ).tensorLeftKernel (peLabelKernel (m := m) peSel)

/-- Each paired IID component with the same complete test announcement. -/
def peLabelledPairedHaarPerSigmaFamily {n m : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (ψ : DensityOp (Signal × Signal)) :
    CQState (Signals n) (Signals (min n m) × (E × Signals n)) :=
  (pairedHaarPerSigmaFamily E pre hpre peSel xSel Q δ ψ).tensorLeftKernel
    (peLabelKernel (m := m) peSel)

/-- The test-labelled component blocks are Bochner integrable for the local Frobenius norm. -/
theorem integrable_peLabelledPairedHaarPerSigmaFamily_blocks {n m : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (x : Signals n) :
    MeasureTheory.Integrable (fun ψ : DensityOp (Signal × Signal) =>
      ((peLabelledPairedHaarPerSigmaFamily (m := m) E pre hpre peSel xSel Q δ ψ).stateMap x).toOp)
      (haarDensityMeasure (((0, 0), (0, 0)) : Signal × Signal)).measure :=
  tensorLeftKernel_blocks_integrable _ _ x
    (integrable_pairedHaarPerSigmaFamily_blocks E pre hpre peSel xSel Q δ x)

/-- Attaching the test label commutes with the paired-Haar component integral. -/
theorem peLabelledRhoEtilde_eq_haar_integral_blocks {n m : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (x : Signals n)
    (i j : Signals (min n m) × (E × Signals n)) :
    ((peLabelledEnVRhoEtilde (m := m) E pre hpre peSel xSel Q δ).stateMap x).toOp i j =
      ∫ ψ : DensityOp (Signal × Signal),
        ((peLabelledPairedHaarPerSigmaFamily (m := m) E pre hpre peSel xSel Q δ ψ).stateMap x).toOp
          i j ∂(haarDensityMeasure (((0, 0), (0, 0)) : Signal × Signal)).measure :=
  tensorLeftKernel_blocks_integral_eq _ _ _
    (rhoEtilde_eq_haar_integral_blocks E pre hpre peSel xSel Q δ) x i j

/-- The test-labelled component blocks depend continuously on the paired state. -/
theorem continuous_peLabelledPairedHaarPerSigmaFamily_blocks {n m : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (x : Signals n) :
    Continuous (fun ψ : DensityOp (Signal × Signal) =>
      ((peLabelledPairedHaarPerSigmaFamily (m := m) E pre hpre peSel xSel Q δ ψ).stateMap
        x).toOp) :=
  tensorLeftKernel_blocks_continuous _ _ x
    (continuous_pairedHaarPerSigmaFamily_blocks E pre hpre peSel xSel Q δ x)

/-- The normalized test label leaves the accepted CKR-mixture weight unchanged. -/
theorem peLabelledRhoEtilde_acceptWeight_eq_ckrMixture {n m : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    ∑ x, ((peLabelledEnVRhoEtilde (m := m) E pre hpre peSel xSel Q δ).stateMap x).trace =
      ∑ ω, ((siftedLocalPEAcceptedPostMeasurementCQState E pre hpre peSel xSel
        (ckrMixtureMeasure ((0, 0) : Signal)) Q δ).stateMap ω).trace := by
  rw [peLabelledEnVRhoEtilde, CQState.tensorLeftKernel_weight _ _ (peLabelKernel_trace peSel)]
  exact rhoEtilde_acceptWeight_eq_ckrMixture E pre hpre peSel xSel Q δ

end QKD.BB84.FiniteKey
