import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.Math.LinearAlgebra.Matrix.EntryIntegral
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PostMeasurementCQ
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.SiftedPassSupport
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.AcceptSplit
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.CKRMixture
import QCryptLean.Quantum.DeFinetti.Haar
import QCryptLean.Quantum.DeFinetti.HaarAlgebra
import QCryptLean.Quantum.DeFinetti.Integral
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Symmetry.Paired

/-! # The accepted paired-Haar marginal

Entrywise integration commutes with the complete linear reference experiment.
Discarding the reference preserves acceptance, so the same weight is obtained
from the CKR mixture on the signal register.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators Quantum.Channels Quantum.Symmetry
open Quantum.DeFinetti InfoTheory.SmoothMinEntropy
open QKD.BB84.Model QKD.BB84.Measurement Matrix MeasureTheory
open scoped Kronecker

variable (E : Type*) [Fintype E] [DecidableEq E]

/-- The accepted reference experiment on the paired symmetric state. -/
def enVRhoEtilde {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) : CQState (Signals n) (E × Signals n) :=
  postMeasurementCQSiftedLocalPEPassFilter (E × Signals n) peSel xSel Q δ
    (siftedTauPostMeasurementNormalizedCQState E pre hpre peSel xSel
      (pairedDeFinettiState Signal n))

/-- The accepted reference blocks are the paired-Haar integrals of their IID component blocks. -/
theorem rhoEtilde_eq_haar_integral_blocks {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (x : Signals n) (i j : E × Signals n) :
    ((enVRhoEtilde E pre hpre peSel xSel Q δ).stateMap x).toOp i j =
      ∫ ψ : DensityOp (Signal × Signal),
        ((pairedHaarPerSigmaFamily E pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
        ∂(haarDensityMeasure (((0, 0), (0, 0)) : Signal × Signal)).measure := by
  let : DecidableEq (Signals n) := Classical.decEq _
  let U := (siftedRotation n peSel xSel ⊗ₖ (1 : Op E)) ⊗ₖ (1 : Op (Signals n))
  let T : Operation (Signals n × Signals n) (E × Signals n) :=
    { toFun := fun M => (U * mapTensorId pre (Signals n) M * Uᴴ).submatrix
        (tauOutcomeEveRefEmbedding x) (tauOutcomeEveRefEmbedding x)
      map_add' := by
        intro A B
        simp only [map_add, Matrix.mul_add, Matrix.add_mul, submatrix_add]
        rfl
      map_smul' := by
        intro c A
        simp only [map_smul, Matrix.mul_smul, Matrix.smul_mul, submatrix_smul,
          RingHom.id_apply]
        rfl }
  let G := fun ψ : DensityOp (Signal × Signal) =>
    ((ψ.tensorPow n).reindex (pairFunctions Signal Signal n)).toOp
  have hg : ∀ a b, Integrable (fun ψ => G ψ a b)
      (haarDensityMeasure (((0, 0), (0, 0)) : Signal × Signal)).measure :=
    fun a b => integrable_tensorPow_entry _ n _ _
  have hp : (pairedDeFinettiState Signal n).toOp =
      Matrix.of (fun a b => ∫ ψ, G ψ a b
        ∂(haarDensityMeasure (((0, 0), (0, 0)) : Signal × Signal)).measure) := by
    change reindex (pairFunctions Signal Signal n) (pairFunctions Signal Signal n)
      (deFinettiState (Signal × Signal) n).toOp = _
    rw [deFinettiState_eq_haar_integral (((0, 0), (0, 0)) : Signal × Signal) n]
    rfl
  by_cases h : siftedLocalPETestPassed peSel xSel δ Q x = true
  · have he (τ : DensityOp (Signals n × Signals n)) :
        ((postMeasurementCQSiftedLocalPEPassFilter (E × Signals n) peSel xSel Q δ
          (siftedTauPostMeasurementNormalizedCQState E pre hpre peSel xSel τ)).stateMap x).toOp =
          T τ.toOp := by
      simp only [postMeasurementCQSiftedLocalPEPassFilter, CQState.filterKeep, h, ite_true]
      rfl
    change _ = ∫ ψ, _ ∂_
    simp only [enVRhoEtilde, pairedHaarPerSigmaFamily, he]
    rw [hp, linearMap_entryIntegral T G hg]
    rfl
  · simp [enVRhoEtilde, pairedHaarPerSigmaFamily, postMeasurementCQSiftedLocalPEPassFilter,
      CQState.filterKeep, h, SubDensityOp.zero]

/-- Tracing out the paired reference preserves the acceptance weight of the CKR mixture. -/
theorem rhoEtilde_acceptWeight_eq_ckrMixture {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    ∑ x, ((enVRhoEtilde E pre hpre peSel xSel Q δ).stateMap x).trace =
      ∑ ω, ((siftedLocalPEAcceptedPostMeasurementCQState E pre hpre peSel xSel
        (ckrMixtureMeasure ((0, 0) : Signal)) Q δ).stateMap ω).trace := by
  have hμ : integralTensorPowerDensity n (ckrMixtureMeasure ((0, 0) : Signal)) =
      ckrDeFinettiState Signal n := by
    apply DensityOp.ext
    exact integralTensorPower_ckrMixtureMeasure (0, 0) n
  have hp (ω : Signals n) :
      partialTraceRight ((enVRhoEtilde E pre hpre peSel xSel Q δ).stateMap ω).toOp =
        ((siftedLocalPEAcceptedPostMeasurementCQState E pre hpre peSel xSel
          (ckrMixtureMeasure ((0, 0) : Signal)) Q δ).stateMap ω).toOp := by
    apply partialTraceRight_passFilter_stateMap
    intro ω'
    rw [hμ]
    exact partialTraceRight_conditioned_eq E pre hpre peSel xSel (pairedDeFinettiState Signal n) ω'
  apply Finset.sum_congr rfl
  intro ω _
  unfold SubDensityOp.trace
  rw [← trace_partialTraceRight, hp ω]

end QKD.BB84.FiniteKey
