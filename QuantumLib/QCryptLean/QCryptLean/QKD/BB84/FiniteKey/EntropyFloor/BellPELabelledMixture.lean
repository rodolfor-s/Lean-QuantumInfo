import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.Math.Analysis.CompactSpaceIntegrable
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PELabelledPerSigmaFloor
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PostMeasurementCQ
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.SiftedPassSupport
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.AcceptSplit
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.Haar
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Operators.Topology
import QCryptLean.Quantum.Symmetry.BellDoubling
import QCryptLean.Quantum.Symmetry.Paired

/-! # Analytic data for the accepted Bell mixture

Bell doubling is followed by the componentwise Boolean-to-bit equivalence.
The accepted component family retains the full reference; filtering commutes
with Bochner integration on each block without any normalization.
The Frobenius norm is selected only locally for these integrals.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators Quantum.Channels Quantum.Symmetry
open Quantum.DeFinetti InfoTheory.SmoothMinEntropy
open QKD.BB84.Model QKD.BB84.Measurement Matrix MeasureTheory
open scoped Kronecker

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

private local instance {X : Type*} [Fintype X] : ContinuousENorm (Op X) :=
  SeminormedAddGroup.toContinuousENorm

local notation "eSignal" => finTwoEquiv.symm.prodCongr finTwoEquiv.symm

/-- Each accepted Bell-component block depends continuously on its source state. -/
theorem continuous_bellPairedHaarPerSigmaFamily_blocks {n : ℕ}
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (x : Signals n) :
    Continuous (fun φ : DensityOp (Bool × Bool) =>
      ((pairedHaarPerSigmaFamily Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
        peSel xSel Q δ ((bellWembed φ).reindex ((eSignal).prodCongr eSignal))).stateMap x).toOp) :=
  (continuous_pairedHaarPerSigmaFamily_blocks Unit _ _ peSel xSel Q δ x).comp
    ((DensityOp.continuous_reindex _).comp continuous_bellWembed)

/-- Accepted Bell-component blocks are integrable against the Haar probability measure. -/
theorem integrable_bellPairedHaarPerSigmaFamily_blocks {n : ℕ}
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (x : Signals n) :
    Integrable (fun φ : DensityOp (Bool × Bool) =>
      ((pairedHaarPerSigmaFamily Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
        peSel xSel Q δ ((bellWembed φ).reindex ((eSignal).prodCongr eSignal))).stateMap x).toOp)
      (haarDensityMeasure (false, false)).measure := by
  have := (haarDensityMeasure (false, false)).isProbability
  exact (continuous_bellPairedHaarPerSigmaFamily_blocks peSel xSel Q δ x).integrable_of_compactSpace

/-- Every accepted reference block commutes with an arbitrary integrable source mixture. -/
theorem siftedLocalPE_blocks_eq_integral_of_toOp_eq_integral {n : ℕ}
    (E : Type*) [Fintype E] [DecidableEq E] {R : Type*} [Fintype R]
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (τ₀ : DensityOp (Signals n × R)) (τ : α → DensityOp (Signals n × R))
    (hint : Integrable (fun a => (τ a).toOp) μ)
    (hτ₀ : τ₀.toOp = ∫ a, (τ a).toOp ∂μ) (x : Signals n) (i j : E × R) :
    ((postMeasurementCQSiftedLocalPEPassFilter (E × R) peSel xSel Q δ
      (siftedTauPostMeasurementNormalizedCQState E pre hpre peSel xSel τ₀)).stateMap x).toOp i j =
      ∫ a, ((postMeasurementCQSiftedLocalPEPassFilter (E × R) peSel xSel Q δ
        (siftedTauPostMeasurementNormalizedCQState E pre hpre peSel xSel (τ a))).stateMap x).toOp
          i j ∂μ := by
  let : DecidableEq (Signals n) := Classical.decEq _
  let : DecidableEq R := Classical.decEq _
  let U := (siftedRotation n peSel xSel ⊗ₖ (1 : Op E)) ⊗ₖ (1 : Op R)
  let L : Op (Signals n × R) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun M => (U * mapTensorId pre R M * Uᴴ)
        (tauOutcomeEveRefEmbedding x i) (tauOutcomeEveRefEmbedding x j)
      map_add' := by
        intro M N
        simp only [map_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]
      map_smul' := by
        intro c M
        simp only [map_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
          RingHom.id_apply] }
  by_cases h : siftedLocalPETestPassed peSel xSel δ Q x = true
  · have he (σ : DensityOp (Signals n × R)) :
        ((postMeasurementCQSiftedLocalPEPassFilter (E × R) peSel xSel Q δ
          (siftedTauPostMeasurementNormalizedCQState E pre hpre peSel xSel σ)).stateMap x).toOp
            i j = L σ.toOp := by
      simp only [postMeasurementCQSiftedLocalPEPassFilter, CQState.filterKeep, h, ite_true]
      rfl
    simp only [he]
    rw [hτ₀]
    exact (L.integral_comp_comm hint).symm
  · simp [postMeasurementCQSiftedLocalPEPassFilter, CQState.filterKeep, h, SubDensityOp.zero]

/-- Grouped Bell-doubled IID states are Haar-integrable on the natural signal registers. -/
theorem bellWembed_reindexedTensorPow_integrable {n : ℕ} :
    Integrable (fun φ : DensityOp (Bool × Bool) =>
      ((((bellWembed φ).reindex ((eSignal).prodCongr eSignal)).tensorPow n).reindex
        (pairFunctions Signal Signal n)).toOp) (haarDensityMeasure (false, false)).measure := by
  have := (haarDensityMeasure (false, false)).isProbability
  have hc := (DensityOp.continuous_reindex ((eSignal).prodCongr eSignal)).comp continuous_bellWembed
  have hi : Continuous (fun φ : DensityOp (Bool × Bool) =>
      ((((bellWembed φ).reindex ((eSignal).prodCongr eSignal)).tensorPow n).reindex
        (pairFunctions Signal Signal n)).toOp) :=
    continuous_pi fun i => continuous_pi fun j =>
      (DensityOp.continuous_tensorPow_entry n _ _).comp hc
  exact hi.integrable_of_compactSpace

end QKD.BB84.FiniteKey
