import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.BellPELabelledMixture
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.BellPurifier
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.SiftedPassSupport
import QCryptLean.QKD.BB84.FiniteKey.Postselection.BellReference
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
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.BellDoubling
import QCryptLean.Quantum.Symmetry.BellHaar
import QCryptLean.Quantum.Symmetry.BellMixture
import QCryptLean.Quantum.Symmetry.BellReference
import QCryptLean.Quantum.Symmetry.Paired
import QCryptLean.Quantum.Symmetry.Purification

/-! # Bell-reference identities for the inner budget

The accepted joint reference and its small-purifier extension use actual product
registers. The marginal, accept-weight and Haar-integral identities preserve the
complete unnormalized state, with the same Bell symmetric-dimension charge.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators Quantum.Channels Quantum.Symmetry
open Quantum.DeFinetti InfoTheory.SmoothMinEntropy
open QKD.BB84.Model QKD.BB84.Measurement Matrix MeasureTheory

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

private local instance {X : Type*} [Fintype X] : ContinuousENorm (Op X) :=
  SeminormedAddGroup.toContinuousENorm

local notation "eSignal" => finTwoEquiv.symm.prodCongr finTwoEquiv.symm
local notation "eSignals(" n ")" => Equiv.piCongrRight (fun _ : Fin n => eSignal)

/-- The canonical Bell reference is invariant under paired permutations of its signal words. -/
theorem isPairedPermInvariant_bellCKRDeFinettiPurification (n : ℕ) :
    IsPairedPermInvariant (bellCKRDeFinettiPurification n) :=
  isPairedPermInvariant_purification _
    ((isPermutationInvariant_bellDeFinettiDensity n).reindex eSignal)

/-- The accepted CQ experiment on the type-coherent Bell joint reference. -/
def bellEnVRhoEtilde {n : ℕ} (E : Type*) [Fintype E] [DecidableEq E]
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) : CQState (Signals n) (E × Signals n) :=
  postMeasurementCQSiftedLocalPEPassFilter (E × Signals n) peSel xSel Q δ
    (siftedTauPostMeasurementNormalizedCQState E pre hpre peSel xSel
      ((bellPairedDeFinettiState n).reindex ((eSignals(n)).prodCongr eSignals(n))))

/-- Discarding the small purifier commutes with extracting a conditional block. -/
theorem partialTrace_bellConditioned_eq {n : ℕ} (E : Type*) [Fintype E] [DecidableEq E]
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) {ρ₀ : DensityOp (Signals n × Signals n)}
    (V : BellPurifierOfMarginal n ρ₀) (ω : Signals n) :
    partialTraceRight (reindex (Equiv.prodAssoc E (Signals n) V.reg).symm
      (Equiv.prodAssoc E (Signals n) V.reg).symm
      (siftedTauEveRefConditioned E pre hpre peSel xSel (enVBellPurification V) ω).toOp) =
      (siftedTauEveRefConditioned E pre hpre peSel xSel ρ₀ ω).toOp := by
  rw [enVBellPurification, siftedTauEveRefConditioned_partialTraceRight_assoc,
    V.purifier_partialTraceRight]

/-- The accepted Bell extension traces down blockwise to the joint Bell reference experiment. -/
theorem enV_bellRhoEV_partialTraceRight_eq_forCoarsen {n : ℕ}
    (E : Type*) [Fintype E] [DecidableEq E]
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (V : BellSymmetricPurifier n) (x : Signals n) :
    partialTraceRight
      (((postMeasurementCQSiftedLocalPEPassFilter (E × (Signals n × V.reg)) peSel xSel Q δ
        (siftedTauPostMeasurementNormalizedCQState E pre hpre peSel xSel
          (enVBellPurification V))).reindex (Equiv.prodAssoc E (Signals n) V.reg).symm).stateMap
            x).toOp =
      ((bellEnVRhoEtilde E pre hpre peSel xSel Q δ).stateMap x).toOp := by
  by_cases hx : siftedLocalPETestPassed peSel xSel δ Q x = true
  · simpa only [bellEnVRhoEtilde, postMeasurementCQSiftedLocalPEPassFilter, CQState.filterKeep,
      hx, ite_true, CQState.reindex, SubDensityOp.reindex,
      siftedTauPostMeasurementNormalizedCQState] using
      partialTrace_bellConditioned_eq E pre hpre peSel xSel V x
  · simp [bellEnVRhoEtilde, postMeasurementCQSiftedLocalPEPassFilter, CQState.filterKeep,
      hx, CQState.reindex, SubDensityOp.reindex, SubDensityOp.zero]

/-- The accepted Bell mixture and canonical Bell purification have the same weight. -/
theorem bellEnVRhoEtilde_acceptWeight_eq {n : ℕ} (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    ∑ x, ((bellEnVRhoEtilde Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
      peSel xSel Q δ).stateMap x).trace =
      siftedEveVisiblePEPassWeight Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
        peSel xSel Q δ (bellCKRDeFinettiPurification n) := by
  have hm (τ : DensityOp (Signals n × Signals n)) (x : Signals n) :
      ((postMeasurementCQSiftedLocalPEPassFilter (Unit × Signals n) peSel xSel Q δ
        (siftedTauPostMeasurementNormalizedCQState Unit (unitRegisterEmbed n)
          (isChannel_unitRegisterEmbed n) peSel xSel τ)).stateMap x).trace =
      ((postMeasurementCQSiftedLocalPEPassFilter Unit peSel xSel Q δ
        (siftedPostMeasurementCQState Unit (unitRegisterEmbed n)
          (isChannel_unitRegisterEmbed n) peSel xSel τ.partialTraceRight)).stateMap x).trace := by
    unfold SubDensityOp.trace
    rw [← trace_partialTraceRight]
    apply congrArg (fun M : Op Unit => M.trace.re)
    apply partialTraceRight_passFilter_stateMap
    exact fun ω => partialTraceRight_conditioned_eq Unit _ _ peSel xSel τ ω
  unfold bellEnVRhoEtilde siftedEveVisiblePEPassWeight
  simp_rw [hm]
  apply congrArg (fun ρ => ∑ x, ((postMeasurementCQSiftedLocalPEPassFilter Unit peSel xSel Q δ
    (siftedPostMeasurementCQState Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
      peSel xSel ρ)).stateMap x).trace)
  rw [(isPurification_bellCKRDeFinettiPurification n).marginal]
  apply DensityOp.ext
  change partialTraceRight (reindex _ _ (bellPairedDeFinettiState n).toOp) = _
  rw [partialTraceRight_reindex]
  change reindex _ _ (bellPairedDeFinettiState n).partialTraceRight.toOp = _
  rw [bellPairedDeFinettiState_partialTraceRight]
  rfl

/-- The accepted Bell mixture is the blockwise Haar integral of Bell-doubled IID components. -/
theorem bellEnVRhoEtilde_eq_haar_integral_blocks {n : ℕ}
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (x : Signals n) (i j : Unit × Signals n) :
    ((bellEnVRhoEtilde Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
      peSel xSel Q δ).stateMap x).toOp i j =
      ∫ φ : DensityOp (Bool × Bool),
        ((pairedHaarPerSigmaFamily Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
          peSel xSel Q δ ((bellWembed φ).reindex ((eSignal).prodCongr eSignal))).stateMap x).toOp
            i j ∂(haarDensityMeasure (false, false)).measure := by
  let τ := fun φ : DensityOp (Bool × Bool) =>
    (((bellWembed φ).reindex ((eSignal).prodCongr eSignal)).tensorPow n).reindex
      (pairFunctions Signal Signal n)
  have hi : Integrable (fun φ => (τ φ).toOp) (haarDensityMeasure (false, false)).measure :=
    bellWembed_reindexedTensorPow_integrable
  apply siftedLocalPE_blocks_eq_integral_of_toOp_eq_integral Unit _ _ peSel xSel Q δ _ τ hi
  ext a b
  let L : Op (Signals n × Signals n) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun M => M a b
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change _ = L (∫ φ, (τ φ).toOp ∂(haarDensityMeasure (false, false)).measure)
  refine Eq.trans ?_ (L.integral_comp_comm hi)
  change (bellPairedDeFinettiState n).toOp ((eSignals(n)).symm a.1, (eSignals(n)).symm a.2)
    ((eSignals(n)).symm b.1, (eSignals(n)).symm b.2) = _
  rw [bellPairedDeFinettiState_eq_haar_integral]
  rfl

end QKD.BB84.FiniteKey
