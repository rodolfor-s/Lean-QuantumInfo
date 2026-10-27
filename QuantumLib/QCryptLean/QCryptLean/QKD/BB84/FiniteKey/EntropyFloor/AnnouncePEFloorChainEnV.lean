import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelProjection
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PerSigmaFamily
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.SiftedPassSupport
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.SymmetricPurifier
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Symmetry.Paired

/-! # Discarding the small symmetric purifier

The common trailing-spectator identity applies to the complete conditional
experiment. The classical acceptance filter commutes with discarding that
spectator, recovering the accepted paired reference without normalization.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators Quantum.Channels Quantum.Symmetry
open InfoTheory.SmoothMinEntropy QKD.BB84.Model QKD.BB84.Measurement Matrix

variable (E : Type*) [Fintype E] [DecidableEq E]

/-- Discarding the small purifier in one conditional block recovers the paired reference block. -/
lemma enV_siftedTauEveRefConditioned_partialTraceRight_eq {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (V : SymmetricPurifier n) (ω : Signals n) :
    partialTraceRight (reindex (Equiv.prodAssoc E (Signals n) V.reg).symm
      (Equiv.prodAssoc E (Signals n) V.reg).symm
      (siftedTauEveRefConditioned E pre hpre peSel xSel (enVCKRPurification V) ω).toOp) =
      (siftedTauEveRefConditioned E pre hpre peSel xSel (pairedDeFinettiState Signal n)
        ω).toOp := by
  rw [enVCKRPurification, siftedTauEveRefConditioned_partialTraceRight_assoc,
    V.purifier_partialTraceRight]

/-- The same trace-out identity holds in every accepted, unnormalized CQ block. -/
theorem enV_rhoEV_partialTraceRight_eq_forCoarsen {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (V : SymmetricPurifier n) (x : Signals n) :
    partialTraceRight
      (((postMeasurementCQSiftedLocalPEPassFilter (E × (Signals n × V.reg)) peSel xSel Q δ
        (siftedTauPostMeasurementNormalizedCQState E pre hpre peSel xSel
          (enVCKRPurification V))).reindex (Equiv.prodAssoc E (Signals n) V.reg).symm).stateMap
            x).toOp =
      ((enVRhoEtilde E pre hpre peSel xSel Q δ).stateMap x).toOp := by
  by_cases hx : siftedLocalPETestPassed peSel xSel δ Q x = true
  · simpa only [enVRhoEtilde, postMeasurementCQSiftedLocalPEPassFilter, CQState.filterKeep,
      hx, ite_true, CQState.reindex, SubDensityOp.reindex,
      siftedTauPostMeasurementNormalizedCQState] using
      enV_siftedTauEveRefConditioned_partialTraceRight_eq E pre hpre peSel xSel V x
  · simp [enVRhoEtilde, postMeasurementCQSiftedLocalPEPassFilter, CQState.filterKeep,
      hx, CQState.reindex, SubDensityOp.reindex, SubDensityOp.zero]

end QKD.BB84.FiniteKey
