import QCryptLean.InfoTheory.QuantumLHL.Extractor
import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.KeyHashEC
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.AgreeBlock.Input
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.AgreeBlock.Output
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Model.SiftedPEAnnounce
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Channels.ConsumerBounds
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Basic

/-! # Agree-block leftover-hashing distance bound

The complete public announcement stays in the LHL conditioning register.
The real and ideal output identities identify the same channel postprocess;
contractivity bounds half their CKR trace norm by the public-seed distance.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators Quantum.Channels Quantum.Metrics
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL
open QKD.BB84.Model QKD.BB84.Measurement

variable (E : Type*) [Fintype E] [DecidableEq E]
variable {R : Type*} [Fintype R]

open scoped Classical in
/-- Half the agree-restricted CKR norm is bounded by public-seed hashing distance,
including the full syndrome, verification seed/tag and test outcomes. -/
theorem half_mul_ckrTraceNorm_agree_le_traceDistanceGen
    {n m : ℕ} (ℓ ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    (τ : DensityOp (Signals n × R)) :
    (1 / 2) * ckrTraceNorm
      ((((1 / (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)) •
        krausMap (fun k => if siftedKeyStringsDiffer peSel ec k.2 then 0
          else Announced.passKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q k)).comp
        ((mapTensorId (classicalMap (id : Signals n → Signals n)) E).comp
          (siftedConjAfterPre E pre peSel xSel))) -
       (((1 / ((2 ^ ℓ : ℂ) * Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))) •
        krausMap (fun k => if siftedKeyStringsDiffer peSel ec k.1 then 0
          else Announced.idealPassKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q k)).comp
        ((mapTensorId (classicalMap (id : Signals n → Signals n)) E).comp
          (siftedConjAfterPre E pre peSel xSel)))) τ ≤
      traceDistanceGen
        (SeedKey.output (aliceKeyHashFamily n ℓ peSel)
          (peAnnounceAgreeLHLInput E (m := m) ℓEV pre hpre peSel xSel ec Q δ τ)
          ).toJointDensity.toOp
        (uniformCQState (C := KeyHashSeed n ℓ peSel × Bits ℓ)
          (peAnnounceAgreeLHLInput E (m := m) ℓEV pre hpre peSel xSel ec Q δ τ).quantumMarginal
          ).toJointDensity.toOp := by
  classical
  let Δ := (((1 / (Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel) : ℂ)) •
        krausMap (fun k => if siftedKeyStringsDiffer peSel ec k.2 then 0
          else Announced.passKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q k)).comp
        ((mapTensorId (classicalMap (id : Signals n → Signals n)) E).comp
          (siftedConjAfterPre E pre peSel xSel))) -
    (((1 / ((2 ^ ℓ : ℂ) * Fintype.card (KeyHashSeedPairEV n ℓ ℓEV peSel))) •
        krausMap (fun k => if siftedKeyStringsDiffer peSel ec k.1 then 0
          else Announced.idealPassKraus E n m ℓ ℓEV peSel xSel leakEC ec δ Q k)).comp
        ((mapTensorId (classicalMap (id : Signals n → Signals n)) E).comp
          (siftedConjAfterPre E pre peSel xSel)))
  have hmap : mapTensorId Δ R τ.toOp =
      peAnnounceAgreeLHLPostprocess E n m ℓ ℓEV leakEC peSel
        ((SeedKey.output (aliceKeyHashFamily n ℓ peSel)
          (peAnnounceAgreeLHLInput E (m := m) ℓEV pre hpre peSel xSel ec Q δ τ)
          ).toJointDensity.toOp -
        (uniformCQState (C := KeyHashSeed n ℓ peSel × Bits ℓ)
          (peAnnounceAgreeLHLInput E (m := m) ℓEV pre hpre peSel xSel ec Q δ τ).quantumMarginal
          ).toJointDensity.toOp) := by
    simp only [Δ, mapTensorId_sub, LinearMap.sub_apply,
      realAgreePass_mapTensorId_eq_lhlPostprocess_seedKeyOutput E ℓ ℓEV pre hpre,
      mapTensorId_idealAgree_eq_postprocess_uniformOutput E ℓ ℓEV pre hpre, map_sub]
  have h := ckrTraceNorm_le_two_traceDistanceGen_of_isChannel_comp_eq Δ τ
    (peAnnounceAgreeLHLPostprocess E n m ℓ ℓEV leakEC peSel)
    (isChannel_peAnnounceAgreeLHLPostprocess E n m ℓ ℓEV leakEC peSel) _ _ hmap
  linarith

end QKD.BB84.FiniteKey
