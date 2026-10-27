import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.Normalized
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.AnnounceConditioningCQ
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.ClassicalAnnounceKernel
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.SiftedPassSupport
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Model.SiftedPEAnnounce
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.QKD.KeyedOutputRegister
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Operators.Basic

/-! # Agree-block hashing input and postprocessing

The accepted CQ input retains the complete syndrome, verification seed/tag and
test string. The postprocess measures only the hashing seed/key register, copies
that key, and structurally rearranges the full conditioning operator into the
public output and retained reference. Announcement coherences are retained.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators Quantum.Channels
open InfoTheory.SmoothMinEntropy QKD.BB84.Model QKD.BB84.Measurement

variable (E : Type*) [Fintype E] [DecidableEq E]
variable {R : Type*} [Fintype R]

/-- Keep precisely the accepted outcomes on which Alice and Bob's corrected keys agree. -/
def siftedAgreeAcceptCQState {n : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    (τ : DensityOp (Signals n × R)) : CQState (Signals n) (E × R) :=
  (siftedTauPostMeasurementNormalizedCQState E pre hpre peSel xSel τ).toCQState.filterKeep
    (siftedAgreeAcceptKeep peSel xSel ec δ Q)

/-- Alice's agree-block LHL input, retaining every disclosed value on the conditioning side. -/
def peAnnounceAgreeLHLInput {n m : ℕ} (ℓEV : ℕ)
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) {leakEC : ℕ} (ec : ECScheme n peSel leakEC) (Q δ : ℝ)
    (τ : DensityOp (Signals n × R)) :
    CQState (KeyBitString n peSel)
      ((Bits leakEC × (KeyHashSeed n ℓEV peSel × Bits ℓEV)) ×
        (Signals (min n m) × (E × R))) :=
  (aliceKeyAnnounceCQ peSel (fun ω => (partEquiv (m := m) peSel ω).2)
    (siftedAgreeAcceptCQState E pre hpre peSel xSel ec Q δ τ)).tensorLeftKernel
      (announceKernel ℓEV peSel ec)

omit [Fintype E] [DecidableEq E] [Fintype R] in
/-- Assemble the actual public tuple while exposing Eve and the external reference. -/
def peAnnounceAgreeLHLPostprocessEquiv (n m ℓ ℓEV leakEC : ℕ) (peSel : Fin n → Bool) :
    (((Bits ℓ × Bits ℓ) × (Bool × KeyHashSeed n ℓ peSel)) ×
      ((Bits leakEC × (KeyHashSeed n ℓEV peSel × Bits ℓEV)) ×
        (Signals (min n m) × (E × R)))) ≃
      ((KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E) × R) where
  toFun p :=
    (((p.1.1, (p.1.2.1, ((((p.1.2.2, p.2.1.2.1), p.2.1.2.2), p.2.1.1), p.2.2.1))),
      p.2.2.2.1), p.2.2.2.2)
  invFun p :=
    ((p.1.1.1, (p.1.1.2.1, p.1.1.2.2.1.1.1.1)),
      ((p.1.1.2.2.1.2, (p.1.1.2.2.1.1.1.2, p.1.1.2.2.1.1.2)),
        (p.1.1.2.2.2, (p.1.2, p.2))))

/-- Copy the hashed key and publish the retained announcement tuple on the full operator space. -/
def peAnnounceAgreeLHLPostprocess (n m ℓ ℓEV leakEC : ℕ) (peSel : Fin n → Bool) :
    Operation (((Bits leakEC × (KeyHashSeed n ℓEV peSel × Bits ℓEV)) ×
      (Signals (min n m) × (E × R))) × (KeyHashSeed n ℓ peSel × Bits ℓ))
      ((KeyedOutput ℓ (PEAnnouncePublic n m ℓ ℓEV peSel leakEC) × E) × R) :=
  let e := peAnnounceAgreeLHLPostprocessEquiv E n m ℓ ℓEV leakEC peSel
  (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap.comp
    ((mapTensorId (classicalMap (fun sz : KeyHashSeed n ℓ peSel × Bits ℓ =>
      ((sz.2, sz.2), (true, sz.1)))) _).comp
        (Matrix.reindexLinearEquiv ℂ ℂ (Equiv.prodComm _ _) (Equiv.prodComm _ _)).toLinearMap)

omit [DecidableEq E] in
/-- The agree-block postprocess is a channel for every finite Eve and reference register. -/
theorem isChannel_peAnnounceAgreeLHLPostprocess (n m ℓ ℓEV leakEC : ℕ)
    (peSel : Fin n → Bool) :
    IsChannel (peAnnounceAgreeLHLPostprocess E (R := R) n m ℓ ℓEV leakEC peSel) :=
  (isChannel_reindex _).comp
    ((isChannel_classicalMap _).mapTensorId.comp (isChannel_reindex _))

end QKD.BB84.FiniteKey
