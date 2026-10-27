import QCryptLean.InfoTheory.QuantumLHL.Main
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.AgreeChannels
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.AgreeAxisFloorTransfer
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.AgreeBlock.Bound
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.AgreeBlock.Input
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Quantum.Operators.Basic

/-! # Any Ref Agree Block -/


noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators Quantum.Channels Quantum.Metrics
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL
open QKD.BB84.Model QKD.BB84.Measurement

variable (E : Type*) [Fintype E] [DecidableEq E] [Nonempty E]
variable {R : Type*} [Fintype R]

/-- An extended labelled entropy floor funds agree-block secrecy at every retained weight. -/
theorem half_mul_ckrTraceNorm_agree_le_add_of_le_smoothMinEntropy
    {n m ℓ ℓEV leakEC : ℕ}
    (pre : Operation (Signals n) (Signals n × E)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ r : ℝ) (hr : 0 ≤ r) (τ : DensityOp (Signals n × R))
    (kEV epsPA : ℝ)
    (hcap : (1 / 2 : ℝ) * Real.sqrt (((2 ^ ℓ : ℕ) : ℝ) * 2 ^ (-kEV)) ≤
      epsPA)
    (hFloor : ∃ σref : SubDensityOp
        ((Bits leakEC × (KeyHashSeed n ℓEV peSel × Bits ℓEV)) ×
          (Signals (min n m) × (E × R))),
      ENNReal.ofReal kEV ≤ smoothMinEntropy r
        (peLabelledLHLInput (m := m) ℓEV E pre hpre peSel xSel ec Q δ τ) σref) :
    (1 / 2) * ckrTraceNorm
      (announcedEveRealAgree E (m := m) ℓ ℓEV pre peSel xSel leakEC ec Q δ -
        announcedEveIdealAgree E (m := m) ℓ ℓEV pre peSel xSel leakEC ec Q δ) τ ≤
      epsPA + 2 * r := by
  let : Nonempty R := τ.nonempty.map Prod.snd
  obtain ⟨σref, hf⟩ := hFloor
  have ha := le_smoothMinEntropy_agreeInput_of_labelled (m := m) ℓEV E pre hpre
    peSel xSel ec Q δ τ r σref kEV hf
  have hLHL := SeedKey.traceDistanceGen_output_le_of_le_smoothMinEntropyOpt
    (aliceKeyHashFamily n ℓ peSel) (isTwoUniversal_aliceKeyHashFamily n ℓ peSel)
    (peAnnounceAgreeLHLInput E (m := m) ℓEV pre hpre peSel xSel ec Q δ τ) r hr kEV
    (ha.trans (smoothMinEntropy_le_smoothMinEntropyOpt _ _ _))
  have hbridge := half_mul_ckrTraceNorm_agree_le_traceDistanceGen
    E (m := m) ℓ ℓEV pre hpre peSel xSel ec Q δ τ
  have hc : (1 / 2 : ℝ) * Real.sqrt ((Fintype.card (Bits ℓ) : ℝ) * 2 ^ (-kEV)) ≤
      epsPA := by simpa [Bits] using hcap
  exact hbridge.trans (hLHL.trans (add_le_add hc le_rfl))

end QKD.BB84.FiniteKey
