import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.QKD.BB84.Constants
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.Budgets.SmoothEntropyBound
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.AEPLevels
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PostMeasurementCQ
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.AgreeChannels
import QCryptLean.QKD.BB84.FiniteKey.KeyRate.AEP
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.AgreeAxisFloorTransfer
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.AnyRefAgreeBlock
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.SymmetricPurifier
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Quantum.Operators.Basic

/-!
# The AEP agree-block leftover-hash bound

The agree-block trace distance is at most
`PA + 2 * (ε_AEP + √(2E))`, with
`PA = ½ exp(-(n-m)/4 * (log 2 - h(Q+2δ)))`.
The extended labelled entropy floor feeds reference-optimised leftover hashing at every weight.
The AEP key-rate condition funds the
bit-register AEP penalty, `2 log₂ C(n+15,15)`, the public syndrome and the verification tag.

References: Nahar et al. 2024, arXiv:2403.11851, `eq:condLHL`, Appendix B;
Renner 2005, `cor:Hmincondrepclass`.
-/

open Quantum.Operators Matrix Quantum.Channels Quantum.Metrics
open QKD.BB84.Measurement
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open Math.RepresentationTheory
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.FiniteKey

/-- The secrecy bound from an extended labelled entropy floor.
The key-rate condition funds `loss = log 2 * P + 2 log g + (leakEC + ℓEV) log 2`, where
`g = C(n+15,15)`. Reference optimisation and leftover hashing cost `2 * (ε_AEP + √(2E))`.
The PA exponent uses exactly the phase-error rate `log 2 - h(Q+2δ)`. Reference: Nahar et al. 2024,
Appendix B, `eq:condLHL`. -/
theorem
 half_mul_ckrTraceNorm_agree_le_of_le_smoothMinEntropy
    {n m ℓ ℓEV leakEC : ℕ} (F : Type*) [Fintype F] [DecidableEq F] [Nonempty F]
    (pre : Operation (Signals n) (Signals n × F)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ ε_AEP : ℝ)
    (hKey : AEPKeyRate n m ℓ ℓEV leakEC Q δ ε_AEP)
    {E : ℝ}
    (hAEP : 0 < ε_AEP)
    (V : SymmetricPurifier n)
    (hFloor :
      ∃ σref : SubDensityOp
          ((Bits leakEC × (KeyHashSeed n ℓEV peSel × Bits ℓEV)) ×
            (Signals (min n m) × (F × (Signals n × V.reg)))),
        ENNReal.ofReal (pairedHaarWindowFloorLevel n m Q δ ε_AEP -
          2 * Real.log (ckrSymmetricDim n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ))) ≤
          smoothMinEntropy
            (ε_AEP + Real.sqrt (2 * E))
            (peLabelledLHLInput (m := m) ℓEV F pre hpre peSel xSel ec Q δ
                (enVCKRPurification V))
            σref) :
    (1 / 2) * ckrTraceNorm
        (announcedEveRealAgree F (m := m) ℓ ℓEV pre peSel
            xSel leakEC ec Q δ -
          announcedEveIdealAgree F (m := m) ℓ ℓEV pre peSel
              xSel leakEC ec Q δ)
        (enVCKRPurification V) ≤
      (1 / 2) * Real.exp (-(keyRounds n m : ℝ) / 4 *
        (Real.log 2 - binaryEntropy (Q + 2 * δ))) +
        2 * (ε_AEP + Real.sqrt (2 * E)) := by
  -- The B16-B17-B19 floor `kEV = kfloor − P − 2·log₂ g − (leakEC + ℓEV)`, at `n_K = n − m`.
  set kEV : ℝ := pairedHaarWindowFloorLevel n m Q δ ε_AEP -
    2 * Real.log (ckrSymmetricDim n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ)) with hkEVdef
  -- **B18 cap: the general-`m` key-rate condition funds `2·ℓ·log 2 + 2·loss` exactly.**
  have hcap_acc :
      (1 / 2 : ℝ) * Real.sqrt (((2 ^ ℓ : ℕ) : ℝ) * 2 ^ (-kEV)) ≤
        (1 / 2) * Real.exp (-(keyRounds n m : ℝ) / 4 *
          (Real.log 2 - binaryEntropy (Q + 2 * δ))) := by
    -- The key-rate condition and component floor charge the same phase-error entropy rate.
    set α : ℝ := Real.log 2 - binaryEntropy (Q + 2 * δ) with hαdef
    set loss : ℝ :=
      Real.log 2 * finiteSizePenalty (keyRounds n m) ε_AEP +
        2 * Real.log (ckrSymmetricDim n : ℝ) + ((leakEC : ℝ) + (ℓEV : ℝ)) * Real.log 2 with hlossdef
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hCdef :
        (ckrSymmetricDim n : ℝ) =
          (Nat.choose (n + signalDim ^ 2 - 1) (signalDim ^ 2 - 1) : ℝ) := by
      rw [ckrSymmetricDim]
    have hkey_loss : 2 * (ℓ : ℝ) * Real.log 2 + 2 * loss ≤
        (keyRounds n m : ℝ) * α := by
      have hk := hKey
      rw [aepKeyRate_iff] at hk
      rw [← hCdef] at hk
      rw [hlossdef, hαdef]
      -- `hk` is this inequality with `loss` expanded term by term.
      linear_combination hk
    have hcap := real_lhl_budget_at_key_rate_with_log_loss (keyRounds n m) ℓ α loss
      hkey_loss
    have hexp_eq : kEV =
        (keyRounds n m : ℝ) / Real.log 2 * α - loss / Real.log 2 := by
      rw [hkEVdef, pairedHaarWindowFloorLevel, hαdef, hlossdef]
      field_simp
      ring
    rw [hexp_eq]
    exact hcap
  exact half_mul_ckrTraceNorm_agree_le_add_of_le_smoothMinEntropy
    (m := m) F pre hpre peSel xSel ec Q δ
    (ε_AEP + Real.sqrt (2 * E)) (by positivity)
    (enVCKRPurification V) kEV
    ((1 / 2) * Real.exp (-(keyRounds n m : ℝ) / 4 *
      (Real.log 2 - binaryEntropy (Q + 2 * δ))))
    hcap_acc hFloor

end QKD.BB84.FiniteKey

end -- noncomputable section
