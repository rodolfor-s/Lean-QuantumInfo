import QCryptLean.InfoTheory.Security.FiniteKey
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.Budgets.BennettPostselectionBudget
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PhaseMixture
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.AgreeChannels
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.InnerBudgetCorrectness
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.PassBlocks
import QCryptLean.QKD.BB84.FiniteKey.KeyRate.AEP
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.AEP
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.ReferencePurification
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.SymmetricPurifier
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.Quantum.Channels.CKRReference
import QCryptLean.Quantum.Channels.CKRReferenceBound
import QCryptLean.Quantum.Channels.Postselection

/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The AEP agree-block budget at the phase-error good set

The own-marginal extended smooth-entropy floor and leftover hashing give
`PA + 2 ε_AEP + 2 √(2E)` on the CKR reference for every accepted weight.
Verification is charged separately by the analysis's exact agree/differ decomposition.

References: Nahar et al. 2024, arXiv:2403.11851, Appendix B, `eq:condLHL`;
Christandl–König–Renner 2009, arXiv:0809.3019, Theorem 1.
-/

open Quantum.Operators Matrix Quantum.Channels Quantum.Metrics
open QKD.BB84.Measurement
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open Quantum.Symmetry Quantum.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.FiniteKey

/-- The agree-block CKR secrecy budget at the phase-error good set.
The labelled extended entropy floor supplies the leftover-hashing bound on a symmetric purifier.
Purification invariance transfers the result to the canonical CKR reference. -/
theorem AEP.half_mul_ckrTraceNorm_le_aepSecrecyBudget
    {n m ℓ ℓEV leakEC : ℕ}
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ ε_AEP : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (hKey : AEPKeyRate n m ℓ ℓEV leakEC Q δ ε_AEP)
    (hAEP : 0 < ε_AEP)
    {E : ℝ}
    (hBad : WindowPhaseTailBound (m := m) Unit (unitRegisterEmbed n)
      (isChannel_unitRegisterEmbed n) peSel xSel Q δ E)
    (hcount : KeyCount n m peSel) :
    (1 / 2) * ckrTraceNorm
        (symPassBlockDelta false n m ℓ ℓEV Q δ peSel xSel leakEC ec)
        (ckrDeFinettiCanonicalPurification Signal n) ≤
      aepSecrecyBudget E n m Q δ ε_AEP := by
  refine (mul_le_mul_of_nonneg_left
    (ckrTraceNorm_symPassBlockDelta_le false n m ℓ ℓEV Q δ
    peSel xSel leakEC ec (ckrDeFinettiCanonicalPurification Signal n)
    (isPairedPermInvariant_ckrDeFinettiCanonicalPurification (X := Signal) (k := n)))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans ?_
  -- The rank-`g` symmetric purifier carrying Nahar et al.'s `R = Eⁿ ⊗ V` register split (B13/B17).
  obtain ⟨V⟩ := nonempty_symmetricPurifier n
  -- The general-`m` raw leftover-hashing output bound on the agree block, at the `EⁿV` reference.
  have hRes :=
      AEP.Window.half_mul_ckrTraceNorm_agree_le
    (m := m) (ℓ := ℓ) (ℓEV := ℓEV) peSel xSel ec Q δ ε_AEP hbelow hKey hAEP hBad
    hcount V
  -- B19: `ckrTraceNorm` is purification-invariant, so the bound moves from the `EⁿV` register
  -- back to the canonical CKR de Finetti purification.
  have hL3 := ckrTraceNorm_canonical_eq_enV (n := n) V
    (announcedEveRealAgree Unit (m := m) ℓ ℓEV (unitRegisterEmbed n)
        peSel xSel leakEC ec Q δ -
      announcedEveIdealAgree Unit (m := m) ℓ ℓEV (unitRegisterEmbed n)
        peSel xSel leakEC ec Q δ)
  change (1 / 2) * ckrTraceNorm
    (announcedEveRealAgree Unit (m := m) ℓ ℓEV
      (unitRegisterEmbed n) peSel xSel leakEC ec Q δ -
      announcedEveIdealAgree Unit (m := m) ℓ ℓEV
        (unitRegisterEmbed n) peSel xSel leakEC ec Q δ)
    (ckrDeFinettiCanonicalPurification Signal n) ≤ _
  rw [hL3]
  simp only [aepSecrecyBudget,
    InfoTheory.Security.acceptanceError,
    InfoTheory.Security.smoothingError,
    QKD.BB84.FiniteKey.aepPrivacyAmplificationError]
  linarith only [hRes]

end QKD.BB84.FiniteKey

end -- noncomputable section
