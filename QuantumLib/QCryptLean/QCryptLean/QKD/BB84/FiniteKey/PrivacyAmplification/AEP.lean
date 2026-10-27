import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PhaseMixture
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.AgreeChannels
import QCryptLean.QKD.BB84.FiniteKey.KeyRate.AEP
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.InnerBudgetAgreeBlock
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.SymmetricPurifier
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.Quantum.Channels.Postselection

/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# AEP agree-block secrecy

The phase-error bad branch has mass at most `E`. The own-marginal mixture floor uses radius
`ε_AEP + √(2E)`. The extended floor and leftover hashing give
`PA + 2 ε_AEP + 2 √(2E)` for every decoder. The phase-error soundness edge is at most one half.

Reference: Nahar et al. 2024, arXiv:2403.11851, Appendix B, `eq:boundingsmoothedmin`,
`eq:splittingoffV` and `eq:condLHL`.
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

/-- The phase-error secrecy bound on the symmetric purifier.
The key count, AEP penalty and PA exponent use `n - m`, while the purifier charge uses the
full-block dimension `C(n+15,15)`. The decoder is arbitrary. -/
theorem AEP.Window.half_mul_ckrTraceNorm_agree_le
    {n m ℓ ℓEV leakEC : ℕ}
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ ε_AEP : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (hKey : AEPKeyRate n m ℓ ℓEV leakEC Q δ ε_AEP)
    (hAEP : 0 < ε_AEP)
    {E : ℝ}
    (hBad : WindowPhaseTailBound (m := m) Unit (unitRegisterEmbed n)
        (isChannel_unitRegisterEmbed n) peSel xSel Q δ E)
    (hcount : KeyCount n m peSel)
    (V : SymmetricPurifier n) :
    (1 / 2) * ckrTraceNorm
        (announcedEveRealAgree Unit (m := m) ℓ ℓEV
            (unitRegisterEmbed n)
            peSel xSel leakEC ec Q δ -
          announcedEveIdealAgree Unit (m := m) ℓ ℓEV
              (unitRegisterEmbed n)
            peSel xSel leakEC ec Q δ)
        (enVCKRPurification V) ≤
      (1 / 2) * Real.exp (-(keyRounds n m : ℝ) / 4 *
        (Real.log 2 - binaryEntropy (Q + 2 * δ))) +
        2 * (ε_AEP + Real.sqrt (2 * E)) := by
  exact half_mul_ckrTraceNorm_agree_le_of_le_smoothMinEntropy
    (m := m) Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
    peSel xSel ec Q δ ε_AEP hKey hAEP V
    (AEP.Window.exists_le_smoothMinEntropy_reference (m := m) (ℓEV := ℓEV)
      peSel xSel hcount ec Q δ hbelow hBad V ε_AEP hAEP)

end QKD.BB84.FiniteKey

end -- noncomputable section
