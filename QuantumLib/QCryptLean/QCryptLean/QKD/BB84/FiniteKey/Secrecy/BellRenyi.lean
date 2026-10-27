import QCryptLean.InfoTheory.Security.FiniteKey
import QCryptLean.Math.Combinatorics.BellSymmetricDim
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.BellHaarMixture
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.BellPurifier
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.Levels
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.AgreeChannels
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.BellInnerBudget
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.PassBlocks
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.BellAcceptSplit
import QCryptLean.QKD.BB84.FiniteKey.Postselection.BellReference
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.AnyRefAgreeBlock
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.BellRenyi
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Quantum.Operators.Basic

/-!
# Bell Rényi secrecy and collective budgets

Leftover hashing converts the extended entropy floor into the agree-block
secrecy bound and the collective inner budget.
-/

open Math.Combinatorics

open InfoTheory.Renyi

open Quantum.Operators Matrix Quantum.Channels Quantum.Metrics
open QKD.BB84.Measurement
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open Quantum.Symmetry Quantum.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.FiniteKey

/-! ## 2. The general-`m` Rényi AGREE-block secrecy residual at the phase-error good set -/

/-- The Bell agree-block secrecy bound from a funded extended entropy floor.
The bound is `epsPA + 2 * (ε_AEP + √(2E))` at every accepted weight.
Reference: Nahar et al. 2024, Appendix B, `eq:condLHL`. -/
theorem
    BellRenyi.half_mul_ckrTraceNorm_agree_le
    {n m ℓ ℓEV leakEC : ℕ}
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ dev ε_AEP : ℝ)
    (hbelow : Q + δ + dev ≤ 1 / 2)
    (hAEP : 0 < ε_AEP)
    (hcount : KeyCount n m peSel)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : BellTailBound peSel xSel Q δ dev E)
    (V : BellSymmetricPurifier n)
    (epsPA : ℝ)
    (hcap : (1 / 2 : ℝ) * Real.sqrt (((2 ^ ℓ : ℕ) : ℝ) *
        2 ^ (-(bellRenyiFloor n m Q δ dev ε_AEP β -
          2 * Real.log (bellSymmetricDim n : ℝ) / Real.log 2 -
          ((leakEC : ℝ) + (ℓEV : ℝ))))) ≤ epsPA) :
    (1 / 2) * ckrTraceNorm
        (announcedEveRealAgree Unit (m := m) ℓ ℓEV
            (unitRegisterEmbed n) peSel xSel
            leakEC ec Q δ -
          announcedEveIdealAgree Unit (m := m) ℓ ℓEV
              (unitRegisterEmbed n) peSel
            xSel leakEC ec Q δ)
        (enVBellPurification V) ≤
      epsPA + 2 * (ε_AEP + Real.sqrt (2 * E)) := by
  exact half_mul_ckrTraceNorm_agree_le_add_of_le_smoothMinEntropy
    (m := m) (ℓ := ℓ) Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
    peSel xSel ec Q δ (ε_AEP + Real.sqrt (2 * E)) (by positivity)
    (enVBellPurification V)
    (bellRenyiFloor n m Q δ dev ε_AEP β -
      2 * Real.log (bellSymmetricDim n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ)))
    epsPA hcap
    (BellRenyi.exists_le_smoothMinEntropy_hashInput
      (m := m) peSel xSel ec Q δ dev ε_AEP hbelow β hβpos hβ1 hAEP hcount hE0 hCap V)

/-- The Bell agree-block secrecy bound from a funded extended entropy floor.
The bound is `epsPA + 2 * (ε_AEP + √(2E))` at every accepted weight.
Reference: Nahar et al. 2024, Appendix B, `eq:condLHL`. -/
theorem
    BellRenyi.Window.half_mul_ckrTraceNorm_agree_le
    {n m ℓ ℓEV leakEC : ℕ}
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ ε_AEP : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (hAEP : 0 < ε_AEP)
    (hcount : KeyCount n m peSel)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : WindowBellTailBound peSel xSel Q δ E)
    (V : BellSymmetricPurifier n)
    (epsPA : ℝ)
    (hcap : (1 / 2 : ℝ) * Real.sqrt (((2 ^ ℓ : ℕ) : ℝ) *
        2 ^ (-(bellRenyiWindowFloor n m Q δ ε_AEP β -
          2 * Real.log (bellSymmetricDim n : ℝ) / Real.log 2 -
          ((leakEC : ℝ) + (ℓEV : ℝ))))) ≤ epsPA) :
    (1 / 2) * ckrTraceNorm
        (announcedEveRealAgree Unit (m := m) ℓ ℓEV
            (unitRegisterEmbed n) peSel xSel
            leakEC ec Q δ -
          announcedEveIdealAgree Unit (m := m) ℓ ℓEV
              (unitRegisterEmbed n) peSel
            xSel leakEC ec Q δ)
        (enVBellPurification V) ≤
      epsPA + 2 * (ε_AEP + Real.sqrt (2 * E)) := by
  -- The doubled-window form is the special case `dev = δ` of the free-deviation residual above.
  exact
    BellRenyi.half_mul_ckrTraceNorm_agree_le
    (n := n) (m := m) (ℓ := ℓ) (ℓEV := ℓEV) peSel xSel ec Q δ δ ε_AEP
    (by rwa [show (Q:ℝ) + δ + δ = Q + 2 * δ from by ring]) hAEP hcount β hβpos hβ1 hE0
    (BellTailBound.of_windowBellTailBound hCap) V
    epsPA
    (by rwa [bellRenyiFloor_self])

/-- The Bell agree-block secrecy bound from a funded extended entropy floor.
The bound is `epsPA + 2 * (ε_AEP + √(2E))` at every accepted weight.
Reference: Nahar et al. 2024, Appendix B, `eq:condLHL`. -/
theorem
    BellRenyi.ClampedOffset.half_mul_ckrTraceNorm_agree_le
    {n m ℓ ℓEV leakEC : ℕ}
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ ε_AEP : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (hAEP : 0 < ε_AEP)
    (hεS : ε_AEP < 1)
    (hcount : KeyCount n m peSel)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : WindowBellTailBound peSel xSel Q δ E)
    (V : BellSymmetricPurifier n)
    (epsPA : ℝ)
    (hcap : (1 / 2 : ℝ) * Real.sqrt (((2 ^ ℓ : ℕ) : ℝ) *
        2 ^ (-(bellRenyiClampedFloor n m Q δ ε_AEP -
          2 * Real.log (bellSymmetricDim n : ℝ) / Real.log 2 -
          ((leakEC : ℝ) + (ℓEV : ℝ))))) ≤ epsPA) :
    (1 / 2) * ckrTraceNorm
        (announcedEveRealAgree Unit (m := m) ℓ ℓEV
            (unitRegisterEmbed n) peSel xSel
            leakEC ec Q δ -
          announcedEveIdealAgree Unit (m := m) ℓ ℓEV
              (unitRegisterEmbed n) peSel
            xSel leakEC ec Q δ)
        (enVBellPurification V) ≤
      epsPA + 2 * (ε_AEP + Real.sqrt (2 * E)) := by
  apply half_mul_ckrTraceNorm_agree_le_add_of_le_smoothMinEntropy
    (m := m) (ℓ := ℓ) Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
    peSel xSel ec Q δ (ε_AEP + Real.sqrt (2 * E)) (by positivity)
    (enVBellPurification V)
    (bellRenyiClampedFloor n m Q δ ε_AEP -
      2 * Real.log (bellSymmetricDim n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ)))
    epsPA hcap
  by_cases hk : 0 < bellRenyiClampedFloor n m Q δ ε_AEP -
      2 * Real.log (bellSymmetricDim n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ))
  · exact BellRenyi.ClampedOffset.exists_le_smoothMinEntropy_hashInput
      (m := m) peSel xSel ec Q δ ε_AEP hbelow
      (lt_of_bellRenyiClampedFloor_charged_pos hk) hAEP hεS hcount hE0 hCap V
  · exact ⟨SubDensityOp.zero, by rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hk)]; exact bot_le⟩

/-- The Bell collective secrecy budget from the extended agree-block floor.
Symmetrization and purification transport preserve the bound
`epsPA + 2 * (ε_AEP + √(2E))` at every accepted weight.
Reference: Nahar et al. 2024, Appendix B. -/
theorem
    BellRenyi.half_mul_ckrTraceNorm_le_bellRenyiSecrecyBudget
    {n m ℓ ℓEV leakEC : ℕ}
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ dev ε_AEP : ℝ)
    (hbelow : Q + δ + dev ≤ 1 / 2)
    (hAEP : 0 < ε_AEP)
    (hcount : KeyCount n m peSel)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    (epsPA : ℝ)
    (hcap : (1 / 2 : ℝ) * Real.sqrt (((2 ^ ℓ : ℕ) : ℝ) *
        2 ^ (-(bellRenyiFloor n m Q δ dev ε_AEP β -
          2 * Real.log (bellSymmetricDim n : ℝ) / Real.log 2 -
          ((leakEC : ℝ) + (ℓEV : ℝ))))) ≤ epsPA)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : BellTailBound peSel xSel Q δ dev E) :
    (1 / 2) * ckrTraceNorm
        (symPassBlockDelta false n m ℓ ℓEV Q δ peSel xSel leakEC ec)
        (bellCKRDeFinettiPurification n) ≤
      bellRenyiSecrecyBudget E ε_AEP epsPA := by
  -- The Bell symmetric purifier `V_Bell` at the affordable register `card V.reg ≤ C(n+3,3)`.
  obtain ⟨V⟩ := nonempty_bellSymmetricPurifier n
  refine (mul_le_mul_of_nonneg_left
    (ckrTraceNorm_symPassBlockDelta_le false n m ℓ ℓEV Q δ peSel xSel
    leakEC ec (bellCKRDeFinettiPurification n)
    (isPairedPermInvariant_bellCKRDeFinettiPurification n))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans ?_
  simp only [passBlockDelta, Bool.false_eq_true, ↓reduceIte]
  -- B19: move the agree bound from the canonical `τ_Bell` to the `Eⁿ⊗V` split.
  have hL3 := Bell.ckrTraceNorm_canonical_eq_enV (n := n) V
    (announcedEveRealAgree Unit (m := m) ℓ ℓEV (unitRegisterEmbed n)
        peSel xSel leakEC ec Q δ -
      announcedEveIdealAgree Unit (m := m) ℓ ℓEV (unitRegisterEmbed n)
        peSel xSel leakEC ec Q δ)
  rw [hL3]
  -- SECRECY HALF: the Rényi Bell-reference agree-block residual, at the free deviation.
  have hRes :=
  BellRenyi.half_mul_ckrTraceNorm_agree_le
    (n := n) (m := m) (ℓ := ℓ) (ℓEV := ℓEV) peSel xSel ec Q δ dev ε_AEP hbelow hAEP
    hcount β hβpos hβ1 hE0 hCap V epsPA hcap
  simpa only [bellRenyiSecrecyBudget, InfoTheory.Security.smoothingError,
    InfoTheory.Security.acceptanceError, mul_add, add_assoc] using hRes

/-! ## 3. The general-`m` Rényi Bell collective inner budget at the phase-error good set -/

/-- The Bell collective secrecy budget from the extended agree-block floor.
Symmetrization and purification transport preserve the bound
`epsPA + 2 * (ε_AEP + √(2E))` at every accepted weight.
Reference: Nahar et al. 2024, Appendix B. -/
theorem
    BellRenyi.Window.half_mul_ckrTraceNorm_le_bellRenyiSecrecyBudget
    {n m ℓ ℓEV leakEC : ℕ}
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ ε_AEP : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (hAEP : 0 < ε_AEP)
    (hcount : KeyCount n m peSel)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    (epsPA : ℝ)
    (hcap : (1 / 2 : ℝ) * Real.sqrt (((2 ^ ℓ : ℕ) : ℝ) *
        2 ^ (-(bellRenyiWindowFloor n m Q δ ε_AEP β -
          2 * Real.log (bellSymmetricDim n : ℝ) / Real.log 2 -
          ((leakEC : ℝ) + (ℓEV : ℝ))))) ≤ epsPA)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : WindowBellTailBound peSel xSel Q δ E) :
    (1 / 2) * ckrTraceNorm
        (symPassBlockDelta false n m ℓ ℓEV Q δ peSel xSel leakEC ec)
        (bellCKRDeFinettiPurification n) ≤
      bellRenyiSecrecyBudget E ε_AEP epsPA := by
  -- The doubled-window form is the special case `dev = δ` of the free-deviation bound above.
  exact BellRenyi.half_mul_ckrTraceNorm_le_bellRenyiSecrecyBudget
    (n := n) (m := m) (ℓ := ℓ) (ℓEV := ℓEV) peSel xSel ec Q δ δ ε_AEP
    (by rwa [show (Q:ℝ) + δ + δ = Q + 2 * δ from by ring]) hAEP hcount β hβpos hβ1
    epsPA
    (by rwa [bellRenyiFloor_self]) hE0
    (BellTailBound.of_windowBellTailBound hCap)

/-- The Bell collective secrecy budget from the extended agree-block floor.
Symmetrization and purification transport preserve the bound
`epsPA + 2 * (ε_AEP + √(2E))` at every accepted weight.
Reference: Nahar et al. 2024, Appendix B. -/
theorem
    BellRenyi.ClampedOffset.half_mul_ckrTraceNorm_le_bellRenyiSecrecyBudget
    {n m ℓ ℓEV leakEC : ℕ}
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ ε_AEP : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (hAEP : 0 < ε_AEP)
    (hεS : ε_AEP < 1)
    (hcount : KeyCount n m peSel)
    (epsPA : ℝ)
    (hcap : (1 / 2 : ℝ) * Real.sqrt (((2 ^ ℓ : ℕ) : ℝ) *
        2 ^ (-(bellRenyiClampedFloor n m Q δ ε_AEP -
          2 * Real.log (bellSymmetricDim n : ℝ) / Real.log 2 -
          ((leakEC : ℝ) + (ℓEV : ℝ))))) ≤ epsPA)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : WindowBellTailBound peSel xSel Q δ E) :
    (1 / 2) * ckrTraceNorm
        (symPassBlockDelta false n m ℓ ℓEV Q δ peSel xSel leakEC ec)
        (bellCKRDeFinettiPurification n) ≤
      bellRenyiSecrecyBudget E ε_AEP epsPA := by
  -- The Bell symmetric purifier `V_Bell` at the affordable register `card V.reg ≤ C(n+3,3)`.
  obtain ⟨V⟩ := nonempty_bellSymmetricPurifier n
  refine (mul_le_mul_of_nonneg_left
    (ckrTraceNorm_symPassBlockDelta_le false n m ℓ ℓEV Q δ peSel xSel
    leakEC ec (bellCKRDeFinettiPurification n)
    (isPairedPermInvariant_bellCKRDeFinettiPurification n))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans ?_
  simp only [passBlockDelta, Bool.false_eq_true, ↓reduceIte]
  -- B19: move the agree bound from the canonical `τ_Bell` to the `Eⁿ⊗V` split.
  have hL3 := Bell.ckrTraceNorm_canonical_eq_enV (n := n) V
    (announcedEveRealAgree Unit (m := m) ℓ ℓEV (unitRegisterEmbed n)
        peSel xSel leakEC ec Q δ -
      announcedEveIdealAgree Unit (m := m) ℓ ℓEV (unitRegisterEmbed n)
        peSel xSel leakEC ec Q δ)
  rw [hL3]
  -- SECRECY HALF: the Rényi Bell-reference agree-block residual, at the free deviation.
  have hRes :=
  BellRenyi.ClampedOffset.half_mul_ckrTraceNorm_agree_le
    (n := n) (m := m) (ℓ := ℓ) (ℓEV := ℓEV) peSel xSel ec Q δ ε_AEP hbelow hAEP hεS
    hcount hE0 hCap V epsPA hcap
  simpa only [bellRenyiSecrecyBudget, InfoTheory.Security.smoothingError,
    InfoTheory.Security.acceptanceError, mul_add, add_assoc] using hRes

/-! ## 3. The general-`m` Rényi Bell collective inner budget at the phase-error good set -/

end QKD.BB84.FiniteKey

end -- noncomputable section
