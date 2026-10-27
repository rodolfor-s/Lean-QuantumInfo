import QCryptLean.InfoTheory.Security.FiniteKey
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelAnalysis
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.Math.Combinatorics.DeFinettiPrefactor
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PELabelledPerSigmaFamily
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.BellInnerBudget
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.AcceptSplit
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.Haar
import QCryptLean.Quantum.Operators.Basic

/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The test-labelled Bell Haar mixture and its scalar budgets -/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators Quantum.Channels Quantum.Symmetry
open Quantum.DeFinetti InfoTheory.SmoothMinEntropy
open QKD.BB84.Model QKD.BB84.Measurement Matrix MeasureTheory

local notation "eSignal" => finTwoEquiv.symm.prodCongr finTwoEquiv.symm
local notation "bellSource(" φ ")" =>
  DensityOp.reindex (Equiv.prodCongr eSignal eSignal) (bellWembed φ)

/-- Attaching the complete test string commutes with the Bell component integral. -/
theorem bellPeLabelledEnVRhoEtilde_eq_haar_integral_blocks {n m : ℕ}
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (x : Signals n)
    (i j : Signals (min n m) × (Unit × Signals n)) :
    (((bellEnVRhoEtilde Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
      peSel xSel Q δ).tensorLeftKernel (peLabelKernel (m := m) peSel)).stateMap x).toOp i j =
      ∫ φ : DensityOp (Bool × Bool),
        ((peLabelledPairedHaarPerSigmaFamily (m := m) Unit (unitRegisterEmbed n)
          (isChannel_unitRegisterEmbed n) peSel xSel Q δ (bellSource(φ))).stateMap x).toOp i j
            ∂(haarDensityMeasure (false, false)).measure :=
  tensorLeftKernel_blocks_integral_eq
    (bellEnVRhoEtilde Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n) peSel xSel Q δ)
    (fun φ => pairedHaarPerSigmaFamily Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
      peSel xSel Q δ (bellSource(φ)))
    (peLabelKernel (m := m) peSel)
    (bellEnVRhoEtilde_eq_haar_integral_blocks peSel xSel Q δ) x i j

/-!
# Bell scalars at an abstract accept tail

The Bell `C(n+3,3)` collective inner budget and security budget, parametrised by an abstract
accept-tail scale `E` in place of a closed accept-tail expression, so that a sharper accept tail
can be substituted without re-deriving the budget.

## Main definitions

* `QKD.BB84.FiniteKey.bellRenyiSecrecyBudget` — the free-`epsPA` collective
  scalar at an abstract accept tail `E`.
* `QKD.BB84.FiniteKey.bellRenyiBudget` — the Bell–Rényi security budget at an
  abstract accept tail.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`) `\label{eq:condLHL}`
(`main.tex:462`–`:467`), `\label{lem:groupPurification}` (`main.tex:354`), App. B; Renner 2005
(`arXiv:quant-ph/0512258v2`) `\label{thm:Hmincondrep}` (`main.tex:4561`), §5, §6.5;
Christandl–König–Renner 2009 (`arXiv:0809.3019`).
-/

/-- **The Bell collective inner budget at a free `epsPA` and an abstract accept-tail scale `E`.**

```
bellRenyiSecrecyBudget E = epsPA + 2·(ε_AEP + √(2·E)) .
```

The scalar reads neither `n` nor `δ`: every occurrence of them was inside the accept tail, which
is now the parameter `E`, or inside the privacy-amplification term, which is now `epsPA`.

Reference: Nahar et al. 2024 (`arXiv:2403.11851`) `\label{eq:condLHL}` (`main.tex:462`–`:467`,
`εPA` free); Renner 2005 (`arXiv:quant-ph/0512258v2`) §6.5. -/
noncomputable def bellRenyiSecrecyBudget
    (E ε_AEP epsPA : ℝ) : ℝ :=
  epsPA + InfoTheory.Security.smoothingError ε_AEP + InfoTheory.Security.acceptanceError E

/-- **The Bell-symmetric security budget at a free `epsPA` and an abstract accept-tail scale `E`.**

The direct correctness charge `2^(−ℓEV)` plus `C(n+3,3)` times the secrecy budget
`bellRenyiSecrecyBudget E ε_AEP εPA`.
This is the budget behind the key-rate condition with a free Rényi offset: the leftover-hash error
`εPA` is a
free parameter (Nahar et al. 2024, `arXiv:2403.11851`, `\label{eq:condLHL}`), funded by
`BellRenyiWindowKeyRate`; its contribution is `C(n+3,3)·εPA`. The accept tail `E`
and the prefactor do not depend on it. -/
noncomputable def bellRenyiBudget (E : ℝ) (n ℓEV : ℕ) (ε_AEP εPA : ℝ) : ℝ :=
  InfoTheory.Security.verificationError ℓEV +
    (Math.Combinatorics.deFinettiPrefactor 4 n : ℝ) * bellRenyiSecrecyBudget E ε_AEP εPA

/-- The Bell–Rényi budget increases with the acceptance-test tail bound. -/
theorem bellRenyiBudget_mono {E E' : ℝ} (n ℓEV : ℕ) (ε εPA : ℝ) (hEE' : E ≤ E') :
    bellRenyiBudget E n ℓEV ε εPA ≤ bellRenyiBudget E' n ℓEV ε εPA := by
  simp only [bellRenyiBudget,
    InfoTheory.Security.verificationError,
    Math.Combinatorics.deFinettiPrefactor_four, bellRenyiSecrecyBudget,
    InfoTheory.Security.smoothingError,
    InfoTheory.Security.acceptanceError]
  gcongr

end QKD.BB84.FiniteKey

end -- noncomputable section
