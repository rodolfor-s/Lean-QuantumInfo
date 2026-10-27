import QCryptLean.InfoTheory.Renyi.FiniteSizePenalty
import QCryptLean.InfoTheory.Security.FiniteKey
import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.Math.Combinatorics.BellSymmetricDim
import QCryptLean.Math.Combinatorics.DeFinettiPrefactor
import QCryptLean.QKD.BB84.FiniteKey.Budgets.SmoothEntropyBound
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.Levels
import QCryptLean.QKD.BB84.SelectionData

/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Bell–Rényi BB84 key-rate conditions and leftover-hashing funding

The key-rate conditions fund the Bell purifier charge, syndrome and verification leakage, the
Rényi finite-size penalty and a freely chosen privacy-amplification error. Their
scalar inequalities bound the real leftover-hashing expression at the completed signed floor.

References: Nahar et al. 2024, arXiv:2403.11851, `eq:condLHL` and Appendix B;
Dupuis–Fawzi 2018, arXiv:1805.11652, Corollary IV.2.
-/

open Math.Combinatorics

open InfoTheory.Renyi

open Math.ClassicalEntropy

noncomputable section

namespace QKD.BB84.FiniteKey

/-- Bell–Rényi key length in bits: entropy minus public leakage, postselection,
Rényi smoothing penalty and leftover-hashing cost. -/
def bellRenyiWindowKeyLength (n m ℓEV leakEC : ℕ) (Q δ ε_AEP εPA β : ℝ) : ℝ :=
  (keyRounds n m : ℝ) * (1 - binaryEntropyBits (Q + 2 * δ)) - leakEC - ℓEV -
    InfoTheory.Security.postselectionCost 4 n -
    renyiPenalty binaryVarianceBound (keyRounds n m) ε_AEP β -
    InfoTheory.Security.privacyAmplificationCost εPA

/-- **The free-parameter Bell–Rényi key-rate condition** (Nahar et al.
`\label{eq:condLHL}` with a free privacy-amplification error `ε_PA` and a free Rényi offset
`β ∈ (0, 1)`, Dupuis–Fawzi Cor. IV.2).

Both analysis parameters are free: the Dupuis–Fawzi Cor IV.2 penalty is charged
at an arbitrary admissible offset `β` (`renyiPenalty`), and the
privacy-amplification error is the free parameter `ε_PA` of `\label{eq:condLHL}`, funded by
`privacyAmplificationCost ε_PA = 2·log₂(1/ε_PA) − 2` bits, instead of being fixed to
  `exp(−n·δ²/2)`.  The AEP/security chain
requires `0 < β < 1`; the scalar funders require no beta-admissibility hypotheses. The
single hashing-cap obligation requires `0 < ε_PA`, with no upper bound on the
privacy-amplification error and no positivity requirement on its logarithmic charge. -/
def BellRenyiWindowKeyRate
    (n m ℓ ℓEV leakEC : ℕ) (Q δ ε_AEP εPA β : ℝ) : Prop :=
  (ℓ : ℝ) ≤ bellRenyiWindowKeyLength n m ℓEV leakEC Q δ ε_AEP εPA β

/-- Conversion of the bit-valued key length to the natural-logarithm hashing inequality. -/
lemma bellRenyiWindowKeyRate_iff (n m ℓ ℓEV leakEC : ℕ) (Q δ ε_AEP εPA β : ℝ) :
    BellRenyiWindowKeyRate n m ℓ ℓEV leakEC Q δ ε_AEP εPA β ↔
    (ℓ : ℝ) * Real.log 2 + (leakEC : ℝ) * Real.log 2 + (ℓEV : ℝ) * Real.log 2 +
      2 * Real.log (Nat.choose (n + 3) 3 : ℝ) +
      Real.log 2 * renyiPenalty binaryVarianceBound
        (keyRounds n m) ε_AEP β +
      (2 * Real.log (1 / εPA) - 2 * Real.log 2) ≤
    (keyRounds n m : ℝ) * (Real.log 2 - binaryEntropy (Q + 2 * δ)) := by
  unfold BellRenyiWindowKeyRate bellRenyiWindowKeyLength binaryEntropyBits
    InfoTheory.Security.postselectionCost InfoTheory.Security.privacyAmplificationCost
  rw [Math.Combinatorics.deFinettiPrefactor_four]
  simp only [Real.logb]
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  constructor <;> intro h
  · have := (mul_le_mul_iff_left₀ hL).2 h
    field_simp at this
    nlinarith
  · apply (mul_le_mul_iff_left₀ hL).1
    field_simp
    nlinarith


/-- Bell–Rényi key length in bits: entropy minus public leakage, postselection,
Rényi smoothing penalty and leftover-hashing cost. -/
def bellRenyiKeyLength (n m ℓEV leakEC : ℕ) (Q δ dev ε_AEP εPA β : ℝ) : ℝ :=
  (keyRounds n m : ℝ) * (1 - binaryEntropyBits (Q + δ + dev)) - leakEC - ℓEV -
    InfoTheory.Security.postselectionCost 4 n -
    renyiPenalty binaryVarianceBound (keyRounds n m) ε_AEP β -
    InfoTheory.Security.privacyAmplificationCost εPA

/-- **The free-parameter key-rate condition at a free phase-error deviation `dev`.**

Like `BellRenyiWindowKeyRate`, with the secret-rate term charged at the deviation edge
`Q + δ + dev` instead of the doubled window edge `Q + 2·δ`: the window half-width `δ =
p.tolerance` keeps only its protocol role — the accept-test window — while `dev` is the
phase-error **deviation** between the window edge and the rate the entropy floor is charged at
(`dev = δ` gives the doubled-window condition up to the arithmetic rewrite `δ + δ = 2 * δ`).

This is the separation of Nahar, Tupkary, Zhao, Lütkenhaus and Tan 2024 (arXiv:2403.11851)
Lemma 9 Eq. 44 with §V.C: the rate is charged at the soundness edge, not at the completeness
window. -/
def BellRenyiKeyRate
    (n m ℓ ℓEV leakEC : ℕ) (Q δ dev ε_AEP εPA β : ℝ) : Prop :=
  (ℓ : ℝ) ≤ bellRenyiKeyLength n m ℓEV leakEC Q δ dev ε_AEP εPA β

/-- Conversion of the bit-valued key length to the natural-logarithm hashing inequality. -/
lemma bellRenyiKeyRate_iff (n m ℓ ℓEV leakEC : ℕ) (Q δ dev ε_AEP εPA β : ℝ) :
    BellRenyiKeyRate n m ℓ ℓEV leakEC Q δ dev ε_AEP εPA β ↔
    (ℓ : ℝ) * Real.log 2 + (leakEC : ℝ) * Real.log 2 + (ℓEV : ℝ) * Real.log 2 +
      2 * Real.log (Nat.choose (n + 3) 3 : ℝ) +
      Real.log 2 * renyiPenalty binaryVarianceBound
        (keyRounds n m) ε_AEP β +
      (2 * Real.log (1 / εPA) - 2 * Real.log 2) ≤
    (keyRounds n m : ℝ) * (Real.log 2 - binaryEntropy (Q + δ + dev)) := by
  unfold BellRenyiKeyRate bellRenyiKeyLength binaryEntropyBits
    InfoTheory.Security.postselectionCost InfoTheory.Security.privacyAmplificationCost
  rw [Math.Combinatorics.deFinettiPrefactor_four]
  simp only [Real.logb]
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  constructor <;> intro h
  · have := (mul_le_mul_iff_left₀ hL).2 h
    field_simp at this
    nlinarith
  · apply (mul_le_mul_iff_left₀ hL).1
    field_simp
    nlinarith


/-- The doubled-window key-rate condition is the free-deviation condition at `dev = δ`
(up to `δ + δ = 2 * δ`). -/
lemma bellRenyiKeyRate_self (n m ℓ ℓEV leakEC : ℕ) (Q δ ε_AEP εPA β : ℝ) :
    BellRenyiKeyRate n m ℓ ℓEV leakEC Q δ δ ε_AEP εPA β
      ↔ BellRenyiWindowKeyRate n m ℓ ℓEV leakEC Q δ ε_AEP εPA β := by
  have hadd : Q + δ + δ = Q + 2 * δ := by ring
  rw [bellRenyiKeyRate_iff, bellRenyiWindowKeyRate_iff]
  constructor
  · intro h; rwa [hadd] at h
  · intro h; rwa [← hadd] at h

/-- **The free-deviation key-rate condition funds the leftover-hash bound at free `ε_PA`**
(`0 < ε_PA`),
with the floor level charged at the deviation edge `Q + δ + dev`.

The window-specialized bound is the special case `dev = δ` of this theorem; the deviation only
moves the entropy argument. -/
theorem
    BellRenyiKeyRate.half_mul_sqrt_le
    {n m ℓ ℓEV leakEC : ℕ} {Q δ dev ε_AEP εPA β : ℝ}
    (h : BellRenyiKeyRate n m ℓ ℓEV leakEC Q δ dev ε_AEP εPA β)
    (hεPA : 0 < εPA) :
    (1 / 2 : ℝ) * Real.sqrt (((2 ^ ℓ : ℕ) : ℝ) *
        2 ^ (-(bellRenyiFloor n m Q δ dev ε_AEP β -
          2 * Real.log (bellSymmetricDim n : ℝ) / Real.log 2 -
          ((leakEC : ℝ) + (ℓEV : ℝ))))) ≤
      εPA := by
  set lpa : ℝ := Real.log (1 / εPA) - Real.log 2 with hlpadef
  set α : ℝ := Real.log 2 - binaryEntropy (Q + δ + dev) with hαdef
  set loss : ℝ :=
    Real.log 2 * renyiPenalty binaryVarianceBound
      (keyRounds n m) ε_AEP β +
      2 * Real.log (bellSymmetricDim n : ℝ) + ((leakEC : ℝ) + (ℓEV : ℝ)) * Real.log 2 with hlossdef
  have hCdef : (bellSymmetricDim n : ℝ) = (Nat.choose (n + 3) 3 : ℝ) := by rw [bellSymmetricDim]
  have hkey_loss : (ℓ : ℝ) * Real.log 2 + loss + 2 * lpa ≤
      (keyRounds n m : ℝ) * α := by
    have hk := h
    rw [bellRenyiKeyRate_iff] at hk
    rw [← hCdef] at hk
    rw [hlossdef, hαdef, hlpadef]
    linarith [hk]
  have hcap := real_lhl_budget_with_pa_loss (keyRounds n m) ℓ α loss lpa hkey_loss
  have hexp_eq : bellRenyiFloor n m Q δ dev ε_AEP β -
        2 * Real.log (bellSymmetricDim n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ)) =
      (keyRounds n m : ℝ) / Real.log 2 * α - loss / Real.log 2 := by
    rw [bellRenyiFloor, hαdef, hlossdef]
    field_simp
    ring
  rw [hexp_eq]
  have hexp : Real.exp (-lpa) = 2 * εPA := by
    rw [hlpadef, neg_sub, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2),
      Real.exp_log (one_div_pos.mpr hεPA)]
    field_simp
  rw [hexp] at hcap
  linarith

/-- **The free-parameter key-rate condition funds the leftover-hash bound at the free
`ε_PA`** (`0 < ε_PA`).

Setting `lpa := log(1/ε_PA) − log 2` in `real_lhl_budget_with_pa_loss` converts the funded budget
into `½·exp(−lpa) = ε_PA` — the free-`ε_PA` slot of Nahar et al.'s `\label{eq:condLHL}`.  The
doubled-window form is the free-deviation bound at `dev = δ`
(`bellRenyiKeyRate_self`, `bellRenyiFloor_self`). -/
theorem
    BellRenyiWindowKeyRate.half_mul_sqrt_le
    {n m ℓ ℓEV leakEC : ℕ} {Q δ ε_AEP εPA β : ℝ}
    (h : BellRenyiWindowKeyRate n m ℓ ℓEV leakEC Q δ ε_AEP εPA β)
    (hεPA : 0 < εPA) :
    (1 / 2 : ℝ) * Real.sqrt (((2 ^ ℓ : ℕ) : ℝ) *
        2 ^ (-(bellRenyiWindowFloor n m Q δ ε_AEP β -
          2 * Real.log (bellSymmetricDim n : ℝ) / Real.log 2 -
          ((leakEC : ℝ) + (ℓEV : ℝ))))) ≤
      εPA := by
  have h' : BellRenyiKeyRate n m ℓ ℓEV leakEC Q δ δ ε_AEP εPA β :=
    (bellRenyiKeyRate_self n m ℓ ℓEV leakEC Q δ ε_AEP εPA β).mpr h
  have hcap := BellRenyiKeyRate.half_mul_sqrt_le
    h' hεPA
  rwa [bellRenyiFloor_self] at hcap

end QKD.BB84.FiniteKey

end -- noncomputable section
