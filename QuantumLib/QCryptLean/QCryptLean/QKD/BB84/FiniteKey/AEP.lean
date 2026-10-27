import QCryptLean.InfoTheory.Security.FiniteKey
import QCryptLean.Math.Analysis.SqrtBounds
import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.Math.Combinatorics.DeFinettiPrefactor
import QCryptLean.Math.Concentration.BernoulliKL
import QCryptLean.QKD.BB84.Constants
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.Budgets.BennettPostselectionBudget
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PostMeasurementCQ
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.AnnouncedChannels
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.PassBlocks
import QCryptLean.QKD.BB84.FiniteKey.KeyRate.AEP
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.PhaseTail
import QCryptLean.QKD.BB84.FiniteKey.Secrecy.AEP
import QCryptLean.QKD.BB84.Model.SiftedPEAnnounce
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.Quantum.Channels.ConsumerBounds
import QCryptLean.Quantum.Channels.Diamond
import QCryptLean.Quantum.Channels.DiamondAlgebra

/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The AEP BB84 security bound

The normalized diamond distance is bounded by
`2^(-ℓEV) + C(n+15,15) * (PA + 2 ε_AEP + 2 √(2E))`, where
`E = exp(-m_X * klBer (Q+δ) (Q+2δ))` and
`PA = ½ exp(-(n-m)/4 * (log 2 - h(Q+2δ)))`.

The exact agree/differ decomposition charges correctness directly. The CKR reduction applies
only to the agree block. The key-rate condition pays `2 log₂ C(n+15,15)` and the bit-register
IID AEP penalty. Its doubled length convention gives a coefficient `4 log C(n+15,15)` in nats.

When the tail is at least `1/8`, the budget is at least one. Empty acceptance gives identical
channels. The remaining branch uses the extended entropy floor at every positive radius.
The only explicit
numerical conditions are positive smoothing, the key-rate inequality and `Q + 2δ ≤ 1/2`.

References: Nahar et al. 2024, arXiv:2403.11851, Appendix B; Renner 2005,
`cor:Hmincondrepclass`; Christandl–König–Renner 2009, arXiv:0809.3019, Theorem 1.
-/

open Quantum.Operators Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open Quantum.Symmetry Quantum.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.FiniteKey

/-- The AEP BB84 diamond bound at the phase-error KL acceptance tail.
The decoder and selectors are arbitrary. The key-count identity ties the entropy copy count
to the actual retained rounds. Only the secrecy part receives the CKR factor `C(n+15,15)`. -/
theorem half_mul_diamondNorm_sub_le_aepBudget
    {n m ℓ ℓEV leakEC : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : KeyCount n m peSel)
    (ec : ECScheme n peSel leakEC)
    (Q δ ε_AEP : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (hKey : AEPKeyRate n m ℓ ℓEV leakEC Q δ ε_AEP)
    (hAEP : 0 < ε_AEP) :
    (1 / 2) * diamondNorm
        (symReal n m ℓ ℓEV Q δ peSel xSel leakEC ec -
          symIdeal n m ℓ ℓEV Q δ peSel xSel leakEC ec) ≤
      aepBudget (windowPhaseTail peSel xSel Q δ) n m ℓEV Q δ ε_AEP := by
  let : Nonempty (Measurement.Signals n) := Fintype.card_pos_iff.mp (by
    have hcard : Fintype.card (Measurement.Signals n) = 4 ^ n := by
      simp [Measurement.Signals, Measurement.Signal, Measurement.Bit]
    exact hcard.symm ▸ Nat.pos_of_ne_zero (NeZero.ne (4 ^ n)))
  have hnorm := diamondNorm_sub_le
    (symReal n m ℓ ℓEV Q δ peSel xSel leakEC ec)
    (symIdeal n m ℓ ℓEV Q δ peSel xSel leakEC ec)
  rw [(isChannel_symReal n m ℓ ℓEV Q δ peSel xSel leakEC ec).diamondNorm_eq_one,
    (isChannel_symIdeal n m ℓ ℓEV Q δ peSel xSel leakEC ec).diamondNorm_eq_one] at hnorm
  have hone : (1 / 2 : ℝ) * diamondNorm
      (symReal n m ℓ ℓEV Q δ peSel xSel leakEC ec -
        symIdeal n m ℓ ℓEV Q δ peSel xSel leakEC ec) ≤ 1 := by linarith only [hnorm]
  have hg : (4 : ℝ) ≤
      (Nat.choose (n + signalDim ^ 2 - 1) (signalDim ^ 2 - 1) : ℝ) := by
    have h16 : (16 : ℝ) ≤ (ckrSymmetricDim n : ℝ) := by
      exact_mod_cast sixteen_le_ckrSymmetricDim (n := n)
    exact (by norm_num : (4 : ℝ) ≤ 16).trans h16
  have hlarge (h : 1 / 8 ≤ windowPhaseTail peSel xSel Q δ) :
      1 ≤ aepBudget (windowPhaseTail peSel xSel Q δ) n m ℓEV Q δ ε_AEP := by
    have hb := Real.one_le_add_mul_add_sqrt_of_large hg
      (show 0 ≤ (2 : ℝ) ^ (-(ℓEV : ℝ)) by positivity) hAEP.le
      (show 0 ≤ (1 / 2 : ℝ) * Real.exp (-(keyRounds n m : ℝ) / 4 *
        (Real.log 2 - binaryEntropy (Q + 2 * δ))) from by positivity)
      (Or.inr (Or.inl h))
    simpa only [aepBudget,
    InfoTheory.Security.verificationError,
    Math.Combinatorics.deFinettiPrefactor, aepSecrecyBudget,
    InfoTheory.Security.acceptanceError,
    InfoTheory.Security.smoothingError,
    QKD.BB84.FiniteKey.aepPrivacyAmplificationError,
      mul_add, add_comm, add_left_comm, add_assoc] using hb
  by_cases hE8 : windowPhaseTail peSel xSel Q δ < 1 / 8
  · by_cases hempty : δ < 0 ∨ Q + δ < 0
    · rw [symReal_eq_symIdeal_of_empty_acceptance n m ℓ ℓEV Q δ peSel xSel leakEC ec hempty,
        sub_self, diamondNorm_zero, mul_zero]
      simp only [aepBudget,
    aepSecrecyBudget,
    InfoTheory.Security.verificationError,
    Math.Combinatorics.deFinettiPrefactor,
    InfoTheory.Security.acceptanceError,
    InfoTheory.Security.smoothingError,
    QKD.BB84.FiniteKey.aepPrivacyAmplificationError]
      positivity
    · have hδ : 0 ≤ δ := le_of_not_gt (fun h => hempty (Or.inl h))
      have hδpos : 0 < δ := by
        rcases hδ.eq_or_lt with hzero | hpos
        · norm_num only [← hzero, windowPhaseTail, mul_zero, add_zero,
            Math.Concentration.BernoulliKL.klBer_self, Real.exp_zero] at hE8
        · exact hpos
      have hbound :=
        AEP.half_mul_ckrTraceNorm_le_aepSecrecyBudget
          (ℓ := ℓ) (ℓEV := ℓEV) peSel xSel ec Q δ ε_AEP hbelow hKey hAEP
          (Window.phaseTailBound_unitEmbed
            (m := m) Q δ hδpos peSel xSel) hcount
      simp only [aepBudget,
    InfoTheory.Security.verificationError,
    Math.Combinatorics.deFinettiPrefactor]
      refine (half_mul_diamondNorm_sub_le_correctness_add
        n m ℓ ℓEV Q δ peSel xSel leakEC ec).trans ?_
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _))
  · exact hone.trans (hlarge (le_of_not_gt hE8))

end QKD.BB84.FiniteKey

end -- noncomputable section
