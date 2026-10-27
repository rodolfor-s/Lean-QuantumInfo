import QCryptLean.InfoTheory.Security.FiniteKey
import QCryptLean.Math.Analysis.SqrtBounds
import QCryptLean.Math.Combinatorics.DeFinettiPrefactor
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.BellHaarMixture
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.AnnouncedChannels
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.PassBlocks
import QCryptLean.QKD.BB84.FiniteKey.KeyRate.BellRenyi
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.BellSourceTail
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.PhaseTail
import QCryptLean.QKD.BB84.FiniteKey.Postselection.BellReductionGeneral
import QCryptLean.QKD.BB84.FiniteKey.Secrecy.BellRenyi
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
# The Bell–Rényi budget at the Cor IV.2 penalty, KL accept tail, general selectors

The Bell-postselection-lifted BB84 composable security bound at the `C(n+3,3)` de Finetti charge,
the privacy-amplification error `εPA`, the Dupuis–Fawzi Cor IV.2 finite-size penalty at the binary
variance bound
`binaryVarianceBound = log₂²(1+√2)`, a general parameter-estimation test-set size `m`, the exact
Bernoulli-KL accept tail
priced on the realised X-subsample size, and arbitrary PE/X-test selectors.

## Main results

-
`QKD.BB84.FiniteKey.Window.half_mul_diamondNorm_sub_le_bellRenyiBudget`:
  the security bound at a free privacy-amplification error `ε_PA` and a free Rényi offset
  `β ∈ (0, 1)`. For `ε_AEP < 1`, the exponential-error specialization follows at
  `εPA = exp(−n·δ²/2)`, `β = clampedRenyiOffset …`; larger smoothing uses the channel bound.
-
`QKD.BB84.FiniteKey.half_mul_diamondNorm_sub_le_bellRenyiBudget`:
  the same at a free phase-error deviation `dev`: the window `δ` stays the protocol's, the entropy
  floor and the accept tail are charged at `Q + δ + dev` and the budget prices
  `phaseTail peSel xSel Q δ dev`; the window-specialized theorem below specializes it at
  `dev = δ ≥ 0` and handles negative windows by rejection.

## Model scope

Announced-PE LOCC two-basis parameter estimation, key-round hash, error verification charged
additively, the source permuted rather than the distributed pairs, fixed key length, no
detector/loss
model, and `hec : ec.IsTranslationEquivariant` funding the `C(n+3,3)` prefactor on the channel
side. `ℓ` occurs in the budget nowhere and the budget is not asserted to be below `1`: this is a
budget statement, not a key-rate claim.

## Relation to the literature

The phase-error good set is **not** in the cited literature; it is licensed by
`QKD.BB84.FiniteKey.Window.div_le_componentAliceZRate_of_phaseRate_le`. Gottesman–Lo
(arXiv:quant-ph/0105121, `main.tex:1638`, footnote `:278`) estimate `p_X` and `p_Z`
separately and demand *each* small — the ancestor of the phase-error conjunction, not authority for
dropping the bit ball.

References: Dupuis–Fawzi 2018 (`arXiv:1805.11652`) `\label{cor:continuity-bound-halpha_new}`
(`EAT-second-order-ieee-1col-r2.tex:784`), `\label{eq_eathmin_halpha}` (`:1053`),
`\label{eq_alphachoiceext}` (`:1061`), `\label{lem:divergence-variance-general-bounds}` (`:394`);
Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`) Lemma 9 Eq. 44, App. B
(`main.tex:1341`–`:1413`, `\label{eq:tausplit}` `:1356`–`:1362`, `\label{eq:boundingsmoothedmin}`
`:1380`, `\label{eq:splittingoffV}` `:1393`), `\label{eq:condLHL}` (`:462`–`:467`),
`\label{lem:groupPurification}` (`:354`) at `x = ∑ᵢ mᵢ² = 4`, §V.C (`:906`–`:919`; general test-set
size `m` at `:909`, `n_key = n − m` at `:913`, `m = 0.05·n` at `:970`); Renner 2005
(`arXiv:quant-ph/0512258v2`) `\label{thm:Hmincondrep}` (`main.tex:4561`), §5, §6.5;
Christandl–König–Renner 2009 (`arXiv:0809.3019`) `main.tex:447`–`:448`.
-/

open InfoTheory.Renyi

open Quantum.Operators Matrix Quantum.Channels Quantum.Metrics
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy InfoTheory.QuantumLHL Math.ClassicalEntropy
open Quantum.Symmetry Quantum.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.FiniteKey

/-! ## The selector-generic Rényi bound at free `ε_PA` and Rényi offset `β` -/

/-- **BB84 composable security at the Bell `C(n+3,3)` charge, a free `ε_PA`, a free Rényi offset
`β ∈ (0, 1)`, a general PE test-set size `m`, the Bernoulli KL accept tail priced on the
realised X-subsample, arbitrary selectors, and a free phase-error deviation `dev`.**

The free-deviation version of
`Window.half_mul_diamondNorm_sub_le_bellRenyiBudget`: the window `δ`
of the accept test stays the protocol's (completeness), while the entropy floor, the accept tail
and the key-rate condition are charged at the soundness edge `Q + δ + dev` (Nahar, Tupkary, Zhao,
Lütkenhaus and Tan 2024, arXiv:2403.11851, Lemma 9 Eq. 44 with §V.C). The budget prices the
deviation-scoped tail `phaseTail peSel xSel Q δ dev =
exp(−m_X·klBer (Q+δ) (Q+δ+dev))`; `dev = δ` gives the doubled-window specialization.
The soundness edge satisfies `Q + δ + dev ≤ 1/2`, the increasing domain of binary entropy.
The key-rate condition alone does not imply this domain: binary entropy is symmetric about `1/2`.

The deviation satisfies `0 ≤ dev`. If the actual tail is at least `1/8`, the budget is at
least one. Otherwise the tail forces `dev > 0`, and the extended entropy floor applies at every
positive smoothing radius and every positive privacy-amplification error.

It is a budget statement, not a key-rate claim, and not a delivered-key claim: no completeness
bound is discharged here.

References: Dupuis–Fawzi 2018 (`arXiv:1805.11652`) Cor. IV.2; Nahar et al. 2024
(`arXiv:2403.11851`) `\label{eq:condLHL}` (`main.tex:462`–`:467`), Lemma 9 Eq. 44, §V.C, App. B;
Renner 2005 (`arXiv:quant-ph/0512258v2`) `\label{thm:Hmincondrep}` (`main.tex:4561`). -/
theorem half_mul_diamondNorm_sub_le_bellRenyiBudget
    {n m ℓ ℓEV leakEC : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : KeyCount n m peSel)
    (ec : ECScheme n peSel leakEC)
    (hec : ec.IsTranslationEquivariant)
    (Q δ dev ε_AEP εPA β : ℝ)
    (hdev : 0 ≤ dev)
    (hbelow : Q + δ + dev ≤ 1 / 2)
    (hKey : BellRenyiKeyRate n m ℓ ℓEV leakEC Q δ dev ε_AEP εPA β)
    (hAEP : 0 < ε_AEP)
    (hεPApos : 0 < εPA)
    (hβpos : 0 < β) (hβ1 : β < 1) :
    (1 / 2) * diamondNorm
        (symReal n m ℓ ℓEV Q δ peSel xSel leakEC ec -
          symIdeal n m ℓ ℓEV Q δ peSel xSel leakEC ec) ≤
      bellRenyiBudget (phaseTail peSel xSel Q δ dev) n ℓEV ε_AEP εPA := by
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
  have hg : (4 : ℝ) ≤ (Nat.choose (n + 3) 3 : ℝ) := by
    exact_mod_cast (show 4 ≤ Nat.choose (n + 3) 3 from
      (by norm_num : 4 = Nat.choose 4 3) ▸ Nat.choose_le_choose 3
        (by have := NeZero.ne n; omega))
  by_cases hE8 : phaseTail peSel xSel Q δ dev < 1 / 8
  · have hdevpos : 0 < dev := by
      rcases hdev.eq_or_lt with hzero | hpos
      · norm_num [← hzero, phaseTail] at hE8
      · exact hpos
    have hgen :=
      BellRenyi.half_mul_ckrTraceNorm_le_bellRenyiSecrecyBudget
      (n := n) (m := m) (ℓ := ℓ) (ℓEV := ℓEV)
      peSel xSel ec Q δ dev ε_AEP hbelow hAEP hcount β hβpos hβ1 εPA
      (BellRenyiKeyRate.half_mul_sqrt_le
        hKey hεPApos)
      (phaseTail_nonneg peSel xSel Q δ dev)
      (bellTailBound_phaseTail peSel xSel Q δ dev hdevpos)
    simp only [bellRenyiBudget,
    InfoTheory.Security.verificationError,
    Math.Combinatorics.deFinettiPrefactor_four]
    refine (half_mul_diamondNorm_sub_le_correctness_add_bell
      n m ℓ ℓEV Q δ peSel xSel leakEC ec hec).trans ?_
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hgen (Nat.cast_nonneg _))
  · apply hone.trans
    simpa only [bellRenyiBudget, Math.Combinatorics.deFinettiPrefactor_four,
      bellRenyiSecrecyBudget, InfoTheory.Security.smoothingError,
      InfoTheory.Security.acceptanceError, mul_add, add_assoc] using
      Real.one_le_add_mul_add_sqrt_of_large (c := InfoTheory.Security.verificationError ℓEV)
        hg (by unfold InfoTheory.Security.verificationError; positivity) hAEP.le hεPApos.le
        (Or.inr (Or.inl (le_of_not_gt hE8)))

/-- **BB84 composable security at the Bell `C(n+3,3)` charge, a free `ε_PA` (`\label{eq:condLHL}`,
Nahar et al. 2024), a free Rényi offset `β ∈ (0, 1)` (Dupuis–Fawzi Cor. IV.2 penalty at `β`), a
general PE test-set size `m`, the Bernoulli KL accept tail priced on the realised X-subsample,
and arbitrary selectors.**

The privacy-amplification error and Rényi offset are free: the
privacy-amplification error is the free parameter `ε_PA`, funded by `2·log(1/ε_PA) − 2·log 2` nats
through
`BellRenyiWindowKeyRate` instead of being fixed to `exp(−n·δ²/2)`, and the Dupuis–Fawzi
finite-size penalty is charged at an arbitrary admissible offset `β` instead of the clamped
optimiser `clampedRenyiOffset`.  The budget `bellRenyiBudget` contains neither `β` nor the
penalty: the penalty reaches the statement only through the key-rate condition, and `β` only
through the key-rate condition together with its admissibility hypotheses (`hβpos`, `hβ1`), via
the single hashing-cap obligation of the level-generic chain. This obligation requires
`0 < εPA`, with no upper bound. When the actual accept tail `E ≥ 1/8`, the budget covers the
channel-distance bound of one.

For `δ ≥ 0` , the theorem with deviation equal to the acceptance tolerance is the free-deviation
theorem
`half_mul_diamondNorm_sub_le_bellRenyiBudget` at `dev = δ`
(`phaseTail_self`, `bellRenyiKeyRate_self`). A negative window rejects
every outcome, so the real and ideal channels agree.

It is a budget statement, not a key-rate claim, and not a delivered-key claim: no completeness
bound is discharged here.

References: Dupuis–Fawzi 2018 (`arXiv:1805.11652`) Cor. IV.2; Nahar et al. 2024
(`arXiv:2403.11851`) `\label{eq:condLHL}` (`main.tex:462`–`:467`), Lemma 9 Eq. 44, App. B; Renner
2005 (`arXiv:quant-ph/0512258v2`) `\label{thm:Hmincondrep}` (`main.tex:4561`). -/
theorem Window.half_mul_diamondNorm_sub_le_bellRenyiBudget
    {n m ℓ ℓEV leakEC : ℕ} [NeZero n] [NeZero (4 ^ n)]
    (peSel xSel : Fin n → Bool) (hcount : KeyCount n m peSel)
    (ec : ECScheme n peSel leakEC)
    (hec : ec.IsTranslationEquivariant)
    (Q δ ε_AEP εPA β : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (hKey : BellRenyiWindowKeyRate n m ℓ ℓEV leakEC Q δ ε_AEP εPA β)
    (hAEP : 0 < ε_AEP)
    (hεPApos : 0 < εPA)
    (hβpos : 0 < β) (hβ1 : β < 1) :
    (1 / 2) * diamondNorm
        (symReal n m ℓ ℓEV Q δ peSel xSel leakEC ec -
          symIdeal n m ℓ ℓEV Q δ peSel xSel leakEC ec) ≤
      bellRenyiBudget (windowPhaseTail peSel xSel Q δ) n ℓEV ε_AEP εPA := by
  by_cases hδ : 0 ≤ δ
  · rw [← phaseTail_self]
    exact QKD.BB84.FiniteKey.half_mul_diamondNorm_sub_le_bellRenyiBudget
      peSel xSel hcount ec hec Q δ δ ε_AEP εPA β hδ
      (by rwa [show (Q : ℝ) + δ + δ = Q + 2 * δ from by ring])
      ((bellRenyiKeyRate_self n m ℓ ℓEV leakEC Q δ ε_AEP εPA β).mpr hKey)
      hAEP hεPApos hβpos hβ1
  · have hchannels := symReal_eq_symIdeal_of_empty_acceptance
      n m ℓ ℓEV Q δ peSel xSel leakEC ec (Or.inl (lt_of_not_ge hδ))
    rw [hchannels, sub_self, diamondNorm_zero, mul_zero]
    simp only [bellRenyiBudget,
    InfoTheory.Security.verificationError,
    Math.Combinatorics.deFinettiPrefactor_four, bellRenyiSecrecyBudget,
    InfoTheory.Security.smoothingError,
    InfoTheory.Security.acceptanceError]
    positivity

end QKD.BB84.FiniteKey

end -- noncomputable section
