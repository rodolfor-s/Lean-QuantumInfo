import QCryptLean.Math.Concentration.BernoulliKL
import QCryptLean.QKD.BB84.Constants
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PhaseMixture
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.PhaseAcceptSplit
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.AcceptSplit
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.Quantum.DeFinetti.CKRMixture

/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The accept tail at the realised X-subsample, on the phase-error good set

For `0 < Q`, `0 < δ`, and `Q + 2δ < errorThreshold`, the accept tail
priced at the realised X-subsample size is:

`windowPhaseTail peSel xSel Q δ = exp(−m_X · klBer (Q+δ) (Q+2δ))`,

which is exactly what `Window.componentAcceptProbability_le_exp_neg_mul_klBer`
(`PhasePivot.lean`) proves on the phase-error good set, with no conversion step and no `hmXZ`.

## Why it is stated on the phase-error good set

At the pivot `goodRateSet Q (2δ)` a bad component may be bit-bad only, and is then caught
by the **Z**-subsample, whose exponent is `m_Z`-shaped; collapsing that to an `m_X`-shaped
conclusion needs `hmXZ : m_X ≤ m_Z`, which pins the X-test selector.  The phase-error good set
deletes
the bit arm, so the `m_X` exponent is earned outright and the statements below are
**selector-generic**: no `hmXZ`, no selector literal.

## What is priced where — the free-lunch discipline

Both security theorems split on the actual KL tail and use the channel-distance bound when it is
large. Quadratic domination is a separate estimate on its stated numerical domain.

## Relation to the literature

The phase-error good set is not in the cited literature; it is licensed by
`QKD.BB84.FiniteKey.Window.div_le_componentAliceZRate_of_phaseRate_le`, whose parent is
hypothesis-free.
The per-component accept-mass bound at the subsample the statistic is measured on is Nahar,
Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`) Lemma 9 Eq. 44; the general test-set size
`m` is `main.tex:909` and `:913`, the simulated fraction `m = 0.05·n` is `:970`
(`\label{sec:plots}`).

## Main definitions

* `QKD.BB84.FiniteKey.windowPhaseTail` — the accept tail at the realised X-subsample.
* `QKD.BB84.FiniteKey.phaseTail` — the same tail at a free phase-error deviation
  `dev` (window `δ`, deviation `dev`); `windowPhaseTail` is the case `dev = δ`.

## Main results

* `QKD.BB84.FiniteKey.windowPhaseTail_le_exp_neg_mul_sq` — dominance over the quadratic
  `exp(−4·m_X·δ²)`.
* `QKD.BB84.FiniteKey.phaseTail_le_exp_neg_mul_sq` — quadratic domination
  at the free deviation, with exponent `klBer (Q+δ) (Q+δ+dev)`.
* `Window.phaseTailBound_unitEmbed` and its free-deviation
  version: the accept-tail interfaces from the exact unit-register accept-mass identity.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`) Lemma 9 Eq. 44, §V.C
`\subsection{Classical part}` (`main.tex:906`–`:919`), `main.tex:909`, `:913`, `:970`, App. B;
Renner 2005 (`arXiv:quant-ph/0512258v2`) §5, §6.5; Christandl–König–Renner 2009 (`arXiv:0809.3019`)
`main.tex:268`–`:401`.
-/

-- The paired-Haar per-σ family wiring states Bochner integrability of `Op`-valued block maps;
-- this uses the Frobenius norm.
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

open Quantum.Operators Matrix Quantum.Channels Quantum.Metrics
open QKD.BB84.Measurement
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy Math.ClassicalEntropy
open Quantum.Symmetry Quantum.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.FiniteKey

/-! ## 1. The tail at the realised X-subsample -/

/-- **The BB84 accept tail at the Bernoulli KL exponent and the REALISED X-subsample.**

`windowPhaseTail peSel xSel Q δ = exp(−m_X · klBer (Q+δ) (Q+2δ))`, with
`m_X = siftedXTestSampleSize peSel xSel`.

For `0 < Q`, `0 < δ` and `Q + 2δ < errorThreshold`, on the phase-error good set the local test
rejects a component whose phase-flip rate exceeds `Q + 2δ`
with probability at least `1 − exp(−m_X · klBer (Q+δ) (Q+2δ))` on its X-subsample
(`binomialPassSum_le_exp_neg_mul_klBer`, through
`Window.componentAcceptProbability_le_exp_neg_mul_klBer`), and no conversion off `m_X`
is performed:
this is the exponent as proved. Outside the displayed domain the definition is only a
total real scalar formula.

`m_X = 0` is covered: the tail is then `1`, and either security budget exceeds two.

Reference: Renner 2005 (`arXiv:quant-ph/0512258v2`) §5; Nahar et al. 2024 (`arXiv:2403.11851`)
Lemma 9 Eq. 44. -/
noncomputable def windowPhaseTail {n : ℕ} (peSel xSel : Fin n → Bool) (Q δ : ℝ) : ℝ :=
  Real.exp (-(siftedXTestSampleSize peSel xSel : ℝ) *
    Math.Concentration.BernoulliKL.klBer (Q + δ) (Q + 2 * δ))

/-- The KL accept tail is positive for `Q + δ ∈ [0, 1]` and `Q + 2δ ∈ (0, 1)`. -/
theorem windowPhaseTail_pos {n : ℕ} (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    (_hp : Q + δ ∈ Set.Icc (0 : ℝ) 1) (_hq : Q + 2 * δ ∈ Set.Ioo (0 : ℝ) 1) :
    0 < windowPhaseTail peSel xSel Q δ :=
  Real.exp_pos _

/-- The `m_X`-scoped KL accept tail is nonnegative — the `hE0` side condition of the accept-tail
slot. -/
theorem windowPhaseTail_nonneg {n : ℕ} (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    0 ≤ windowPhaseTail peSel xSel Q δ :=
  Real.exp_nonneg _

/-! ## 2. The tail at a free phase-error deviation -/

/-- **The BB84 accept tail at a free phase-error deviation and the REALISED X-subsample.**

`phaseTail peSel xSel Q δ dev = exp(−m_X · klBer (Q+δ) (Q+δ+dev))`, with
`m_X = siftedXTestSampleSize peSel xSel`.

The accept-tail bound below applies for `0 < Q`, `0 < δ`, `0 < dev`, and
`Q + δ + dev < errorThreshold`. More generally, the displayed Bernoulli divergence is finite
for `Q + δ ∈ [0, 1]` and `Q + δ + dev ∈ (0, 1)`; outside that domain this is only a
total real scalar formula.

This separates the two roles the accept-test half-width `δ` plays in `windowPhaseTail`: the
**window** `δ` of the accept test (`|observed X-error rate − Q| ≤ δ`, fixed by the protocol and
its completeness requirement) and the **deviation** `dev` between the window edge `Q + δ` and the
phase-error rate the entropy floor is charged at (fixed by soundness, i.e. by how small the
accept tail must be).  The pivot is `goodPhaseRateSet Q (δ + dev)`;
`windowPhaseTail` is the case `dev = δ`.

`m_X = 0` is covered: the tail is then `1` and the Bell budget exceeds two.
The security theorem handles this case with the channel-distance bound.

Reference: Nahar et al. 2024 (`arXiv:2403.11851`) Lemma 9 Eq. 44, §V.C; Renner 2005
(`arXiv:quant-ph/0512258v2`) §5. -/
noncomputable def phaseTail {n : ℕ} (peSel xSel : Fin n → Bool) (Q δ dev : ℝ) : ℝ :=
  Real.exp (-(siftedXTestSampleSize peSel xSel : ℝ) *
    Math.Concentration.BernoulliKL.klBer (Q + δ) (Q + δ + dev))

/-- At `dev = δ` the deviation-scoped KL accept tail **is** the `2δ` tail: `Q + δ + δ` and
`Q + 2 * δ` agree only propositionally, so this is a `rw`, not `rfl`. -/
theorem phaseTail_self {n : ℕ} (peSel xSel : Fin n → Bool) (Q δ : ℝ) :
    phaseTail peSel xSel Q δ δ = windowPhaseTail peSel xSel Q δ := by
  unfold phaseTail windowPhaseTail
  rw [show Q + δ + δ = Q + 2 * δ from by ring]

/-- The deviation-scoped KL tail is positive for `Q + δ ∈ [0, 1]`
and `Q + δ + dev ∈ (0, 1)`. -/
theorem phaseTail_pos {n : ℕ} (peSel xSel : Fin n → Bool) (Q δ dev : ℝ)
    (_hp : Q + δ ∈ Set.Icc (0 : ℝ) 1)
    (_hq : Q + δ + dev ∈ Set.Ioo (0 : ℝ) 1) :
    0 < phaseTail peSel xSel Q δ dev :=
  Real.exp_pos _

/-- The deviation-scoped KL accept tail is nonnegative — the `hE0` side condition of the
accept-tail slot. -/
theorem phaseTail_nonneg {n : ℕ} (peSel xSel : Fin n → Bool) (Q δ dev : ℝ) :
    0 ≤ phaseTail peSel xSel Q δ dev :=
  Real.exp_nonneg _

/-- **The deviation-scoped KL accept tail is bounded by the quadratic X-subsample tail
`exp(−4·m_X·dev²)`** on the admissible box.

One application of `Math.Concentration.BernoulliKL.four_mul_sq_le_klBer_add`: on `0 < Q`, `0
< δ`,
`0 < dev`, `Q + δ + dev < 0.11` that lemma gives `4·dev² ≤ klBer (Q+δ) (Q+δ+dev)`, and multiplying
by the nonnegative `m_X` turns it into the exponent inequality.  `errorThreshold` is read, not
moved. -/
theorem phaseTail_le_exp_neg_mul_sq {n : ℕ} {peSel xSel : Fin n → Bool}
    {Q δ dev : ℝ} (hQ : 0 < Q) (hδ : 0 < δ) (hdev : 0 < dev)
    (hbelow : Q + δ + dev < errorThreshold) :
    phaseTail peSel xSel Q δ dev ≤
      Real.exp (-4 * (siftedXTestSampleSize peSel xSel : ℝ) * dev ^ 2) := by
  have hKL : 4 * dev ^ 2 ≤ Math.Concentration.BernoulliKL.klBer (Q + δ) (Q + δ + dev) := by
    refine Math.Concentration.BernoulliKL.four_mul_sq_le_klBer_add Q δ dev hQ hδ hdev ?_
    have hthr : errorThreshold = (0.11 : ℝ) := by norm_num [errorThreshold]
    rw [← hthr]; exact hbelow
  have hmXnn : (0 : ℝ) ≤ (siftedXTestSampleSize peSel xSel : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hKL hmXnn
  unfold phaseTail
  refine Real.exp_le_exp.mpr ?_
  nlinarith only [hmul]

/-! ## 3. The scalar side conditions, priced at `m_X` -/

/-- **The `m_X`-scoped KL accept tail is bounded by the quadratic X-subsample tail
`exp(−4·m_X·δ²)`** on the admissible box.

One application of `Math.Concentration.BernoulliKL.four_mul_sq_le_klBer_add_two_mul`: on `0 < Q`,
`0 < δ`,
`Q + 2δ < 0.11` that lemma gives `4·δ² ≤ klBer (Q+δ) (Q+2δ)`, and multiplying by the nonnegative
`m_X` turns it into the exponent inequality.  `errorThreshold` is read, not moved. -/
theorem windowPhaseTail_le_exp_neg_mul_sq {n : ℕ} {peSel xSel : Fin n → Bool} {Q δ : ℝ}
    (hQ : 0 < Q) (hδ : 0 < δ) (hbelow : Q + 2 * δ < errorThreshold) :
    windowPhaseTail peSel xSel Q δ ≤
      Real.exp (-4 * (siftedXTestSampleSize peSel xSel : ℝ) * δ ^ 2) := by
  -- `dev = δ` corollary of `phaseTail_le_exp_neg_mul_sq`.
  have h : phaseTail peSel xSel Q δ δ ≤
      Real.exp (-4 * (siftedXTestSampleSize peSel xSel : ℝ) * δ ^ 2) :=
    phaseTail_le_exp_neg_mul_sq hQ hδ hδ
      (by rw [show Q + δ + δ = Q + 2 * δ from by ring]; exact hbelow)
  rwa [phaseTail_self] at h

/-! ## 4. The accept-tail interfaces -/

/-- The unit register embedding satisfies the phase-error bad-branch bound at the KL tail.
The accepted mass equals the source mass on each component, so the phase-bad branch costs `E`.

Reference: Nahar et al. 2024 (arXiv:2403.11851), Lemma 9 Eq. 44 and Appendix B. -/
theorem phaseTailBound_unitEmbed
    {n m : ℕ}
    (Q δ dev : ℝ) (hdev : 0 < dev) (peSel xSel : Fin n → Bool) :
    PhaseTailBound (m := m) Unit (unitRegisterEmbed n)
      (isChannel_unitRegisterEmbed n) peSel xSel Q δ dev
      (phaseTail peSel xSel Q δ dev) := by
  have hcap := QKD.BB84.FiniteKey.integral_badPhase_le_exp_kl
    peSel xSel Q δ dev hdev (ckrMixtureMeasure ((0, 0) : Signal))
  have h :=
    QKD.BB84.FiniteKey.sum_re_trace_badBranch_le (m := m)
      Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n) peSel xSel Q δ dev
      1 zero_le_one
      (fun σ _ => by rw [unitRegisterEmbed_localAcceptMass_eq_onComponent, one_mul])
      (phaseTail peSel xSel Q δ dev) hcap
  simp only [one_mul] at h
  exact h

/-- The KL bad-branch bound at the phase-error good set with deviation equal to the window.

Reference: Nahar et al. 2024 (arXiv:2403.11851), Lemma 9 Eq. 44 and Appendix B. -/
theorem Window.phaseTailBound_unitEmbed
    {n m : ℕ}
    (Q δ : ℝ) (hδ : 0 < δ) (peSel xSel : Fin n → Bool) :
    WindowPhaseTailBound (m := m) Unit (unitRegisterEmbed n)
      (isChannel_unitRegisterEmbed n) peSel xSel Q δ (windowPhaseTail peSel xSel Q δ) := by
  have h := QKD.BB84.FiniteKey.phaseTailBound_unitEmbed
    (m := m) Q δ δ hδ peSel xSel
  unfold PhaseTailBound at h
  rw [show (δ : ℝ) + δ = 2 * δ from by ring, phaseTail_self] at h
  exact h

end QKD.BB84.FiniteKey

end -- noncomputable section
