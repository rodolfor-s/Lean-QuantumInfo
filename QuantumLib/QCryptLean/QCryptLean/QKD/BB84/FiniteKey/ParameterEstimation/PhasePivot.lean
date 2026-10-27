import QCryptLean.Math.Concentration.BernoulliKL
import QCryptLean.Math.Concentration.BinomialKLChernoff
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PELabelledPerSigmaFamily
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.BadBranchConcentration
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.PEConcentration
import QCryptLean.QKD.BB84.Model.ErrorModel
import QCryptLean.QKD.BB84.Model.ProtocolPair
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.Quantum.DeFinetti.CKRMixture
import QCryptLean.Quantum.Operators.Basic

/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The phase-error good set set and the `hmXZ`-free accept split

A split-test bad-branch bound quantified over `goodRateSet` carries a hypothesis
`hmXZ : m_X ≤ m_Z`: the pivot set `goodRateSet` is a **conjunction** of a bit-error ball and a
phase-error ball, so its complement is a **disjunction**, and a bit-bad component is caught only
by the Z-subsample, whose exponent is `m_Z`-shaped; `hmXZ` weakens that down to the single
`m_X`-shaped conclusion.

This module replaces the pivot set by the phase ball alone.  The bit arm of the disjunction then
does not exist, the exponent is `m_X` outright, and `hmXZ` is not needed.

## Direction of the change

`goodRateSet Q δ ⊆ goodPhaseRateSet Q δ`, so the good set grows and the bad set shrinks.  The
bad branch then integrates a nonnegative integrand over a smaller domain, so the tail side is
strictly easier; the burden that moves is the good branch, where the entropy floor must hold on
the larger set — it does, since `Window.div_le_componentAliceZRate_of_phaseRate_le`
binds only
`hbound : Q + 2δ ≤ 1/2` and the phase bound.

## Relation to the literature

No paper in the cited literature runs a phase-error good set set.  Gottesman–Lo
(arXiv:quant-ph/0105121, `main.tex:1638`, footnote `:278`) estimate `p_X` and `p_Z`
separately and demand each small — that is the ancestor of the two-basis **conjunction**, not
authority for dropping the bit ball.  Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024
(arXiv:2403.11851, `main.tex` §V.C, App. B, Lemma 9 Eq. 44) supply the per-component
acceptance-probability bound used below.  The comparator
(arXiv:2311.01600, `adaptivepaper.tex:206`, `:537` `\label{eq:acceptancetest}`, `:642`
`\label{eq:confinterval}`, `:1320` `\label{lemma:concentration}`) runs one statistic on all `m`
test rounds and carries the full `m` in its exponent, never a per-basis `min`.  The phase-error
pivot set here is our own, not transcribed from a source.

## Main definitions

- `QKD.BB84.FiniteKey.goodPhaseRateSet`: `goodRateSet` with the bit-error conjunct deleted.

## Main results

- `QKD.BB84.FiniteKey.lt_phaseRate_of_mem_goodPhaseRateSet_compl`: complement membership yields a
single
  inequality, not a disjunction.
- `QKD.BB84.FiniteKey.goodRateSet_subset_goodPhaseRateSet` /
  `QKD.BB84.FiniteKey.goodPhaseRateSet_compl_subset_goodRateSet_compl`: the inclusion.
- `QKD.BB84.FiniteKey.Window.isClosed_preimage_goodPhaseRateSet`: the Carathéodory input for the
  migrated pivot set.
- `QKD.BB84.FiniteKey.Window.componentAcceptProbability_le_exp_neg_mul_klBer`: the
per-σ bad-branch
bound
  at the KL-Chernoff exponent, without `hmXZ`.

## Window and deviation

The free-deviation twins (`isClosed_preimage_goodPhaseRateSet`,
`componentAcceptProbability_le_exp_neg_mul_klBer`) free the phase-error **deviation**
`dev`
from the accept-test **window** `δ`: the pivot reads `goodPhaseRateSet Q (δ + dev)` and the
KL-Chernoff exponent edge is `klBer (Q+δ) (Q+δ+dev)`, while the accept probability stays keyed to
the window `δ`.  The `2δ` forms in the Main results list are the case `dev = δ` (the window
half-width charged twice, once as window and once as deviation).  Reference: Nahar et al. 2024
(arXiv:2403.11851) Lemma 9 Eq. 44, §V.C.
-/

-- The paired-Haar per-σ family wiring states Bochner integrability of `Op`-valued block maps;
-- as in `AcceptSplit.lean` / `PerSigmaFamily.lean`, this uses the Frobenius norm.
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

open Quantum.Operators Matrix Quantum.Channels QKD.BB84.Measurement
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy
open Quantum.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder Kronecker
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.FiniteKey

/-! ## 1. The phase-error good set set -/

/-- **The phase-error good-rate set.**

`goodRateSet Q δ` (`Model/ProtocolPair.lean`) with the `bitFlipErrorRate`
conjunct deleted: the de Finetti components whose per-component single-round marginal
`componentAliceBobMarginal σ` has phase-flip error rate `≤ Q + δ`, with no constraint on the
bit-flip rate.

Keyed to the **per-component** marginal for the same reason as `goodRateSet`: a covariant mixture
(apply `X^{⊗n}` w.p. `f`, identity otherwise) carries a bad average while every per-component
statistic stays good, so an average-keyed classifier fails for the clean-majority covariant
mixture.  The membership predicate mentions no attack object and no block length.

This is a larger set than `goodRateSet Q δ` (`goodRateSet_subset_goodPhaseRateSet`), and the
inclusion is strict.  `bitFlipProjector = |β₀₁⟩⟨β₀₁| + |β₁₁⟩⟨β₁₁|` and `phaseFlipProjector =
|β₁₀⟩⟨β₁₀| + |β₁₁⟩⟨β₁₁|` (`QCryptLean/QKD/BB84/Model/ErrorModel.lean`), so the Bell
component `|β₀₁⟩⟨β₀₁|` has bit-flip rate `1` and phase-flip rate `0`: it lies in
`goodPhaseRateSet 0 0` and not in `goodRateSet 0 0`.  On components whose two rates coincide,
the two sets agree; the honest pair is one of them (`honestPauliChannel`: bit and phase flips
each with probability `Q`, never both).  The enlargement bites exactly on the bit-heavy components
that the AEP theorem's entropy floor never reads.

Reference for the per-component statistic: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024
(arXiv:2403.11851) Lemma 9 Eq. 44.  The phase-error restriction itself is not from the literature —
see the module docstring. -/
def goodPhaseRateSet
    (Q δ : ℝ) :
    Set (DensityOp Signal) :=
  {σ | phaseFlipErrorRate (componentAliceBobMarginal σ) ≤ Q + δ}

/-- Measurability of the phase-error good-rate set. -/
theorem measurableSet_goodPhaseRateSet
    (Q δ : ℝ) :
    MeasurableSet (goodPhaseRateSet Q δ) := by
  simpa [goodPhaseRateSet] using
    ((phaseFlipErrorRate_measurable.comp
        componentAliceBobMarginal_measurable).le' measurable_const)

/-- **Outside `goodPhaseRateSet`, the phase-flip rate exceeds `Q + δ`.**

This is a *single* inequality, not a disjunction of a bit- and a phase-error bound — which is
why `hmXZ` is absent from every bound below. -/
theorem lt_phaseRate_of_mem_goodPhaseRateSet_compl
    (Q δ : ℝ) {σ : DensityOp Signal}
    (hσ : σ ∈ (goodPhaseRateSet Q δ)ᶜ) :
    Q + δ < phaseFlipErrorRate (componentAliceBobMarginal σ) := by
  have hnot : ¬ (phaseFlipErrorRate (componentAliceBobMarginal σ) ≤ Q + δ) := by
    simpa [goodPhaseRateSet] using hσ
  exact lt_of_not_ge hnot

/-- **The good set grows**: `goodRateSet Q δ ⊆ goodPhaseRateSet Q δ`, by projecting the
conjunction onto its phase component.

No `0 ≤ δ` side condition is needed: the two sets are taken at the same margin and the inclusion
is a projection, not a threshold comparison. -/
theorem goodRateSet_subset_goodPhaseRateSet
    (Q δ : ℝ) :
    goodRateSet Q δ ⊆ goodPhaseRateSet Q δ := fun _ hσ => hσ.2

/-- **The bad set shrinks**: `(goodPhaseRateSet Q δ)ᶜ ⊆ (goodRateSet Q δ)ᶜ`.

Complement direction of `goodRateSet_subset_goodPhaseRateSet`. -/
theorem goodPhaseRateSet_compl_subset_goodRateSet_compl
    (Q δ : ℝ) :
    (goodPhaseRateSet Q δ)ᶜ ⊆ (goodRateSet Q δ)ᶜ :=
  Set.compl_subset_compl.mpr (goodRateSet_subset_goodPhaseRateSet Q δ)

/-! ## 1b. Strictness of the inclusion -/

/-- The `Tr_B`-pullback of the phase-error good-rate set at the deviation-scoped radius `δ + dev` —
the Carathéodory input of the floor chain at the free phase-error deviation (the window `δ` stays
the protocol's; only the deviation moves).  The `2δ` form
`Window.isClosed_preimage_goodPhaseRateSet` is the special case `dev = δ`. -/
theorem isClosed_preimage_goodPhaseRateSet (Q δ dev : ℝ) :
    IsClosed ((DensityOp.partialTraceRight :
        DensityOp (Signal × Signal) → DensityOp Signal) ⁻¹'
      (goodPhaseRateSet Q (δ + dev))) := by
  have hphase : Continuous (fun σ : DensityOp Signal =>
      phaseFlipErrorRate (componentAliceBobMarginal σ)) :=
    continuous_phaseFlipErrorRate.comp componentAliceBobMarginal_continuous
  have hgood : IsClosed (goodPhaseRateSet Q (δ + dev)) := isClosed_le hphase continuous_const
  exact hgood.preimage Quantum.DeFinetti.continuous_partialTraceRight

/-- The `Tr_B`-pullback of the phase-error good-rate set is closed — the Carathéodory input of the
finite decomposition `integralRestrict_eq_finite_subConvexCombination`, at the migrated pivot set.

`goodPhaseRateSet` is a single `≤`-sublevel set of the continuous
`phaseFlipErrorRate ∘ componentAliceBobMarginal`, hence closed, and
`DensityOp.partialTraceRight` is continuous. -/
theorem Window.isClosed_preimage_goodPhaseRateSet (Q δ : ℝ) :
    IsClosed ((DensityOp.partialTraceRight :
        DensityOp (Signal × Signal) → DensityOp Signal) ⁻¹'
      (goodPhaseRateSet Q (2 * δ))) := by
  rw [show (2:ℝ) * δ = δ + δ from by ring]
  exact QKD.BB84.FiniteKey.isClosed_preimage_goodPhaseRateSet Q δ δ

/-! ## 2. The per-arm bad-branch concentration, without `hmXZ` -/

/-- **The KL-exponent bad-branch bound on the phase-error good set at a free deviation,
without
`hmXZ`.**

The window/deviation split of `phaseTail` (`PhaseTail.lean`):
the accept-test **window** stays `δ` (the pass threshold `Q + δ` of
`componentAcceptProbability_le_binomialPassSum`), while the **deviation** `dev` sets the pivot edge
`Q + δ + dev` and hence the KL exponent edge.  The `2δ` form
(`Window.componentAcceptProbability_le_exp_neg_mul_klBer`) is the case `dev = δ`.

Only the positive deviation is needed, through the pivot edge `Q + δ < Q + δ + dev`.

References: Renner (2005) §5; Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851)
Lemma 9 Eq. 44. -/
theorem componentAcceptProbability_le_exp_neg_mul_klBer
    {n : ℕ}
    (peSel xSel : Fin n → Bool) (Q δ dev : ℝ) (hdev : 0 < dev)
    (σ : DensityOp Signal) (hσ : σ ∈ (goodPhaseRateSet Q (δ + dev))ᶜ) :
    componentAcceptProbability n peSel xSel Q δ σ ≤
      Real.exp (-(siftedXTestSampleSize peSel xSel : ℝ) *
        Math.Concentration.BernoulliKL.klBer (Q + δ) (Q + δ + dev)) := by
  classical
  have hQedge : Q + δ < Q + δ + dev := by linarith
  have hphase := lt_phaseRate_of_mem_goodPhaseRateSet_compl Q (δ + dev) hσ
  rw [componentAliceBobMarginal_eq] at hphase
  -- `Q + (δ + dev)` is `Q + δ + dev` up to association, not definitionally.
  have hphase' : Q + δ + dev < phaseFlipErrorRate σ := by linarith
  have hbounds := phaseFlipErrorRate_bounds σ
  refine (componentAcceptProbability_le_binomialPassSum peSel xSel Q δ σ).trans ?_
  exact Math.Concentration.BinomialKLChernoff.binomialPassSum_le_exp_neg_mul_klBer
    (siftedXTestSampleSize peSel xSel) Q δ (Q + δ + dev) (phaseFlipErrorRate σ)
    hQedge hphase'.le hbounds.1 hbounds.2 (lt_of_lt_of_le hphase' hbounds.2)

/-- **The KL-exponent bad-branch bound on the phase-error good set, without `hmXZ`.**

Conclusion `exp(−m_X · klBer (Q+δ) (Q+2δ))`: with the bit branch gone, the KL exponent is
exactly what `binomialPassSum_le_exp_neg_mul_klBer` returns on the X-subsample, with no `m_Z → m_X`
weakening step needed.

The positive window supplies the deviation between `Q + δ` and `Q + 2δ`.

References: Renner (2005) §5; Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851)
Lemma 9 Eq. 44. -/
theorem Window.componentAcceptProbability_le_exp_neg_mul_klBer
    {n : ℕ}
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (hδ : 0 < δ)
    (σ : DensityOp Signal) (hσ : σ ∈ (goodPhaseRateSet Q (2 * δ))ᶜ) :
    componentAcceptProbability n peSel xSel Q δ σ ≤
      Real.exp (-(siftedXTestSampleSize peSel xSel : ℝ) *
        Math.Concentration.BernoulliKL.klBer (Q + δ) (Q + 2 * δ)) := by
  -- the free-deviation theorem at `dev = δ`, with the `2δ` edges read back off the result
  have h := QKD.BB84.FiniteKey.componentAcceptProbability_le_exp_neg_mul_klBer (n :=
    n) peSel xSel Q δ δ
    hδ
    σ (by rw [show (2:ℝ) * δ = δ + δ from by ring] at hσ; exact hσ)
  rwa [show (Q:ℝ) + δ + δ = Q + 2 * δ from by ring] at h

/-! ## 3. The two halves of the accept split, at the phase-error good set -/

end QKD.BB84.FiniteKey

end -- noncomputable section
