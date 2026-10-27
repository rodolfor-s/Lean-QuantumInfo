import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelAnalysis
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PELabelledPerSigmaFamily
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.BellAcceptSplit
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.PhasePivot
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.PhaseTail
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

/-!
# The Bell accept split at the realised-X-subsample KL tail, on the phase-error good set

The instance of `WindowBellTailBound` at
`windowPhaseTail peSel xSel Q δ = exp(−m_X · klBer (Q+δ) (Q+2δ))`, and the general-`m`
labelled bad-branch bound on the `m`-sized announced-PE label register.

On the phase-error good set the failing statistic is a single phase inequality
(`lt_phaseRate_of_mem_goodPhaseRateSet_compl`), so the per-component bound
`Window.componentAcceptProbability_le_exp_neg_mul_klBer` (`PhasePivot.lean`) lands
directly on
the realised X-subsample with no bit arm and no selector pin. Its conclusion is
`windowPhaseTail peSel xSel Q δ` unfolded, so the interface instance is that lemma applied
pointwise.

## `m_X = 0` is covered, not excluded

There the tail is `1`; the Bell–Rényi security budget exceeds two and the channel-distance bound
applies. The exact accept-tail interface itself requires only a positive phase-error deviation.

## Relation to the literature

The phase-error good set is not in the cited literature; it is licensed by
`QKD.BB84.FiniteKey.Window.div_le_componentAliceZRate_of_phaseRate_le`. Gottesman–Lo
(arXiv:quant-ph/0105121, `main.tex:1638`, footnote `:278`) estimate `p_X` and `p_Z`
separately and demand each small — the ancestor of the phase-error conjunction, not authority for
dropping the bit ball.

## Window and deviation

The free-deviation declarations of this module (`bellTailBound_phaseTail`
in §1, `Bell.sum_re_trace_badBranch_le_of_tailBound`) free
the phase-error **deviation** `dev` from the accept-test **window** `δ`: the pivot reads
`goodPhaseRateSet Q (δ + dev)`, the tail is
`phaseTail peSel xSel Q δ dev = exp(−m_X · klBer (Q+δ) (Q+δ+dev))`, and the window
`δ` keeps only its protocol role; the `2δ` forms are the case `dev = δ`.  This is the window and
deviation split of Nahar et al. 2024 (arXiv:2403.11851) Lemma 9 Eq. 44, §V.C.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`) Lemma 9 Eq. 44 (the
per-component accept-mass bound at the subsample the statistic is measured on), App. B
`\label{eq:tausplit}` (`main.tex:1356`–`:1361`), §V.C (`main.tex:909`, `:913`, `:970`); Renner 2005
(`arXiv:quant-ph/0512258v2`) §5, §6.5.
-/

open Quantum.DeFinetti

open Quantum.Operators Matrix Quantum.Channels Quantum.Metrics
open QKD.BB84.Measurement
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy Math.ClassicalEntropy
open Quantum.Symmetry Quantum.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.FiniteKey

local notation "eSignal" => finTwoEquiv.symm.prodCongr finTwoEquiv.symm
local notation "bellSource(" φ ")" =>
  DensityOp.reindex (Equiv.prodCongr eSignal eSignal) (bellWembed φ)

/-! ## 1. The interface instance at the free phase-error deviation

The window `δ` is the accept test's half-width (protocol, completeness side); the deviation `dev`
is the gap between the window edge `Q + δ` and where the entropy floor is charged, `Q + δ + dev`
(soundness side).  Here `dev` enters only through the pivot `goodPhaseRateSet Q (δ + dev)`
and the KL exponent; the window `δ` is untouched, exactly as in Nahar et al. (arXiv:2403.11851)
Lemma 9 Eq. 44 with the deviation split of §V.C. -/

/-- **The Bell chain meets its phase-error accept-tail interface at the realised-`m_X` KL tail
widened by the free deviation `dev`, at arbitrary selectors.**  The incumbent 2δ form
`windowBellTailBound_windowPhaseTail` (§1b below) is the case `dev = δ`.

`componentAcceptProbability_le_exp_neg_mul_klBer` (`PhasePivot.lean`) caps a
component in the widened bad set `(goodPhaseRateSet Q (δ + dev))ᶜ` — the pivot of the
deviation-scoped chain, not the accept window, which stays `δ` — at
`exp(−m_X · klBer (Q+δ) (Q+δ+dev))`, i.e. `phaseTail peSel xSel Q δ dev`
unfolded.  As in §1b the interface is pointwise, so the instance is that lemma with the quantifier
reintroduced; no exponent conversion happens anywhere in this proof.

Reference: Nahar et al. 2024 (`arXiv:2403.11851`) Lemma 9 Eq. 44, §V.C (window/deviation split),
App. B `\label{eq:tausplit}` (`main.tex:1356`–`:1361`); Renner 2005
(`arXiv:quant-ph/0512258v2`) §5. -/
theorem bellTailBound_phaseTail
    {n : ℕ}
    (peSel xSel : Fin n → Bool) (Q δ dev : ℝ) (hdev : 0 < dev) :
    BellTailBound peSel xSel Q δ dev
      (phaseTail peSel xSel Q δ dev) :=
  fun σ hσ =>
    componentAcceptProbability_le_exp_neg_mul_klBer peSel xSel Q δ dev hdev
      σ hσ

/-! ## 1b. The interface instance at the realised X-subsample -/

/-- **The Bell chain meets its phase-error accept-tail interface at the realised-`m_X` KL tail**, at
arbitrary selectors.

`Window.componentAcceptProbability_le_exp_neg_mul_klBer` (`PhasePivot.lean`) caps a
phase-rate-bad component's source accept mass at `exp(−m_X · klBer (Q+δ) (Q+2δ))`, which is
`windowPhaseTail peSel xSel Q δ` unfolded.  The interface is pointwise, so the instance is
that lemma with the quantifier reintroduced — no exponent conversion happens anywhere in this
proof.  The proof is the `dev = δ` case of
`bellTailBound_phaseTail` (§1): its marker at `dev = δ` is this
marker after the `δ + δ = 2 * δ` rewrite, and the tail is read back with
`phaseTail_self`.

Reference: Nahar et al. 2024 (`arXiv:2403.11851`) Lemma 9 Eq. 44, App. B `\label{eq:tausplit}`
(`main.tex:1356`–`:1361`); Renner 2005 (`arXiv:quant-ph/0512258v2`) §5. -/
theorem windowBellTailBound_windowPhaseTail
    {n : ℕ}
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (hδ : 0 < δ) :
    WindowBellTailBound peSel xSel Q δ
      (windowPhaseTail peSel xSel Q δ) := by
  -- the free-deviation theorem at `dev = δ`; its marker is this marker after the `δ + δ = 2 * δ`
  -- rewrite
  have h := bellTailBound_phaseTail peSel xSel Q δ δ hδ
  rw [phaseTail_self] at h
  exact fun σ hσ => h σ (by rw [show (2:ℝ) * δ = δ + δ from by ring] at hσ; exact hσ)

/-! ## 2. The labelled bad-branch bound on the `m`-sized PE label register -/

/-- **The general-`m` labelled Bell accept-split bad-branch bound at an abstract phase-error source
cap.**

`tr (label block ⊗ M) = tr M`, entrywise under the set integral
(`trace_setIntegral_tensorLeftKernel_blocks_eq`), so attaching the general-`m` PE label leaves the
bad-branch trace unchanged and the `m`-free base bound
`Bell.Window.sum_re_trace_unlabelled_badBranch_le` applies verbatim.  The
defeq that makes the transport typecheck is `peLabelledPairedHaarPerSigmaFamily`'s own body
(`PELabelledPerSigmaFamily.lean`): it is
`(pairedHaarPerSigmaFamily …).tensorLeftKernel (peLabelKernel (m := m) peSel)`.

The positive deviation and exponent arithmetic enter only when constructing the source cap.

References: Nahar et al. 2024 (`arXiv:2403.11851`) App. B, `\label{eq:tausplit}`
(`main.tex:1356`–`:1361`) through `\label{eq:boundingsmoothedmin}` (`main.tex:1380`–`:1387`), and
`main.tex:909`, `:913` for the general-`m` split; Renner 2005 (`arXiv:quant-ph/0512258v2`) §6.5. -/
theorem Bell.Window.sum_re_trace_badBranch_le_of_tailBound
    {n m : ℕ}
    (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    (E : ℝ) (hE0 : 0 ≤ E) (hCap : WindowBellTailBound peSel xSel Q δ E) :
    ∑ x : Signals n,
        ((Matrix.of fun i j : (Signals (min n m) × (Unit × Signals n)) =>
            ∫ φ in ((fun φ' : DensityOp (Bool × Bool) =>
              DensityOp.partialTraceRight (bellSource(φ'))) ⁻¹'
                  (goodPhaseRateSet Q (2 * δ)))ᶜ,
              ((peLabelledPairedHaarPerSigmaFamily (m := m) Unit (unitRegisterEmbed n)
                (isChannel_unitRegisterEmbed n) peSel xSel Q δ
                (bellSource(φ))).stateMap x).toOp i j
              ∂(haarDensityMeasure (false, false)).measure :
          Op (Signals (min n m) × (Unit × Signals n))).trace).re ≤
      E := by
  have hsame : ∀ x : Signals n,
      (Matrix.of fun i j : (Signals (min n m) × (Unit × Signals n)) =>
          ∫ φ in ((fun φ' : DensityOp (Bool × Bool) =>
              DensityOp.partialTraceRight (bellSource(φ'))) ⁻¹'
                (goodPhaseRateSet Q (2 * δ)))ᶜ,
            ((peLabelledPairedHaarPerSigmaFamily (m := m) Unit (unitRegisterEmbed n)
              (isChannel_unitRegisterEmbed n) peSel xSel Q δ
              (bellSource(φ))).stateMap x).toOp i j
            ∂(haarDensityMeasure (false, false)).measure :
        Op (Signals (min n m) × (Unit × Signals n))).trace =
      (Matrix.of fun i j : (Unit × Signals n) =>
          ∫ φ in ((fun φ' : DensityOp (Bool × Bool) =>
              DensityOp.partialTraceRight (bellSource(φ'))) ⁻¹'
                (goodPhaseRateSet Q (2 * δ)))ᶜ,
            ((pairedHaarPerSigmaFamily Unit (unitRegisterEmbed n)
                (isChannel_unitRegisterEmbed n) peSel xSel Q δ
              (bellSource(φ))).stateMap x).toOp i j
            ∂(haarDensityMeasure (false, false)).measure :
        Op (Unit × Signals n)).trace := fun x =>
    trace_setIntegral_tensorLeftKernel_blocks_eq
      (fun φ : DensityOp (Bool × Bool) =>
        pairedHaarPerSigmaFamily Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
            peSel xSel Q δ (bellSource(φ)))
      (peLabelKernel (m := m) peSel)
      (peLabelKernel_matrix_trace (m := m) peSel) _ x
  simp_rw [hsame]
  exact Bell.Window.sum_re_trace_unlabelled_badBranch_le peSel xSel Q δ E hE0
    hCap

/-! ## 2b. The labelled bad-branch bound at the free phase-error deviation

The free-deviation analogue of §2: the pivot preimage moves from `goodPhaseRateSet Q (2 * δ)` to
`goodPhaseRateSet Q (δ + dev)` — the entropy-charge point of the deviation-scoped chain —
while the accept window `δ` and the label transport are unchanged.
The base bound consumed is
`Bell.sum_re_trace_unlabelled_badBranch_le_of_tailBound`
(`BellAcceptSplit.lean`), so the source cap is the free-deviation predicate. -/

/-- **The free-deviation analogue of
`Bell.Window.sum_re_trace_badBranch_le_of_tailBound`**: the
general-`m` labelled Bell accept-split bad-branch bound at an abstract phase-error source cap on
the widened bad set `(goodPhaseRateSet Q (δ + dev))ᶜ`.

Same transport as §2: `tr (label block ⊗ M) = tr M`, entrywise under the set integral
(`trace_setIntegral_tensorLeftKernel_blocks_eq`), so attaching the general-`m` PE label leaves
the bad-branch trace unchanged and the free-deviation bound
`Bell.sum_re_trace_unlabelled_badBranch_le_of_tailBound` applies verbatim.
The pivot of the integration domain is `δ + dev`; the accept window stays `δ`.

The positive deviation and exponent arithmetic enter only when constructing the source cap.

References: Nahar et al. 2024 (`arXiv:2403.11851`) Lemma 9 Eq. 44, §V.C (window/deviation
split), App. B, `\label{eq:tausplit}` (`main.tex:1356`–`:1361`) through
`\label{eq:boundingsmoothedmin}` (`main.tex:1380`–`:1387`), and `main.tex:909`, `:913` for the
general-`m` split; Renner 2005 (`arXiv:quant-ph/0512258v2`) §6.5. -/
theorem Bell.sum_re_trace_badBranch_le_of_tailBound
    {n m : ℕ}
    (peSel xSel : Fin n → Bool) (Q δ dev : ℝ)
    (E : ℝ) (hE0 : 0 ≤ E)
    (hCap : BellTailBound peSel xSel Q δ dev E) :
    ∑ x : Signals n,
        ((Matrix.of fun i j : (Signals (min n m) × (Unit × Signals n)) =>
            ∫ φ in ((fun φ' : DensityOp (Bool × Bool) =>
              DensityOp.partialTraceRight (bellSource(φ'))) ⁻¹'
                  (goodPhaseRateSet Q (δ + dev)))ᶜ,
              ((peLabelledPairedHaarPerSigmaFamily (m := m) Unit (unitRegisterEmbed n)
                (isChannel_unitRegisterEmbed n) peSel xSel Q δ
                (bellSource(φ))).stateMap x).toOp i j
              ∂(haarDensityMeasure (false, false)).measure :
          Op (Signals (min n m) × (Unit × Signals n))).trace).re ≤
      E := by
  have hsame : ∀ x : Signals n,
      (Matrix.of fun i j : (Signals (min n m) × (Unit × Signals n)) =>
          ∫ φ in ((fun φ' : DensityOp (Bool × Bool) =>
              DensityOp.partialTraceRight (bellSource(φ'))) ⁻¹'
                (goodPhaseRateSet Q (δ + dev)))ᶜ,
            ((peLabelledPairedHaarPerSigmaFamily (m := m) Unit (unitRegisterEmbed n)
              (isChannel_unitRegisterEmbed n) peSel xSel Q δ
              (bellSource(φ))).stateMap x).toOp i j
            ∂(haarDensityMeasure (false, false)).measure :
        Op (Signals (min n m) × (Unit × Signals n))).trace =
      (Matrix.of fun i j : (Unit × Signals n) =>
          ∫ φ in ((fun φ' : DensityOp (Bool × Bool) =>
              DensityOp.partialTraceRight (bellSource(φ'))) ⁻¹'
                (goodPhaseRateSet Q (δ + dev)))ᶜ,
            ((pairedHaarPerSigmaFamily Unit (unitRegisterEmbed n)
                (isChannel_unitRegisterEmbed n) peSel xSel Q δ
              (bellSource(φ))).stateMap x).toOp i j
            ∂(haarDensityMeasure (false, false)).measure :
        Op (Unit × Signals n)).trace := fun x =>
    trace_setIntegral_tensorLeftKernel_blocks_eq
      (fun φ : DensityOp (Bool × Bool) =>
        pairedHaarPerSigmaFamily Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
            peSel xSel Q δ (bellSource(φ)))
      (peLabelKernel (m := m) peSel)
      (peLabelKernel_matrix_trace (m := m) peSel) _ x
  simp_rw [hsame]
  exact Bell.sum_re_trace_unlabelled_badBranch_le_of_tailBound peSel xSel Q δ
    dev E hE0 hCap

end QKD.BB84.FiniteKey

end -- noncomputable section
