import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.MixtureWeight
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.BellPELabelledMixture
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.BadBranchConcentration
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.PhaseAcceptSplit
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.PhasePivot
import QCryptLean.QKD.BB84.FiniteKey.PerRound.BellPhaseGoodSet
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
# The Bell accept split at the phase-error good set

The accept-tail interface of the Bell chain and its accept-split bad-branch bound, at the
phase-error good set `(goodPhaseRateSet Q (2δ))ᶜ` in place of `(goodRateSet Q (2δ))ᶜ`.

The free-deviation variants `BellTailBound` and
`Bell.sum_re_trace_unlabelled_badBranch_le_of_tailBound` take the pivot at
`goodPhaseRateSet Q (δ + dev)`: the accept-test **window** stays `δ` (protocol), while the
**deviation** `dev` sets the pivot the entropy floor is charged at (Nahar et al. 2024,
`arXiv:2403.11851`, Lemma 9 Eq. 44, §V.C); the `2δ` forms are the case `dev = δ`.

The interface is pointwise: it carries no measure, no Bochner integrability side condition and no
register width — it reads `componentAcceptProbability` alone.
Since `goodRateSet Q r ⊆ goodPhaseRateSet Q r`, the phase-bad complement is contained in
the two-error complement. A uniform cap on the two-error complement therefore restricts to
the phase-bad complement. Both halves of the accept split use the same phase-error good set.

The identity `unitRegisterEmbed_localAcceptMass_eq_onComponent` holds for every component,
so the accepted mass equals the source mass on either phase-bad set.

## Relation to the literature

The phase-error good set is not in the cited literature; it is licensed by
`QKD.BB84.FiniteKey.Window.div_le_componentAliceZRate_of_phaseRate_le`.  Gottesman–Lo
(arXiv:quant-ph/0105121, `main.tex:1638`, footnote `:278`) estimate `p_X` and `p_Z`
separately and demand *each* small — the ancestor of the phase-error conjunction, not authority for
dropping the bit ball.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (`arXiv:2403.11851`) App. B,
`\label{eq:tausplit}` (`main.tex:1356`–`:1361`) through `\label{eq:boundingsmoothedmin}`
(`main.tex:1380`–`:1387`), Lemma 9 Eq. 44; Renner 2005 (`arXiv:quant-ph/0512258v2`) §5, §6.5.
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

/-! ## 1. The phase-error accept-tail interface of the Bell chain -/

/-- **The accept-tail interface of the Bell chain, at the phase-error good set.**

`WindowBellTailBound peSel xSel Q δ E` says the source accept mass of every
**phase**-rate-bad component is at most `E`.

The phase-bad complement is contained in the two-error complement, because
`goodRateSet Q (2 * δ) ⊆ goodPhaseRateSet Q (2 * δ)`. A uniform source cap on the two-error
complement restricts to this interface with the same `E`.

The instance at the realised-X-subsample KL exponent is
`windowBellTailBound_windowPhaseTail` (`BellSourceTail.lean`).

Reference: Nahar et al. 2024 (`arXiv:2403.11851`) App. B, `\label{eq:tausplit}`
(`main.tex:1356`–`:1361`), Lemma 9 Eq. 44; Renner 2005 (`arXiv:quant-ph/0512258v2`) §5, §6.5. -/
def WindowBellTailBound {n : ℕ} (peSel xSel : Fin n → Bool) (Q δ E : ℝ) : Prop :=
  ∀ σ : DensityOp Signal, σ ∈ (goodPhaseRateSet Q (2 * δ))ᶜ →
    componentAcceptProbability n peSel xSel Q δ σ ≤ E

/-- **The Bell accept-tail interface at the phase-error good set, at a free phase-error deviation.**

The window/deviation split: the accept-test **window** stays `δ` (it fixes the accept mass
`componentAcceptProbability … Q δ …`), while the
**deviation** `dev` sets the bad set the cap is quantified over,
`(goodPhaseRateSet Q (δ + dev))ᶜ`.  The `2δ` form
(`WindowBellTailBound`) is the case `dev = δ`.  It is the hypothesis the free-deviation Bell
accept-split bound below consumes; the instance at the realised-X-subsample KL exponent is
`bellTailBound_phaseTail` (`BellSourceTail.lean`).

Reference: Nahar et al. 2024 (`arXiv:2403.11851`) Lemma 9 Eq. 44, §V.C; Renner 2005
(`arXiv:quant-ph/0512258v2`) §5, §6.5. -/
def BellTailBound {n : ℕ} (peSel xSel : Fin n → Bool)
    (Q δ dev E : ℝ) : Prop :=
  ∀ σ : DensityOp Signal, σ ∈ (goodPhaseRateSet Q (δ + dev))ᶜ →
    componentAcceptProbability n peSel xSel Q δ σ ≤ E

/-- The `dev = δ` interface identity `WindowBellTailBound → BellTailBound`: at `dev = δ` the
two quantification domains agree after the `δ + δ = 2 * δ` rewrite (not defeq). -/
theorem BellTailBound.of_windowBellTailBound
    {n : ℕ} {peSel xSel : Fin n → Bool} {Q δ E : ℝ}
    (hCap : WindowBellTailBound peSel xSel Q δ E) :
    BellTailBound peSel xSel Q δ δ E := by
  intro σ hσ
  rw [show (δ : ℝ) + δ = 2 * δ from by ring] at hσ
  exact hCap σ hσ

/-! ## 2. The Bell accept split at the phase-error good set -/

/-- **The Bell accept-split bad-branch bound at an abstract phase-error source cap, at a free
phase-error deviation.**

The accept-test window `δ` fixes the accept masses, while the deviation `dev` moves the
pivot to `goodPhaseRateSet Q (δ + dev)` and hence the cap `hCap` and the bad branch.  The
`2δ` form (`Bell.Window.sum_re_trace_unlabelled_badBranch_le`) is
the case `dev = δ`. The component accepted mass equals the source mass by
`unitRegisterEmbed_localAcceptMass_eq_onComponent`, so the phase-bad half costs `E`.

References: Nahar et al. 2024 (`arXiv:2403.11851`) Lemma 9 Eq. 44, App. B
`\label{eq:tausplit}` (`main.tex:1356`–`:1361`); Renner 2005 (`arXiv:quant-ph/0512258v2`) §6.5. -/
theorem Bell.sum_re_trace_unlabelled_badBranch_le_of_tailBound
    {n : ℕ}
    (peSel xSel : Fin n → Bool) (Q δ dev : ℝ)
    (E : ℝ) (hE0 : 0 ≤ E) (hCap : BellTailBound peSel xSel Q δ dev E) :
    ∑ x : Signals n,
        ((Matrix.of fun i j : Unit × Signals n =>
            ∫ φ in ((fun φ' : DensityOp (Bool × Bool) =>
              DensityOp.partialTraceRight (bellSource(φ'))) ⁻¹'
                  (goodPhaseRateSet Q (δ + dev)))ᶜ,
              ((pairedHaarPerSigmaFamily Unit (unitRegisterEmbed n)
                  (isChannel_unitRegisterEmbed n) peSel xSel Q δ
                (bellSource(φ))).stateMap x).toOp i j
              ∂(haarDensityMeasure (false, false)).measure :
            Op (Unit × Signals n)).trace).re
      ≤ E := by
  have hμP : MeasureTheory.IsProbabilityMeasure (haarDensityMeasure (false, false)).measure :=
    (haarDensityMeasure (false, false)).isProbability
  -- The `Sᶜ` pointwise cap at the ABSTRACT phase-error source cap, on the widened bad set.
  have hbadB : ∀ φ ∈
        ((fun φ' : DensityOp (Bool × Bool) => DensityOp.partialTraceRight (bellSource(φ'))) ⁻¹'
        (goodPhaseRateSet Q (δ + dev)))ᶜ,
      ∑ x : Signals n,
        ((pairedHaarPerSigmaFamily Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
            peSel xSel Q δ
          (bellSource(φ))).stateMap x).toOp.trace.re ≤ E := by
    intro φ hφ
    have hσbad : DensityOp.partialTraceRight (bellSource(φ)) ∈
        (goodPhaseRateSet Q (δ + dev))ᶜ := hφ
    rw [pairedHaarPerSigmaFamily_weightRe_eq_preLocalAcceptMass Unit
      (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n) peSel xSel Q δ (bellSource(φ))]
    rw [unitRegisterEmbed_localAcceptMass_eq_onComponent]
    exact hCap (DensityOp.partialTraceRight (bellSource(φ))) hσbad
  apply CQState.sum_trace_entryIntegral_le (haarDensityMeasure (false, false))
    (fun φ => pairedHaarPerSigmaFamily Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
      peSel xSel Q δ (bellSource(φ)))
    (continuous_bellPairedHaarPerSigmaFamily_blocks peSel xSel Q δ) _ hE0
  filter_upwards [MeasureTheory.ae_restrict_mem
    (Bell.measurableSet_preimage_goodPhaseRateSet Q δ dev).compl] with φ hφ
  exact hbadB φ hφ

/-- **The Bell accept-split bad-branch bound at an abstract phase-error source cap.**

The good set is the phase-error preimage
`S = (φ ↦ Tr_B (bellSource(φ)))⁻¹'(goodPhaseRateSet Q (2δ))`. If every phase-rate-bad
component’s source accept mass is at most `E`, the accept mass carried over `Sᶜ` is at most `E`.
The component accept mass equals the source mass. The assumptions on the window and exponent
belong to the source cap.

References: Nahar et al. 2024 (`arXiv:2403.11851`) App. B, `\label{eq:tausplit}`
(`main.tex:1356`–`:1361`) through `\label{eq:boundingsmoothedmin}` (`main.tex:1380`–`:1387`);
Renner 2005 (`arXiv:quant-ph/0512258v2`) §6.5. -/
theorem Bell.Window.sum_re_trace_unlabelled_badBranch_le
    {n : ℕ}
    (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    (E : ℝ) (hE0 : 0 ≤ E) (hCap : WindowBellTailBound peSel xSel Q δ E) :
    ∑ x : Signals n,
        ((Matrix.of fun i j : Unit × Signals n =>
            ∫ φ in ((fun φ' : DensityOp (Bool × Bool) =>
              DensityOp.partialTraceRight (bellSource(φ'))) ⁻¹'
                  (goodPhaseRateSet Q (2 * δ)))ᶜ,
              ((pairedHaarPerSigmaFamily Unit (unitRegisterEmbed n)
                  (isChannel_unitRegisterEmbed n) peSel xSel Q δ
                (bellSource(φ))).stateMap x).toOp i j
              ∂(haarDensityMeasure (false, false)).measure :
            Op (Unit × Signals n)).trace).re
      ≤ E := by
  -- the `dev = δ` instance of the free-deviation bound; the marker converts via the interface
  -- identity.
  have h := Bell.sum_re_trace_unlabelled_badBranch_le_of_tailBound peSel xSel
    Q δ δ E hE0 (BellTailBound.of_windowBellTailBound hCap)
  rwa [show (δ : ℝ) + δ = 2 * δ from by ring] at h

end QKD.BB84.FiniteKey

end -- noncomputable section
