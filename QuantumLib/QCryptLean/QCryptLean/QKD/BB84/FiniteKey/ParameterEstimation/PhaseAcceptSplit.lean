import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelAnalysis
import QCryptLean.Math.Analysis.CompactSpaceIntegrable
import QCryptLean.Math.Concentration.BernoulliKL
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PELabelledPerSigmaFamily
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.BadBranchConcentration
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.PhasePivot
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.AcceptSplit
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.CKRMixture
import QCryptLean.Quantum.DeFinetti.Haar
import QCryptLean.Quantum.Operators.Basic

/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# KL accept splits at the phase-error good set

The source accept mass over the complement of `goodPhaseRateSet Q (δ + dev)` is bounded by
`exp(-m_X * klBer (Q + δ) (Q + δ + dev))`. The protocol window is `δ`; the deviation `dev`
sets the phase-error edge. Setting `dev = δ` gives the pivot `goodPhaseRateSet Q (2 * δ)`.

For an arbitrary CPTP pre-channel and `c ≥ 0`, componentwise domination
`acceptedMass ≤ c * sourceMass`
transfers a source cap `T` to phase-bad mass `c * T`.
The choice `c = 2` permits factor-two domination. At the unit register embedding, the accepted
mass equals the source accept mass on every component
(`unitRegisterEmbed_localAcceptMass_eq_onComponent`), giving the phase-bad bound `T`.
Adjoining the announced-PE label preserves these bounds because its kernel has unit trace.

References: Nahar, Tupkary, Zhao, Lütkenhaus, Tan 2024 (arXiv:2403.11851), Lemma 9 Eq. 44,
§V.C and Appendix B; Renner 2005 (arXiv:quant-ph/0512258v2), §5 and §6.5.
-/

open Quantum.DeFinetti

-- The paired-Haar per-σ family wiring states Bochner integrability of `Op`-valued block maps;
-- as in `PhasePivot.lean`, this uses the Frobenius norm.
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
attribute [local instance] Matrix.frobeniusNormedSpace

private noncomputable local instance (X : Type*) [Fintype X] :
    ContinuousENorm (Quantum.Operators.Op X) :=
  SeminormedAddGroup.toContinuousENorm

open Quantum.Operators Matrix Quantum.Channels Quantum.Metrics
open QKD.BB84.Measurement
open Math.RepresentationTheory
open InfoTheory.SmoothMinEntropy Math.ClassicalEntropy
open Quantum.Symmetry Quantum.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.FiniteKey

/-! ## 1. The KL source cap at a free phase-error deviation -/

/-- **C3 at the KL exponent on the phase-error good set at a free deviation, integral form —
against any `DensityMeasure`.**

The window/deviation split: the accept-test **window** stays `δ` (it is in the integrand
`componentAcceptProbability … Q δ …`, fixed by the protocol), while the
**deviation** `dev` sets the pivot `goodPhaseRateSet Q (δ + dev)` and the exponent edge
`klBer (Q+δ) (Q+δ+dev)`.  The `2δ` form
(`Window.integral_badPhase_le_exp_neg_mul_klBer`) is the case
`dev = δ`; the mechanism is pointwise
(`componentAcceptProbability_le_exp_neg_mul_klBer`, `PhasePivot.lean`), so the integral
follows by integrating over the probability measure.

References: Renner 2005 §5; Nahar et al. 2024 (`arXiv:2403.11851`) Lemma 9 Eq. 44. -/
theorem integral_badPhase_le_exp_kl
    {n : ℕ}
    (peSel xSel : Fin n → Bool) (Q δ dev : ℝ) (hdev : 0 < dev)
    (μ : Quantum.DeFinetti.DensityMeasure Signal) :
    (∫ σ in (goodPhaseRateSet Q (δ + dev))ᶜ,
        componentAcceptProbability n peSel xSel Q δ σ ∂μ.measure) ≤
      Real.exp (-(siftedXTestSampleSize peSel xSel : ℝ) *
        Math.Concentration.BernoulliKL.klBer (Q + δ) (Q + δ + dev)) := by
  have hPerσ :
      ∀ σ : DensityOp Signal, σ ∈ (goodPhaseRateSet Q (δ + dev))ᶜ →
        componentAcceptProbability n peSel xSel Q δ σ ≤
          Real.exp (-(siftedXTestSampleSize peSel xSel : ℝ) *
            Math.Concentration.BernoulliKL.klBer (Q + δ) (Q + δ + dev)) :=
    fun σ hσ =>
      componentAcceptProbability_le_exp_neg_mul_klBer peSel xSel Q δ dev hdev
        σ hσ
  have hProb : MeasureTheory.IsProbabilityMeasure μ.measure := μ.isProbability
  have hInt : MeasureTheory.Integrable
      (componentAcceptProbability n peSel xSel Q δ) μ.measure := by
    have hAE := (continuous_componentAcceptProbability n peSel xSel Q
      δ).aestronglyMeasurable (μ := μ.measure)
    apply MeasureTheory.Integrable.of_bound hAE 1
    filter_upwards with σ
    rw [Real.norm_eq_abs,
      abs_of_nonneg (componentAcceptProbability_nonneg n peSel xSel Q δ σ)]
    exact componentAcceptProbability_le_one n peSel xSel Q δ σ
  have hMeas : MeasurableSet ((goodPhaseRateSet Q (δ + dev))ᶜ) :=
    (measurableSet_goodPhaseRateSet Q (δ + dev)).compl
  have hConstInt :
      MeasureTheory.IntegrableOn
        (fun _ => Real.exp (-(siftedXTestSampleSize peSel xSel : ℝ) *
          Math.Concentration.BernoulliKL.klBer (Q + δ) (Q + δ + dev)))
        ((goodPhaseRateSet Q (δ + dev))ᶜ) μ.measure :=
    MeasureTheory.integrableOn_const
  have hmono :=
    MeasureTheory.setIntegral_mono_on hInt.integrableOn hConstInt hMeas hPerσ
  rw [MeasureTheory.setIntegral_const, smul_eq_mul] at hmono
  refine hmono.trans ?_
  exact mul_le_of_le_one_left (Real.exp_pos _).le MeasureTheory.measureReal_le_one

/-! ## 2. The KL source cap at the phase-error good set -/

/-- **C3 at the KL exponent on the phase-error good set, integral form — against any
`DensityMeasure`.**

The `μ`-integral of the accept mass over `(goodPhaseRateSet Q (2δ))ᶜ` is at most
`exp(−m_X · klBer (Q+δ) (Q+2δ))` for **any** `DensityMeasure μ`: the `dev = δ`
corollary of `QKD.BB84.FiniteKey.integral_badPhase_le_exp_kl`.

References: Renner 2005 §5; Nahar et al. 2024 (`arXiv:2403.11851`) Lemma 9 Eq. 44. -/
theorem Window.integral_badPhase_le_exp_neg_mul_klBer
    {n : ℕ}
    (peSel xSel : Fin n → Bool) (Q δ : ℝ) (hδ : 0 < δ)
    (μ : Quantum.DeFinetti.DensityMeasure Signal) :
    (∫ σ in (goodPhaseRateSet Q (2 * δ))ᶜ,
        componentAcceptProbability n peSel xSel Q δ σ ∂μ.measure) ≤
      Real.exp (-(siftedXTestSampleSize peSel xSel : ℝ) *
        Math.Concentration.BernoulliKL.klBer (Q + δ) (Q + 2 * δ)) := by
  have h := QKD.BB84.FiniteKey.integral_badPhase_le_exp_kl
    peSel xSel Q δ δ hδ μ
  -- Read the `dev = δ` instance back in the `2δ` shape.
  rwa [show (Q:ℝ) + δ + δ = Q + 2 * δ from by ring,
    show (δ:ℝ) + δ = 2 * δ from by ring] at h

/-! ## 3. The `Sᶜ` half of the accept split at an ABSTRACT source cap, phase-error good set -/

/-- A componentwise bound `acceptedMass ≤ c * sourceMass` transfers a source cap `T` to
phase-bad mass at most `c * T`, for an arbitrary CPTP pre-channel and retained Eve register.
The Haar pushforward turns the block-entry integral into the CKR source integral. -/
theorem sum_re_trace_badBranch_le_of_integral_le {n : ℕ}
    (Eve : Type*) [Fintype Eve] [DecidableEq Eve]
    (pre : Op (Signals n) →ₗ[ℂ] Op (Signals n × Eve)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    (goodSet : Set (DensityOp Signal)) (hgoodMeas : MeasurableSet goodSet)
    (c : ℝ) (hc : 0 ≤ c)
    (hdom : ∀ σ ∈ goodSetᶜ,
      siftedPreLocalAcceptMass Eve pre hpre peSel xSel Q δ σ ≤
        c * componentAcceptProbability n peSel xSel Q δ σ)
    (T : ℝ)
    (hcap : (∫ σ in goodSetᶜ,
        componentAcceptProbability n peSel xSel Q δ σ
        ∂(ckrMixtureMeasure ((0, 0) : Signal)).measure) ≤ T) :
    ∑ x : Signals n,
        ((Matrix.of fun i j : (Eve × Signals n) =>
            ∫ ψ in ((DensityOp.partialTraceRight :
                  DensityOp (Signal × Signal) → DensityOp Signal) ⁻¹'
                goodSet)ᶜ,
              ((pairedHaarPerSigmaFamily Eve pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
              ∂(haarDensityMeasure (((0, 0), (0, 0)) : Signal × Signal)).measure :
            Op (Eve × Signals n)).trace).re
      ≤ c * T := by
  set μ16 := (haarDensityMeasure (((0, 0), (0, 0)) : Signal × Signal)).measure with hμ16
  set ckr := ckrMixtureMeasure ((0, 0) : Signal) with hckr
  have hckrProb : MeasureTheory.IsProbabilityMeasure ckr.measure := ckr.isProbability
  set S : Set (DensityOp Signal) := goodSetᶜ with hS
  have hSmeas : MeasurableSet S := hgoodMeas.compl
  set Spaired : Set (DensityOp (Signal × Signal)) :=
    ((DensityOp.partialTraceRight :
        DensityOp (Signal × Signal) → DensityOp Signal) ⁻¹'
      goodSet)ᶜ with hSpaired
  have hSpairedMeas : MeasurableSet Spaired :=
    (continuous_partialTraceRight.measurable hgoodMeas).compl
  have hmapeq : MeasureTheory.Measure.map
      (DensityOp.partialTraceRight :
        DensityOp (Signal × Signal) → DensityOp Signal) μ16 = ckr.measure := by
    dsimp [ckr, μ16, ckrMixtureMeasure, haarDensityMeasure]
    rw [MeasureTheory.Measure.map_map continuous_partialTraceRight.measurable
      (continuous_pureStateMap _).measurable]
    rfl
  -- Entry-eval continuous linear map `M ↦ M i j` ⇒ block-entry integrability.
  let entryCLM : (Eve × Signals n) →
      (Eve × Signals n) →
      (Op (Eve × Signals n) →L[ℝ] ℂ) := fun i j =>
    LinearMap.toContinuousLinearMap
      { toFun := fun M => M i j
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
  have hblockInt : ∀ x : Signals n,
      MeasureTheory.Integrable
        (fun ψ => ((pairedHaarPerSigmaFamily Eve pre hpre peSel xSel Q δ ψ).stateMap x).toOp)
            μ16 :=
    integrable_pairedHaarPerSigmaFamily_blocks Eve pre hpre peSel xSel Q δ
  have hentInt : ∀ (x : Signals n)
      (i : (Eve × Signals n)),
      MeasureTheory.IntegrableOn
        (fun ψ => ((pairedHaarPerSigmaFamily Eve pre hpre peSel xSel Q δ ψ).stateMap x).toOp
            i i)
        Spaired μ16 :=
    fun x i => ((entryCLM i i).integrable_comp (hblockInt x)).integrableOn
  -- (1) The per-ψ block reduction: the summed filtered trace is the attacked accept mass of the
  -- AB-marginal `Tr_B ψ`.
  have hsumψ := pairedHaarPerSigmaFamily_weightRe_eq_preLocalAcceptMass
    Eve pre hpre peSel xSel Q δ
  have hcont := continuous_siftedPreLocalAcceptMass Eve pre hpre peSel xSel Q δ
  -- (2) Reduce the entry-integral trace sum to the `S`-restricted attacked accept-mass integral.
  have hreduce :
      (∑ x : Signals n,
        ((Matrix.of fun i j : (Eve × Signals n) =>
            ∫ ψ in Spaired,
              ((pairedHaarPerSigmaFamily Eve pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
                  ∂μ16 :
            Op (Eve × Signals n)).trace).re)
        = ∫ σ in S, siftedPreLocalAcceptMass Eve pre hpre peSel xSel Q δ σ ∂ckr.measure := by
    have hperx : ∀ x : Signals n,
        ((Matrix.of fun i j : (Eve × Signals n) =>
            ∫ ψ in Spaired,
              ((pairedHaarPerSigmaFamily Eve pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
                  ∂μ16 :
            Op (Eve × Signals n)).trace).re =
          ∫ ψ in Spaired,
            ((pairedHaarPerSigmaFamily Eve pre hpre peSel xSel Q δ ψ).stateMap
                x).toOp.trace.re ∂μ16 := by
      intro x
      rw [Matrix.trace]
      simp only [Matrix.diag_apply, Matrix.of_apply]
      rw [← MeasureTheory.integral_finsetSum _ (fun i _ => hentInt x i), ← Complex.reCLM_apply,
        ← ContinuousLinearMap.integral_comp_comm Complex.reCLM
          (MeasureTheory.integrable_finsetSum _ (fun i _ => hentInt x i))]
      refine MeasureTheory.setIntegral_congr_fun hSpairedMeas (fun ψ _ => ?_)
      simp only [Complex.reCLM_apply, Matrix.trace, Matrix.diag_apply, Complex.re_sum]
    rw [Finset.sum_congr rfl (fun x _ => hperx x)]
    have htrInt : ∀ x : Signals n,
        MeasureTheory.IntegrableOn
          (fun ψ => ((pairedHaarPerSigmaFamily Eve pre hpre peSel xSel Q δ ψ).stateMap
              x).toOp.trace.re)
          Spaired μ16 := by
      intro x
      have heq : (fun ψ =>
            ((pairedHaarPerSigmaFamily Eve pre hpre peSel xSel Q δ ψ).stateMap
                x).toOp.trace.re)
          = fun ψ =>
            ∑ i, (((pairedHaarPerSigmaFamily Eve pre hpre peSel xSel Q δ ψ).stateMap x).toOp
                i i).re := by
        funext ψ; simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum]
      rw [heq]
      exact MeasureTheory.integrable_finsetSum _ fun i _ =>
        Complex.reCLM.integrable_comp (hentInt x i)
    rw [← MeasureTheory.integral_finsetSum _ (fun x _ => htrInt x),
      MeasureTheory.setIntegral_congr_fun hSpairedMeas (fun ψ _ => hsumψ ψ),
      show Spaired = (DensityOp.partialTraceRight :
            DensityOp (Signal × Signal) → DensityOp Signal) ⁻¹' S by
        rw [hSpaired, hS, Set.preimage_compl],
      ← MeasureTheory.setIntegral_map hSmeas hcont.aestronglyMeasurable
        continuous_partialTraceRight.measurable.aemeasurable, hmapeq]
  rw [hreduce]
  have hsource := continuous_componentAcceptProbability n peSel xSel Q δ
  have hmono := MeasureTheory.setIntegral_mono_on
    (hcont.integrable_of_compactSpace (μ := ckr.measure)).integrableOn
    ((continuous_const.mul hsource).integrable_of_compactSpace
      (μ := ckr.measure)).integrableOn hSmeas hdom
  simp only [Pi.mul_apply] at hmono
  rw [MeasureTheory.integral_const_mul] at hmono
  exact hmono.trans (mul_le_mul_of_nonneg_left hcap hc)

/-- **The `Sᶜ` half at an abstract source cap, phase-error good set.**

The pivot is the phase-error good-rate set `goodPhaseRateSet Q (2δ)`; the cap is over its
complement against the CKR mixture measure.  Corollary of
`sum_re_trace_badBranch_le_of_integral_le` at `goodSet =
goodPhaseRateSet Q (2δ)`.

References: Nahar et al. 2024 (arXiv:2403.11851) main.tex:1364–:1372; Renner 2005 §6.5. -/
theorem Window.sum_re_trace_phaseBadBranch_le_mul_of_sourceCap {n : ℕ}
    (Eve : Type*) [Fintype Eve] [DecidableEq Eve]
    (pre : Op (Signals n) →ₗ[ℂ] Op (Signals n × Eve)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hdom : ∀ σ ∈ (goodPhaseRateSet Q (2 * δ))ᶜ,
      siftedPreLocalAcceptMass Eve pre hpre peSel xSel Q δ σ ≤
        c * componentAcceptProbability n peSel xSel Q δ σ)
    (T : ℝ)
    (hcap : (∫ σ in (goodPhaseRateSet Q (2 * δ))ᶜ,
        componentAcceptProbability n peSel xSel Q δ σ
        ∂(ckrMixtureMeasure ((0, 0) : Signal)).measure) ≤ T) :
    ∑ x : Signals n,
        ((Matrix.of fun i j : (Eve × Signals n) =>
            ∫ ψ in ((DensityOp.partialTraceRight :
                  DensityOp (Signal × Signal) → DensityOp Signal) ⁻¹'
                (goodPhaseRateSet Q (2 * δ)))ᶜ,
              ((pairedHaarPerSigmaFamily Eve pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
              ∂(haarDensityMeasure (((0, 0), (0, 0)) : Signal × Signal)).measure :
            Op (Eve × Signals n)).trace).re
      ≤ c * T := by
  refine sum_re_trace_badBranch_le_of_integral_le Eve pre hpre peSel
    xSel Q δ (goodPhaseRateSet Q (2 * δ))
    (measurableSet_goodPhaseRateSet Q (2 * δ)) c hc hdom T hcap

/-- The phase-bad mass at a free deviation is bounded by `c * T` under componentwise domination.
The window `δ` fixes acceptance; the deviation `dev` sets `goodPhaseRateSet Q (δ + dev)`. -/
theorem sum_re_trace_phaseBadBranch_le_mul_of_sourceCap {n : ℕ}
    (Eve : Type*) [Fintype Eve] [DecidableEq Eve]
    (pre : Op (Signals n) →ₗ[ℂ] Op (Signals n × Eve)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ dev : ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hdom : ∀ σ ∈ (goodPhaseRateSet Q (δ + dev))ᶜ,
      siftedPreLocalAcceptMass Eve pre hpre peSel xSel Q δ σ ≤
        c * componentAcceptProbability n peSel xSel Q δ σ)
    (T : ℝ)
    (hcap : (∫ σ in (goodPhaseRateSet Q (δ + dev))ᶜ,
        componentAcceptProbability n peSel xSel Q δ σ
        ∂(ckrMixtureMeasure ((0, 0) : Signal)).measure) ≤ T) :
    ∑ x : Signals n,
        ((Matrix.of fun i j : (Eve × Signals n) =>
            ∫ ψ in ((DensityOp.partialTraceRight :
                  DensityOp (Signal × Signal) → DensityOp Signal) ⁻¹'
                (goodPhaseRateSet Q (δ + dev)))ᶜ,
              ((pairedHaarPerSigmaFamily Eve pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
              ∂(haarDensityMeasure (((0, 0), (0, 0)) : Signal × Signal)).measure :
            Op (Eve × Signals n)).trace).re
      ≤ c * T := by
  exact sum_re_trace_badBranch_le_of_integral_le Eve pre hpre peSel
    xSel Q δ (goodPhaseRateSet Q (δ + dev))
    (measurableSet_goodPhaseRateSet Q (δ + dev)) c hc hdom T hcap

/-! ## 5. The PE-labelled accept split at an abstract source cap, phase-error good set -/

/-- **The general-`m` PE-labelled accept split at an abstract source cap, phase-error good set.**

`tr (label block ⊗ M) = tr M`, entrywise under the set integral, so the PE-labelled bad-branch trace
is the unlabelled one and `Window.sum_re_trace_phaseBadBranch_le_mul_of_sourceCap`
applies verbatim.

References: Nahar et al. 2024 (`arXiv:2403.11851`) App. B; Renner 2005
(`arXiv:quant-ph/0512258v2`) §6.5. -/
theorem Window.sum_re_trace_badBranch_le
    {n m : ℕ}
    (Eve : Type*) [Fintype Eve] [DecidableEq Eve]
    (pre : Op (Signals n) →ₗ[ℂ] Op (Signals n × Eve)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ : ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hdom : ∀ σ ∈ (goodPhaseRateSet Q (2 * δ))ᶜ,
      siftedPreLocalAcceptMass Eve pre hpre peSel xSel Q δ σ ≤
        c * componentAcceptProbability n peSel xSel Q δ σ)
    (T : ℝ)
    (hcap : (∫ σ in (goodPhaseRateSet Q (2 * δ))ᶜ,
        componentAcceptProbability n peSel xSel Q δ σ
        ∂(ckrMixtureMeasure ((0, 0) : Signal)).measure) ≤ T) :
    ∑ x : Signals n,
        ((Matrix.of fun i j : (Signals (min n m) × (Eve × Signals n)) =>
            ∫ ψ in ((DensityOp.partialTraceRight :
                    DensityOp (Signal × Signal) → DensityOp Signal) ⁻¹'
                  (goodPhaseRateSet Q (2 * δ)))ᶜ,
              ((peLabelledPairedHaarPerSigmaFamily (m := m)
                Eve pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
              ∂(haarDensityMeasure (((0, 0), (0, 0)) : Signal × Signal)).measure :
          Op (Signals (min n m) × (Eve × Signals n))).trace).re ≤
      c * T := by
  have hsame : ∀ x : Signals n,
      (Matrix.of fun i j : (Signals (min n m) × (Eve × Signals n)) =>
          ∫ ψ in ((DensityOp.partialTraceRight :
                  DensityOp (Signal × Signal) → DensityOp Signal) ⁻¹'
                (goodPhaseRateSet Q (2 * δ)))ᶜ,
            ((peLabelledPairedHaarPerSigmaFamily (m := m)
              Eve pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
            ∂(haarDensityMeasure (((0, 0), (0, 0)) : Signal × Signal)).measure :
        Op (Signals (min n m) × (Eve × Signals n))).trace =
      (Matrix.of fun i j : (Eve × Signals n) =>
          ∫ ψ in ((DensityOp.partialTraceRight :
                  DensityOp (Signal × Signal) → DensityOp Signal) ⁻¹'
                (goodPhaseRateSet Q (2 * δ)))ᶜ,
            ((pairedHaarPerSigmaFamily Eve pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
            ∂(haarDensityMeasure (((0, 0), (0, 0)) : Signal × Signal)).measure :
        Op (Eve × Signals n)).trace := fun x =>
    trace_setIntegral_tensorLeftKernel_blocks_eq
      (fun ψ => pairedHaarPerSigmaFamily Eve pre hpre peSel xSel Q δ ψ)
      (peLabelKernel (m := m) peSel)
      (peLabelKernel_matrix_trace (m := m) peSel) _ x
  simp_rw [hsame]
  exact Window.sum_re_trace_phaseBadBranch_le_mul_of_sourceCap
    Eve pre hpre peSel xSel Q δ c hc hdom T hcap

/-- Adjoining the PE label preserves the bad-mass bound `c * T` at a free deviation.
Each label block has trace one, so the labelled bad-branch trace equals the unlabelled trace. -/
theorem sum_re_trace_badBranch_le
    {n m : ℕ}
    (Eve : Type*) [Fintype Eve] [DecidableEq Eve]
    (pre : Op (Signals n) →ₗ[ℂ] Op (Signals n × Eve)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ dev : ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hdom : ∀ σ ∈ (goodPhaseRateSet Q (δ + dev))ᶜ,
      siftedPreLocalAcceptMass Eve pre hpre peSel xSel Q δ σ ≤
        c * componentAcceptProbability n peSel xSel Q δ σ)
    (T : ℝ)
    (hcap : (∫ σ in (goodPhaseRateSet Q (δ + dev))ᶜ,
        componentAcceptProbability n peSel xSel Q δ σ
        ∂(ckrMixtureMeasure ((0, 0) : Signal)).measure) ≤ T) :
    ∑ x : Signals n,
        ((Matrix.of fun i j : (Signals (min n m) × (Eve × Signals n)) =>
            ∫ ψ in ((DensityOp.partialTraceRight :
                    DensityOp (Signal × Signal) → DensityOp Signal) ⁻¹'
                  (goodPhaseRateSet Q (δ + dev)))ᶜ,
              ((peLabelledPairedHaarPerSigmaFamily (m := m)
                Eve pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
              ∂(haarDensityMeasure (((0, 0), (0, 0)) : Signal × Signal)).measure :
          Op (Signals (min n m) × (Eve × Signals n))).trace).re ≤
      c * T := by
  have hsame : ∀ x : Signals n,
      (Matrix.of fun i j : (Signals (min n m) × (Eve × Signals n)) =>
          ∫ ψ in ((DensityOp.partialTraceRight :
                  DensityOp (Signal × Signal) → DensityOp Signal) ⁻¹'
                (goodPhaseRateSet Q (δ + dev)))ᶜ,
            ((peLabelledPairedHaarPerSigmaFamily (m := m)
              Eve pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
            ∂(haarDensityMeasure (((0, 0), (0, 0)) : Signal × Signal)).measure :
        Op (Signals (min n m) × (Eve × Signals n))).trace =
      (Matrix.of fun i j : (Eve × Signals n) =>
          ∫ ψ in ((DensityOp.partialTraceRight :
                  DensityOp (Signal × Signal) → DensityOp Signal) ⁻¹'
                (goodPhaseRateSet Q (δ + dev)))ᶜ,
            ((pairedHaarPerSigmaFamily Eve pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
            ∂(haarDensityMeasure (((0, 0), (0, 0)) : Signal × Signal)).measure :
        Op (Eve × Signals n)).trace := fun x =>
    trace_setIntegral_tensorLeftKernel_blocks_eq
      (fun ψ => pairedHaarPerSigmaFamily Eve pre hpre peSel xSel Q δ ψ)
      (peLabelKernel (m := m) peSel)
      (peLabelKernel_matrix_trace (m := m) peSel) _ x
  simp_rw [hsame]
  exact sum_re_trace_phaseBadBranch_le_mul_of_sourceCap
    Eve pre hpre peSel xSel Q δ dev c hc hdom T hcap

end QKD.BB84.FiniteKey

end -- noncomputable section
