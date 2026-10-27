import QCryptLean.InfoTheory.Renyi.FiniteSizePenalty
import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelAnalysis
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.Mixture
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.BellHaarMixture
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.BellPELabelledMixture
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.ClassicalAnnounceKernel
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.Levels
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PELabelledPerSigmaFamily
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.BellInnerBudget
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.BellAcceptSplit
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.BellSourceTail
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.PhasePivot
import QCryptLean.QKD.BB84.FiniteKey.PerRound.BellRenyi
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.AcceptSplit
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.Haar
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Topology
import QCryptLean.Quantum.Symmetry.BellDoubling

/-!
# Bell Rényi entropy floors after public announcements

The accepted Bell mixture uses its own quantum marginal as reference.
The syndrome and verification announcements incur their stated entropy charges.
-/

open QKD.BB84.FiniteKey

open Quantum.DeFinetti

open InfoTheory.Renyi

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

/-! ## 1. The general-`m` Rényi Bell floor chain at the phase-error good set -/

/-- The extended Bell mixture floor after the PE announcement, at
a free Rényi offset. The completed signed floor satisfies
`ENNReal.ofReal k ≤ smoothMinEntropy (ε_AEP + √(2E)) ρ σ` for some reference `σ`.
Reference: Nahar et al. 2024, Appendix B; Dupuis–Fawzi 2018, Corollary IV.2. -/
theorem
    BellRenyi.exists_le_smoothMinEntropy_peState
    {n m : ℕ}
    (peSel xSel : Fin n → Bool) (hcount : KeyCount n m peSel)
    (Q δ dev : ℝ)
    (hbelow : Q + δ + dev ≤ 1 / 2)
    (ε_AEP : ℝ) (hAEP : 0 < ε_AEP)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : BellTailBound peSel xSel Q δ dev E) :
    ∃ σref : SubDensityOp
        (Signals (min n m) × (Unit × Signals n)),
      ENNReal.ofReal (bellRenyiFloor n m Q δ dev ε_AEP β) ≤
        smoothMinEntropy
          (ε_AEP + Real.sqrt (2 * E))
          (CQState.coarsen (aliceKeyString peSel)
            ((bellEnVRhoEtilde Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
                peSel xSel Q δ).tensorLeftKernel
              (peLabelKernel (m := m) peSel))) σref := by
  refine ⟨((bellEnVRhoEtilde Unit (unitRegisterEmbed n)
    (isChannel_unitRegisterEmbed n) peSel xSel Q δ).tensorLeftKernel
      (peLabelKernel (m := m) peSel)).quantumMarginal, ?_⟩
  by_cases hmn : m < n
  swap
  · by_cases hεlt1 : ε_AEP < 1
    · have hzero : keyRounds n m = 0 := Nat.sub_eq_zero_of_le (by omega)
      have hpen := renyiPenalty_nonneg binaryVarianceBound
        binaryVarianceBound_pos.le (keyRounds n m) ε_AEP β hAEP
        hεlt1.le hβpos.le hβ1.le
      have hlevel : bellRenyiFloor n m Q δ dev ε_AEP β ≤ 0 := by
        unfold bellRenyiFloor
        rw [hzero, Nat.cast_zero, zero_div, zero_mul]
        rw [hzero] at hpen
        linarith
      rw [ENNReal.ofReal_eq_zero.mpr hlevel]
      exact bot_le
    · rw [smoothMinEntropy_eq_top_of_weight_le_eps_sq (by positivity)]
      · exact le_top
      · have hw := (CQState.coarsen (aliceKeyString peSel)
          ((bellEnVRhoEtilde Unit (unitRegisterEmbed n)
            (isChannel_unitRegisterEmbed n) peSel xSel Q δ).tensorLeftKernel
              (peLabelKernel (m := m) peSel))).weight_le_one
        nlinarith [Real.sqrt_nonneg (2 * E)]
  set G : Set (DensityOp (Bool × Bool)) :=
    (fun φ' : DensityOp (Bool × Bool) => DensityOp.partialTraceRight (bellSource(φ'))) ⁻¹'
      goodPhaseRateSet Q (δ + dev) with hG
  have hgoodClosed : IsClosed G :=
    (QKD.BB84.FiniteKey.isClosed_preimage_goodPhaseRateSet Q δ dev).preimage
      ((DensityOp.continuous_reindex _).comp continuous_bellWembed)
  -- The general-`m` Rényi per-σ Bell labelled floor at the PHASE-ONLY pivot, at the deviation
  -- edge, at PURE accepting rate-good components.
  have hf_smoothFloor : ∀ φ ∈ G, φ ∈ Set.ofPred (fun φ' : DensityOp (Bool × Bool) => φ'.IsPure) →
      ENNReal.ofReal (bellRenyiFloor n m Q δ dev ε_AEP β) ≤
        smoothMinEntropy ε_AEP
          (CQState.coarsen (aliceKeyString peSel)
            (peLabelledPairedHaarPerSigmaFamily (m := m) Unit (unitRegisterEmbed n)
              (isChannel_unitRegisterEmbed n) peSel xSel Q δ (bellSource(φ))))
          (peLabelledPairedHaarPerSigmaFamily (m := m) Unit (unitRegisterEmbed n)
            (isChannel_unitRegisterEmbed n) peSel xSel Q δ (bellSource(φ))).quantumMarginal := by
    intro φ hφ hφpure
    have hfloor :=
      BellRenyi.le_smoothMinEntropy_component
        (m := m) peSel xSel hcount Q δ dev
        hbelow hmn
        ε_AEP hAEP β hβpos hβ1 φ hφ hφpure
    rw [CQState.quantumMarginal_coarsen] at hfloor
    exact hfloor
  -- The Bell de Finetti Haar measure is supported on the closed pure-state locus.
  have hPpure_closed : IsClosed (Set.ofPred (fun φ : DensityOp (Bool × Bool) => φ.IsPure)) := by
    have hcont : Continuous (fun φ : DensityOp (Bool × Bool) => φ.toOp) := continuous_induced_dom
    exact isClosed_eq (hcont.mul hcont) hcont
  have hPpure_ae : ∀ᵐ φ ∂(haarDensityMeasure (false, false)).measure,
      φ ∈ Set.ofPred (fun φ' : DensityOp (Bool × Bool) => φ'.IsPure) :=
    isProductStateMeasure_haarDensityMeasure (false, false)
  exact
    Mixture.le_smoothMinEntropy_coarsen_of_heavy_marginal
    (g := aliceKeyString peSel)
    (μ := haarDensityMeasure (false, false))
    (ρ := (bellEnVRhoEtilde Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
        peSel xSel Q δ).tensorLeftKernel
      (peLabelKernel (m := m) peSel))
    (f := fun φ : DensityOp (Bool × Bool) =>
      peLabelledPairedHaarPerSigmaFamily (m := m) Unit (unitRegisterEmbed n)
          (isChannel_unitRegisterEmbed n) peSel xSel Q δ (bellSource(φ)))
    (bellPeLabelledEnVRhoEtilde_eq_haar_integral_blocks (m := m) peSel xSel Q δ)
    (fun x => tensorLeftKernel_blocks_continuous
      (fun φ : DensityOp (Bool × Bool) =>
        pairedHaarPerSigmaFamily Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
            peSel xSel Q δ (bellSource(φ)))
      (peLabelKernel (m := m) peSel) x
      (continuous_bellPairedHaarPerSigmaFamily_blocks peSel xSel Q δ x))
    G hgoodClosed
    (P := Set.ofPred (fun φ : DensityOp (Bool × Bool) => φ.IsPure))
    hPpure_closed hPpure_ae
    (bellRenyiFloor n m Q δ dev ε_AEP β) ε_AEP
    E
    hAEP.le
    (by
      rw [hG]
      exact Bell.sum_re_trace_badBranch_le_of_tailBound
        (m := m) peSel xSel Q δ dev E hE0 hCap)
    (fun τ hτ hP _ => hf_smoothFloor τ hτ hP)

/-- The extended Bell mixture floor after the PE announcement, at
a free Rényi offset. The completed signed floor satisfies
`ENNReal.ofReal k ≤ smoothMinEntropy (ε_AEP + √(2E)) ρ σ` for some reference `σ`.
Reference: Nahar et al. 2024, Appendix B; Dupuis–Fawzi 2018, Corollary IV.2. -/
theorem
    BellRenyi.Window.exists_le_smoothMinEntropy_peState
    {n m : ℕ}
    (peSel xSel : Fin n → Bool) (hcount : KeyCount n m peSel)
    (Q δ : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (ε_AEP : ℝ) (hAEP : 0 < ε_AEP)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : WindowBellTailBound peSel xSel Q δ E) :
    ∃ σref : SubDensityOp
        (Signals (min n m) × (Unit × Signals n)),
      ENNReal.ofReal (bellRenyiWindowFloor n m Q δ ε_AEP β) ≤
        smoothMinEntropy
          (ε_AEP + Real.sqrt (2 * E))
          (CQState.coarsen (aliceKeyString peSel)
            ((bellEnVRhoEtilde Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
                peSel xSel Q δ).tensorLeftKernel
              (peLabelKernel (m := m) peSel))) σref := by
  -- The doubled-window form is the special case `dev = δ` of the free-deviation bound above.
  obtain ⟨σ0, hfloor⟩ :=
    BellRenyi.exists_le_smoothMinEntropy_peState
      (m := m) peSel xSel hcount Q δ δ
      (by rwa [show (Q:ℝ) + δ + δ = Q + 2 * δ from by ring]) ε_AEP hAEP β hβpos hβ1
      hE0
      (BellTailBound.of_windowBellTailBound hCap)
  exact ⟨σ0, by rwa [bellRenyiFloor_self] at hfloor⟩

/-- The extended Bell mixture floor after the PE announcement, at
the fixed Rényi optimizer. The completed signed floor satisfies
`ENNReal.ofReal k ≤ smoothMinEntropy (ε_AEP + √(2E)) ρ σ` for some reference `σ`.
Reference: Nahar et al. 2024, Appendix B; Dupuis–Fawzi 2018, Corollary IV.2. -/
theorem
    BellRenyi.ClampedOffset.exists_le_smoothMinEntropy_peState
    {n m : ℕ}
    (peSel xSel : Fin n → Bool) (hcount : KeyCount n m peSel)
    (Q δ : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (hmn : m < n)
    (ε_AEP : ℝ) (hAEP : 0 < ε_AEP)
    (hεS : ε_AEP < 1)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : WindowBellTailBound peSel xSel Q δ E) :
    ∃ σref : SubDensityOp
        (Signals (min n m) × (Unit × Signals n)),
      ENNReal.ofReal (bellRenyiClampedFloor n m Q δ ε_AEP) ≤
        smoothMinEntropy
          (ε_AEP + Real.sqrt (2 * E))
          (CQState.coarsen (aliceKeyString peSel)
            ((bellEnVRhoEtilde Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
                peSel xSel Q δ).tensorLeftKernel
              (peLabelKernel (m := m) peSel))) σref := by
  have hnK : NeZero (keyRounds n m) := neZero_keyRounds hmn
  refine BellRenyi.Window.exists_le_smoothMinEntropy_peState
    (m := m) peSel xSel hcount Q δ hbelow ε_AEP hAEP
    (clampedRenyiOffset binaryVarianceBound (keyRounds n m) ε_AEP) ?_ ?_
    hE0 hCap
  · exact clampedRenyiOffset_pos binaryVarianceBound binaryVarianceBound_pos
      (keyRounds n m) ε_AEP hAEP hεS
  · exact (clampedRenyiOffset_le_one_sixteenth binaryVarianceBound (keyRounds n m)
      ε_AEP).trans_lt (by norm_num)

/-- The extended Bell mixture floor after the syndrome and verification announcement, at
a free Rényi offset. The completed signed floor satisfies
`ENNReal.ofReal k ≤ smoothMinEntropy (ε_AEP + √(2E)) ρ σ` for some reference `σ`.
Reference: Nahar et al. 2024, Appendix B; Dupuis–Fawzi 2018, Corollary IV.2. -/
theorem
    BellRenyi.exists_le_smoothMinEntropy_announcedState
    {n m leakEC ℓEV : ℕ}
    (peSel xSel : Fin n → Bool) (hcount : KeyCount n m peSel)
    (ec : ECScheme n peSel leakEC)
    (Q δ dev : ℝ)
    (hbelow : Q + δ + dev ≤ 1 / 2)
    (ε_AEP : ℝ) (hAEP : 0 < ε_AEP)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : BellTailBound peSel xSel Q δ dev E) :
    ∃ σref : SubDensityOp
        ((Bits leakEC × (KeyHashSeed n ℓEV peSel × Bits ℓEV)) ×
          (Signals (min n m) × (Unit × Signals n))),
      ENNReal.ofReal (bellRenyiFloor n m Q δ dev ε_AEP β -
        ((leakEC : ℝ) + (ℓEV : ℝ))) ≤
        smoothMinEntropy
          (ε_AEP + Real.sqrt (2 * E))
          ((CQState.coarsen (aliceKeyString peSel)
            ((bellEnVRhoEtilde Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
                peSel xSel Q δ).tensorLeftKernel
              (peLabelKernel (m := m) peSel))).tensorLeftKernel
            (announceKernel ℓEV peSel ec)) σref := by
  -- The free-deviation per-σ PE-announcement bound is the witness.
  obtain ⟨σ0, hfloor⟩ :=
    BellRenyi.exists_le_smoothMinEntropy_peState
      (m := m) peSel xSel hcount Q δ dev hbelow ε_AEP hAEP β hβpos hβ1 hE0
      hCap
  refine ⟨(DensityOp.maxMixed (X := Bits leakEC ×
    (KeyHashSeed n ℓEV peSel × Bits ℓEV))).toSubDensityOp.kronecker σ0, ?_⟩
  have hann := smoothMinEntropy_le_announce_add_leak ℓEV peSel ec
    (ε_AEP + Real.sqrt (2 * E))
    (CQState.coarsen (aliceKeyString peSel)
      ((bellEnVRhoEtilde Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n) peSel xSel
          Q δ).tensorLeftKernel
        (peLabelKernel (m := m) peSel)))
    σ0
  rw [ENNReal.ofReal_sub _ (by positivity)]
  exact tsub_le_iff_right.mpr (hfloor.trans hann)

/-- The extended Bell mixture floor after the syndrome and verification announcement, at
a free Rényi offset. The completed signed floor satisfies
`ENNReal.ofReal k ≤ smoothMinEntropy (ε_AEP + √(2E)) ρ σ` for some reference `σ`.
Reference: Nahar et al. 2024, Appendix B; Dupuis–Fawzi 2018, Corollary IV.2. -/
theorem
    BellRenyi.Window.exists_le_smoothMinEntropy_announcedState
    {n m leakEC ℓEV : ℕ}
    (peSel xSel : Fin n → Bool) (hcount : KeyCount n m peSel)
    (ec : ECScheme n peSel leakEC)
    (Q δ : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (ε_AEP : ℝ) (hAEP : 0 < ε_AEP)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : WindowBellTailBound peSel xSel Q δ E) :
    ∃ σref : SubDensityOp
        ((Bits leakEC × (KeyHashSeed n ℓEV peSel × Bits ℓEV)) ×
          (Signals (min n m) × (Unit × Signals n))),
      ENNReal.ofReal (bellRenyiWindowFloor n m Q δ ε_AEP β -
        ((leakEC : ℝ) + (ℓEV : ℝ))) ≤
        smoothMinEntropy
          (ε_AEP + Real.sqrt (2 * E))
          ((CQState.coarsen (aliceKeyString peSel)
            ((bellEnVRhoEtilde Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
                peSel xSel Q δ).tensorLeftKernel
              (peLabelKernel (m := m) peSel))).tensorLeftKernel
            (announceKernel ℓEV peSel ec)) σref := by
  -- The doubled-window form is the special case `dev = δ` of the free-deviation bound above.
  obtain ⟨σ0, hfloor⟩ :=
    BellRenyi.exists_le_smoothMinEntropy_announcedState
      (m := m) (ℓEV := ℓEV) peSel xSel hcount ec Q δ δ
      (by rwa [show (Q:ℝ) + δ + δ = Q + 2 * δ from by ring]) ε_AEP hAEP β hβpos hβ1
      hE0
      (BellTailBound.of_windowBellTailBound hCap)
  exact ⟨σ0, by rwa [bellRenyiFloor_self] at hfloor⟩

/-- The extended Bell mixture floor after the syndrome and verification announcement, at
the fixed Rényi optimizer. The completed signed floor satisfies
`ENNReal.ofReal k ≤ smoothMinEntropy (ε_AEP + √(2E)) ρ σ` for some reference `σ`.
Reference: Nahar et al. 2024, Appendix B; Dupuis–Fawzi 2018, Corollary IV.2. -/
theorem
    BellRenyi.ClampedOffset.exists_le_smoothMinEntropy_announcedState
    {n m leakEC ℓEV : ℕ}
    (peSel xSel : Fin n → Bool) (hcount : KeyCount n m peSel)
    (ec : ECScheme n peSel leakEC)
    (Q δ : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (hmn : m < n)
    (ε_AEP : ℝ) (hAEP : 0 < ε_AEP)
    (hεS : ε_AEP < 1)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : WindowBellTailBound peSel xSel Q δ E) :
    ∃ σref : SubDensityOp
        ((Bits leakEC × (KeyHashSeed n ℓEV peSel × Bits ℓEV)) ×
          (Signals (min n m) × (Unit × Signals n))),
      ENNReal.ofReal (bellRenyiClampedFloor n m Q δ ε_AEP -
        ((leakEC : ℝ) + (ℓEV : ℝ))) ≤
        smoothMinEntropy
          (ε_AEP + Real.sqrt (2 * E))
          ((CQState.coarsen (aliceKeyString peSel)
            ((bellEnVRhoEtilde Unit (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n)
                peSel xSel Q δ).tensorLeftKernel
              (peLabelKernel (m := m) peSel))).tensorLeftKernel
            (announceKernel ℓEV peSel ec)) σref := by
  -- Specialize the free-offset bound at `β = clampedRenyiOffset …`.
  have hnK : NeZero (keyRounds n m) := neZero_keyRounds hmn
  refine BellRenyi.Window.exists_le_smoothMinEntropy_announcedState
    (m := m) peSel xSel hcount ec Q δ hbelow ε_AEP hAEP
    (clampedRenyiOffset binaryVarianceBound (keyRounds n m) ε_AEP) ?_ ?_
    hE0 hCap
  · exact clampedRenyiOffset_pos binaryVarianceBound binaryVarianceBound_pos
      (keyRounds n m) ε_AEP hAEP hεS
  · exact (clampedRenyiOffset_le_one_sixteenth binaryVarianceBound (keyRounds n m)
      ε_AEP).trans_lt (by norm_num)

end QKD.BB84.FiniteKey

end -- noncomputable section
