import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelInterchange
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelProjection
import QCryptLean.InfoTheory.SmoothMinEntropy.Mixture
import QCryptLean.InfoTheory.SmoothMinEntropy.Normalized
import QCryptLean.InfoTheory.SmoothMinEntropy.RegisterExtension
import QCryptLean.InfoTheory.SmoothMinEntropy.Reindex
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.AEPLevels
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.AnnounceConditioningCQ
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.AnnouncePEFloorChainEnV
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.ClassicalAnnounceKernel
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PELabelledPerSigmaFamily
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PerSigmaFamily
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PhaseComponent
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PostMeasurementCQ
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.SiftedPassSupport
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.PhasePivot
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.SymmetricPurifier
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.Haar
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The AEP PE-labelled phase-error entropy floor

The good set is the phase-good preimage alone. Its complement has accepted mass at most `E`.
Each component is measured against its own marginal. Light components use zero-state smoothing
witnesses, so the mixture radius is `εTensor + √(2E)` without a light-component mass charge.
The mixture reference is its full quantum marginal.

The announcement costs `leakEC + ℓEV` bits. Adjoining the symmetric purifier costs
`2 * log₂ (ckrSymmetricDim n)`, where `ckrSymmetricDim n = C(n+15,15)`. The soundness edge is
`Q + δ + dev ≤ 1/2`; the doubled-window declarations specialize at `dev = δ`.

Reference: Nahar et al. 2024, arXiv:2403.11851, Appendix B, `eq:boundingsmoothedmin`,
`eq:splittingoffV`, `lemma:infsmoothedmin`.
-/

open QKD.BB84.FiniteKey

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

/-! ## 1. The phase-error accept-split interface -/

/-- The accepted mass outside `Tr_B⁻¹'(goodPhaseRateSet Q (2 * δ))` is at most `E`.
The PE-label register is included in the family, and no component-weight cut is imposed. -/
def WindowPhaseTailBound {n m : ℕ}
    (Env : Type*) [Fintype Env] [DecidableEq Env]
    (pre : Op (Signals n) →ₗ[ℂ] Op (Signals n × Env)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ E : ℝ) : Prop :=
    ∑ x : Signals n,
        ((Matrix.of fun i j : (Signals (min n m) × (Env × Signals n)) =>
            ∫ ψ in ((DensityOp.partialTraceRight :
                    DensityOp (Signal × Signal) → DensityOp Signal) ⁻¹'
                  (goodPhaseRateSet Q (2 * δ)))ᶜ,
              ((peLabelledPairedHaarPerSigmaFamily (m := m)
                Env pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
              ∂(haarDensityMeasure (((0, 0), (0, 0)) : Signal × Signal)).measure :
          Op (Signals (min n m) × (Env × Signals n))).trace).re ≤
      E

/-- The accepted mass outside `Tr_B⁻¹'(goodPhaseRateSet Q (δ + dev))` is at most `E`.
The PE-label register is included in the family, and no component-weight cut is imposed. -/
def PhaseTailBound {n m : ℕ}
    (Env : Type*) [Fintype Env] [DecidableEq Env]
    (pre : Op (Signals n) →ₗ[ℂ] Op (Signals n × Env)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ dev E : ℝ) : Prop :=
    ∑ x : Signals n,
        ((Matrix.of fun i j : (Signals (min n m) × (Env × Signals n)) =>
            ∫ ψ in ((DensityOp.partialTraceRight :
                    DensityOp (Signal × Signal) → DensityOp Signal) ⁻¹'
                  (goodPhaseRateSet Q (δ + dev)))ᶜ,
              ((peLabelledPairedHaarPerSigmaFamily (m := m)
                Env pre hpre peSel xSel Q δ ψ).stateMap x).toOp i j
              ∂(haarDensityMeasure (((0, 0), (0, 0)) : Signal × Signal)).measure :
          Op (Signals (min n m) × (Env × Signals n))).trace).re ≤
      E

/-- The `dev = δ` interface identity `WindowPhaseTailBound → PhaseTailBound`: at
`dev = δ` the two pivot radii agree after the `δ + δ = 2 * δ` rewrite (not defeq, as the
free-deviation
def's docstring records). -/
theorem PhaseTailBound.of_windowPhaseTailBound
    (n m : ℕ) (Env : Type*) [Fintype Env] [DecidableEq Env]
    (pre : Op (Signals n) →ₗ[ℂ] Op (Signals n × Env)) (hpre : IsChannel pre)
    (peSel xSel : Fin n → Bool) (Q δ E : ℝ)
    (h : WindowPhaseTailBound (m := m) Env pre hpre peSel xSel Q δ E) :
    PhaseTailBound
      (m := m) Env pre hpre peSel xSel Q δ δ E := by
  rw [PhaseTailBound,
    show (δ : ℝ) + δ = 2 * δ from by ring]
  exact h

/-! ## 2. The general-`m` floor chain at the phase-error good set

The mixture floor uses the closed phase-good set and the component floor
`AEP.le_smoothMinEntropy_component`.
The announcement and register-split theorems transport that floor. Positivity of the floor
implies `m < n`, ensuring that the key-round count is nonzero.
-/

/-- The extended labelled mixture floor `ofReal k ≤ smoothMinEntropy` against its marginal.
The phase-error bad mass is `E`, the smoothing radius is `ε + √(2E)`, and the soundness edge is
`Q + δ + dev ≤ 1/2`. Announcement costs `leakEC + ℓEV`; purifier adjunction costs `2 log₂ g`.
Reference: Nahar et al. 2024, arXiv:2403.11851, Appendix B. -/
theorem AEP.le_smoothMinEntropy_peState
    {n m : ℕ}
    (peSel xSel : Fin n → Bool) (hcount : KeyCount n m peSel)
    (Q δ dev : ℝ)
    (hbelowDev : Q + δ + dev ≤ 1 / 2)
    {E : ℝ}
    (hBad : PhaseTailBound (m := m) Unit (unitRegisterEmbed n)
        (isChannel_unitRegisterEmbed n) peSel xSel Q δ dev E)
    (εTensor : ℝ) (hεTensor_pos : 0 < εTensor) :
    ENNReal.ofReal (pairedHaarFloorLevel n m Q δ dev εTensor) ≤
      smoothMinEntropy
          (εTensor + Real.sqrt (2 * E))
        (CQState.coarsen (aliceKeyString peSel)
          (peLabelledEnVRhoEtilde (m := m) Unit (unitRegisterEmbed n)
              (isChannel_unitRegisterEmbed n) peSel xSel Q δ))
        (peLabelledEnVRhoEtilde (m := m) Unit (unitRegisterEmbed n)
          (isChannel_unitRegisterEmbed n) peSel xSel Q δ).quantumMarginal := by
  by_cases hLevelPos : 0 < pairedHaarFloorLevel n m Q δ dev εTensor
  swap
  · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hLevelPos)]
    exact bot_le
  have hmn := lt_of_pairedHaarFloorLevel_pos hLevelPos
  set G : Set (DensityOp (Signal × Signal)) :=
    (DensityOp.partialTraceRight :
      DensityOp (Signal × Signal) → DensityOp Signal) ⁻¹'
        goodPhaseRateSet Q (δ + dev) with hG
  have hgoodClosed : IsClosed G := QKD.BB84.FiniteKey.isClosed_preimage_goodPhaseRateSet Q δ dev
  -- The general-`m` labelled per-σ floor at the deviation, at PURE accepting rate-good `τ`.
  have hf_smoothFloor : ∀ τ ∈ G, τ.IsPure →
      ENNReal.ofReal (pairedHaarFloorLevel n m Q δ dev εTensor) ≤
        smoothMinEntropy εTensor
          (CQState.coarsen (aliceKeyString peSel)
            (peLabelledPairedHaarPerSigmaFamily (m := m) Unit (unitRegisterEmbed n)
              (isChannel_unitRegisterEmbed n) peSel xSel Q δ τ))
          (peLabelledPairedHaarPerSigmaFamily (m := m) Unit (unitRegisterEmbed n)
            (isChannel_unitRegisterEmbed n) peSel xSel Q δ τ).quantumMarginal := by
    intro τ hτ hτpure
    have hfloor :=
      AEP.le_smoothMinEntropy_component
        (m := m) peSel xSel hcount Q δ dev hbelowDev hmn εTensor
        hεTensor_pos τ hτ hτpure
    classical
    rw [CQState.quantumMarginal_coarsen] at hfloor
    exact hfloor
  -- The de Finetti Haar measure is supported on the closed pure-state locus.
  have hPpure_closed : IsClosed
      (Set.ofPred (fun σ : DensityOp (Signal × Signal) => σ.IsPure)) := by
    have hcont : Continuous (fun σ : DensityOp (Signal × Signal) => σ.toOp) :=
      continuous_induced_dom
    exact isClosed_eq (hcont.mul hcont) hcont
  have hPpure_ae :
      ∀ᵐ τ ∂(haarDensityMeasure (((0, 0), (0, 0)) : Signal × Signal)).measure,
        τ ∈ Set.ofPred (fun σ : DensityOp (Signal × Signal) => σ.IsPure) :=
    isProductStateMeasure_haarDensityMeasure (((0, 0), (0, 0)) : Signal × Signal)
  exact
    Mixture.le_smoothMinEntropy_coarsen_of_heavy_marginal
    (g := aliceKeyString peSel)
    (μ := haarDensityMeasure (((0, 0), (0, 0)) : Signal × Signal))
    (ρ := peLabelledEnVRhoEtilde (m := m) Unit (unitRegisterEmbed n)
        (isChannel_unitRegisterEmbed n) peSel xSel Q δ)
    (f := peLabelledPairedHaarPerSigmaFamily (m := m) Unit (unitRegisterEmbed n)
        (isChannel_unitRegisterEmbed n) peSel xSel Q δ)
    (peLabelledRhoEtilde_eq_haar_integral_blocks (m := m) Unit (unitRegisterEmbed n)
        (isChannel_unitRegisterEmbed n) peSel xSel Q δ)
    (continuous_peLabelledPairedHaarPerSigmaFamily_blocks (m := m) Unit (unitRegisterEmbed n)
        (isChannel_unitRegisterEmbed n) peSel xSel Q δ)
    G hgoodClosed
    (P := Set.ofPred (fun σ : DensityOp (Signal × Signal) => σ.IsPure))
    hPpure_closed hPpure_ae
    (pairedHaarFloorLevel n m Q δ dev εTensor) εTensor
    E
    hεTensor_pos.le
    hBad
    (fun τ hτ hP _ => hf_smoothFloor τ hτ hP)

/-- The extended labelled mixture floor after charging the syndrome and verification tag.
The phase-error bad mass is `E`, the smoothing radius is `ε + √(2E)`, and the soundness edge is
`Q + δ + dev ≤ 1/2`. Announcement costs `leakEC + ℓEV`; purifier adjunction costs `2 log₂ g`.
Reference: Nahar et al. 2024, arXiv:2403.11851, Appendix B. -/
theorem AEP.le_smoothMinEntropy_announcedState
    {n m leakEC ℓEV : ℕ}
    (peSel xSel : Fin n → Bool) (hcount : KeyCount n m peSel)
    (ec : ECScheme n peSel leakEC)
    (Q δ dev : ℝ)
    (hbelowDev : Q + δ + dev ≤ 1 / 2)
    {E : ℝ}
    (hBad : PhaseTailBound (m := m) Unit (unitRegisterEmbed n)
        (isChannel_unitRegisterEmbed n) peSel xSel Q δ dev E)
    (εTensor : ℝ) (hεTensor_pos : 0 < εTensor) :
    ENNReal.ofReal (pairedHaarFloorLevel n m Q δ dev εTensor - ((leakEC : ℝ) + (ℓEV : ℝ))) ≤
      smoothMinEntropy
          (εTensor + Real.sqrt (2 * E))
        (CQState.coarsen (aliceKeyString peSel)
          ((peLabelledEnVRhoEtilde (m := m) Unit (unitRegisterEmbed n)
              (isChannel_unitRegisterEmbed n) peSel xSel Q δ).tensorLeftKernel
            (fun ω => announceKernel ℓEV peSel ec (aliceKeyString peSel ω))))
        ((DensityOp.maxMixed (X := Bits leakEC ×
          (KeyHashSeed n ℓEV peSel × Bits ℓEV))).toSubDensityOp.kronecker
            (peLabelledEnVRhoEtilde (m := m) Unit (unitRegisterEmbed n)
              (isChannel_unitRegisterEmbed n) peSel xSel Q δ).quantumMarginal) := by
  have hslide := CQState.coarsen_tensorLeftKernel_factor
    (peLabelledEnVRhoEtilde (m := m) Unit (unitRegisterEmbed n)
      (isChannel_unitRegisterEmbed n) peSel xSel Q δ)
    (aliceKeyString peSel) (announceKernel ℓEV peSel ec)
  simp only [Function.comp_def] at hslide
  rw [hslide]
  -- The labelled mixture floor at the deviation (free-deviation bound), charged with the
  -- announcement.
  have hfloor := AEP.le_smoothMinEntropy_peState
      (m := m)
    peSel xSel hcount Q δ dev hbelowDev hBad εTensor hεTensor_pos
  have hann := smoothMinEntropy_le_announce_add_leak ℓEV peSel ec
    (εTensor + Real.sqrt (2 * E))
    (CQState.coarsen (aliceKeyString peSel)
      (peLabelledEnVRhoEtilde (m := m) Unit (unitRegisterEmbed n)
          (isChannel_unitRegisterEmbed n) peSel xSel Q δ))
    (peLabelledEnVRhoEtilde (m := m) Unit (unitRegisterEmbed n)
          (isChannel_unitRegisterEmbed n) peSel xSel Q δ).quantumMarginal
  rw [ENNReal.ofReal_sub _ (by positivity)]
  exact tsub_le_iff_right.mpr (hfloor.trans hann)

/-! ## 3. Adjoining the de Finetti purifier `V` -/

/-- The extended announced labelled floor after adjoining the symmetric purifier.
The phase-error bad mass is `E`, the smoothing radius is `ε + √(2E)`, and the soundness edge is
`Q + δ + dev ≤ 1/2`. Announcement costs `leakEC + ℓEV`; purifier adjunction costs `2 log₂ g`.
Reference: Nahar et al. 2024, arXiv:2403.11851, Appendix B. -/
theorem AEP.exists_le_smoothMinEntropy_reference
    {n m leakEC ℓEV : ℕ}
    (peSel xSel : Fin n → Bool) (hcount : KeyCount n m peSel)
    (ec : ECScheme n peSel leakEC)
    (Q δ dev : ℝ)
    (hbelow : Q + δ + dev ≤ 1 / 2)
    {E : ℝ}
    (hBad : PhaseTailBound (m := m) Unit (unitRegisterEmbed n)
        (isChannel_unitRegisterEmbed n) peSel xSel Q δ dev E)
    (V : SymmetricPurifier n)
    (ε_AEP : ℝ) (hAEP : 0 < ε_AEP) :
    ∃ σref : SubDensityOp
        ((Bits leakEC × (KeyHashSeed n ℓEV peSel × Bits ℓEV)) ×
          (Signals (min n m) × (Unit × (Signals n × V.reg)))),
      ENNReal.ofReal (pairedHaarFloorLevel n m Q δ dev ε_AEP -
        2 * Real.log (ckrSymmetricDim n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ))) ≤
        smoothMinEntropy
          (ε_AEP + Real.sqrt (2 * E))
          ((aliceKeyAnnounceCQ peSel (fun ω => (partEquiv (m := m) peSel ω).2)
              (postMeasurementCQSiftedLocalPEPassFilter (Unit × (Signals n × V.reg)) peSel xSel Q δ
                (siftedTauPostMeasurementNormalizedCQState Unit (unitRegisterEmbed n)
                    (isChannel_unitRegisterEmbed n) peSel xSel
                  (enVCKRPurification V)).toCQState)).tensorLeftKernel
            (announceKernel ℓEV peSel ec)) σref := by
  classical
  let : Nonempty V.reg := V.purifier.nonempty.map Prod.snd
  let Ann := Bits leakEC × (KeyHashSeed n ℓEV peSel × Bits ℓEV)
  let Lab := Signals (min n m)
  let Ref := Unit × Signals n
  let K := announceKernel ℓEV peSel ec
  let L := peLabelKernel (m := m) peSel
  let g := aliceKeyString peSel
  let ρE := enVRhoEtilde Unit (unitRegisterEmbed n)
    (isChannel_unitRegisterEmbed n) peSel xSel Q δ
  let ρV := postMeasurementCQSiftedLocalPEPassFilter (Unit × (Signals n × V.reg))
    peSel xSel Q δ (siftedTauPostMeasurementNormalizedCQState Unit (unitRegisterEmbed n)
      (isChannel_unitRegisterEmbed n) peSel xSel (enVCKRPurification V))
  let e0 := (Equiv.prodAssoc Unit (Signals n) V.reg).symm
  let ρVL := ((ρV.reindex e0).tensorLeftKernel L).reindex (Equiv.prodAssoc Lab Ref V.reg).symm
  let ρVC := ρVL.coarsen g
  let ρVA := (ρVC.tensorLeftKernel K).reindex (Equiv.prodAssoc Ann (Lab × Ref) V.reg).symm
  let ρA := ((ρE.tensorLeftKernel L).coarsen g).tensorLeftKernel K
  let σ := (DensityOp.maxMixed (X := Ann)).toSubDensityOp.kronecker
    (ρE.tensorLeftKernel L).quantumMarginal
  let e := ((Equiv.refl Ann).prodCongr
    (((Equiv.refl Lab).prodCongr e0).trans (Equiv.prodAssoc Lab Ref V.reg).symm)).trans
      (Equiv.prodAssoc Ann (Lab × Ref) V.reg).symm
  have hb (x : Signals n) : partialTraceRight ((ρV.reindex e0).stateMap x).toOp =
      (ρE.stateMap x).toOp :=
    enV_rhoEV_partialTraceRight_eq_forCoarsen Unit (unitRegisterEmbed n)
      (isChannel_unitRegisterEmbed n) peSel xSel Q δ V x
  have hl : ρVL.partialTraceRight = ρE.tensorLeftKernel L :=
    CQState.partialTraceRight_tensorLeftKernel _ _ _ hb
  have hc : ρVC.partialTraceRight = (ρE.tensorLeftKernel L).coarsen g := by
    rw [CQState.partialTraceRight_coarsen, hl]
  have ha : ρVA.partialTraceRight = ρA :=
    CQState.partialTraceRight_tensorLeftKernel _ _ _ (fun c =>
      congrArg (fun τ => (τ.stateMap c).toOp) hc)
  have hf : ENNReal.ofReal (pairedHaarFloorLevel n m Q δ dev ε_AEP -
      ((leakEC : ℝ) + (ℓEV : ℝ))) ≤
      smoothMinEntropy (ε_AEP + Real.sqrt (2 * E)) ρA σ := by
    have h := AEP.le_smoothMinEntropy_announcedState (ℓEV := ℓEV)
      peSel xSel hcount ec Q δ dev hbelow hBad ε_AEP hAEP
    have hs := CQState.coarsen_tensorLeftKernel_factor
      (peLabelledEnVRhoEtilde (m := m) Unit (unitRegisterEmbed n)
        (isChannel_unitRegisterEmbed n) peSel xSel Q δ)
      (aliceKeyString peSel) (announceKernel ℓEV peSel ec)
    simp only [Function.comp_def] at hs
    rw [hs] at h
    exact h
  have hext := smoothMinEntropy_le_extension_add ρVA σ (ε_AEP + Real.sqrt (2 * E))
  rw [ha] at hext
  have hmono : 2 * Real.logb 2 (Fintype.card V.reg : ℝ) ≤
      2 * Real.log (ckrSymmetricDim n : ℝ) / Real.log 2 := by
    rw [Real.logb, ← mul_div_assoc]
    gcongr
    exact_mod_cast V.card_reg_le_ckrSymmetricDim
  have hpen : 0 ≤ 2 * Real.log (ckrSymmetricDim n : ℝ) / Real.log 2 := by
    apply div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg ?_))
      (Real.log_pos one_lt_two).le
    exact_mod_cast ckrSymmetricDim_pos n
  have hh := tsub_le_iff_right.mpr
    (hf.trans (hext.trans (add_le_add (le_refl _) (ENNReal.ofReal_le_ofReal hmono))))
  rw [← ENNReal.ofReal_sub _ hpen] at hh
  let σV := σ.kronecker (DensityOp.maxMixed (X := V.reg)).toSubDensityOp
  refine ⟨σV.reindex e.symm, ?_⟩
  have he : ρVA =
      (((aliceKeyAnnounceCQ peSel (fun ω => (partEquiv (m := m) peSel ω).2) ρV).tensorLeftKernel
        K).reindex e) := by
    apply CQState.ext
    funext c
    apply SubDensityOp.ext
    ext i j
    simp only [ρVA, ρVC, ρVL, aliceKeyAnnounceCQ, announceCoarsenCQ, CQState.coarsen,
      CQState.ofBlocks, CQState.reindex, CQState.tensorLeftKernel, SubDensityOp.reindex,
      SubDensityOp.kronecker, Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.kroneckerMap_apply, Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply]
    rfl
  rw [he] at hh
  have hs : σV = (σV.reindex e.symm).reindex e := by
    apply SubDensityOp.ext
    ext i j
    simp [SubDensityOp.reindex]
  change ENNReal.ofReal _ ≤ smoothMinEntropy _ _ σV at hh
  rw [hs, smoothMinEntropy_reindex] at hh
  convert hh using 1
  congr 1
  ring

/-! ## 4. The `2δ` specializations

Each `2δ` theorem specializes the free-deviation theorem at `dev = δ`: the accept-split
marker converts through the interface identity `PhaseTailBound.of_windowPhaseTailBound`, the
threshold hypothesis through `Q + δ + δ = Q + 2 * δ`, and the carried level reads back through
`pairedHaarFloorLevel_self`. -/

/-- The extended labelled mixture floor `ofReal k ≤ smoothMinEntropy` against its marginal.
The phase-error bad mass is `E`, the smoothing radius is `ε + √(2E)`, and the soundness edge is
`Q + 2δ ≤ 1/2`. Announcement costs `leakEC + ℓEV`; purifier adjunction costs `2 log₂ g`.
Reference: Nahar et al. 2024, arXiv:2403.11851, Appendix B. -/
theorem AEP.Window.le_smoothMinEntropy_peState
    {n m : ℕ}
    (peSel xSel : Fin n → Bool) (hcount : KeyCount n m peSel)
    (Q δ : ℝ)
    (hbelow2 : Q + 2 * δ ≤ 1 / 2)
    {E : ℝ}
    (hBad : WindowPhaseTailBound (m := m) Unit (unitRegisterEmbed n)
        (isChannel_unitRegisterEmbed n) peSel xSel Q δ E)
    (εTensor : ℝ) (hεTensor_pos : 0 < εTensor) :
    ENNReal.ofReal (pairedHaarWindowFloorLevel n m Q δ εTensor) ≤
      smoothMinEntropy
          (εTensor + Real.sqrt (2 * E))
        (CQState.coarsen (aliceKeyString peSel)
          (peLabelledEnVRhoEtilde (m := m) Unit (unitRegisterEmbed n)
              (isChannel_unitRegisterEmbed n) peSel xSel Q δ))
        (peLabelledEnVRhoEtilde (m := m) Unit (unitRegisterEmbed n)
          (isChannel_unitRegisterEmbed n) peSel xSel Q δ).quantumMarginal := by
  -- Specialize at `dev = δ` and convert the bad-branch bound through the interface
  -- identity, and the carried level reads back through `pairedHaarFloorLevel_self`.
  have h := AEP.le_smoothMinEntropy_peState
      (m := m)
    peSel xSel hcount Q δ δ
    (by rwa [show (Q : ℝ) + δ + δ = Q + 2 * δ from by ring])
    (PhaseTailBound.of_windowPhaseTailBound n m Unit
      (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n) peSel xSel Q δ E hBad)
    εTensor hεTensor_pos
  rwa [pairedHaarFloorLevel_self] at h

/-! The announcement specialization. -/

/-- The extended labelled mixture floor after charging the syndrome and verification tag.
The phase-error bad mass is `E`, the smoothing radius is `ε + √(2E)`, and the soundness edge is
`Q + 2δ ≤ 1/2`. Announcement costs `leakEC + ℓEV`; purifier adjunction costs `2 log₂ g`.
Reference: Nahar et al. 2024, arXiv:2403.11851, Appendix B. -/
theorem AEP.Window.le_smoothMinEntropy_announcedState
    {n m leakEC ℓEV : ℕ}
    (peSel xSel : Fin n → Bool) (hcount : KeyCount n m peSel)
    (ec : ECScheme n peSel leakEC)
    (Q δ : ℝ)
    (hbelow2 : Q + 2 * δ ≤ 1 / 2)
    {E : ℝ}
    (hBad : WindowPhaseTailBound (m := m) Unit (unitRegisterEmbed n)
        (isChannel_unitRegisterEmbed n) peSel xSel Q δ E)
    (εTensor : ℝ) (hεTensor_pos : 0 < εTensor) :
    ENNReal.ofReal (pairedHaarWindowFloorLevel n m Q δ εTensor - ((leakEC : ℝ) + (ℓEV : ℝ))) ≤
      smoothMinEntropy
          (εTensor + Real.sqrt (2 * E))
        (CQState.coarsen (aliceKeyString peSel)
          ((peLabelledEnVRhoEtilde (m := m) Unit (unitRegisterEmbed n)
              (isChannel_unitRegisterEmbed n) peSel xSel Q δ).tensorLeftKernel
            (fun ω => announceKernel ℓEV peSel ec (aliceKeyString peSel ω))))
        ((DensityOp.maxMixed (X := Bits leakEC ×
          (KeyHashSeed n ℓEV peSel × Bits ℓEV))).toSubDensityOp.kronecker
            (peLabelledEnVRhoEtilde (m := m) Unit (unitRegisterEmbed n)
              (isChannel_unitRegisterEmbed n) peSel xSel Q δ).quantumMarginal) := by
  -- Specialize at `dev = δ` and convert the bad-branch bound through the interface
  -- identity, and the carried level reads back through `pairedHaarFloorLevel_self`.
  have h := AEP.le_smoothMinEntropy_announcedState
      (m := m) (ℓEV := ℓEV)
    peSel xSel hcount ec Q δ δ
    (by rwa [show (Q : ℝ) + δ + δ = Q + 2 * δ from by ring])
    (PhaseTailBound.of_windowPhaseTailBound n m Unit
      (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n) peSel xSel Q δ E hBad)
    εTensor hεTensor_pos
  rwa [pairedHaarFloorLevel_self] at h

/-! The register-split specialization. -/

/-- The extended announced labelled floor after adjoining the symmetric purifier.
The phase-error bad mass is `E`, the smoothing radius is `ε + √(2E)`, and the soundness edge is
`Q + 2δ ≤ 1/2`. Announcement costs `leakEC + ℓEV`; purifier adjunction costs `2 log₂ g`.
Reference: Nahar et al. 2024, arXiv:2403.11851, Appendix B. -/
theorem AEP.Window.exists_le_smoothMinEntropy_reference
    {n m leakEC ℓEV : ℕ}
    (peSel xSel : Fin n → Bool) (hcount : KeyCount n m peSel)
    (ec : ECScheme n peSel leakEC)
    (Q δ : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    {E : ℝ}
    (hBad : WindowPhaseTailBound (m := m) Unit (unitRegisterEmbed n)
        (isChannel_unitRegisterEmbed n) peSel xSel Q δ E)
    (V : SymmetricPurifier n)
    (ε_AEP : ℝ) (hAEP : 0 < ε_AEP) :
    ∃ σref : SubDensityOp
        ((Bits leakEC × (KeyHashSeed n ℓEV peSel × Bits ℓEV)) ×
          (Signals (min n m) × (Unit × (Signals n × V.reg)))),
      ENNReal.ofReal (pairedHaarWindowFloorLevel n m Q δ ε_AEP -
        2 * Real.log (ckrSymmetricDim n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ))) ≤
        smoothMinEntropy
          (ε_AEP + Real.sqrt (2 * E))
          ((aliceKeyAnnounceCQ peSel (fun ω => (partEquiv (m := m) peSel ω).2)
              (postMeasurementCQSiftedLocalPEPassFilter (Unit × (Signals n × V.reg)) peSel xSel Q δ
                (siftedTauPostMeasurementNormalizedCQState Unit (unitRegisterEmbed n)
                    (isChannel_unitRegisterEmbed n) peSel xSel
                  (enVCKRPurification V)).toCQState)).tensorLeftKernel
            (announceKernel ℓEV peSel ec)) σref := by
  -- Specialize at `dev = δ` and convert the bad-branch bound through the interface
  -- identity, and the carried level reads back through `pairedHaarFloorLevel_self`.
  have h := AEP.exists_le_smoothMinEntropy_reference
      (m := m) (ℓEV := ℓEV)
    peSel xSel hcount ec Q δ δ
    (by rwa [show (Q : ℝ) + δ + δ = Q + 2 * δ from by ring])
    (PhaseTailBound.of_windowPhaseTailBound n m Unit
      (unitRegisterEmbed n) (isChannel_unitRegisterEmbed n) peSel xSel Q δ E hBad)
    V ε_AEP hAEP
  rw [pairedHaarFloorLevel_self] at h
  exact h

end QKD.BB84.FiniteKey

end -- noncomputable section
