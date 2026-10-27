import QCryptLean.InfoTheory.Renyi.FiniteSizePenalty
import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelProjection
import QCryptLean.InfoTheory.SmoothMinEntropy.Penalty
import QCryptLean.InfoTheory.SmoothMinEntropy.RegisterExtension
import QCryptLean.InfoTheory.SmoothMinEntropy.Reindex
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.Math.Combinatorics.BellSymmetricDim
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.AnnounceConditioningCQ
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.BellPurifier
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.BellRenyi
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.ClassicalAnnounceKernel
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.Levels
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PELabelledPerSigmaFamily
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.BellInnerBudget
import QCryptLean.QKD.BB84.FiniteKey.InnerBudget.SiftedPassSupport
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.BellAcceptSplit
import QCryptLean.QKD.BB84.FiniteKey.PrivacyAmplification.AgreeAxisFloorTransfer
import QCryptLean.QKD.BB84.KeyHash
import QCryptLean.QKD.BB84.Model.SiftedMeasurement
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-!
# Bell Rényi leftover-hashing input floors

The symmetric purifier extension and structural register associations carry the
announced entropy floor to the leftover-hashing input reference.
-/

open Math.Combinatorics InfoTheory.Renyi
open Quantum.Operators Matrix Quantum.Channels
open InfoTheory.SmoothMinEntropy Quantum.Symmetry
open QKD.BB84.Model QKD.BB84.Measurement

noncomputable section

namespace QKD.BB84.FiniteKey

/-- The extended Bell leftover-hash input floor after the purifier
-- charge.
For `k = floor - 2 log₂ C(n+3,3) - (leakEC + ℓEV)`, there is a reference `σ` with
`ENNReal.ofReal k ≤ smoothMinEntropy (ε_AEP + √(2E)) ρ σ`.
Reference: Nahar et al. 2024, Appendix B, `eq:splittingoffV`. -/
theorem
    BellRenyi.exists_le_smoothMinEntropy_hashInput
    {n m ℓEV leakEC : ℕ}
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ dev ε_AEP : ℝ)
    (hbelow : Q + δ + dev ≤ 1 / 2)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    (hAEP : 0 < ε_AEP)
    (hcount : KeyCount n m peSel)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : BellTailBound peSel xSel Q δ dev E)
    (V : BellSymmetricPurifier n) :
    ∃ σref : SubDensityOp
        ((Bits leakEC × (KeyHashSeed n ℓEV peSel × Bits ℓEV)) ×
          (Signals (min n m) × (Unit × (Signals n × V.reg)))),
      ENNReal.ofReal (bellRenyiFloor n m Q δ dev ε_AEP β -
            2 * Real.log (bellSymmetricDim n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ))) ≤
        smoothMinEntropy
          (ε_AEP + Real.sqrt (2 * E))
          (peLabelledLHLInput (m := m) ℓEV Unit (unitRegisterEmbed n)
              (isChannel_unitRegisterEmbed n) peSel xSel ec Q δ
            (enVBellPurification V)) σref := by
  classical
  let : Nonempty V.reg := V.purifier.nonempty.map Prod.snd
  let Ann := Bits leakEC × (KeyHashSeed n ℓEV peSel × Bits ℓEV)
  let Lab := Signals (min n m)
  let Ref := Unit × Signals n
  let K := announceKernel ℓEV peSel ec
  let L := peLabelKernel (m := m) peSel
  let g := aliceKeyString peSel
  let ρE := bellEnVRhoEtilde Unit (unitRegisterEmbed n)
    (isChannel_unitRegisterEmbed n) peSel xSel Q δ
  let ρV := postMeasurementCQSiftedLocalPEPassFilter (Unit × (Signals n × V.reg))
    peSel xSel Q δ (siftedTauPostMeasurementNormalizedCQState Unit (unitRegisterEmbed n)
      (isChannel_unitRegisterEmbed n) peSel xSel (enVBellPurification V))
  let e0 := (Equiv.prodAssoc Unit (Signals n) V.reg).symm
  let ρVL := ((ρV.reindex e0).tensorLeftKernel L).reindex (Equiv.prodAssoc Lab Ref V.reg).symm
  let ρVC := ρVL.coarsen g
  let ρVA := (ρVC.tensorLeftKernel K).reindex (Equiv.prodAssoc Ann (Lab × Ref) V.reg).symm
  let ρA := ((ρE.tensorLeftKernel L).coarsen g).tensorLeftKernel K
  let e := ((Equiv.refl Ann).prodCongr
    (((Equiv.refl Lab).prodCongr e0).trans (Equiv.prodAssoc Lab Ref V.reg).symm)).trans
      (Equiv.prodAssoc Ann (Lab × Ref) V.reg).symm
  have hb (x : Signals n) : partialTraceRight ((ρV.reindex e0).stateMap x).toOp =
      (ρE.stateMap x).toOp :=
    enV_bellRhoEV_partialTraceRight_eq_forCoarsen Unit (unitRegisterEmbed n)
      (isChannel_unitRegisterEmbed n) peSel xSel Q δ V x
  have hl : ρVL.partialTraceRight = ρE.tensorLeftKernel L :=
    CQState.partialTraceRight_tensorLeftKernel _ _ _ hb
  have hc : ρVC.partialTraceRight = (ρE.tensorLeftKernel L).coarsen g := by
    rw [CQState.partialTraceRight_coarsen, hl]
  have ha : ρVA.partialTraceRight = ρA :=
    CQState.partialTraceRight_tensorLeftKernel _ _ _ (fun c =>
      congrArg (fun τ => (τ.stateMap c).toOp) hc)
  obtain ⟨σ, hf⟩ := BellRenyi.exists_le_smoothMinEntropy_announcedState
    (m := m) (ℓEV := ℓEV) peSel xSel hcount ec Q δ dev hbelow ε_AEP hAEP
    β hβpos hβ1 hE0 hCap
  change ENNReal.ofReal _ ≤ smoothMinEntropy _ ρA σ at hf
  have hext := smoothMinEntropy_le_extension_add ρVA σ (ε_AEP + Real.sqrt (2 * E))
  rw [ha] at hext
  have hmono : 2 * Real.logb 2 (Fintype.card V.reg : ℝ) ≤
      2 * Real.log (bellSymmetricDim n : ℝ) / Real.log 2 := by
    rw [Real.logb, ← mul_div_assoc]
    gcongr
    exact_mod_cast V.card_reg_le_bellSymmetricDim
  have hpen : 0 ≤ 2 * Real.log (bellSymmetricDim n : ℝ) / Real.log 2 := by
    apply div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg ?_))
      (Real.log_pos one_lt_two).le
    exact_mod_cast bellSymmetricDim_pos n
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
  · congr 1
    ring
  · rfl

/-- The extended Bell leftover-hash input floor after the purifier
-- charge.
For `k = floor - 2 log₂ C(n+3,3) - (leakEC + ℓEV)`, there is a reference `σ` with
`ENNReal.ofReal k ≤ smoothMinEntropy (ε_AEP + √(2E)) ρ σ`.
Reference: Nahar et al. 2024, Appendix B, `eq:splittingoffV`. -/
theorem
    BellRenyi.Window.exists_le_smoothMinEntropy_hashInput
    {n m ℓEV leakEC : ℕ}
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ ε_AEP : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    (hAEP : 0 < ε_AEP)
    (hcount : KeyCount n m peSel)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : WindowBellTailBound peSel xSel Q δ E)
    (V : BellSymmetricPurifier n) :
    ∃ σref : SubDensityOp
        ((Bits leakEC × (KeyHashSeed n ℓEV peSel × Bits ℓEV)) ×
          (Signals (min n m) × (Unit × (Signals n × V.reg)))),
      ENNReal.ofReal (bellRenyiWindowFloor n m Q δ ε_AEP β -
            2 * Real.log (bellSymmetricDim n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ))) ≤
        smoothMinEntropy
          (ε_AEP + Real.sqrt (2 * E))
          (peLabelledLHLInput (m := m) ℓEV Unit (unitRegisterEmbed n)
              (isChannel_unitRegisterEmbed n) peSel xSel ec Q δ
            (enVBellPurification V)) σref := by
  -- The doubled-window form is the special case `dev = δ` of the free-deviation host above.
  obtain ⟨σ0, hFloor⟩ :=
    BellRenyi.exists_le_smoothMinEntropy_hashInput
      (m := m) (ℓEV := ℓEV) peSel xSel ec Q δ δ ε_AEP
      (by rwa [show (Q:ℝ) + δ + δ = Q + 2 * δ from by ring]) β hβpos hβ1
      hAEP hcount hE0
      (BellTailBound.of_windowBellTailBound hCap) V
  exact ⟨σ0, by rwa [bellRenyiFloor_self] at hFloor⟩

/-- The extended Bell leftover-hash input floor after the purifier
-- charge.
For `k = floor - 2 log₂ C(n+3,3) - (leakEC + ℓEV)`, there is a reference `σ` with
`ENNReal.ofReal k ≤ smoothMinEntropy (ε_AEP + √(2E)) ρ σ`.
Reference: Nahar et al. 2024, Appendix B, `eq:splittingoffV`. -/
theorem
    BellRenyi.ClampedOffset.exists_le_smoothMinEntropy_hashInput
    {n m ℓEV leakEC : ℕ}
    (peSel xSel : Fin n → Bool) (ec : ECScheme n peSel leakEC)
    (Q δ ε_AEP : ℝ)
    (hbelow : Q + 2 * δ ≤ 1 / 2)
    (hmn : m < n)
    (hAEP : 0 < ε_AEP)
    (hεS : ε_AEP < 1)
    (hcount : KeyCount n m peSel)
    {E : ℝ} (hE0 : 0 ≤ E)
    (hCap : WindowBellTailBound peSel xSel Q δ E)
    (V : BellSymmetricPurifier n) :
    ∃ σref : SubDensityOp
        ((Bits leakEC × (KeyHashSeed n ℓEV peSel × Bits ℓEV)) ×
          (Signals (min n m) × (Unit × (Signals n × V.reg)))),
      ENNReal.ofReal (bellRenyiClampedFloor n m Q δ ε_AEP -
            2 * Real.log (bellSymmetricDim n : ℝ) / Real.log 2 - ((leakEC : ℝ) + (ℓEV : ℝ))) ≤
        smoothMinEntropy
          (ε_AEP + Real.sqrt (2 * E))
          (peLabelledLHLInput (m := m) ℓEV Unit (unitRegisterEmbed n)
              (isChannel_unitRegisterEmbed n) peSel xSel ec Q δ
            (enVBellPurification V)) σref := by
  -- Specialize the free-offset bound at `β = clampedRenyiOffset …`.
  have hnK : NeZero (keyRounds n m) := neZero_keyRounds hmn
  refine BellRenyi.Window.exists_le_smoothMinEntropy_hashInput
    (m := m) peSel xSel ec Q δ ε_AEP hbelow
    (clampedRenyiOffset binaryVarianceBound (keyRounds n m) ε_AEP) ?_ ?_
    hAEP hcount hE0 hCap V
  · exact clampedRenyiOffset_pos binaryVarianceBound binaryVarianceBound_pos
      (keyRounds n m) ε_AEP hAEP hεS
  · exact (clampedRenyiOffset_le_one_sixteenth binaryVarianceBound (keyRounds n m)
      ε_AEP).trans_lt (by norm_num)

end QKD.BB84.FiniteKey

end -- noncomputable section
