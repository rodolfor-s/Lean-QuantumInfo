import QCryptLean.InfoTheory.Renyi.FiniteSizePenalty
import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.Levels
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PELabelledPerSigmaFamily
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PELabelledPerSigmaFloor
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.PhasePivot
import QCryptLean.QKD.BB84.FiniteKey.PerRound.BellPhaseGoodSet
import QCryptLean.QKD.BB84.FiniteKey.PerRound.DevetakWinter
import QCryptLean.QKD.BB84.FiniteKey.PerRound.RenyiPenalty
import QCryptLean.QKD.BB84.Model.ErrorModel
import QCryptLean.QKD.BB84.Model.ProtocolPair
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Symmetry.BellDoubling

/-! # Bell Renyi -/

/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/


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

/-- The Bell component floor at a free Rényi offset and phase-error deviation. -/
theorem
    BellRenyi.le_smoothMinEntropy_component
    {n m : ℕ}
    (peSel xSel : Fin n → Bool) (hcount : KeyCount n m peSel)
    (Q δ dev : ℝ) (hbound : Q + δ + dev ≤ 1 / 2) (hmn : m < n)
    (εTensor : ℝ) (hεTensor_pos : 0 < εTensor)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    (φ : DensityOp (Bool × Bool))
    (hφ : DensityOp.partialTraceRight (bellSource(φ)) ∈ goodPhaseRateSet Q (δ + dev))
    (hφPure : φ.IsPure) :
    ENNReal.ofReal (bellRenyiFloor n m Q δ dev εTensor β) ≤
      smoothMinEntropy εTensor
        (CQState.coarsen (aliceKeyString peSel)
          (peLabelledPairedHaarPerSigmaFamily (m := m) Unit (unitRegisterEmbed n)
              (isChannel_unitRegisterEmbed n) peSel xSel Q δ
            (bellSource(φ))))
        (CQState.coarsen (aliceKeyString peSel)
          (peLabelledPairedHaarPerSigmaFamily (m := m) Unit (unitRegisterEmbed n)
            (isChannel_unitRegisterEmbed n) peSel xSel Q δ (bellSource(φ)))).quantumMarginal := by
  have hnK : NeZero (keyRounds n m) := neZero_keyRounds hmn
  -- (C1) the good rate bound on the component `σ = Tr_B (Wembed φ)`, at the deviation edge.
  -- The phase-error membership IS the phase bound; membership carries `Q + (δ + dev)`.
  have hphase : phaseFlipErrorRate (DensityOp.partialTraceRight (bellSource(φ)))
      ≤ Q + δ + dev := by
    have h : phaseFlipErrorRate
        (componentAliceBobMarginal (DensityOp.partialTraceRight (bellSource(φ)))) ≤
        Q + (δ + dev) := hφ
    rw [componentAliceBobMarginal_eq] at h
    linarith
  have hrate := QKD.BB84.FiniteKey.div_le_componentAliceZRate_of_phaseRate_le
    (DensityOp.partialTraceRight (bellSource(φ))) Q δ dev hbound hphase
  rw [componentAliceZRate] at hrate
  -- (C2) the `n_K`-fold smooth AEP lift at the Cor IV.2 penalty at the FREE offset `β`,
  -- at `n_K = n − m`.  Deviation-blind: reads the component's rate, not the pivot.
  have hAEP := le_smoothMinEntropy_tensorPower_renyiPenalty
    (DensityOp.partialTraceRight (bellSource(φ))) (keyRounds n m) εTensor β hεTensor_pos
    hβpos hβ1
  have hnn : (0 : ℝ) ≤ (keyRounds n m : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hrate hnn
  -- (e) the key-round isometric invariance, at the general-`m` copy count.
  have he := le_smoothMinEntropy_keyTensorPower
    (n := n) (m := m) εTensor (bellSource(φ))
    ((bellWembed_isPure hφPure).reindex _)
  -- the labelled announce, free.
  have hA1 := smoothMinEntropy_tensorPower_le_peLabelled (m := m)
    peSel xSel Q δ εTensor (bellSource(φ))
  -- the labelled register transport.
  rw [smoothMinEntropy_coarsen_key_eq_sortedSplit
    peSel xSel hcount Q δ εTensor (bellSource(φ))]
  unfold bellRenyiFloor
  have hid : (keyRounds n m : ℝ) / Real.log 2 *
        (Real.log 2 - Math.ClassicalEntropy.binaryEntropy (Q + δ + dev)) =
      (keyRounds n m : ℝ) *
        ((Real.log 2 - Math.ClassicalEntropy.binaryEntropy (Q + δ + dev)) / Real.log 2) := by ring
  rw [hid]
  exact (ENNReal.ofReal_le_ofReal (sub_le_sub_right hmul _)).trans
    (hAEP.trans (he.trans hA1))

/-- The free-offset Bell component floor when deviation equals the protocol window. -/
theorem
    BellRenyi.Window.le_smoothMinEntropy_component
    {n m : ℕ}
    (peSel xSel : Fin n → Bool) (hcount : KeyCount n m peSel)
    (Q δ : ℝ) (hbound : Q + 2 * δ ≤ 1 / 2) (hmn : m < n)
    (εTensor : ℝ) (hεTensor_pos : 0 < εTensor)
    (β : ℝ) (hβpos : 0 < β) (hβ1 : β < 1)
    (φ : DensityOp (Bool × Bool))
    (hφ : DensityOp.partialTraceRight (bellSource(φ)) ∈ goodPhaseRateSet Q (2 * δ))
    (hφPure : φ.IsPure) :
    ENNReal.ofReal (bellRenyiWindowFloor n m Q δ εTensor β) ≤
      smoothMinEntropy εTensor
        (CQState.coarsen (aliceKeyString peSel)
          (peLabelledPairedHaarPerSigmaFamily (m := m) Unit (unitRegisterEmbed n)
              (isChannel_unitRegisterEmbed n) peSel xSel Q δ
            (bellSource(φ))))
        (CQState.coarsen (aliceKeyString peSel)
          (peLabelledPairedHaarPerSigmaFamily (m := m) Unit (unitRegisterEmbed n)
            (isChannel_unitRegisterEmbed n) peSel xSel Q δ (bellSource(φ)))).quantumMarginal := by
  -- the doubled-window floor is the free-deviation floor at `dev = δ`: the pivot widens to
  -- `goodPhaseRateSet Q (δ + δ)` (the same membership up to the edge associativity), the
  -- level reads back via `bellRenyiFloor_self`, and `hbound` is
  -- `Q + 2 * δ ≤ 1/2` at `dev = δ`.
  have h := BellRenyi.le_smoothMinEntropy_component
    peSel xSel hcount Q δ δ (by linarith) hmn εTensor hεTensor_pos β hβpos hβ1
    φ (by rw [show (2:ℝ) * δ = δ + δ from by ring] at hφ; exact hφ) hφPure
  rwa [bellRenyiFloor_self] at h

/-- The Bell component floor at the clamped Rényi offset, without a regime premise. -/
theorem
    BellRenyi.ClampedOffset.le_smoothMinEntropy_component
    {n m : ℕ}
    (peSel xSel : Fin n → Bool) (hcount : KeyCount n m peSel)
    (Q δ : ℝ) (hbound : Q + 2 * δ ≤ 1 / 2) (hmn : m < n)
    (εTensor : ℝ) (hεTensor_pos : 0 < εTensor) (hεTensor_lt_one : εTensor < 1)
    (φ : DensityOp (Bool × Bool))
    (hφ : DensityOp.partialTraceRight (bellSource(φ)) ∈ goodPhaseRateSet Q (2 * δ))
    (hφPure : φ.IsPure) :
    ENNReal.ofReal (bellRenyiClampedFloor n m Q δ εTensor) ≤
      smoothMinEntropy εTensor
        (CQState.coarsen (aliceKeyString peSel)
          (peLabelledPairedHaarPerSigmaFamily (m := m) Unit (unitRegisterEmbed n)
              (isChannel_unitRegisterEmbed n) peSel xSel Q δ
            (bellSource(φ))))
        (CQState.coarsen (aliceKeyString peSel)
          (peLabelledPairedHaarPerSigmaFamily (m := m) Unit (unitRegisterEmbed n)
            (isChannel_unitRegisterEmbed n) peSel xSel Q δ (bellSource(φ)))).quantumMarginal := by
  -- specialize the free-offset floor at `β = clampedRenyiOffset …`.
  have hnK : NeZero (keyRounds n m) := neZero_keyRounds hmn
  refine BellRenyi.Window.le_smoothMinEntropy_component
    peSel xSel hcount Q δ hbound hmn εTensor hεTensor_pos
    (clampedRenyiOffset binaryVarianceBound (keyRounds n m) εTensor) ?_ ?_
    φ hφ hφPure
  · exact clampedRenyiOffset_pos binaryVarianceBound binaryVarianceBound_pos
      (keyRounds n m) εTensor hεTensor_pos hεTensor_lt_one
  · exact (clampedRenyiOffset_le_one_sixteenth binaryVarianceBound (keyRounds n m)
      εTensor).trans_lt (by norm_num)

end QKD.BB84.FiniteKey

end -- noncomputable section
