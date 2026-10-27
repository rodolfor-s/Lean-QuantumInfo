import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.QKD.BB84.ErrorCorrection
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.AEPLevels
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PELabelledPerSigmaFamily
import QCryptLean.QKD.BB84.FiniteKey.EntropyFloor.PELabelledPerSigmaFloor
import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.PhasePivot
import QCryptLean.QKD.BB84.FiniteKey.PerRound.DevetakWinter
import QCryptLean.QKD.BB84.Model.ErrorModel
import QCryptLean.QKD.BB84.Model.ProtocolPair
import QCryptLean.QKD.BB84.Model.UnitRegisterEmbed
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.SelectionData
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The component AEP floor at the phase-error good set

Each pure paired component is measured against its own quantum marginal. Its Alice-key entropy
is at least the phase-error Devetak–Winter rate over `n - m` rounds minus the bit-register IID
AEP penalty. The PE announcement and register transport preserve that reference without a
postselection logarithm. The extended floor also applies to light components, whose entropy
is infinite when the smoothing ball contains zero.

The window `δ` controls acceptance, and `dev` controls the soundness edge `Q + δ + dev ≤ 1/2`.

References: Renner 2005, `cor:Hmincondrepclass`; Nahar et al. 2024, arXiv:2403.11851,
Appendix B, `eq:boundingsmoothedmin` and `lemma:infsmoothedmin`.
-/

open Quantum.Operators Matrix Quantum.Channels QKD.BB84.Measurement
open InfoTheory.SmoothMinEntropy
open Quantum.DeFinetti
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open QKD.BB84.Model

noncomputable section

namespace QKD.BB84.FiniteKey

/-- The labelled Alice-key component floor against its own quantum marginal.
At the soundness edge `Q + δ + dev ≤ 1/2`, the floor is the phase-error entropy rate minus the
bit-register IID AEP penalty, cast by `ENNReal.ofReal` into the extended entropy.
The component must be pure. -/
theorem AEP.le_smoothMinEntropy_component
    {n m : ℕ}
    (peSel xSel : Fin n → Bool) (hcount : KeyCount n m peSel)
    (Q δ dev : ℝ) (hbound : Q + δ + dev ≤ 1 / 2) (hmn : m < n)
    (εTensor : ℝ) (hεTensor_pos : 0 < εTensor)
    (ψ : DensityOp (Signal × Signal))
    (hψ : DensityOp.partialTraceRight ψ ∈ goodPhaseRateSet Q (δ + dev))
    (hψPure : ψ.IsPure) :
    ENNReal.ofReal (pairedHaarFloorLevel n m Q δ dev εTensor) ≤
      smoothMinEntropy εTensor
        (CQState.coarsen (aliceKeyString peSel)
          (peLabelledPairedHaarPerSigmaFamily (m := m) Unit (unitRegisterEmbed n)
              (isChannel_unitRegisterEmbed n) peSel xSel Q δ ψ))
        (CQState.coarsen (aliceKeyString peSel)
          (peLabelledPairedHaarPerSigmaFamily (m := m) Unit (unitRegisterEmbed n)
            (isChannel_unitRegisterEmbed n) peSel xSel Q δ ψ)).quantumMarginal := by
  have hnK : NeZero (keyRounds n m) := neZero_keyRounds hmn
  -- (C1) good error bounds on the component `σ = Tr_B ψ`, at the deviation edge `Q + δ + dev`.
  -- Only the PHASE rate is read: the phase-error floor needs no bit-flip hypothesis.
  have hphase : phaseFlipErrorRate (DensityOp.partialTraceRight ψ) ≤ Q + δ + dev := by
    have h : phaseFlipErrorRate
        (componentAliceBobMarginal (DensityOp.partialTraceRight ψ)) ≤ Q + (δ + dev) := hψ
    rw [componentAliceBobMarginal_eq] at h
    linarith
  have hrate := QKD.BB84.FiniteKey.div_le_componentAliceZRate_of_phaseRate_le
    (DensityOp.partialTraceRight ψ) Q δ
    dev hbound hphase
  rw [componentAliceZRate] at hrate
  -- (C2) the `n_K`-fold smooth AEP lift and its penalty leaf, at `n_K = n − m`.
  have hAEP := le_smoothMinEntropy_tensorPower (DensityOp.partialTraceRight ψ)
    (keyRounds n m) εTensor hεTensor_pos
  have hnn : (0 : ℝ) ≤ (keyRounds n m : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hrate hnn
  -- (e) the key-round isometric invariance.
  have he := le_smoothMinEntropy_keyTensorPower
    (n := n) (m := m) εTensor ψ hψPure
  -- the labelled announce, free.
  have hA1 := smoothMinEntropy_tensorPower_le_peLabelled (m := m)
    peSel xSel Q δ εTensor ψ
  -- the labelled register transport.
  rw [smoothMinEntropy_coarsen_key_eq_sortedSplit
    peSel xSel hcount Q δ εTensor ψ]
  unfold pairedHaarFloorLevel
  have hid : (keyRounds n m : ℝ) / Real.log 2 *
        (Real.log 2 - Math.ClassicalEntropy.binaryEntropy (Q + δ + dev)) =
      (keyRounds n m : ℝ) *
        ((Real.log 2 - Math.ClassicalEntropy.binaryEntropy (Q + δ + dev)) / Real.log 2) := by ring
  rw [hid]
  exact (ENNReal.ofReal_le_ofReal (sub_le_sub_right hmul _)).trans
    (hAEP.trans (he.trans hA1))

/-- The labelled Alice-key component floor against its own quantum marginal.
At the soundness edge `Q + 2δ ≤ 1/2`, the floor is the phase-error entropy rate minus the
bit-register IID AEP penalty, cast by `ENNReal.ofReal` into the extended entropy.
The component must be pure. -/
theorem AEP.Window.le_smoothMinEntropy_component {n m : ℕ}
    (peSel xSel : Fin n → Bool) (hcount : KeyCount n m peSel)
    (Q δ : ℝ) (hbound : Q + 2 * δ ≤ 1 / 2) (hmn : m < n)
    (εTensor : ℝ) (hεTensor_pos : 0 < εTensor)
    (ψ : DensityOp (Signal × Signal))
    (hψ : DensityOp.partialTraceRight ψ ∈ goodPhaseRateSet Q (2 * δ))
    (hψPure : ψ.IsPure) :
    ENNReal.ofReal (pairedHaarWindowFloorLevel n m Q δ εTensor) ≤
      smoothMinEntropy εTensor
        (CQState.coarsen (aliceKeyString peSel)
          (peLabelledPairedHaarPerSigmaFamily (m := m) Unit (unitRegisterEmbed n)
              (isChannel_unitRegisterEmbed n) peSel xSel Q δ ψ))
        (CQState.coarsen (aliceKeyString peSel)
          (peLabelledPairedHaarPerSigmaFamily (m := m) Unit (unitRegisterEmbed n)
            (isChannel_unitRegisterEmbed n) peSel xSel Q δ ψ)).quantumMarginal := by
  -- the `2δ` floor is the free-deviation floor at `dev = δ`: the pivot widens to
  -- `goodPhaseRateSet Q (δ + δ)` (the same membership up to the edge associativity), the
  -- level reads back via `pairedHaarFloorLevel_self`, and `hbound` is `Q + 2 * δ ≤ 1/2`
  -- at `dev = δ`.
  have h := AEP.le_smoothMinEntropy_component
    peSel xSel hcount Q δ δ (by linarith) hmn εTensor hεTensor_pos ψ
    (by rw [show (2:ℝ) * δ = δ + δ from by ring] at hψ; exact hψ) hψPure
  rwa [pairedHaarFloorLevel_self] at h

end QKD.BB84.FiniteKey

end -- noncomputable section
