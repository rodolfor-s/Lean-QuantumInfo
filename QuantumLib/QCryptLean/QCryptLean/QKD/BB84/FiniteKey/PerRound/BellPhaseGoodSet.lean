import QCryptLean.QKD.BB84.FiniteKey.ParameterEstimation.PhasePivot
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Topology
import QCryptLean.Quantum.Symmetry.BellDoubling

/-
Copyright (c) 2026 Maor Ben-Shahar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # Bell-component phase-error good sets

The phase-error set is pulled back through Bell doubling, the componentwise
Boolean-to-bit identification, and the signal marginal. Closedness and
measurability follow from the common continuity API.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

open Quantum.Operators Quantum.Symmetry Quantum.DeFinetti

local notation "eSignal" => finTwoEquiv.symm.prodCongr finTwoEquiv.symm

/-- The Bell-component phase-error good set is closed at the protocol window. -/
lemma Bell.Window.isClosed_preimage_goodPhaseRateSet (Q δ : ℝ) :
    IsClosed ((fun φ : DensityOp (Bool × Bool) =>
      ((bellWembed φ).reindex ((eSignal).prodCongr eSignal)).partialTraceRight) ⁻¹'
        goodPhaseRateSet Q (2 * δ)) :=
  (QKD.BB84.FiniteKey.Window.isClosed_preimage_goodPhaseRateSet Q δ).preimage
    ((DensityOp.continuous_reindex _).comp continuous_bellWembed)

/-- The Bell-component phase-error good set is measurable at the protocol window. -/
lemma Bell.Window.measurableSet_preimage_goodPhaseRateSet (Q δ : ℝ) :
    MeasurableSet ((fun φ : DensityOp (Bool × Bool) =>
      ((bellWembed φ).reindex ((eSignal).prodCongr eSignal)).partialTraceRight) ⁻¹'
        goodPhaseRateSet Q (2 * δ)) :=
  (Bell.Window.isClosed_preimage_goodPhaseRateSet Q δ).measurableSet

/-- The Bell-component good set remains measurable at any free phase-error deviation. -/
lemma Bell.measurableSet_preimage_goodPhaseRateSet (Q δ dev : ℝ) :
    MeasurableSet ((fun φ : DensityOp (Bool × Bool) =>
      ((bellWembed φ).reindex ((eSignal).prodCongr eSignal)).partialTraceRight) ⁻¹'
        goodPhaseRateSet Q (δ + dev)) :=
  ((QKD.BB84.FiniteKey.isClosed_preimage_goodPhaseRateSet Q δ dev).preimage
    ((DensityOp.continuous_reindex _).comp continuous_bellWembed)).measurableSet

end QKD.BB84.FiniteKey
