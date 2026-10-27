import QCryptLean.Math.Probability.UnitaryHaar
import QCryptLean.Math.Probability.UnitaryHaarTransport
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Topology

/-! # Haar -/


noncomputable section

namespace Quantum.DeFinetti

open Matrix Quantum.Operators MeasureTheory

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A distribution supported almost everywhere on pure single-copy states. -/
def DensityMeasure.IsProductStateMeasure (μ : DensityMeasure X) : Prop :=
  ∀ᵐ ρ ∂μ.measure, ρ.IsPure

/-- A column of a unitary matrix is a normalized ket. -/
def unitaryColumn (x : X) (U : unitaryGroup X ℂ) : NormKet X where
  vec i := U.val i x
  normalized := by
    change (∑ j, star (U.val j x) * U.val j x) = 1
    have h := congrFun (congrFun (UnitaryGroup.star_mul_self U) x) x
    simpa only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] using h

/-- Haar unitaries act on a chosen computational basis state. -/
def pureStateMap (x : X) (U : unitaryGroup X ℂ) : DensityOp X :=
  (unitaryColumn x U).toDensityOp

/-- Every column projector of a unitary is pure. -/
theorem isPure_pureStateMap (x : X) (U : unitaryGroup X ℂ) :
    (pureStateMap x U).IsPure := (unitaryColumn x U).isPure_toDensityOp

/-- The pure-state map is continuous in the entrywise topology. -/
theorem continuous_pureStateMap (x : X) : Continuous (pureStateMap x) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun U : unitaryGroup X ℂ => U.val i x * star (U.val j x))
  have hi : Continuous (fun U : unitaryGroup X ℂ => U.val i x) :=
    (continuous_apply x).comp ((continuous_apply i).comp continuous_subtype_val)
  have hj : Continuous (fun U : unitaryGroup X ℂ => U.val j x) :=
    (continuous_apply x).comp ((continuous_apply j).comp continuous_subtype_val)
  exact hi.mul hj.star

/-- The probability Haar measure pushed forward to pure density operators. -/
def haarDensityMeasure (x : X) : DensityMeasure X where
  measure := Measure.map (pureStateMap x) (UnitaryGroup.haarProbUnitary X)
  isProbability := by
    let := UnitaryGroup.isProbabilityMeasure_haarProbUnitary X
    constructor
    rw [Measure.map_apply (continuous_pureStateMap x).measurable MeasurableSet.univ]
    simp

omit [DecidableEq X] in
/-- Purity is a closed, hence measurable, condition in the state topology. -/
theorem measurableSet_isPure : MeasurableSet {ρ : DensityOp X | ρ.IsPure} :=
  (isClosed_eq (DensityOp.continuous_toOp.mul DensityOp.continuous_toOp)
    DensityOp.continuous_toOp).measurableSet

/-- The Haar pushforward is supported on pure states. -/
theorem isProductStateMeasure_haarDensityMeasure (x : X) :
    (haarDensityMeasure x).IsProductStateMeasure := by
  apply (ae_map_iff (continuous_pureStateMap x).measurable.aemeasurable
    measurableSet_isPure).mpr
  exact ae_of_all _ (isPure_pureStateMap x)

end Quantum.DeFinetti
