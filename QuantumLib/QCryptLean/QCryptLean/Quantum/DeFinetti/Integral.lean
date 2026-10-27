import QCryptLean.Math.Analysis.CompactSpaceIntegrable
import QCryptLean.Math.LinearAlgebra.Matrix.EntryIntegral
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Operators.Topology

/-! # Integral -/


noncomputable section

namespace Quantum.DeFinetti

open Quantum.Operators MeasureTheory
open scoped ComplexOrder

variable {X : Type*} [Fintype X]

/-- Tensor-power entries are integrable against every probability measure on states. -/
theorem integrable_tensorPow_entry (μ : DensityMeasure X) (k : ℕ) (x y : Fin k → X) :
    Integrable (fun ρ : DensityOp X => (ρ.tensorPow k).toOp x y) μ.measure := by
  have := μ.isProbability
  exact (DensityOp.continuous_tensorPow_entry k x y).integrable_of_compactSpace

/-- A mixture of tensor powers is positive. -/
theorem posSemidef_integralTensorPower (μ : DensityMeasure X) (k : ℕ) :
    (integralTensorPower k μ).PosSemidef :=
  Matrix.posSemidef_entryIntegral (fun ρ => (ρ.tensorPow k).posSemidef)
    (integrable_tensorPow_entry μ k)

/-- A probability mixture of tensor powers has trace one. -/
theorem trace_integralTensorPower (μ : DensityMeasure X) (k : ℕ) :
    (integralTensorPower k μ).trace = 1 := by
  have := μ.isProbability
  rw [integralTensorPower, Matrix.trace_entryIntegral (fun i => integrable_tensorPow_entry μ k i i)]
  simp only [DensityOp.trace_one, integral_const, Measure.real, measure_univ,
    ENNReal.toReal_one, one_smul]

/-- The normalized state associated with the intrinsic tensor-power mixture. -/
def integralTensorPowerDensity (k : ℕ) (μ : DensityMeasure X) : DensityOp (Fin k → X) where
  toOp := integralTensorPower k μ
  posSemidef := posSemidef_integralTensorPower μ k
  trace_one := trace_integralTensorPower μ k

end Quantum.DeFinetti
