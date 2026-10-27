import QCryptLean.Math.Analysis.CompactSpaceIntegrable
import QCryptLean.Math.LinearAlgebra.Matrix.EntryIntegral
import QCryptLean.Math.SpectralTheory.RpowContinuity
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.Integral
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Operators.Topology

/-!
# Mixtures of canonical IID purifications

Each tensor power is purified before integration. This generally produces a
mixed joint state. Scalar entrywise integration avoids a global matrix norm.
The square root uses the local Löwner order and the ordinary matrix topology.
-/

noncomputable section

namespace Quantum.DeFinetti

open Matrix Quantum.Operators MeasureTheory
open scoped ComplexOrder MatrixOrder

variable {X : Type*} [Fintype X]

/-- Canonical square-root purification varies continuously with the density operator. -/
theorem continuous_purification : Continuous (DensityOp.purification (X := X)) := by
  classical
  have hs : Continuous (fun ρ : DensityOp X => CFC.sqrt ρ.toOp) :=
    Math.SpectralTheory.continuousOn_sqrt_posSemidef.comp_continuous
      DensityOp.continuous_toOp (fun ρ => ρ.posSemidef)
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (((continuous_apply i.2).comp ((continuous_apply i.1).comp hs)).mul
    (((continuous_apply j.2).comp ((continuous_apply j.1).comp hs)).star))

/-- Entries of the canonical tensor-power purification are integrable on the compact state space. -/
theorem integrable_purificationTensorPow_entry (μ : DensityMeasure X) (k : ℕ)
    (i j : (Fin k → X) × (Fin k → X)) :
    Integrable (fun ρ : DensityOp X => (ρ.tensorPow k).purification.toOp i j) μ.measure := by
  have := μ.isProbability
  have ht : Continuous (fun ρ : DensityOp X => ρ.tensorPow k) := by
    apply continuous_induced_rng.mpr
    exact continuous_pi fun x => continuous_pi fun y => DensityOp.continuous_tensorPow_entry k x y
  exact ((continuous_apply j).comp ((continuous_apply i).comp
    (DensityOp.continuous_toOp.comp (continuous_purification.comp ht)))).integrable_of_compactSpace

/-- The joint mixture of the canonical purifications of IID components. -/
def purificationMixtureOp (k : ℕ) (μ : DensityMeasure X) :
    Op ((Fin k → X) × (Fin k → X)) :=
  Matrix.of fun i j => ∫ ρ, (ρ.tensorPow k).purification.toOp i j ∂μ.measure

/-- The purification mixture is positive, by scalar integration of quadratic forms. -/
theorem posSemidef_purificationMixtureOp (k : ℕ) (μ : DensityMeasure X) :
    (purificationMixtureOp k μ).PosSemidef :=
  Matrix.posSemidef_entryIntegral (fun ρ => (ρ.tensorPow k).purification.posSemidef)
    (integrable_purificationTensorPow_entry μ k)

/-- The purification mixture has trace one. -/
theorem trace_purificationMixtureOp (k : ℕ) (μ : DensityMeasure X) :
    (purificationMixtureOp k μ).trace = 1 := by
  have := μ.isProbability
  rw [purificationMixtureOp, Matrix.trace_entryIntegral
    (fun i => integrable_purificationTensorPow_entry μ k i i)]
  simp only [DensityOp.trace_one, integral_const, Measure.real, measure_univ,
    ENNReal.toReal_one, one_smul]

/-- The bundled mixture of canonical IID purifications. -/
def purificationMixture (k : ℕ) (μ : DensityMeasure X) :
    DensityOp ((Fin k → X) × (Fin k → X)) where
  toOp := purificationMixtureOp k μ
  posSemidef := posSemidef_purificationMixtureOp k μ
  trace_one := trace_purificationMixtureOp k μ

/-- Discarding the reference of the purification mixture recovers the original IID mixture. -/
theorem partialTraceRight_purificationMixture (k : ℕ) (μ : DensityMeasure X) :
    (purificationMixture k μ).partialTraceRight = integralTensorPowerDensity k μ := by
  apply DensityOp.ext
  ext i j
  change (∑ r, ∫ ρ, (ρ.tensorPow k).purification.toOp (i,r) (j,r) ∂μ.measure) = _
  rw [← integral_finsetSum _ (fun r _ => integrable_purificationTensorPow_entry μ k _ _)]
  change (∫ ρ, (ρ.tensorPow k).purification.partialTraceRight.toOp i j ∂μ.measure) = _
  simp only [DensityOp.partialTraceRight_purification]
  rfl

end Quantum.DeFinetti
