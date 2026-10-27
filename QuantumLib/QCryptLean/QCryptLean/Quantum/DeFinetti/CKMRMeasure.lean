import QCryptLean.Math.Analysis.CompactSpaceIntegrable
import QCryptLean.Math.LinearAlgebra.Matrix.EntryIntegral
import QCryptLean.Math.LinearAlgebra.Matrix.PositiveTrace
import QCryptLean.Math.Probability.UnitaryHaar
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.CKMRCoherent
import QCryptLean.Quantum.DeFinetti.Haar
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Operators.Topology
import QCryptLean.Quantum.Symmetry.Basic

/-! # The coherent-state probability measure of a symmetric input -/
noncomputable section
namespace Quantum.DeFinetti
open Matrix Quantum.Operators Quantum.Symmetry MeasureTheory
open scoped ComplexOrder
variable {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}

/-- Density of the coherent POVM outcome relative to probability Haar measure. -/
def coherentWeight (x : X) (ρ : DensityOp (Fin n → X)) (U : unitaryGroup X ℂ) : ℝ :=
  (symmetricProjector X n).trace.re * (((pureStateMap x U).tensorPow n).toOp * ρ.toOp).trace.re

/-- Coherent measurement weights are nonnegative. -/
theorem coherentWeight_nonneg (x : X) (ρ : DensityOp (Fin n → X)) (U : unitaryGroup X ℂ) :
    0 ≤ coherentWeight x ρ U :=
  mul_nonneg (Complex.nonneg_iff.mp symmetricProjector_posSemidef.trace_nonneg).1
    (Complex.nonneg_iff.mp (((pureStateMap x U).tensorPow n).posSemidef.trace_mul_nonneg
      ρ.posSemidef)).1

/-- The complex weight equals the product of the two complex traces. -/
theorem ofReal_coherentWeight (x : X) (ρ : DensityOp (Fin n → X)) (U : unitaryGroup X ℂ) :
    (coherentWeight x ρ U : ℂ) =
      (symmetricProjector X n).trace * (((pureStateMap x U).tensorPow n).toOp * ρ.toOp).trace := by
  have hs := (Complex.nonneg_iff.mp
    (symmetricProjector_posSemidef (X := X) (k := n)).trace_nonneg).2
  have ht := (Complex.nonneg_iff.mp
    (((pureStateMap x U).tensorPow n).posSemidef.trace_mul_nonneg ρ.posSemidef)).2
  apply Complex.ext <;> simp [coherentWeight, Complex.mul_re, Complex.mul_im, hs.symm, ht.symm]

/-- The coherent outcome weight is continuous on the unitary group. -/
theorem continuous_coherentWeight (x : X) (ρ : DensityOp (Fin n → X)) :
    Continuous (coherentWeight x ρ) := by
  have hc : Continuous (fun U : unitaryGroup X ℂ => ((pureStateMap x U).tensorPow n).toOp) :=
    continuous_pi fun i => continuous_pi fun j =>
      (DensityOp.continuous_tensorPow_entry n i j).comp (continuous_pureStateMap x)
  exact continuous_const.mul (Complex.continuous_re.comp
    ((hc.mul continuous_const).matrix_trace))

/-- Symmetric support normalizes the coherent POVM weight. -/
theorem integral_coherentWeight [Nonempty X] (x : X) (ρ : DensityOp (Fin n → X))
    (hρ : symmetricProjector X n * ρ.toOp * symmetricProjector X n = ρ.toOp) :
    ∫ U, coherentWeight x ρ U ∂UnitaryGroup.haarProbUnitary X = 1 := by
  have hs : symmetricProjector X n * ρ.toOp = ρ.toOp := by
    calc
      _ = symmetricProjector X n * (symmetricProjector X n * ρ.toOp *
          symmetricProjector X n) := congrArg (symmetricProjector X n * ·) hρ.symm
      _ = symmetricProjector X n * ρ.toOp * symmetricProjector X n := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, symmetricProjector_mul_self]
      _ = ρ.toOp := hρ
  have hc : Continuous (fun U : unitaryGroup X ℂ => ((pureStateMap x U).tensorPow n).toOp) :=
    continuous_pi fun i => continuous_pi fun j =>
      (DensityOp.continuous_tensorPow_entry n i j).comp (continuous_pureStateMap x)
  have hi (i j) : Integrable (fun U => ((pureStateMap x U).tensorPow n).toOp i j)
      (UnitaryGroup.haarProbUnitary X) :=
    ((continuous_apply j).comp ((continuous_apply i).comp hc)).integrable_of_compactSpace
  have hp (i j) : Integrable (fun U => (((pureStateMap x U).tensorPow n).toOp * ρ.toOp) i j)
      (UnitaryGroup.haarProbUnitary X) :=
    ((continuous_apply j).comp ((continuous_apply i).comp
    (hc.mul (continuous_const (y := ρ.toOp))))).integrable_of_compactSpace
  have he : (∫ U, (coherentWeight x ρ U : ℂ) ∂UnitaryGroup.haarProbUnitary X) = 1 := by
    simp_rw [ofReal_coherentWeight]
    rw [integral_const_mul, ← trace_entryIntegral (μ := UnitaryGroup.haarProbUnitary X)
      (fun i => hp i i), ← entryIntegral_mul _ (fun i j => hi i j)]
    rw [← smul_eq_mul, ← trace_smul, ← Matrix.smul_mul,
      ← symmetricProjector_eq_scaled_haar x n, hs, ρ.trace_one]
  rw [_root_.integral_complex_ofReal] at he
  exact_mod_cast he

/-- The state-dependent coherent measure is independent of the retained number of sites. -/
def coherentMeasure [Nonempty X] (x : X) (ρ : DensityOp (Fin n → X))
    (hρ : symmetricProjector X n * ρ.toOp * symmetricProjector X n = ρ.toOp) :
    DensityMeasure X where
  measure := Measure.map (pureStateMap x) ((UnitaryGroup.haarProbUnitary X).withDensity
    (fun U => ENNReal.ofReal (coherentWeight x ρ U)))
  isProbability := by
    have hp : IsProbabilityMeasure ((UnitaryGroup.haarProbUnitary X).withDensity
        (fun U => ENNReal.ofReal (coherentWeight x ρ U))) := by
      constructor
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        ← ofReal_integral_eq_lintegral_ofReal
          (continuous_coherentWeight x ρ).integrable_of_compactSpace
          (ae_of_all _ (coherentWeight_nonneg x ρ)), integral_coherentWeight x ρ hρ]
      simp
    constructor
    rw [Measure.map_apply (continuous_pureStateMap x).measurable MeasurableSet.univ]
    simp

/-- Coherent-measure mixtures are weighted Haar integrals of coherent tensor powers. -/
theorem integralTensorPower_coherentMeasure [Nonempty X] (x : X)
    (ρ : DensityOp (Fin n → X))
    (hρ : symmetricProjector X n * ρ.toOp * symmetricProjector X n = ρ.toOp) (k : ℕ) :
    integralTensorPower k (coherentMeasure x ρ hρ) =
      of fun i j => ∫ U, (coherentWeight x ρ U : ℂ) *
        ((pureStateMap x U).tensorPow k).toOp i j ∂UnitaryGroup.haarProbUnitary X := by
  ext i j
  change (∫ σ, (σ.tensorPow k).toOp i j ∂Measure.map (pureStateMap x) _) = _
  rw [integral_map (continuous_pureStateMap x).measurable.aemeasurable
    (DensityOp.continuous_tensorPow_entry k i j).measurable.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      (continuous_coherentWeight x ρ).measurable.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (coherentWeight_nonneg x ρ _), Complex.real_smul, of_apply]

end Quantum.DeFinetti
