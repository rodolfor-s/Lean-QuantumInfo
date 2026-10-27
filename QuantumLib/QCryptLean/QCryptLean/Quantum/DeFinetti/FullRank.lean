import QCryptLean.Math.Analysis.CompactSpaceIntegrable
import QCryptLean.Math.LinearAlgebra.Matrix.EntryIntegral
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.Integral
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Operators.Topology

/-! # Full Rank -/


noncomputable section

namespace Quantum.DeFinetti

open Matrix Quantum.Operators MeasureTheory
open scoped ComplexOrder

variable {X : Type*} [Fintype X] [Nonempty X]

/-- Tensor mixtures of an open-positive measure are strictly positive. -/
theorem posDef_integralTensorPower_of_isOpenPosMeasure (μ : DensityMeasure X)
    (hμ : μ.measure.IsOpenPosMeasure) (k : ℕ) : (integralTensorPower k μ).PosDef := by
  classical
  have := μ.isProbability
  have : Measure.IsOpenPosMeasure μ.measure := hμ
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (posSemidef_integralTensorPower μ k).isHermitian
  intro v hv
  let f : DensityOp X → ℝ := fun ρ => (star v ⬝ᵥ (ρ.tensorPow k).toOp *ᵥ v).re
  have hc : Continuous f := by
    apply Complex.continuous_re.comp
    exact continuous_finsetSum _ fun i _ => continuous_const.mul
      (continuous_finsetSum _ fun j _ =>
        (DensityOp.continuous_tensorPow_entry k i j).mul continuous_const)
  have hi : Integrable f μ.measure := hc.integrable_of_compactSpace
  have hn : 0 ≤ f := fun ρ =>
    (Complex.nonneg_iff.mp ((ρ.tensorPow k).posSemidef.dotProduct_mulVec_nonneg v)).1
  have hm : (DensityOp.maxMixed (X := X)).toOp.PosDef := by
    apply Matrix.PosDef.smul Matrix.PosDef.one
    exact_mod_cast (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos) :
      0 < (Fintype.card X : ℝ)⁻¹)
  have hp : ((DensityOp.maxMixed (X := X)).tensorPow k).toOp.PosDef :=
    Matrix.PosDef.piTensorProduct fun _ => hm
  have hf : f (DensityOp.maxMixed (X := X)) ≠ 0 :=
    ne_of_gt (Complex.pos_iff.mp (hp.dotProduct_mulVec_pos hv)).1
  have hpos := integral_pos_of_integrable_nonneg_nonzero hc hi hn hf
  have hq : Integrable (fun ρ : DensityOp X => star v ⬝ᵥ (ρ.tensorPow k).toOp *ᵥ v)
      μ.measure := integrable_finsetSum _ fun i _ =>
    (integrable_finsetSum _ fun j _ =>
      (integrable_tensorPow_entry μ k i j).mul_const (v j)).const_mul (star v i)
  apply Complex.pos_iff.mpr
  constructor
  · rw [integralTensorPower, Matrix.dotProduct_mulVec_entryIntegral
      (integrable_tensorPow_entry μ k)]
    change 0 < RCLike.re (∫ ρ, star v ⬝ᵥ (ρ.tensorPow k).toOp *ᵥ v ∂μ.measure)
    rw [← integral_re hq]
    exact hpos
  · exact (Complex.nonneg_iff.mp
      ((posSemidef_integralTensorPower μ k).dotProduct_mulVec_nonneg v)).2

/-- The mixture therefore has full rank on the function register. -/
theorem rank_integralTensorPower_of_isOpenPosMeasure (μ : DensityMeasure X)
    (hμ : μ.measure.IsOpenPosMeasure) (k : ℕ) :
    (integralTensorPower k μ).rank = Fintype.card X ^ k := by
  classical
  have h := (posDef_integralTensorPower_of_isOpenPosMeasure μ hμ k).isUnit
  simpa using Matrix.rank_of_isUnit (integralTensorPower k μ) h

end Quantum.DeFinetti
