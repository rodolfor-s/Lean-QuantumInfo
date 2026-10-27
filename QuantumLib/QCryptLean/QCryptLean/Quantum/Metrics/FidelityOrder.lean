import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Algebra

/-! # Monotonicity of fidelity in a positive argument

Matrix star order and the L2 operator norm are scoped locally to this proof.
-/
namespace Quantum.Metrics
open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {X : Type*} [Fintype X]

/-- Increasing a positive argument increases fidelity. The order is the local star order. -/
theorem fidelity_mono_right (A B C : PosSemidefOp X) (h : B.val ≤ C.val) :
    fidelity A B ≤ fidelity A C := by
  classical
  have hs := (isHermitian_sqrtPosSemidefOp A).eq
  have hd := (nonneg_iff_posSemidef.mp (sub_nonneg.mpr h)).conjTranspose_mul_mul_same
    (sqrtPosSemidefOp A)
  rw [hs, mul_sub, sub_mul] at hd
  have ht := (nonneg_iff_posSemidef.mp (sub_nonneg.mpr
    (CFC.sqrt_le_sqrt _ _ (sub_nonneg.mp hd.nonneg)))).trace_nonneg
  simpa only [fidelity, Matrix.trace_sub, Complex.sub_re, sub_nonneg] using
    (Complex.nonneg_iff.mp ht).1

end Quantum.Metrics
