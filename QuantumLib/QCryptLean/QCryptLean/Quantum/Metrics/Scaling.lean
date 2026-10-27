import QCryptLean.Math.LinearAlgebra.Matrix.SqrtScale
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Algebra

/-!
# Native fidelity homogeneity

This statement uses positive bundles for both the inputs and the scaled outputs.
Thus callers need no new scalar-action instance on the positive cone.
-/

namespace Quantum.Metrics

open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder

variable {X : Type*} [Fintype X]

/-- Scaling the two positive operands scales fidelity by the geometric mean. -/
theorem fidelity_smul_smul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (A B A' B' : PosSemidefOp X) (hA : A'.val = (a : ℂ) • A.val)
    (hB : B'.val = (b : ℂ) • B.val) :
    fidelity A' B' = Real.sqrt (a * b) * fidelity A B := by
  classical
  have hs := (isHermitian_sqrtPosSemidefOp A).eq
  have hp : (sqrtPosSemidefOp A * B.val * sqrtPosSemidefOp A).PosSemidef := by
    simpa only [hs] using B.property.mul_mul_conjTranspose_same (sqrtPosSemidefOp A)
  have hc : (Real.sqrt a : ℂ) * (b : ℂ) * Real.sqrt a = (a * b : ℝ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    calc Real.sqrt a * b * Real.sqrt a = Real.sqrt a * Real.sqrt a * b := by ring
         _ = a * b := by rw [Real.mul_self_sqrt ha]
  change (CFC.sqrt A.val * B.val * CFC.sqrt A.val).PosSemidef at hp
  unfold fidelity sqrtPosSemidefOp
  rw [hA, hB, A.property.sqrt_ofReal_smul ha,
    smul_mul_smul_comm, smul_mul_smul_comm, hc, hp.sqrt_ofReal_smul (mul_nonneg ha hb),
    Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

end Quantum.Metrics
