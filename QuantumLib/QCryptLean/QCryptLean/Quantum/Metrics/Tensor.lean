import QCryptLean.Math.LinearAlgebra.Matrix.SqrtKronecker
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.Tensor

/-! # Tensor -/


noncomputable section

namespace Quantum.Metrics

open Matrix Quantum.Operators
open scoped Kronecker ComplexOrder MatrixOrder

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Unsquared fidelity multiplies under independent tensor products. -/
theorem fidelity_kronecker (A B : PosSemidefOp X) (C D : PosSemidefOp Y) :
    fidelity (A.kronecker C) (B.kronecker D) = fidelity A B * fidelity C D := by
  classical
  have hA := nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A.val)
  have hC := nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.val)
  have hAB : (CFC.sqrt A.val * B.val * CFC.sqrt A.val).PosSemidef := by
    simpa only [hA.isHermitian.eq] using B.property.conjTranspose_mul_mul_same (CFC.sqrt A.val)
  have hCD : (CFC.sqrt C.val * D.val * CFC.sqrt C.val).PosSemidef := by
    simpa only [hC.isHermitian.eq] using D.property.conjTranspose_mul_mul_same (CFC.sqrt C.val)
  unfold fidelity sqrtPosSemidefOp
  change (CFC.sqrt (CFC.sqrt (A.val ⊗ₖ C.val) * (B.val ⊗ₖ D.val) *
    CFC.sqrt (A.val ⊗ₖ C.val))).trace.re = _
  rw [A.property.sqrt_kronecker C.property, ← mul_kronecker_mul, ← mul_kronecker_mul,
    hAB.sqrt_kronecker hCD, trace_kronecker, Complex.mul_re]
  have hi := (Complex.nonneg_iff.mp
    (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg
      (CFC.sqrt A.val * B.val * CFC.sqrt A.val))).trace_nonneg).2
  rw [← hi, zero_mul, sub_zero]

/-- Squared fidelity also multiplies under independent tensor products. -/
theorem fidelitySq_kronecker (A B : PosSemidefOp X) (C D : PosSemidefOp Y) :
    fidelitySq (A.kronecker C) (B.kronecker D) = fidelitySq A B * fidelitySq C D := by
  simp only [fidelitySq, fidelity_kronecker, mul_pow]

end Quantum.Metrics
