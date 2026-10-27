import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.PurifiedBasic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.Projector

/-! # Fidelity of positive sandwiches -/

namespace Quantum.Metrics
open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder
variable {X : Type*} [Fintype X]

/-- A positive sandwich has fidelity equal to the trace pairing. -/
theorem fidelity_positive_sandwich (A B : PosSemidefOp X) :
    fidelity A ⟨B.val * A.val * B.val, by
      simpa only [B.property.isHermitian.eq] using
        A.property.conjTranspose_mul_mul_same B.val⟩ = (A.val * B.val).trace.re := by
  classical
  have hs : (sqrtPosSemidefOp A).IsHermitian :=
    (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A.val)).isHermitian
  have hp : (sqrtPosSemidefOp A * B.val * sqrtPosSemidefOp A).PosSemidef := by
    simpa only [hs.eq] using B.property.conjTranspose_mul_mul_same (sqrtPosSemidefOp A)
  have he : sqrtPosSemidefOp A * (B.val * A.val * B.val) * sqrtPosSemidefOp A =
      (sqrtPosSemidefOp A * B.val * sqrtPosSemidefOp A) *
        (sqrtPosSemidefOp A * B.val * sqrtPosSemidefOp A) := by
    conv_lhs => rw [← sqrtPosSemidefOp_mul_self A]
    simp only [Matrix.mul_assoc]
  simp only [fidelity, he, CFC.sqrt_mul_self _ hp.nonneg]
  rw [trace_mul_cycle, sqrtPosSemidefOp_mul_self]

/-- For a projector sandwich, fidelity is the surviving trace. -/
theorem fidelity_projectorSandwich (A : PosSemidefOp X) {P : Op X}
    (hP : IsOrthogonalProjector P) :
    fidelity A ⟨P * A.val * P, by
      simpa only [hP.isHermitian.eq] using A.property.conjTranspose_mul_mul_same P⟩ =
      (P * A.val * P).trace.re := by
  rw [fidelity_positive_sandwich A ⟨P, hP.posSemidef⟩]
  rw [trace_mul_cycle, hP.idempotent, trace_mul_comm]

end Quantum.Metrics
