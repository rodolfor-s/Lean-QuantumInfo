import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.FidelityMonotone
import QCryptLean.Quantum.Metrics.Flagged
import QCryptLean.Quantum.Metrics.PartialTrace
import QCryptLean.Quantum.Operators.Algebra

/-! # Flagged Bounds -/


noncomputable section

namespace Quantum.Metrics

open scoped ComplexOrder MatrixOrder

open Matrix Quantum.Operators

variable {X I : Type*} [Fintype X] [Fintype I] {n : ℕ}

/-- Fidelity of classically flagged operators is additive. Native block square-root proof. -/
theorem fidelity_cqBlock_eq_sum [DecidableEq I]
    (A B : I → PosSemidefOp X) :
    fidelity (cqBlockPosSemidefOp A) (cqBlockPosSemidefOp B) =
      ∑ i, fidelity (A i) (B i) := by
  classical
  have hp (i : I) : (CFC.sqrt (A i).val * (B i).val * CFC.sqrt (A i).val).PosSemidef := by
    simpa only [(nonneg_iff_posSemidef.mp
      (CFC.sqrt_nonneg (A i).val)).isHermitian.eq] using
      (B i).property.mul_mul_conjTranspose_same (CFC.sqrt (A i).val)
  unfold fidelity sqrtPosSemidefOp cqBlockPosSemidefOp
  rw [Matrix.PosSemidef.sqrt_blockDiagonal (fun i => (A i).property),
    ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul,
    Matrix.PosSemidef.sqrt_blockDiagonal hp, Matrix.trace_blockDiagonal, Complex.re_sum]

/-- Discarding a classical flag gives finite superadditivity of fidelity. -/
theorem sum_fidelity_le_fidelity_sum [Nonempty X] (A B : I → PosSemidefOp X) :
    ∑ i, fidelity (A i) (B i) ≤
      fidelity (sumPosSemidefOp Finset.univ A) (sumPosSemidefOp Finset.univ B) := by
  classical
  have h := fidelity_le_partialTraceRight (cqBlockPosSemidefOp A) (cqBlockPosSemidefOp B)
  rwa [fidelity_cqBlock_eq_sum, cqBlockPosSemidefOp_partialTraceRight,
    cqBlockPosSemidefOp_partialTraceRight] at h

end Quantum.Metrics
