import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceNormSum
import QCryptLean.Quantum.Operators.Basic

/-! # Finite sums and block diagonals for the explicit trace norm -/
noncomputable section
namespace Quantum.Metrics
open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder
variable {X I : Type*} [Fintype X]

/-- A block-diagonal operator has trace norm equal to the sum of the block trace norms. -/
theorem traceNorm_blockDiagonal [Fintype I] [DecidableEq I] (A : I → Op X) :
    traceNorm (blockDiagonal A) = ∑ i, traceNorm (A i) := by
  classical
  rw [traceNorm_eq_trace_sqrt, blockDiagonal_conjTranspose, ← blockDiagonal_mul,
    PosSemidef.sqrt_blockDiagonal (fun i => posSemidef_conjTranspose_mul_self (A i)),
    trace_blockDiagonal, Complex.re_sum]
  simp only [traceNorm_eq_trace_sqrt]

open scoped Kronecker in
/-- Appending a fixed classical record preserves the trace norm of every operator. -/
theorem traceNorm_kronecker_single [Fintype I] [DecidableEq I] (A : Op X) (i : I) :
    traceNorm (A ⊗ₖ (single i i 1 : Op I)) = traceNorm A := by
  have he : A ⊗ₖ (single i i 1 : Op I) =
      blockDiagonal (fun j => if j = i then A else 0) := by
    ext ⟨x, j⟩ ⟨y, k⟩
    by_cases hj : j = i <;> by_cases hk : k = i <;>
      simp_all [kroneckerMap_apply, single_apply, blockDiagonal_apply, eq_comm]
  rw [he, traceNorm_blockDiagonal]
  simp only [apply_ite traceNorm, traceNorm_zero]
  simp

end Quantum.Metrics
