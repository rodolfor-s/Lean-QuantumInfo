import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD
import QCryptLean.Math.LinearAlgebra.Matrix.Blocks
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Algebra

/-!
# Positive sums and classical flags

A classical label is kept as an actual product factor. The positive refinement
stores Mathlib positivity; sums are formed on matrices without introducing a
second additive instance on that subtype. No matrix norm is selected.
-/

namespace Quantum.Metrics

open Matrix Quantum.Operators
open scoped ComplexOrder

variable {X I : Type*}

/-- The positive refinement of a finite sum of positive matrices. -/
def sumPosSemidefOp (s : Finset I) (A : I → PosSemidefOp X) : PosSemidefOp X :=
  ⟨∑ i ∈ s, (A i).val, posSemidef_sum s fun i _ => (A i).property⟩

/-- A classical flag makes a family of positive matrices block diagonal. -/
def cqBlockPosSemidefOp [Finite X] [Finite I] [DecidableEq I]
    (A : I → PosSemidefOp X) : PosSemidefOp (X × I) :=
  ⟨blockDiagonal (fun i => (A i).val), posSemidef_blockDiagonal (fun i => (A i).property)⟩

/-- Discarding a classical flag sums its positive blocks. -/
theorem cqBlockPosSemidefOp_partialTraceRight [Finite X] [Fintype I] [DecidableEq I]
    (A : I → PosSemidefOp X) :
    (cqBlockPosSemidefOp A).partialTraceRight = sumPosSemidefOp Finset.univ A := by
  apply Subtype.ext
  ext x y
  simp [cqBlockPosSemidefOp, PosSemidefOp.partialTraceRight, sumPosSemidefOp,
    partialTraceRight_apply, Matrix.sum_apply]

end Quantum.Metrics
