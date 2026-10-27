import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceNorm
import QCryptLean.Quantum.Operators.Basic

/-! # Generalized trace-distance identities for finite registers -/
namespace Quantum.Metrics
open Quantum.Operators
variable {X : Type*} [Fintype X]

/-- Generalized trace distance is symmetric. -/
theorem traceDistanceGen_symm (A B : Op X) : traceDistanceGen A B = traceDistanceGen B A := by
  have hn : traceNorm (A - B) = traceNorm (B - A) := by
    rw [← traceNorm_neg (B - A), neg_sub]
  simp only [traceDistanceGen, traceDistance, hn, Complex.sub_re, abs_sub_comm]

/-- Generalized trace distance satisfies the triangle inequality on all operators. -/
theorem traceDistanceGen_triangle (A B C : Op X) :
    traceDistanceGen A C ≤ traceDistanceGen A B + traceDistanceGen B C := by
  have hn := traceNorm_add_le (A - B) (B - C)
  rw [sub_add_sub_cancel] at hn
  have ht := abs_sub_le A.trace.re B.trace.re C.trace.re
  simp only [traceDistanceGen, traceDistance, Complex.sub_re]
  linarith

end Quantum.Metrics
