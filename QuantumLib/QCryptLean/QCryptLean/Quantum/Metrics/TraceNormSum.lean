import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceNorm
import QCryptLean.Quantum.Operators.Basic

/-! # The finite triangle inequality for the intrinsic trace norm -/

namespace Quantum.Metrics

open Quantum.Operators

/-- The trace norm of a finite sum is bounded by the sum of the trace norms. -/
theorem traceNorm_sum_le {X I : Type*} [Fintype X] (s : Finset I) (A : I → Op X) :
    traceNorm (∑ i ∈ s, A i) ≤ ∑ i ∈ s, traceNorm (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [traceNorm_zero]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (traceNorm_add_le _ _).trans (add_le_add le_rfl ih)

end Quantum.Metrics
