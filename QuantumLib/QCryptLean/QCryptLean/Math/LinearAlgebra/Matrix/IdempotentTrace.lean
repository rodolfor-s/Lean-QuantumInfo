import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Trace

/-! # Trace of a finite idempotent matrix -/

namespace Matrix

variable {X K : Type*} [Fintype X] [Field K]

/-- An idempotent matrix has trace equal to its rank, without a Hermiticity assumption. -/
theorem trace_eq_rank_of_mul_self_eq (P : Matrix X X K) (hP : P * P = P) :
    P.trace = (P.rank : K) := by
  classical
  have hi : IsIdempotentElem P.toLin' := by
    change P.toLin'.comp P.toLin' = P.toLin'
    rw [← Matrix.toLin'_mul, hP]
  have h := (LinearMap.IsIdempotentElem.isProj_range _ hi).trace
  rw [Matrix.trace_toLin'_eq] at h
  simp only [Matrix.toLin'_apply'] at h
  unfold Matrix.rank
  convert h using 1
  congr 1

end Matrix
