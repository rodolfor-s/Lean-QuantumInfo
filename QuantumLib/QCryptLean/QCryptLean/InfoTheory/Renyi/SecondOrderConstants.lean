import QCryptLean.InfoTheory.Renyi.ConditionalVariance.Bounds
import QCryptLean.InfoTheory.Renyi.ConditionalVariance.Continuity

/-! # Second Order Constants -/


open Matrix 
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators

noncomputable section

namespace InfoTheory.Renyi

/-- The binary classical Dupuis–Fawzi remainder base `K_* = log³(2 + e²) / (6 log 2)`. -/
def binarySecondOrderRemainderBase : ℝ :=
  Real.log (2 + Real.exp 2) ^ 3 / (6 * Real.log 2)

/-- The binary classical Dupuis–Fawzi remainder bound `K_β = K_* · 2^β / (1 - β)^3`,
valid for Rényi offsets `0 < β < 1`. -/
def binarySecondOrderRemainderBound (β : ℝ) : ℝ :=
  binarySecondOrderRemainderBase * (2 : ℝ) ^ β / (1 - β) ^ 3

/-- The binary remainder bound is nonnegative for `β ≤ 1`. -/
lemma binarySecondOrderRemainderBound_nonneg {β : ℝ} (hβ : β ≤ 1) :
    0 ≤ binarySecondOrderRemainderBound β := by
  have hlog : 0 ≤ Real.log (2 + Real.exp 2) := Real.log_nonneg (by
    have := Real.exp_pos (2 : ℝ)
    linarith)
  have hden : 0 ≤ 1 - β := sub_nonneg.mpr hβ
  unfold binarySecondOrderRemainderBound binarySecondOrderRemainderBase
  positivity

end InfoTheory.Renyi

end
