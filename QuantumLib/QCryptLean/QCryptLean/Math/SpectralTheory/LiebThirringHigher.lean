import Mathlib.Analysis.Matrix.Order
import QCryptLean.Math.SpectralTheory.KyFan.Basic
import QCryptLean.Math.SpectralTheory.KyFan.PositivePart

/-!
# Spectral Theory: Ky Fan partial-sum clamping

## Main statements

- `eigenvaluePartialSum_clamp`: the Ky Fan `eigenvaluePartialSum` clamps at
  dimension `N`, so values for `k ≥ N` collapse to the full-dimension value.
-/

open scoped Matrix BigOperators ComplexConjugate ComplexOrder MatrixOrder
open Matrix

noncomputable section

namespace Math.SpectralTheory

/-- The partial-sum function clamps at the ambient dimension: for `k ≥ N`, all
terms above `N` are dropped, so the value coincides with the full-dim one. -/
lemma eigenvaluePartialSum_clamp {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.IsHermitian)
    {k : ℕ} (hk : N ≤ k) :
    eigenvaluePartialSum A hA k = eigenvaluePartialSum A hA N := by
  rw [eigenvaluePartialSum_of_le A hA N le_rfl]
  unfold eigenvaluePartialSum
  refine Finset.sum_equiv (finCongr (Nat.min_eq_right hk)) ?_ ?_
  · intro i; simp
  · intro i _; simp [finCongr]

end Math.SpectralTheory
