import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Choose.Bounds

/-!
# A power bound for binomial coefficients

A power bound for binomial coefficients.
-/


noncomputable section

/-- Real-valued form of the binomial dimension bound
`C(n + k, k) ≤ (n + 1)^k`. -/
lemma _root_.Nat.cast_choose_add_le_pow_succ (n k : ℕ) :
    (Nat.choose (n + k) k : ℝ) ≤ (n + 1 : ℝ) ^ k := by
  have h :
      (Nat.choose (n + k) k : ℝ) ≤ (((n + 1) ^ k : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.choose_add_le_add_one_pow n k)
  simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using h

end
