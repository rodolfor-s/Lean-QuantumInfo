import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Comparison of binomial coefficients

Comparison of binomial coefficients.
-/


noncomputable section

/-- Binomial coefficient monotonicity: `C(n+3, 3) ≤ C(n+15, 15)`. -/
lemma _root_.Nat.choose_add_three_le_choose_add_fifteen (n : ℕ) :
    Nat.choose (n + 3) 3 ≤ Nat.choose (n + 15) 15 := by
  rw [show n + 3 = 3 + n from by omega, Nat.choose_symm_add,
      show n + 15 = 15 + n from by omega, Nat.choose_symm_add]
  exact Nat.choose_le_choose n (by omega)

end
