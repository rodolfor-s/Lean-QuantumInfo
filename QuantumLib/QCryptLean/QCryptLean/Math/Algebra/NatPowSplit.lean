import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic

/-!
# Splitting natural powers

Splitting natural powers.
-/


noncomputable section

/-- Dimension factoring: d^n = d^k * d^(n-k) when k ≤ n. -/
lemma _root_.Nat.pow_eq_mul_pow_sub {d n k : ℕ} (hk : k ≤ n) :
    d ^ n = d ^ k * d ^ (n - k) := by
  rw [← pow_add, Nat.add_sub_cancel' hk]

end
