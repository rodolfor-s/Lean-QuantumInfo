import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators

/-! # Triple Sum -/


open scoped BigOperators

noncomputable section

/-- A sum over `Ω × A × B` whose summand reads only the `(B, Ω)` factors factors through
    `Fintype.card A`. -/
lemma _root_.Fintype.sum_prod_prod_eq_card_mul_sum_sum {Ω A B : Type*} [Fintype Ω] [Fintype A]
    [Fintype B] (F : B → Ω → ℝ) :
    ∑ k : Ω × A × B, F k.2.2 k.1 = (Fintype.card A : ℝ) * ∑ b : B, ∑ ω : Ω, F b ω := by
  classical
  simp only [Fintype.sum_prod_type_right]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]

end
