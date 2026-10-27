import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! # Direct -/


noncomputable section

open scoped BigOperators

namespace InfoTheory.QuantumLHL.SeedKey

/-- Cauchy-Schwarz for a seed average over a seed-output product register. -/
lemma sq_seed_average_sum_le_card_output_mul_seed_average_sum_sq
    {S Z : Type*} [Fintype S] [Nonempty S] [Fintype Z] (a : S × Z → ℝ) :
    ((1 / (Fintype.card S : ℝ)) * ∑ sz : S × Z, a sz) ^ 2 ≤
      (Fintype.card Z : ℝ) *
        ((1 / (Fintype.card S : ℝ)) * ∑ sz : S × Z, (a sz) ^ 2) := by
  have hS_pos : (0 : ℝ) < (Fintype.card S : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hS_ne : (Fintype.card S : ℝ) ≠ 0 := ne_of_gt hS_pos
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (S × Z))) (f := a)
  have hcard :
      (Fintype.card (S × Z) : ℝ) =
        (Fintype.card S : ℝ) * (Fintype.card Z : ℝ) := by
    exact_mod_cast Fintype.card_prod S Z
  rw [Finset.card_univ] at hcs
  rw [hcard] at hcs
  field_simp [hS_ne]
  nlinarith [hcs, hS_pos]

end InfoTheory.QuantumLHL.SeedKey

end -- noncomputable section
