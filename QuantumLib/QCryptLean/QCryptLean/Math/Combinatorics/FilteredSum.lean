import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic

/-!
# Predicate-gated finite sums

A single comparison lemma for finite sums where terms indexed by a predicate `P` are
zeroed out (`if P i then 0 else a i`): a per-index slack bound on the ungated terms
lifts to a bound on the gated sums with an additive `card * slack` term.
-/

open scoped BigOperators

namespace Math.Finset

/-- A finite sum gated by a predicate can absorb a nonnegative uniform slack once
per index. -/
lemma _root_.Finset.sum_ite_le_sum_ite_add_card_mul
    {ι : Type*} (s : Finset ι)
    (P : ι → Prop) [DecidablePred P]
    (a b : ι → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ i ∈ s, ¬ P i → a i ≤ b i + c) :
    ∑ i ∈ s, (if P i then (0 : ℝ) else a i) ≤
      ∑ i ∈ s, (if P i then (0 : ℝ) else b i) + (s.card : ℝ) * c := by
  calc
    ∑ i ∈ s, (if P i then (0 : ℝ) else a i)
        ≤ ∑ i ∈ s, ((if P i then (0 : ℝ) else b i) + c) := by
          apply Finset.sum_le_sum
          intro i hi
          by_cases hPi : P i
          · simp [hPi, hc]
          · simpa [hPi] using hbound i hi hPi
    _ = ∑ i ∈ s, (if P i then (0 : ℝ) else b i) + (s.card : ℝ) * c := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]

end Math.Finset
