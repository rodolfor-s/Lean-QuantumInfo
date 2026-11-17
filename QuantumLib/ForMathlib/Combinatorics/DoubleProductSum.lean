import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Factoring sums of products over pairs of strings

Factoring sums of products over pairs of strings.
-/

open scoped BigOperators

noncomputable section

/-- **Summing a round-wise product over two strings factors round by round.** -/
theorem _root_.Fintype.sum_sum_prod {R : Type*} [CommSemiring R] {ι α : Type} [Fintype ι]
    [DecidableEq ι] [Fintype α] (g : ι → α → α → R) :
    (∑ u : ι → α, ∑ v : ι → α, ∏ r, g r (u r) (v r)) = ∏ r, ∑ x, ∑ y, g r x y := by
  symm
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

end
