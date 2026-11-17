import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Total filtering of a probability mass function

This module extends `PMF.filter` with an explicit fallback for a zero-mass set. The construction
uses a support witness only in the positive branch; otherwise it returns the supplied pure
distribution.
-/

namespace PMF

noncomputable section

variable {α : Type*}

/-- Filter and normalize on a positive-mass set; otherwise return the explicit fallback point. -/
def filterOrPure (p : PMF α) (s : Set α) (fallback : α) : PMF α := by
  classical
  exact if h : ∃ a ∈ s, a ∈ p.support then p.filter s h else PMF.pure fallback

/-- On an explicitly inhabited support intersection, `filterOrPure` is Mathlib's normalized
filter. -/
theorem filterOrPure_eq_filter (p : PMF α) (s : Set α) (fallback : α)
    (h : ∃ a ∈ s, a ∈ p.support) :
    filterOrPure p s fallback = p.filter s h := by
  classical
  unfold filterOrPure
  split
  · rfl
  · contradiction

/-- If the set misses the PMF support, `filterOrPure` is the supplied pure fallback. -/
theorem filterOrPure_eq_pure (p : PMF α) (s : Set α) (fallback : α)
    (h : ¬∃ a ∈ s, a ∈ p.support) :
    filterOrPure p s fallback = PMF.pure fallback := by
  classical
  unfold filterOrPure
  split
  · contradiction
  · rfl

/-- Pointwise formula in the positive-support branch. -/
theorem filterOrPure_apply_of_exists (p : PMF α) (s : Set α) (fallback a : α)
    (h : ∃ x ∈ s, x ∈ p.support) :
    filterOrPure p s fallback a =
      s.indicator p a * (∑' x, s.indicator p x)⁻¹ := by
  classical
  rw [filterOrPure_eq_filter p s fallback h]
  exact PMF.filter_apply h a

/-- Pointwise formula in the zero-support branch. -/
theorem filterOrPure_apply_of_not_exists (p : PMF α) (s : Set α) (fallback a : α)
    (h : ¬∃ x ∈ s, x ∈ p.support) :
    filterOrPure p s fallback a = PMF.pure fallback a := by
  rw [filterOrPure_eq_pure p s fallback h]

/-- Filtering on the empty set always exercises the explicit fallback branch. -/
theorem filterOrPure_empty (p : PMF α) (fallback : α) :
    filterOrPure p ∅ fallback = PMF.pure fallback := by
  classical
  apply filterOrPure_eq_pure
  simp

end

end PMF
