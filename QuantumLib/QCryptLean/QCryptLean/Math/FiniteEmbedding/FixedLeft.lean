import Mathlib.Logic.Equiv.Sum

/-!
# Restriction of a sum equivalence fixing its left summand

This module explicitly restricts an equivalence of `α ⊕ β` that fixes every left value to a
permutation of `β`. The construction applies to arbitrary sum types, without finiteness or
inhabitance assumptions.
-/

namespace Math.FiniteEmbedding

variable {α β : Type*}

/-- An equivalence of a sum fixes its left summand pointwise. -/
def SumEquivFixesLeft (q : α ⊕ β ≃ α ⊕ β) : Prop :=
  ∀ i : α, q (Sum.inl i) = Sum.inl i

/-- The inverse of a fixed-left sum equivalence also fixes the left summand. -/
theorem sumEquiv_symm_fixesLeft (q : α ⊕ β ≃ α ⊕ β)
    (h : SumEquivFixesLeft q) :
    SumEquivFixesLeft q.symm := by
  intro i
  apply q.injective
  simp [h i]

/-- Explicit right coordinate obtained by inspecting the image under a fixed-left equivalence. -/
def rightMapOfFixesLeft (q : α ⊕ β ≃ α ⊕ β)
    (h : SumEquivFixesLeft q) (j : β) : β :=
  match hq : q (Sum.inr j) with
  | Sum.inl i =>
      False.elim (Sum.inl_ne_inr (q.injective ((h i).trans hq.symm)))
  | Sum.inr j' => j'

/-- A fixed-left sum equivalence sends a right input to its explicit right coordinate. -/
theorem sumEquiv_right_image (q : α ⊕ β ≃ α ⊕ β)
    (h : SumEquivFixesLeft q) (j : β) :
    q (Sum.inr j) = Sum.inr (rightMapOfFixesLeft q h j) := by
  unfold rightMapOfFixesLeft
  split
  · rename_i i hq
    exfalso
    exact Sum.inl_ne_inr (q.injective ((h i).trans hq.symm))
  · assumption

/-- Explicit right coordinate obtained from the inverse fixed-left equivalence. -/
def rightMapOfFixesLeftSymm (q : α ⊕ β ≃ α ⊕ β)
    (h : SumEquivFixesLeft q) (j : β) : β :=
  rightMapOfFixesLeft q.symm (sumEquiv_symm_fixesLeft q h) j

/-- The inverse equivalence sends a right input to its explicit inverse right coordinate. -/
theorem sumEquiv_symm_right_image (q : α ⊕ β ≃ α ⊕ β)
    (h : SumEquivFixesLeft q) (j : β) :
    q.symm (Sum.inr j) = Sum.inr (rightMapOfFixesLeftSymm q h j) := by
  exact sumEquiv_right_image q.symm (sumEquiv_symm_fixesLeft q h) j

/-- The inverse right map is a left inverse of the forward right map. -/
theorem rightMapOfFixesLeft_leftInverse (q : α ⊕ β ≃ α ⊕ β)
    (h : SumEquivFixesLeft q) (j : β) :
    rightMapOfFixesLeftSymm q h (rightMapOfFixesLeft q h j) = j := by
  have hs :
      (Sum.inr (rightMapOfFixesLeftSymm q h (rightMapOfFixesLeft q h j)) : α ⊕ β) =
        Sum.inr j := by
    rw [← sumEquiv_symm_right_image, ← sumEquiv_right_image]
    simp
  exact Sum.inr.inj hs

/-- The inverse right map is a right inverse of the forward right map. -/
theorem rightMapOfFixesLeft_rightInverse (q : α ⊕ β ≃ α ⊕ β)
    (h : SumEquivFixesLeft q) (j : β) :
    rightMapOfFixesLeft q h (rightMapOfFixesLeftSymm q h j) = j := by
  have hs :
      (Sum.inr (rightMapOfFixesLeft q h (rightMapOfFixesLeftSymm q h j)) : α ⊕ β) =
        Sum.inr j := by
    rw [← sumEquiv_right_image, ← sumEquiv_symm_right_image]
    simp
  exact Sum.inr.inj hs

/-- Permutation induced on the right summand by a fixed-left sum equivalence. -/
def rightPermOfFixesLeft (q : α ⊕ β ≃ α ⊕ β)
    (h : SumEquivFixesLeft q) : Equiv.Perm β where
  toFun := rightMapOfFixesLeft q h
  invFun := rightMapOfFixesLeftSymm q h
  left_inv := rightMapOfFixesLeft_leftInverse q h
  right_inv := rightMapOfFixesLeft_rightInverse q h

/-- A fixed-left sum equivalence is reconstructed by its induced right permutation. -/
theorem sumEquiv_eq_sumCongr_rightPerm (q : α ⊕ β ≃ α ⊕ β)
    (h : SumEquivFixesLeft q) :
    q = Equiv.sumCongr (Equiv.refl α) (rightPermOfFixesLeft q h) := by
  apply Equiv.ext
  rintro (i | j)
  · simpa using h i
  · simpa [rightPermOfFixesLeft] using sumEquiv_right_image q h j

/-! ## Definition-driven formulas -/

/-- The induced permutation applies the explicit forward right map. -/
theorem rightPermOfFixesLeft_apply (q : α ⊕ β ≃ α ⊕ β)
    (h : SumEquivFixesLeft q) (j : β) :
    rightPermOfFixesLeft q h j = rightMapOfFixesLeft q h j := by
  rfl

/-- The inverse induced permutation applies the explicit inverse right map. -/
theorem rightPermOfFixesLeft_symm_apply (q : α ⊕ β ≃ α ⊕ β)
    (h : SumEquivFixesLeft q) (j : β) :
    (rightPermOfFixesLeft q h).symm j = rightMapOfFixesLeftSymm q h j := by
  rfl

end Math.FiniteEmbedding
