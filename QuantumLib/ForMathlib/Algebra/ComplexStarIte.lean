import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Conjugation of a conditional scalar

Conjugation of a conditional scalar.
-/


noncomputable section

/-- Complex conjugation distributes over an `if` expression whose false branch
is zero. -/
lemma _root_.Complex.star_ite_zero {b : Prop} [Decidable b] (a : ℂ) :
    star (if b then a else 0) = if b then star a else 0 := by
  split_ifs <;> simp

end
