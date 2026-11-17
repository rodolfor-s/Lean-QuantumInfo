import Mathlib.Logic.Equiv.Defs

/-!
# Heterogeneous equality for types equal to Unit

Heterogeneous equality for types equal to Unit.
-/

noncomputable section

/-- Two one-element coordinate types carry heterogeneously equal elements. -/
theorem _root_.HEq.of_eq_unit {XX YY : Type} (hX : XX = Unit) (hY : YY = Unit) (x : XX) (y : YY) :
    x ≍ y := by
  subst hX
  subst hY
  exact heq_of_eq (Subsingleton.elim x y)

end
