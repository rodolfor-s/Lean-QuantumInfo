import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Square roots bounded by exponentials

Square roots bounded by exponentials.
-/

noncomputable section

/-- A square-root input bounded by an exponential has square root bounded by the
exponential with half the exponent. -/
lemma _root_.Real.sqrt_le_exp_half_of_le_exp {x y : ℝ} (h : x ≤ Real.exp y) :
    Real.sqrt x ≤ Real.exp (y / 2) := by
  calc
    Real.sqrt x ≤ Real.sqrt (Real.exp y) := Real.sqrt_le_sqrt h
    _ = Real.exp (y / 2) := by
        rw [← Real.exp_half]

end
