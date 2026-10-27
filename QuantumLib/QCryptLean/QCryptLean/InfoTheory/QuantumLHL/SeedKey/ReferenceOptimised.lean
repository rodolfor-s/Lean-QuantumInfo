import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import QCryptLean.InfoTheory.QuantumLHL.SeedKey.Smoothing

/-! # Reference Optimised -/


open InfoTheory.QuantumLHL

open   Matrix
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.QuantumLHL.SeedKey

/-- The seed-key smooth LHL bound is continuous in the entropy level. -/
lemma continuous_half_mul_sqrt_mul_rpow_neg_add (Zcard : ℕ) (ε : ℝ) :
    Continuous (fun t : ℝ => (1 / 2) * Real.sqrt ((Zcard : ℝ) * 2 ^ (-t)) + 2 * ε) := by
  refine Continuous.add (continuous_const.mul ?_) continuous_const
  refine Real.continuous_sqrt.comp (continuous_const.mul ?_)
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  exact (Real.continuous_const_rpow h2).comp continuous_neg

end InfoTheory.QuantumLHL.SeedKey

end -- noncomputable section
