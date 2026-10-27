import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import QCryptLean.InfoTheory.QuantumLHL.HashingError
import QCryptLean.InfoTheory.QuantumLHL.SeedKey.Direct

/-! # Smoothing -/


open InfoTheory.QuantumLHL

open   Matrix Real
open scoped ComplexOrder

noncomputable section

namespace InfoTheory.QuantumLHL.SeedKey

/-- Infinite entropy removes the hashing term, leaving only the smoothing charge. -/
lemma _root_.InfoTheory.QuantumLHL.le_two_mul_of_forall_hashing_bound (d ε : ℝ) (z : ℕ)
    (h : ∀ k : ℝ, d ≤ (1 / 2) * Real.sqrt ((z : ℝ) * 2 ^ (-k)) + 2 * ε) :
    d ≤ 2 * ε := by
  have hp := (tendsto_rpow_atBot_of_base_gt_one 2 one_lt_two).comp
    Filter.tendsto_neg_atTop_atBot
  have hs := (Real.continuous_sqrt.tendsto 0).comp
    (show Filter.Tendsto (fun k : ℝ => (z : ℝ) * 2 ^ (-k)) Filter.atTop (nhds 0) by
      simpa only [Function.comp_def, mul_zero] using hp.const_mul (z : ℝ))
  have hf := (hs.const_mul (1 / 2 : ℝ)).add_const (2 * ε)
  simpa using ge_of_tendsto' hf h

end InfoTheory.QuantumLHL.SeedKey

end -- noncomputable section
