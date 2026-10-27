import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Tensor Power -/


noncomputable section

open scoped BigOperators


/-- The library's shared noise factor for the Renner AEP correction:
`√((log₂(1/ε) + 1) / n_copies)` (Renner 2005, arXiv:quant-ph/0512258v2,
`main.tex:6288`–`:6289`). The printed theorem `thm:Hmincondrep` at `:4572`
instead places `+1` outside the fraction. The rate interpretation requires `n_copies > 0`
and `0 < ε < 1`; the scalar formula is total, using Mathlib's conventions for `Real.logb`,
inversion and square roots. -/
noncomputable def InfoTheory.SmoothMinEntropy.noiseFactor
    (n_copies : ℕ) (ε : ℝ) : ℝ :=
  Real.sqrt ((Real.logb 2 ε⁻¹ + 1) / (n_copies : ℝ))


end
