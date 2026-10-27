import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.QKD.BB84.FiniteKey.Budgets.SmoothEntropyBound
import QCryptLean.QKD.BB84.FiniteKey.KeyRate.AEP
import QCryptLean.QKD.BB84.SelectionData

/-!
# AEP component entropy levels

The IID AEP entropy level at fixed and free phase-error deviations, and positivity of the key-round
count.
-/


noncomputable section

open scoped BigOperators
open Math.ClassicalEntropy

namespace QKD.BB84.FiniteKey

/-- The component entropy floor `(n_K / log 2) * (log 2 - h(Q + 2δ)) - P(n_K, ε)`.
Here `n_K = n - m` and `P` is the bit-register IID AEP penalty. Components are compared with
their own quantum marginals, so this floor pays no reference-change logarithm. The separate
purifier adjunction costs `2 log₂ C(n+15,15)`.

References: Renner 2005, `cor:Hmincondrepclass`; Nahar et al. 2024, arXiv:2403.11851,
Appendix B, `eq:boundingsmoothedmin` and `eq:splittingoffV`. -/
noncomputable def pairedHaarWindowFloorLevel (n m : ℕ) (Q δ εTensor : ℝ) : ℝ :=
  (keyRounds n m : ℝ) / Real.log 2 *
      (Real.log 2 - binaryEntropy (Q + 2 * δ)) -
    finiteSizePenalty (keyRounds n m) εTensor

/-- The component entropy floor `(n_K / log 2) * (log 2 - h(Q + δ + dev)) - P(n_K, ε)`.
Here `n_K = n - m` and `P` is the bit-register IID AEP penalty. Components are compared with
their own quantum marginals, so this floor pays no reference-change logarithm. The separate
purifier adjunction costs `2 log₂ C(n+15,15)`.

References: Renner 2005, `cor:Hmincondrepclass`; Nahar et al. 2024, arXiv:2403.11851,
Appendix B, `eq:boundingsmoothedmin` and `eq:splittingoffV`. -/
noncomputable def pairedHaarFloorLevel (n m : ℕ) (Q δ dev εTensor : ℝ) : ℝ :=
  (keyRounds n m : ℝ) / Real.log 2 *
      (Real.log 2 - binaryEntropy (Q + δ + dev)) -
    finiteSizePenalty (keyRounds n m) εTensor

/-- A positive component entropy floor requires at least one key round. -/
lemma lt_of_pairedHaarFloorLevel_pos {n m : ℕ} {Q δ dev ε : ℝ}
    (h : 0 < pairedHaarFloorLevel n m Q δ dev ε) : m < n := by
  by_contra hmn
  have hzero : keyRounds n m = 0 := Nat.sub_eq_zero_of_le (by omega)
  simp [pairedHaarFloorLevel, hzero, finiteSizePenalty] at h

/-- The carried floor level is the free-deviation level at `dev = δ` (up to `δ + δ = 2 * δ`). -/
lemma pairedHaarFloorLevel_self (n m : ℕ) (Q δ εTensor : ℝ) :
    pairedHaarFloorLevel n m Q δ δ εTensor = pairedHaarWindowFloorLevel n m Q δ εTensor := by
  unfold pairedHaarFloorLevel pairedHaarWindowFloorLevel
  rw [add_assoc, two_mul]

end QKD.BB84.FiniteKey

end
