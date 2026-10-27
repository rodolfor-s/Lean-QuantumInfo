import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IID.TensorPower
import QCryptLean.Math.Analysis.SqrtBounds
import QCryptLean.Math.Analysis.SqrtExp
import QCryptLean.Math.ClassicalEntropy.BinaryEntropy
import QCryptLean.QKD.BB84.SelectionData

/-!
# BB84 finite-size AEP penalty and leftover-hash arithmetic

`finiteSizePenalty` prices Alice's classical bit, the register to which the IID AEP applies:
`P(n, ε) = 2 log₂ 5 · n √((log₂(1/ε) + 1)/n)`. The scalar leftover-hash lemmas fund the PA output
from a key-rate condition.

Reference: Renner 2005, `cor:Hmincondrepclass`, at the classical-rank cap of two and the
own-marginal trace bound.
-/

open InfoTheory.SmoothMinEntropy
open Math.ClassicalEntropy
open scoped ComplexConjugate ComplexOrder

noncomputable section

namespace QKD.BB84.FiniteKey

/-!
## 0. Key-rate condition
-/

/-- The finite-size IID AEP penalty for Alice's classical `Z` bit.

The classical rank is at most two and the own-marginal trace factor is at most one, giving
`2 log₂(2 + 1 + 2) = 2 log₂ 5`. The noise factor is `√((log₂(1/ε) + 1)/n)`.
Reference: Renner 2005, `cor:Hmincondrepclass`. -/
noncomputable def finiteSizePenalty (n : ℕ) (ε : ℝ) : ℝ :=
  (n : ℝ) * (2 * Real.logb 2 5 * noiseFactor n ε)

/-- The BB84 finite-size penalty is nonnegative. -/
lemma finiteSizePenalty_nonneg (n : ℕ) (ε : ℝ) :
    0 ≤ finiteSizePenalty n ε := by
  unfold finiteSizePenalty noiseFactor
  exact mul_nonneg (Nat.cast_nonneg n)
    (mul_nonneg (mul_nonneg (by norm_num) (Real.logb_nonneg (by norm_num) (by norm_num)))
      (Real.sqrt_nonneg _))

/-- Rewrites the LHL power factor with an additive logarithmic loss as an exponential. -/
lemma real_lhl_power_factor_eq_exp
    (n ℓ : ℕ) (α loss : ℝ) :
    (((2 ^ ℓ : ℕ) : ℝ) *
        (2 : ℝ) ^ (-((n : ℝ) / Real.log 2 * α - loss / Real.log 2))) =
      Real.exp ((ℓ : ℝ) * Real.log 2 - (n : ℝ) * α + loss) := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog_ne : Real.log 2 ≠ 0 := ne_of_gt hlog
  calc
    (((2 ^ ℓ : ℕ) : ℝ) *
        (2 : ℝ) ^ (-((n : ℝ) / Real.log 2 * α - loss / Real.log 2)))
        = (2 : ℝ) ^ (ℓ : ℝ) *
            (2 : ℝ) ^ (-((n : ℝ) / Real.log 2 * α - loss / Real.log 2)) := by
          simp [Real.rpow_natCast]
    _ = Real.exp (Real.log 2 * (ℓ : ℝ)) *
          Real.exp (Real.log 2 * (-((n : ℝ) / Real.log 2 * α - loss / Real.log 2))) := by
          rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (ℓ : ℝ),
            Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)
              (-((n : ℝ) / Real.log 2 * α - loss / Real.log 2))]
    _ = Real.exp (Real.log 2 * (ℓ : ℝ) +
          Real.log 2 * (-((n : ℝ) / Real.log 2 * α - loss / Real.log 2))) := by
          rw [← Real.exp_add]
    _ = Real.exp ((ℓ : ℝ) * Real.log 2 - (n : ℝ) * α + loss) := by
          congr 1
          field_simp [hlog_ne]
          ring

/-- Real-variable LHL budget inequality with an additive logarithmic entropy loss. -/
lemma real_lhl_budget_at_key_rate_with_log_loss
    (n ℓ : ℕ) (α loss : ℝ)
    (hkey_rate_loss :
      2 * (ℓ : ℝ) * Real.log 2 + 2 * loss ≤ (n : ℝ) * α) :
    (1 / 2) * Real.sqrt
        (((2 ^ ℓ : ℕ) : ℝ) *
          (2 : ℝ) ^ (-((n : ℝ) / Real.log 2 * α - loss / Real.log 2))) ≤
      (1 / 2) * Real.exp (-(n : ℝ) / 4 * α) := by
  have h_exp_arg : (ℓ : ℝ) * Real.log 2 - (n : ℝ) * α + loss ≤
      -((n : ℝ) / 2 * α) := by
    linarith [hkey_rate_loss]
  have h_inside_le :
      (((2 ^ ℓ : ℕ) : ℝ) *
          (2 : ℝ) ^ (-((n : ℝ) / Real.log 2 * α - loss / Real.log 2))) ≤
        Real.exp (-((n : ℝ) / 2 * α)) := by
    rw [real_lhl_power_factor_eq_exp]
    exact Real.exp_le_exp.mpr h_exp_arg
  have h_sqrt_le :
      Real.sqrt
          (((2 ^ ℓ : ℕ) : ℝ) *
            (2 : ℝ) ^ (-((n : ℝ) / Real.log 2 * α - loss / Real.log 2))) ≤
        Real.exp (-(n : ℝ) / 4 * α) := by
    calc
      Real.sqrt
          (((2 ^ ℓ : ℕ) : ℝ) *
            (2 : ℝ) ^ (-((n : ℝ) / Real.log 2 * α - loss / Real.log 2)))
          ≤ Real.exp ((-((n : ℝ) / 2 * α)) / 2) :=
            Real.sqrt_le_exp_half_of_le_exp h_inside_le
      _ = Real.exp (-(n : ℝ) / 4 * α) := by
          congr 1
          ring
  exact mul_le_mul_of_nonneg_left h_sqrt_le (by norm_num)

/-- **Real-variable LHL budget inequality with a δ-scale privacy-amplification error**.

    The full-SP analogue of `real_lhl_budget_at_key_rate_with_log_loss`: instead of forcing the
    hashing term down to the fixed `½·exp(−nα/4)`, it caps it at the **free** `½·exp(−lpa)` for any
    `lpa` funded by the budget.  With `lpa = nα/4` and the doubled `2·loss` hypothesis this recovers
    the existing lemma; the δ-scale specialization uses `lpa = 2n·δ²` with the single-coefficient
    hypothesis `ℓ·log 2 + loss + 2·lpa ≤ n·α`. -/
lemma real_lhl_budget_with_pa_loss
    (n ℓ : ℕ) (α loss lpa : ℝ)
    (hkey :
      (ℓ : ℝ) * Real.log 2 + loss + 2 * lpa ≤ (n : ℝ) * α) :
    (1 / 2) * Real.sqrt
        (((2 ^ ℓ : ℕ) : ℝ) *
          (2 : ℝ) ^ (-((n : ℝ) / Real.log 2 * α - loss / Real.log 2))) ≤
      (1 / 2) * Real.exp (-lpa) := by
  have h_exp_arg : (ℓ : ℝ) * Real.log 2 - (n : ℝ) * α + loss ≤ -(2 * lpa) := by
    linarith [hkey]
  have h_inside_le :
      (((2 ^ ℓ : ℕ) : ℝ) *
          (2 : ℝ) ^ (-((n : ℝ) / Real.log 2 * α - loss / Real.log 2))) ≤
        Real.exp (-(2 * lpa)) := by
    rw [real_lhl_power_factor_eq_exp]
    exact Real.exp_le_exp.mpr h_exp_arg
  have h_sqrt_le :
      Real.sqrt
          (((2 ^ ℓ : ℕ) : ℝ) *
            (2 : ℝ) ^ (-((n : ℝ) / Real.log 2 * α - loss / Real.log 2))) ≤
        Real.exp (-lpa) := by
    calc
      Real.sqrt
          (((2 ^ ℓ : ℕ) : ℝ) *
            (2 : ℝ) ^ (-((n : ℝ) / Real.log 2 * α - loss / Real.log 2)))
          ≤ Real.exp ((-(2 * lpa)) / 2) :=
            Real.sqrt_le_exp_half_of_le_exp h_inside_le
      _ = Real.exp (-lpa) := by
          congr 1
          ring
  exact mul_le_mul_of_nonneg_left h_sqrt_le (by norm_num)

end QKD.BB84.FiniteKey

end -- noncomputable section
