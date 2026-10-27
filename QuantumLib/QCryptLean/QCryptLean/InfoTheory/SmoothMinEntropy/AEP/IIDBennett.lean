import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.BennettScalar
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IID.ErrorBudget
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IID.TensorPower

/-! # IIDBennett -/



noncomputable section

open scoped BigOperators

namespace InfoTheory.SmoothMinEntropy


/-- **The Bernstein exponent budget** `a = 4·log 2·noiseFactor²`.

`a/2 = 2·log 2·noiseFactor²` is the natural-log exponent per copy that Renner's discarded-mass
budget `ε²/4` allows: `n·(a/2)/log 2 = 2·n·noiseFactor² = 2·log₂(1/ε) + 2`. -/
noncomputable def bennettExponentBudget (n_copies : ℕ) (ε : ℝ) : ℝ :=
  4 * Real.log 2 * noiseFactor n_copies ε ^ 2

/-- **The Bennett tilt width** `w = bennettFactor a`, the unique `w ≥ 0` with
`3w²/(6 + 2w) = a/2`.  Renner's clamped tilt sits at width `min(2·noiseFactor, log 2)`. -/
noncomputable def bennettTiltWidth (n_copies : ℕ) (ε : ℝ) : ℝ :=
  bennettFactor (bennettExponentBudget n_copies ε)

/-- **The Bennett regime** `a ≤ 3/4`, equivalently `w ≤ 1`, equivalently
`n_copies ≥ (16·log 2/3)·(log₂(1/ε) + 1)`.

This is exactly the admissibility condition `v⋆ = log(1 + w) ≤ log 2` of Renner's `lem:rtbound`.
Renner's own `AEP.IID.LargeBlockRegime` is `noiseFactor ≤ (2 − log 2)/2`, i.e.
`n_copies ≥ 2.3421…·(log₂(1/ε) + 1)`. -/
def AEP.IID.BennettRegime (n_copies : ℕ) (ε : ℝ) : Prop :=
  bennettExponentBudget n_copies ε ≤ 3 / 4

/-- **The Bennett discarded-mass tail bound** `2^(−n·(3w²/(6 + 2w))/log 2)`.

The incumbent `AEP.IID.rtErrorBound` is `2^(−n·δ²/(2·(log₂ μ)²)) = 2^(−n·w²/2)` at Renner's
width; here the Gaussian exponent `w²/2` is replaced by Bernstein's `3w²/(6 + 2w)/log 2`, which
is what the exact tilt actually delivers.  Independent of `ρ`, `σ` and the witness. -/
noncomputable def AEP.IID.bennettRtErrorBound (n_copies : ℕ) (ε : ℝ) : ℝ :=
  (2 : ℝ) ^ (-(n_copies : ℝ)
    * (3 * bennettTiltWidth n_copies ε ^ 2 / (6 + 2 * bennettTiltWidth n_copies ε))
    / Real.log 2)

lemma bennettExponentBudget_nonneg (n_copies : ℕ) (ε : ℝ) :
    0 ≤ bennettExponentBudget n_copies ε := by
  unfold bennettExponentBudget
  have : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  positivity

lemma bennettTiltWidth_nonneg (n_copies : ℕ) (ε : ℝ) :
    0 ≤ bennettTiltWidth n_copies ε :=
  bennettFactor_nonneg (bennettExponentBudget_nonneg n_copies ε)

/-- On the Bennett regime the tilt width is at most `1`, i.e. `v⋆ ≤ log 2`. -/
lemma bennettTiltWidth_le_one {n_copies : ℕ} {ε : ℝ}
    (hregime : AEP.IID.BennettRegime n_copies ε) :
    bennettTiltWidth n_copies ε ≤ 1 :=
  bennettFactor_le_one_of_le_three_quarters (bennettExponentBudget_nonneg n_copies ε) hregime

/-- Off the Bennett regime the tilt width is at least `1`. -/
lemma one_le_bennettTiltWidth {n_copies : ℕ} {ε : ℝ}
    (hsmall : ¬ AEP.IID.BennettRegime n_copies ε) :
    1 ≤ bennettTiltWidth n_copies ε := by
  unfold AEP.IID.BennettRegime at hsmall
  push Not at hsmall
  exact one_le_bennettFactor_of_three_quarters_le hsmall.le

/-- **The Bennett tail bound meets Renner's discarded-mass budget.**

`AEP.IID.bennettRtErrorBound n_copies ε ≤ ε²/2` for `ε ∈ (0,1)` and `n_copies ≥ 1`.

`bennettTiltWidth` is by construction the root of `3w²/(6 + 2w) = a/2` with
`a = 4·log 2·noiseFactor²`, so the exponent is `−n·(a/2)/log 2 = −2·n·noiseFactor² =
−2·log₂(1/ε) − 2` and the bound evaluates to `ε²/4`, exactly as the incumbent
`AEP.IID.rtExponentToSmoothingBudget_of_bitSpectralSetup` does.  The `n_copies`-dependence cancels,
so no
finite-size regime hypothesis is needed. -/
theorem AEP.IID.bennettRtErrorBound_le_smoothingTraceBudget
    {n_copies : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε_lt_one : ε < 1) (hn : 1 ≤ (n_copies : ℝ)) :
    AEP.IID.bennettRtErrorBound n_copies ε ≤ AEP.IID.smoothingTraceBudget ε := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hn_pos : (0 : ℝ) < (n_copies : ℝ) := by linarith
  have hbern := three_mul_sq_div_bennettFactor (bennettExponentBudget_nonneg n_copies ε)
  -- `3w²/(6 + 2w) = a/2 = 2·log 2·noiseFactor²`
  have hbern' : 3 * bennettTiltWidth n_copies ε ^ 2 / (6 + 2 * bennettTiltWidth n_copies ε)
      = 2 * Real.log 2 * noiseFactor n_copies ε ^ 2 := by
    rw [bennettTiltWidth, hbern, bennettExponentBudget]; ring
  -- `noiseFactor² = (log₂(1/ε) + 1)/n`
  have hnf_sq : noiseFactor n_copies ε ^ 2 = (Real.logb 2 ε⁻¹ + 1) / (n_copies : ℝ) := by
    have hlogb_inv_nonneg : 0 ≤ Real.logb 2 ε⁻¹ :=
      Real.logb_nonneg (by norm_num)
        (by rw [le_inv_comm₀ (by norm_num) hε]; linarith)
    unfold noiseFactor
    rw [Real.sq_sqrt]; positivity
  have hexp_val : -(n_copies : ℝ)
        * (3 * bennettTiltWidth n_copies ε ^ 2 / (6 + 2 * bennettTiltWidth n_copies ε))
        / Real.log 2
      = -(2 * Real.logb 2 ε⁻¹) + -(2 : ℝ) := by
    rw [hbern', hnf_sq]
    field_simp
    ring
  unfold AEP.IID.bennettRtErrorBound AEP.IID.smoothingTraceBudget
  rw [hexp_val, Real.rpow_add (by norm_num)]
  have hε_term : (2 : ℝ) ^ (-(2 * Real.logb 2 ε⁻¹)) = ε ^ 2 := by
    rw [Real.logb_inv, show -(2 * -Real.logb 2 ε) = Real.logb 2 ε * 2 by ring,
      Real.rpow_mul (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) hε,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hε_term]
  have htwopow_eq : (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 := by
    rw [show (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
    norm_num
  have hε_sq_nonneg : 0 ≤ ε ^ 2 := sq_nonneg ε
  calc ε ^ 2 * (2 : ℝ) ^ (-(2 : ℝ))
      = ε ^ 2 * (1 / 4) := by rw [htwopow_eq]
    _ ≤ ε ^ 2 * (1 / 2) := by
        exact mul_le_mul_of_nonneg_left (by norm_num) hε_sq_nonneg
    _ = ε ^ 2 / 2 := by ring


/-- **The Bennett remainder at the exact tilt.** At `v = log(1 + w)`,

`φ(v) − v·w + 3w²/(6 + 2w) ≤ 0`,  `φ(v) = e^v − v − 1`,

for every `w ≥ 0`.  The first two terms sum to `−h(w)` **identically**
(`bennett_tilt_identity`), and `h(w) ≥ 3w²/(6 + 2w)` (`three_mul_sq_div_le_bennettH`).

The quadratic analogue is `quadratic_remainder_nonpos_of_eq_min`, which balances the
envelope's `(1/log 2 − 1/2)·v²` against `w²/2` at the clamped tilt. -/
private lemma bennett_remainder_nonpos {w : ℝ} (hw : 0 ≤ w) :
    Real.exp (Real.log (1 + w)) - Real.log (1 + w) - 1 - Real.log (1 + w) * w
        + 3 * w ^ 2 / (6 + 2 * w) ≤ 0 := by
  rw [bennett_tilt_identity (by linarith : (-1 : ℝ) < w)]
  linarith [three_mul_sq_div_le_bennettH hw]


end InfoTheory.SmoothMinEntropy

end -- noncomputable section
