import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDSingleCopyEnvelope

/-! # IIDChernoff Tail -/



noncomputable section

open scoped BigOperators

namespace InfoTheory.SmoothMinEntropy


/-- **Cramér–Chernoff per-term Markov bound.** For a nonpositive tilt `t ≤ 0` (so
`s = −t ≥ 0`), the over-threshold cap-indicator term `p · o` (active only on the
event `λ q < p`) is dominated by the tilted MGF term
`λ^t · (p^(1+(−t)) · q^(−(−t)) · o)`. On the cap event with `q > 0` this is
`1 ≤ (p/(λ q))^{−t}`. When `q = 0` the support hypothesis `hsupp` forces the
overlap `o` to vanish. `hsupp` is required only on the cap event, where `0 < p` is
forced (`0 ≤ λ q < p`); a zero block eigenvalue is genuinely possible in the
reference kernel, so the positivity guard is essential. -/
lemma chernoff_termwise_bound
    (p o lam q t : ℝ)
    (hp : 0 ≤ p) (ho : 0 ≤ o) (hlam : 0 < lam) (hq : 0 ≤ q)
    (ht : t ≤ 0) (hsupp : 0 < p → q = 0 → o = 0) :
    (if lam * q < p then p * o else 0)
      ≤ lam ^ t * (p ^ (1 + -t) * q ^ (-(-t)) * o) := by
  have hs : 0 ≤ -t := by linarith
  have hrhs_nn : 0 ≤ lam ^ t * (p ^ (1 + -t) * q ^ (-(-t)) * o) := by
    have h1 := Real.rpow_nonneg hlam.le t
    have h2 := Real.rpow_nonneg hp (1 + -t)
    have h3 := Real.rpow_nonneg hq (-(-t))
    positivity
  split_ifs with hcap
  · -- cap event `λ q < p`
    rcases eq_or_lt_of_le hq with hq0 | hqpos
    · -- reference kernel `q = 0`: `0 < p` is forced, so the support fact applies
      have hppos : 0 < p := lt_of_le_of_lt (mul_nonneg hlam.le hq) hcap
      rw [hsupp hppos hq0.symm]; simp
    · -- bulk `q > 0`
      have hlamq_pos : 0 < lam * q := mul_pos hlam hqpos
      have hppos : 0 < p := lt_trans hlamq_pos hcap
      have hpsplit : p ^ (1 + -t) = p * p ^ (-t) := by
        rw [Real.rpow_add hppos, Real.rpow_one]
      -- the tilted factor exceeds one
      have h1 : p ^ t ≤ lam ^ t * q ^ t := by
        have := Real.rpow_le_rpow_of_nonpos hlamq_pos (le_of_lt hcap) ht
        rwa [Real.mul_rpow hlam.le hq] at this
      have h2 : p ^ t * p ^ (-t) ≤ lam ^ t * q ^ t * p ^ (-t) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hp _)
      have h3 : p ^ t * p ^ (-t) = 1 := by
        rw [← Real.rpow_add hppos]; simp
      have key : (1 : ℝ) ≤ lam ^ t * p ^ (-t) * q ^ t := by
        have h2' : (1 : ℝ) ≤ lam ^ t * q ^ t * p ^ (-t) := h3 ▸ h2
        exact le_of_le_of_eq h2' (by ring)
      calc p * o = (p * o) * 1 := (mul_one _).symm
        _ ≤ (p * o) * (lam ^ t * p ^ (-t) * q ^ t) :=
              mul_le_mul_of_nonneg_left key (mul_nonneg hp ho)
        _ = lam ^ t * (p ^ (1 + -t) * q ^ (-(-t)) * o) := by
              rw [hpsplit, neg_neg]; ring
  · exact hrhs_nn

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
