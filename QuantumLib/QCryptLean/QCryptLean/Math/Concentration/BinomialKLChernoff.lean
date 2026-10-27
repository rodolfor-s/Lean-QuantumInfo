import QCryptLean.Math.Concentration.BernoulliKL
import QCryptLean.Math.Concentration.BinomialKLTail
import QCryptLean.Math.Concentration.BinomialPassSum

/-!
# Binomial KL-rate Chernoff bounds for the PE-pass mass

This file packages the (Kullback–Leibler rate) Chernoff tail bounds of
`Math.Concentration.BinomialKLTail` into bounds on the PE-pass mass `binomialPassSum`
(`Math.Concentration.BinomialPassSum.binomialPassSum`), as opposed to the weaker Hoeffding
rate `exp(-2 m ε²)` available in `Math.Concentration.BinomialHoeffding`.

The classical large-deviations statement is: for `m` IID Bernoulli(`p`) trials and a
threshold `a < p`, the probability of an empirical fraction `k/m ≤ a` is at most
`exp(-m · klBer a b)` for any reference rate `b` with `a < b ≤ p`, where `klBer` is the
Bernoulli KL divergence (`Math.Concentration.BernoulliKL.klBer`).  This is the
method-of-types / Chernoff exponent (Cover–Thomas, *Elements of Information Theory*, §11.1).

## Main statements

- `binomialPassSum_le_exp_neg_mul_klBer`: the PE-pass binomial mass at true rate `p` outside the
  band, with margin to a reference rate `b`, is bounded by `exp(-m · klBer (Q+δ) b)`.
- `one_sub_binomialPassSum_le_exp_add_exp`: the band-failure mass `1 - binomialPassSum m Q δ
q`
  is at most `exp(-m · klBer (Q+δ) q) + exp(-m · klBer (Q-δ) q)` for `Q - δ < q < Q + δ`
  (both one-sided KL exponents, no margin inside the band).

References: standard Chernoff/large-deviations exponent for the binomial lower tail
(Cover–Thomas, *Elements of Information Theory*, §11.1); Renner (2005),
`arXiv:quant-ph/0512258v2`, §5 (parameter estimation).
-/

open scoped BigOperators
open Real

namespace Math.Concentration.BinomialKLChernoff

/-- **KL-rate Chernoff bound on the binomial PE-pass mass.**

If the true per-trial rate `p ∈ [0, 1]` lies at or above a reference rate `b` strictly above
the upper edge of the PE-pass band (`Q + δ < b ≤ p`, `b < 1`), then the PE-pass mass
`binomialPassSum m Q δ p` is at most the KL-rate Chernoff exponent `exp(-m · klBer (Q+δ) b)`.

The PE-band sum is termwise dominated by the lower-tail sum at threshold `Q + δ`, because
`|k/m - Q| ≤ δ ⟹ k/m ≤ Q + δ`; the conclusion is then
`BinomialKLTail.lowerTail_le_exp_neg_mul_klBer`
(which also covers the degenerate `Q + δ ≤ 0` regime).  Sharper analogue of
`Math.Concentration.BinomialPassSum.binomialPassSum_le_hoeffding`. -/
theorem binomialPassSum_le_exp_neg_mul_klBer (m : ℕ) (Q δ b p : ℝ)
    (hb : Q + δ < b) (hbp : b ≤ p) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hb1 : b < 1) :
    Math.Concentration.BinomialPassSum.binomialPassSum m Q δ p ≤
      Real.exp (-(m : ℝ) * Math.Concentration.BernoulliKL.klBer (Q + δ) b) := by
  classical
  unfold Math.Concentration.BinomialPassSum.binomialPassSum
  have hp_nonneg : 0 ≤ p := hp0
  -- The PE-band sum is termwise dominated by the lower-tail sum at threshold `Q + δ`.
  have hdom :
      (∑ k ∈ Finset.range (m + 1),
          if |(k : ℝ) / m - Q| ≤ δ then
            (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)
          else 0) ≤
        ∑ k ∈ Finset.range (m + 1),
          if ((k : ℝ) / m ≤ Q + δ) then
            (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)
          else 0 := by
    refine Finset.sum_le_sum ?_
    intro k _hk
    have hw_nonneg : 0 ≤ (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) := by
      have hpk : 0 ≤ p ^ k := pow_nonneg hp_nonneg _
      have h1pk : 0 ≤ (1 - p) ^ (m - k) := pow_nonneg (by linarith) _
      positivity
    by_cases hband : |(k : ℝ) / m - Q| ≤ δ
    · rw [ite_eq_left hband]
      have hle : (k : ℝ) / m ≤ Q + δ := by
        have h1 : (k : ℝ) / m - Q ≤ δ := (abs_le.mp hband).2
        linarith
      rw [ite_eq_left hle]
    · rw [ite_eq_right hband]
      by_cases hlt : (k : ℝ) / m ≤ Q + δ
      · rw [ite_eq_left hlt]; exact hw_nonneg
      · rw [ite_eq_right hlt]
  exact hdom.trans (BinomialKLTail.lowerTail_le_exp_neg_mul_klBer m p (Q + δ) b hb hbp hp1 hb1)

/-- **KL-rate Chernoff bound on the two-sided PE-band failure mass.**

For `m : ℕ` trials at true rate `q ∈ (0, 1)` lying strictly inside the PE band
(`Q - δ < q < Q + δ`), the failure mass `1 - binomialPassSum m Q δ q` — the binomial mass outside
the band `Q - δ ≤ k/m ≤ Q + δ` — is at most the sum of the two one-sided KL-rate Chernoff
exponents `exp(-m · klBer (Q+δ) q) + exp(-m · klBer (Q-δ) q)`.  No margin is needed: the total
binomial mass is `1` as the algebraic identity `(p + (1-p))^m = 1`, so the failure mass splits
exactly into the mass of `k/m < Q - δ` plus that of `k/m > Q + δ`, each dominated by the
corresponding one-sided tail; degenerate band edges (`Q - δ ≤ 0`, `Q + δ ≥ 1`) need no separate
treatment because the corresponding tail sum is then empty and `Real.exp` is positive.

Sharper analogue of
`Math.Concentration.BinomialPassSum.one_sub_binomialPassSum_le_two_hoeffding_of_mem_band`
(which needs a margin `η` inside the band and prices the tails at the Hoeffding rate). -/
theorem one_sub_binomialPassSum_le_exp_add_exp (m : ℕ) (Q δ q : ℝ)
    (hq0 : 0 < q) (hq1 : q < 1) (hlo : Q - δ < q) (hhi : q < Q + δ) :
    1 - Math.Concentration.BinomialPassSum.binomialPassSum m Q δ q ≤
      Real.exp (-(m : ℝ) * Math.Concentration.BernoulliKL.klBer (Q + δ) q) +
        Real.exp (-(m : ℝ) * Math.Concentration.BernoulliKL.klBer (Q - δ) q) := by
  classical
  -- Total binomial mass is `1` (the algebraic identity `(q + (1-q))^m = 1`).
  have htotal : (∑ k ∈ Finset.range (m + 1),
      (m.choose k : ℝ) * q ^ k * (1 - q) ^ (m - k)) = 1 := by
    simpa using BinomialKLTail.binomial_tilt_sum_eq q 1 m
  -- Termwise: in-band counts are carried by the pass sum; a count failing the band lies in the
  -- lower tail (`k/m ≤ Q - δ`) or the upper tail (`Q + δ ≤ k/m`).
  have hsplit : (∑ k ∈ Finset.range (m + 1),
      (m.choose k : ℝ) * q ^ k * (1 - q) ^ (m - k))
      ≤ Math.Concentration.BinomialPassSum.binomialPassSum m Q δ q
        + (∑ k ∈ Finset.range (m + 1),
            if (k : ℝ) / m ≤ Q - δ then
              (m.choose k : ℝ) * q ^ k * (1 - q) ^ (m - k)
            else 0)
        + (∑ k ∈ Finset.range (m + 1),
            if Q + δ ≤ (k : ℝ) / m then
              (m.choose k : ℝ) * q ^ k * (1 - q) ^ (m - k)
            else 0) := by
    unfold Math.Concentration.BinomialPassSum.binomialPassSum
    -- Combine the three sums into one, to argue termwise.
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    -- `positivity` cannot use `hq0`/`hq1`; spell out nonnegativity from the hypotheses.
    have hwpos : 0 ≤ (m.choose k : ℝ) * q ^ k * (1 - q) ^ (m - k) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq0.le _))
        (pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - q) _)
    by_cases hband : |(k : ℝ) / m - Q| ≤ δ
    · rw [ite_eq_left hband]
      split_ifs <;> linarith [hwpos]
    · rw [ite_eq_right hband]
      -- Outside the band means `k/m < Q - δ` or `Q + δ < k/m` (valid for every sign of `δ`).
      have hout : (k : ℝ) / m < Q - δ ∨ Q + δ < (k : ℝ) / m := by
        by_contra hcon
        push Not at hcon
        exact hband (abs_le.mpr ⟨by linarith, by linarith⟩)
      rcases hout with hlow | hhigh
      · rw [ite_eq_left (by linarith : (k : ℝ) / m ≤ Q - δ)]
        split_ifs <;> linarith [hwpos]
      · rw [ite_eq_right (by linarith : ¬ ((k : ℝ) / m ≤ Q - δ)),
          ite_eq_left (by linarith : Q + δ ≤ (k : ℝ) / m)]
        linarith [hwpos]
  -- The two tails are priced at the KL rate by the one-sided bounds.
  have hlow := BinomialKLTail.lowerTail_le_exp_neg_mul_klBer m q (Q - δ) q hlo (le_refl q) hq1.le
    hq1
  have hhigh := BinomialKLTail.upperTail_le_exp_neg_mul_klBer m q (Q + δ) q hhi.le (le_refl q)
    hq0.le hq0
  linarith [hsplit, htotal, hlow, hhigh]

end Math.Concentration.BinomialKLChernoff
