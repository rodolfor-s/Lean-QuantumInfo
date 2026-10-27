import QCryptLean.Math.Concentration.BernoulliKL
import QCryptLean.Math.Concentration.BinomialKLChernoff
import QCryptLean.Math.Concentration.HypergeometricTail.Basic
import QCryptLean.Math.Concentration.HypergeometricTail.UncenteredMGF

/-!
# Hypergeometric (without-replacement) KL-rate Chernoff lower tail

This file states the **without-replacement (hypergeometric) lower-tail bound at the
Kullback–Leibler rate**: for an `m`-of-`N` sample drawn uniformly without replacement from a
population with `K` successes, the probability that the sample shows an empirical success
fraction `k/m ≤ a` — when the population fraction `K/N` sits at or above a reference tilt
`b > a` — is at most `exp(-m · klBer a b)`.

This is the without-replacement (WOR) analogue of the with-replacement (binomial)
`Math.Concentration.BinomialKLChernoff.binomialPassSum_le_exp_neg_mul_klBer`, with the binomial
weight
`C(m,k)·p^k·(1-p)^(m-k)` replaced by
the hypergeometric choose weight `chooseWeight N m K k = C(K,k)·C(N-K,m-k)`
(`HypergeometricTail.chooseWeight`) normalized by `C(N,m)`, and the fixed rate
`p` replaced by the population fraction `K/N`.

## Argument (Hoeffding 1963, Theorem 4; Cover–Thomas §11.1)

The bound is obtained in two stages:

1. **Chernoff tilt reduction** (reusing the binomial algebra
   `Math.Concentration.BinomialKLTail.lowerTail_le_exp_neg_mul_klBer_of_pos`,
   verbatim on the fixed-rate RHS): trade the lower-tail indicator for the exponential weight and
   optimise the tilt at the KL optimum, reducing to the un-centered WOR moment-generating function
   at tilt `c = e^{-s} ∈ (0,1)`.

2. **Without-replacement convex domination** (Hoeffding 1963, Theorem 4): the un-centered WOR MGF
   is dominated by the with-replacement (binomial) MGF at the same population rate `p = K/N`,
   ```
   (∑_k chooseWeight N m K k · c^k) / C(N,m)  ≤  ((K/N)·c + (N-K)/N)^m,
   ```
   after which the reference-rate monotonicity `b ≤ K/N` and the KL exponent identity give
   `exp(-m · klBer a b)`.

## The domination step

Stage 2 proves an un-centered, fixed-rate without-replacement
moment-generating-function domination `hypergeometricPowMGF N m K c ≤ (gBase N K c) ^ m`
(`hypergeometricPowMGF_le_gBase_pow`, `UncenteredMGF.lean`), proved by strong induction on the
sample size
via the per-step comparison `weighted_gBase_pow_le` rather than a general negative-association or
convex-order argument.

References: Hoeffding (1963), *Probability inequalities for sums of bounded random variables*,
J. Amer. Statist. Assoc. 58, Theorem 4 (sampling without replacement, convex domination);
Cover–Thomas, *Elements of Information Theory*, §11.1 (method-of-types Chernoff exponent);
Renner (2005), `arXiv:quant-ph/0512258v2`, §5 (parameter estimation).
-/

open scoped BigOperators
open Real

namespace Math.Concentration.HypergeometricTail

/-- **WOR lower-tail Chernoff sum at an explicit tilt.**  Mirror of
`BinomialKLTail.lowerTail_le_tilt` with the hypergeometric choose weights.  For `s > 0`,
tilt `c = exp(-s)`, the normalized lower-tail weight is bounded by
`exp(s·m·a) · hypergeometricPowMGF N m K c`. -/
lemma worLowerTail_le_tilt {N m K : ℕ} (hmN : m ≤ N) (hm : m ≠ 0) (a s : ℝ) (hs : 0 < s) :
    (∑ k ∈ Finset.range (m + 1),
        if (k : ℝ) / m ≤ a then chooseWeight N m K k else 0) / (N.choose m : ℝ) ≤
      Real.exp (s * ((m : ℝ) * a)) * hypergeometricPowMGF N m K (Real.exp (-s)) := by
  classical
  have hden_pos : 0 < (N.choose m : ℝ) := by exact_mod_cast Nat.choose_pos hmN
  set c := Real.exp (-s) with hc
  have hmpos : 0 < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have hnum :
      (∑ k ∈ Finset.range (m + 1), if (k : ℝ) / m ≤ a then chooseWeight N m K k else 0) ≤
        Real.exp (s * ((m : ℝ) * a)) *
          ∑ k ∈ Finset.range (m + 1), chooseWeight N m K k * c ^ k := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _hk
    have hw_nn : 0 ≤ chooseWeight N m K k := chooseWeight_nonneg N m K k
    have hexp_k : Real.exp (s * ((m : ℝ) * a)) * c ^ k = Real.exp (s * ((m : ℝ) * a - k)) := by
      rw [hc, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1; ring
    by_cases hbad : (k : ℝ) / m ≤ a
    · rw [ite_eq_left hbad]
      have hk_le : (k : ℝ) ≤ (m : ℝ) * a := by rw [div_le_iff₀ hmpos] at hbad; linarith
      calc
        chooseWeight N m K k = chooseWeight N m K k * 1 := (mul_one _).symm
        _ ≤ chooseWeight N m K k * Real.exp (s * ((m : ℝ) * a - k)) :=
              mul_le_mul_of_nonneg_left
                (Real.one_le_exp (mul_nonneg hs.le (by linarith))) hw_nn
        _ = Real.exp (s * ((m : ℝ) * a)) * (chooseWeight N m K k * c ^ k) := by
              rw [← hexp_k]; ring
    · rw [ite_eq_right hbad]
      have : 0 ≤ Real.exp (s * ((m : ℝ) * a)) * (chooseWeight N m K k * c ^ k) :=
        mul_nonneg (Real.exp_pos _).le (mul_nonneg hw_nn (pow_nonneg (Real.exp_pos _).le k))
      exact this
  rw [hypergeometricPowMGF, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hnum hden_pos.le

/-- **Exponent identity at the KL-optimal tilt.**  With `s = log(b(1-a)/(a(1-b)))` and
`c = a(1-b)/(b(1-a)) = exp(-s)`, the tilted fixed-rate base collapses to the KL exponent:
`exp(s·m·a) · (b·c + (1-b))^m = exp(-m·klBer a b)`.  This is the `Real.log` algebra of
`BinomialKLTail.lowerTail_le_exp_neg_mul_klBer_of_pos`, factored out for reuse on the WOR RHS. -/
private lemma exp_tilt_base_eq (m : ℕ) (a b s c : ℝ)
    (ha : 0 < a) (hab : a < b) (hb1 : b < 1)
    (hs : s = Real.log (b * (1 - a) / (a * (1 - b))))
    (hc : c = a * (1 - b) / (b * (1 - a))) :
    Real.exp (s * ((m : ℝ) * a)) * (b * c + (1 - b)) ^ m
      = Real.exp (-(m : ℝ) * Math.Concentration.BernoulliKL.klBer a b) := by
  have hb_pos : 0 < b := ha.trans hab
  have h1a_pos : 0 < 1 - a := by linarith
  have h1b_pos : 0 < 1 - b := by linarith
  have hbac_pos : 0 < b * (1 - a) := by positivity
  have habc_pos : 0 < a * (1 - b) := by positivity
  have hbc : b * c + (1 - b) = (1 - b) / (1 - a) := by rw [hc]; field_simp; ring
  rw [hbc]
  have hratio_pos : 0 < (1 - b) / (1 - a) := by positivity
  rw [show ((1 - b) / (1 - a)) ^ m = Real.exp ((m : ℝ) * Real.log ((1 - b) / (1 - a))) by
        rw [Real.exp_nat_mul, Real.exp_log hratio_pos]]
  rw [← Real.exp_add]
  congr 1
  rw [hs, Math.Concentration.BernoulliKL.klBer]
  rw [Real.log_div hbac_pos.ne' habc_pos.ne', Real.log_div h1b_pos.ne' h1a_pos.ne',
      Real.log_mul hb_pos.ne' h1a_pos.ne', Real.log_mul ha.ne' h1b_pos.ne',
      Real.log_div ha.ne' hb_pos.ne', Real.log_div h1a_pos.ne' h1b_pos.ne']
  ring

/-- **Hypergeometric (without-replacement) KL-rate Chernoff lower tail.**

For an `m`-of-`N` sample drawn uniformly without replacement from a population with `K` successes
(`K ≤ N`, `m ≤ N`, `m ≠ 0`), if the population fraction sits at or above a reference tilt
`b` strictly above the empirical threshold `a` (`a < b ≤ K/N`, `b < 1`), then the normalized
lower-tail weight `(∑_{k/m ≤ a} chooseWeight N m K k) / C(N,m)` is bounded by the KL-rate
Chernoff exponent `exp(-m · klBer a b)`.

The load-bearing hypothesis is `hbK : b ≤ K/N` — the population success rate is at or above the
tilt point `b`, which is strictly above the empirical threshold `a`. This is the WOR analogue of
the with-replacement `Math.Concentration.BinomialKLChernoff.binomialPassSum_le_exp_neg_mul_klBer`.

The proof reduces, via the KL tilt (`worLowerTail_le_tilt`), to the Hoeffding 1963
without-replacement convex domination of the un-centered hypergeometric MGF by the fixed-rate
binomial MGF at rate `K/N` (`hypergeometricPowMGF_le_gBase_pow`, in `UncenteredMGF.lean`);
reference-rate
monotonicity `b ≤ K/N` and the exponent identity `exp_tilt_base_eq` then deliver the KL rate.
The degenerate thresholds `a ≤ 0` are handled directly (empty lower-tail sum / the `k = 0` term,
the latter using the `c = 0` case of the domination). -/
theorem hypergeometricPassSum_le_exp_neg_mul_klBer (N m K : ℕ) (a b : ℝ)
    (hKN : K ≤ N) (hmN : m ≤ N) (hm : m ≠ 0)
    (ha : a < b) (hbK : b ≤ (K : ℝ) / N) (hb1 : b < 1) :
    (∑ k ∈ Finset.range (m + 1),
        if (k : ℝ) / m ≤ a then
          Math.Concentration.HypergeometricTail.chooseWeight N m K k
        else 0) / (N.choose m : ℝ) ≤
      Real.exp (-(m : ℝ) * Math.Concentration.BernoulliKL.klBer a b) := by
  classical
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm
  have hN_pos : 0 < (N : ℝ) := Nat.cast_pos.mpr (hmpos.trans_le hmN)
  have hN_ne : (N : ℝ) ≠ 0 := hN_pos.ne'
  have h1b_pos : 0 < 1 - b := sub_pos.mpr hb1
  rcases lt_trichotomy a 0 with ha_neg | ha_zero | ha_pos
  · -- `a < 0`: the lower-tail sum is empty, since every `k / m ≥ 0 > a`.
    have hzero :
        (∑ k ∈ Finset.range (m + 1),
            if (k : ℝ) / m ≤ a then chooseWeight N m K k else 0) = 0 :=
      Finset.sum_eq_zero fun k _ => ite_eq_right (not_le.mpr (ha_neg.trans_le (by positivity)))
    rw [hzero, zero_div]
    exact (Real.exp_pos _).le
  · -- `a = 0`: only `k = 0` passes; use the `c = 0` domination.
    subst ha_zero
    have h0_mem : 0 ∈ Finset.range (m + 1) := Finset.mem_range.mpr m.succ_pos
    have hLHS :
        (∑ k ∈ Finset.range (m + 1),
            if (k : ℝ) / m ≤ 0 then chooseWeight N m K k else 0) = chooseWeight N m K 0 := by
      rw [Finset.sum_eq_single_of_mem 0 h0_mem, ite_eq_left (by rw [Nat.cast_zero, zero_div])]
      intro k _hk hk0
      have hk_pos : (0 : ℝ) < k / m := by positivity
      exact ite_eq_right (not_le.mpr hk_pos)
    have hworZero : hypergeometricPowMGF N m K 0 = chooseWeight N m K 0 / (N.choose m : ℝ) := by
      rw [hypergeometricPowMGF, Finset.sum_eq_single_of_mem 0 h0_mem, pow_zero, mul_one]
      intro k _hk hk0
      rw [zero_pow hk0, mul_zero]
    rw [hLHS, ← hworZero]
    refine (hypergeometricPowMGF_le_gBase_pow hKN hmN (le_refl (0 : ℝ)) zero_le_one).trans ?_
    -- `gBase N K 0 = (N - K)/N = 1 - K/N ≤ 1 - b`, and `exp(-m·klBer 0 b) = (1 - b)^m`.
    have hGbase0 : gBase N K 0 = ((N - K : ℕ) : ℝ) / N := by rw [gBase, mul_zero, zero_add]
    have hrate : ((N - K : ℕ) : ℝ) / N ≤ 1 - b := by
      rw [Nat.cast_sub hKN, sub_div, div_self hN_ne]
      exact sub_le_sub_left hbK 1
    have hrate_nn : 0 ≤ ((N - K : ℕ) : ℝ) / N :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg N)
    have hkl0 : Math.Concentration.BernoulliKL.klBer 0 b = -Real.log (1 - b) := by
      rw [Math.Concentration.BernoulliKL.klBer]; simp
    rw [hGbase0, hkl0, neg_mul_neg, Real.exp_nat_mul, Real.exp_log h1b_pos]
    exact pow_le_pow_left₀ hrate_nn hrate m
  · -- `0 < a`: the calculus-free tilt + domination argument.
    set c := a * (1 - b) / (b * (1 - a)) with hc_def
    have hb_pos : 0 < b := ha_pos.trans ha
    have h1a_pos : 0 < 1 - a := sub_pos.mpr (ha.trans hb1)
    have hbac_pos : 0 < b * (1 - a) := mul_pos hb_pos h1a_pos
    have hc_pos : 0 < c := div_pos (mul_pos ha_pos h1b_pos) hbac_pos
    -- `c < 1` is `a(1-b) < b(1-a)`, i.e. `a < b`.
    have hc_lt_one : c < 1 := by
      rw [hc_def, div_lt_one hbac_pos]
      linear_combination ha
    set s := Real.log (b * (1 - a) / (a * (1 - b))) with hs_def
    have hinv : b * (1 - a) / (a * (1 - b)) = c⁻¹ := by rw [hc_def, inv_div]
    have hexp_neg_s : Real.exp (-s) = c := by
      rw [hs_def, hinv, Real.log_inv, neg_neg, Real.exp_log hc_pos]
    have hs_pos : 0 < s := by
      rw [hs_def, hinv]
      exact Real.log_pos (one_lt_inv_iff₀.mpr ⟨hc_pos, hc_lt_one⟩)
    have htilt := worLowerTail_le_tilt (K := K) hmN hm a s hs_pos
    rw [hexp_neg_s] at htilt
    refine htilt.trans ?_
    have hexp_pos : (0 : ℝ) ≤ Real.exp (s * ((m : ℝ) * a)) := (Real.exp_pos _).le
    have hbase_nn : 0 ≤ gBase N K c := by rw [gBase]; positivity
    -- Reference-rate monotonicity: `b·c + (1-b) - gBase N K c = (K/N - b)·(1 - c) ≥ 0`.
    have hmono_base : gBase N K c ≤ b * c + (1 - b) := by
      have hgap : b * c + (1 - b) - gBase N K c = ((K : ℝ) / N - b) * (1 - c) := by
        rw [gBase, Nat.cast_sub hKN, sub_div, div_self hN_ne]
        ring
      rw [← sub_nonneg, hgap]
      exact mul_nonneg (sub_nonneg.mpr hbK) (sub_nonneg.mpr hc_lt_one.le)
    calc
      Real.exp (s * ((m : ℝ) * a)) * hypergeometricPowMGF N m K c
          ≤ Real.exp (s * ((m : ℝ) * a)) * gBase N K c ^ m :=
            mul_le_mul_of_nonneg_left
              (hypergeometricPowMGF_le_gBase_pow hKN hmN hc_pos.le hc_lt_one.le) hexp_pos
      _ ≤ Real.exp (s * ((m : ℝ) * a)) * (b * c + (1 - b)) ^ m :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase_nn hmono_base m) hexp_pos
      _ = Real.exp (-(m : ℝ) * Math.Concentration.BernoulliKL.klBer a b) :=
            exp_tilt_base_eq m a b s c ha_pos ha hb1 hs_def hc_def

end Math.Concentration.HypergeometricTail
