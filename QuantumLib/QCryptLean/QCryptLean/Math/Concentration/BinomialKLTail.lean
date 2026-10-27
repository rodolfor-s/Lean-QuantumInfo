import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.LinearCombination
import QCryptLean.Math.Concentration.BernoulliKL

/-!
# Binomial KL-rate Chernoff tails

This file proves the Kullback–Leibler rate Chernoff bounds for the one-sided
tails of the binomial distribution: for `m` IID Bernoulli(`p`) trials and a threshold `a`,
the probability of an empirical fraction `k/m ≤ a` is at most `exp(-m · klBer a b)` for any
reference rate `a < b ≤ p`, where `klBer` is the Bernoulli relative entropy
(`Math.Concentration.BernoulliKL.klBer`); the upper tail is the mirror statement.  This is
the method-of-types / Chernoff exponent (Cover–Thomas, *Elements of Information Theory*,
§11.1).

## Approach

The proof is the standard Chernoff optimisation performed **without calculus**: rather than
maximising the Chernoff exponent over the tilt parameter, we instantiate the tilt at its
known optimum `c = a(1-b)/(b(1-a))` for the *reference* rate `b` with `a < b ≤ p`, and verify
the resulting bound `exp(-m · klBer a b)` by direct `Real.log`/`Real.exp` algebra:

1. **Chernoff reduction** (termwise `exp` domination): trade the lower-tail indicator
   `I[k/m ≤ a]` for the exponential weight `exp(s·(m·a - k))` at any tilt `s > 0`.
2. **Binomial MGF identity** (`add_pow`): the tilted sum factorises to `(p·c + 1-p)^m` with
   `c = exp(-s)`.
3. **Rate monotonicity in `p`**: since `c < 1`, the base `p·c + 1-p = 1 - p(1-c)` is
   decreasing in `p`, so `(p·c+1-p)^m ≤ (b·c+1-b)^m` whenever `b ≤ p`.
4. **Exponent identity**: at the optimal tilt `c = a(1-b)/(b(1-a))`, `b·c + 1-b = (1-b)/(1-a)`
   and `s·m·a + m·log((1-b)/(1-a)) = -m·klBer a b`, by elementary `log` algebra.

## Main statements

- `lowerTail_le_exp_neg_mul_klBer`: the binomial lower-tail sum at threshold `a` is bounded by
  `exp(-m · klBer a b)` for any reference rate `a < b ≤ p ≤ 1`.
- `upperTail_le_exp_neg_mul_klBer`: the binomial upper-tail mass at threshold `a` is at most
  `exp(-m · klBer a b)` for `0 ≤ p ≤ b ≤ a` (mirror of `lowerTail_le_exp_neg_mul_klBer` via
  `klBer_compl`).

References: standard Chernoff/large-deviations exponent for the binomial lower tail
(Cover–Thomas, *Elements of Information Theory*, §11.1); Renner (2005),
`arXiv:quant-ph/0512258v2`, §5 (parameter estimation).
-/

open scoped BigOperators
open Real

namespace Math.Concentration.BinomialKLTail

/-- **Binomial MGF identity at a multiplicative tilt `c`.**

For any base rate `p`, tilt `c : ℝ`, and `m : ℕ`,
`∑_k C(m,k) p^k (1-p)^(m-k) · c^k = (p·c + (1-p))^m`.

This is the binomial theorem (`add_pow`) applied to `x = p·c` and `y = 1-p`. -/
lemma binomial_tilt_sum_eq (p c : ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1),
        (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) * c ^ k =
      (p * c + (1 - p)) ^ m := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_pow]
  ring

/-- **Lower-tail Chernoff sum at an explicit tilt.**

For `m : ℕ`, `0 ≤ p ≤ 1`, tilt `s > 0`, threshold `a : ℝ`, the lower-tail pass sum
`∑_{k/m ≤ a} C(m,k) p^k (1-p)^(m-k)` is bounded by `exp(s·m·a) · (p·exp(-s) + (1-p))^m`. -/
lemma lowerTail_le_tilt (m : ℕ) (p a s : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (hs : 0 < s) :
    (∑ k ∈ Finset.range (m + 1),
        if (k : ℝ) / m ≤ a then
          (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)
        else 0) ≤
      Real.exp (s * ((m : ℝ) * a)) * (p * Real.exp (-s) + (1 - p)) ^ m := by
  classical
  -- Termwise: `I[k/m ≤ a]·w_k ≤ w_k·exp(s·(m·a - k))`, then factor `exp(s·m·a)·c^k`.
  have hbound :
      (∑ k ∈ Finset.range (m + 1),
          if (k : ℝ) / m ≤ a then
            (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)
          else 0) ≤
        ∑ k ∈ Finset.range (m + 1),
          ((m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)) *
            Real.exp (s * ((m : ℝ) * a - (k : ℝ))) := by
    apply Finset.sum_le_sum
    intro k hk
    have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hw_nonneg : 0 ≤ (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) := by
      have hpk : 0 ≤ p ^ k := pow_nonneg h0 _
      have h1pk : 0 ≤ (1 - p) ^ (m - k) := pow_nonneg (by linarith) _
      positivity
    by_cases hbad : (k : ℝ) / m ≤ a
    · rw [ite_eq_left hbad]
      -- On the bad set, `m·a - k ≥ 0` so `exp(...) ≥ 1`.
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · -- `m = 0`: only `k = 0`, exponent `0`, `exp 0 = 1`.
        have hk0 : k = 0 := by omega
        subst hm0; subst hk0
        simp
      · have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hmpos
        have hk_le : (k : ℝ) ≤ (m : ℝ) * a := by
          rw [div_le_iff₀ hm_pos] at hbad; linarith
        have hexp : 1 ≤ Real.exp (s * ((m : ℝ) * a - (k : ℝ))) :=
          Real.one_le_exp (mul_nonneg hs.le (sub_nonneg.mpr hk_le))
        exact le_mul_of_one_le_right hw_nonneg hexp
    · rw [ite_eq_right hbad]
      exact mul_nonneg hw_nonneg (Real.exp_pos _).le
  refine hbound.trans (le_of_eq ?_)
  -- Factor `exp(s·(m·a - k)) = exp(s·m·a) · exp(-s)^k`.
  rw [← binomial_tilt_sum_eq p (Real.exp (-s)) m, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [show s * ((m : ℝ) * a - (k : ℝ)) = s * ((m : ℝ) * a) + (k : ℝ) * (-s) by ring,
      Real.exp_add, ← Real.exp_nat_mul]
  ring

/-- **Binomial KL-rate Chernoff lower tail (strictly positive threshold).**

For `m : ℕ` trials at true rate `p`, threshold `a`, and a reference rate `b` with
`0 < a < b ≤ p`, `b < 1`, the binomial lower-tail mass `∑_{k/m ≤ a} C(m,k) p^k (1-p)^(m-k)`
is bounded by the KL-rate Chernoff exponent `exp(-m · klBer a b)`.

The bound is obtained by instantiating `lowerTail_le_tilt` at the optimal tilt
`s = log((b(1-a))/(a(1-b)))` (so `exp(-s) = a(1-b)/(b(1-a)) =: c`), monotonicity in `p`
(`p·c + 1-p ≤ b·c + 1-b` since `c < 1` and `b ≤ p`), and the exponent identity
`s·m·a + m·log((1-b)/(1-a)) = -m·klBer a b`. -/
theorem lowerTail_le_exp_neg_mul_klBer_of_pos (m : ℕ) (p a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hbp : b ≤ p) (hp1 : p ≤ 1) (hb1 : b < 1) :
    (∑ k ∈ Finset.range (m + 1),
        if (k : ℝ) / m ≤ a then
          (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)
        else 0) ≤
      Real.exp (-(m : ℝ) * Math.Concentration.BernoulliKL.klBer a b) := by
  have hb_pos : 0 < b := ha.trans hab
  have hp_pos : 0 < p := hb_pos.trans_le hbp
  have h1a_pos : 0 < 1 - a := sub_pos.mpr (hab.trans hb1)
  have h1b_pos : 0 < 1 - b := sub_pos.mpr hb1
  have hp_le_one : p ≤ 1 := hp1
  have hp_nonneg : 0 ≤ p := hp_pos.le
  -- The optimal tilt and its exponential.
  set c : ℝ := a * (1 - b) / (b * (1 - a)) with hc_def
  have hbac_pos : 0 < b * (1 - a) := mul_pos hb_pos h1a_pos
  have habc_pos : 0 < a * (1 - b) := mul_pos ha h1b_pos
  have hc_pos : 0 < c := div_pos habc_pos hbac_pos
  -- `c < 1` since `a(1-b) < b(1-a)` ⟺ `a < b`.
  have hc_lt_one : c < 1 := by
    rw [hc_def, div_lt_one hbac_pos]
    linear_combination hab
  set s : ℝ := Real.log (b * (1 - a) / (a * (1 - b))) with hs_def
  -- `exp(-s) = c`.
  have hinv : b * (1 - a) / (a * (1 - b)) = c⁻¹ := by
    rw [hc_def, inv_div]
  have hexp_neg_s : Real.exp (-s) = c := by
    rw [hs_def, hinv, Real.log_inv, neg_neg, Real.exp_log hc_pos]
  -- `s > 0` since the argument `c⁻¹ > 1`.
  have hs_pos : 0 < s := by
    rw [hs_def, hinv]
    apply Real.log_pos
    exact one_lt_inv_iff₀.mpr ⟨hc_pos, hc_lt_one⟩
  -- Apply the tilt bound.
  have htilt := lowerTail_le_tilt m p a s hp_nonneg hp_le_one hs_pos
  rw [hexp_neg_s] at htilt
  refine htilt.trans ?_
  -- Monotonicity in `p`: `p·c + 1-p ≤ b·c + 1-b`.
  have hbase_p_pos : 0 ≤ p * c + (1 - p) := by linarith [mul_nonneg hp_nonneg hc_pos.le]
  -- `b·c + (1-b) - (p·c + (1-p)) = (p - b)·(1 - c) ≥ 0`.
  have hmono : p * c + (1 - p) ≤ b * c + (1 - b) := by
    rw [← sub_nonneg, show b * c + (1 - b) - (p * c + (1 - p)) = (p - b) * (1 - c) by ring]
    exact mul_nonneg (sub_nonneg.mpr hbp) (sub_nonneg.mpr hc_lt_one.le)
  have hpow_le : (p * c + (1 - p)) ^ m ≤ (b * c + (1 - b)) ^ m :=
    pow_le_pow_left₀ hbase_p_pos hmono m
  have hexp_pos : (0 : ℝ) ≤ Real.exp (s * ((m : ℝ) * a)) := (Real.exp_pos _).le
  refine (mul_le_mul_of_nonneg_left hpow_le hexp_pos).trans ?_
  -- Exponent identity: `b·c + 1-b = (1-b)/(1-a)`.
  have hbc : b * c + (1 - b) = (1 - b) / (1 - a) := by
    rw [hc_def]
    field_simp
    ring
  rw [hbc]
  -- `((1-b)/(1-a))^m = exp(m·log((1-b)/(1-a)))`.
  have hratio_pos : 0 < (1 - b) / (1 - a) := by positivity
  rw [show ((1 - b) / (1 - a)) ^ m = Real.exp ((m : ℝ) * Real.log ((1 - b) / (1 - a))) by
        rw [Real.exp_nat_mul, Real.exp_log hratio_pos]]
  rw [← Real.exp_add]
  apply le_of_eq
  congr 1
  -- `s·(m·a) + m·log((1-b)/(1-a)) = -m·klBer a b`.
  rw [hs_def, Math.Concentration.BernoulliKL.klBer]
  -- expand `log`s.
  rw [Real.log_div hbac_pos.ne' habc_pos.ne', Real.log_div h1b_pos.ne' h1a_pos.ne',
      Real.log_mul hb_pos.ne' h1a_pos.ne', Real.log_mul ha.ne' h1b_pos.ne',
      Real.log_div ha.ne' hb_pos.ne', Real.log_div h1a_pos.ne' h1b_pos.ne']
  ring

/-- **Binomial lower-tail mass at threshold `0` is `(1-p)^m`.**  Only the `k = 0` term passes
`k/m ≤ 0` (as `k/m ≥ 0`), contributing `(1-p)^m`; all other terms vanish. -/
lemma lowerTail_zero_eq (m : ℕ) (p : ℝ) :
    (∑ k ∈ Finset.range (m + 1),
        if (k : ℝ) / m ≤ 0 then
          (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)
        else 0) = (1 - p) ^ m := by
  classical
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0; simp at hk; omega
    · have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hmpos
      have : ¬ ((k : ℝ) / m ≤ 0) := by
        rw [not_le]; positivity
      rw [ite_eq_right this]
  · intro h; simp at h

/-- **Binomial KL-rate Chernoff lower tail.**

For `m : ℕ` trials at true rate `p`, threshold `a`, and a reference rate `b` with `a < b ≤ p`,
`b < 1` (so `0 < b < 1` in the non-degenerate regime `0 ≤ a`), the binomial lower-tail mass
`∑_{k/m ≤ a} C(m,k) p^k (1-p)^(m-k)` is bounded by the KL-rate Chernoff exponent
`exp(-m · klBer a b)`.

The threshold `a` is allowed to be `≤ 0` (the physically degenerate `Q + δ ≤ 0` regime):
- `a < 0`: no count passes `k/m ≤ a`, so the sum is `0 < exp(...)`;
- `a = 0`: only `k = 0` passes, contributing `(1-p)^m ≤ (1-b)^m = exp(-m·klBer 0 b)`
  (since `klBer 0 b = -log(1-b)`);
- `0 < a`: the calculus-free tilt argument `lowerTail_le_exp_neg_mul_klBer_of_pos`. -/
theorem lowerTail_le_exp_neg_mul_klBer (m : ℕ) (p a b : ℝ)
    (hab : a < b) (hbp : b ≤ p) (hp1 : p ≤ 1) (hb1 : b < 1) :
    (∑ k ∈ Finset.range (m + 1),
        if (k : ℝ) / m ≤ a then
          (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)
        else 0) ≤
      Real.exp (-(m : ℝ) * Math.Concentration.BernoulliKL.klBer a b) := by
  classical
  rcases lt_trichotomy a 0 with ha_neg | ha_zero | ha_pos
  · -- `a < 0`: the lower-tail sum is empty.
    have hzero :
        (∑ k ∈ Finset.range (m + 1),
            if (k : ℝ) / m ≤ a then
              (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)
            else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k _hk
      have : ¬ ((k : ℝ) / m ≤ a) := by
        rw [not_le]
        have hk_nonneg : 0 ≤ (k : ℝ) / m := by positivity
        linarith
      rw [ite_eq_right this]
    rw [hzero]
    exact (Real.exp_pos _).le
  · -- `a = 0`: only `k = 0` passes; bound `(1-p)^m ≤ (1-b)^m`.
    subst ha_zero
    rw [lowerTail_zero_eq m p]
    have h1b_pos : 0 < 1 - b := by linarith
    have hp_le_one : p ≤ 1 := hp1
    have hbp_one : (1 - p) ≤ (1 - b) := by linarith
    have h1p_nonneg : 0 ≤ 1 - p := by linarith
    -- `klBer 0 b = -log(1-b)`, so `exp(-m·klBer 0 b) = (1-b)^m`.
    have hkl : Math.Concentration.BernoulliKL.klBer 0 b = -Real.log (1 - b) := by
      rw [Math.Concentration.BernoulliKL.klBer]
      simp
    rw [hkl]
    rw [show (-(m : ℝ) * -Real.log (1 - b)) = (m : ℝ) * Real.log (1 - b) by ring,
        Real.exp_nat_mul, Real.exp_log h1b_pos]
    exact pow_le_pow_left₀ h1p_nonneg hbp_one m
  · -- `0 < a`: the tilt argument.
    exact lowerTail_le_exp_neg_mul_klBer_of_pos m p a b ha_pos hab hbp hp1 hb1

/-- **Binomial KL-rate Chernoff upper tail.**

For `m : ℕ` trials at true rate `p`, threshold `a`, and a reference rate `b` with `0 ≤ p ≤ b ≤ a`,
`0 < b`, the binomial upper-tail mass `∑_{a ≤ k/m} C(m,k) p^k (1-p)^(m-k)` is bounded by the
KL-rate Chernoff exponent `exp(-m · klBer a b)`.

Mirror of `lowerTail_le_exp_neg_mul_klBer` by the symmetry `k ↦ m - k`, `p ↦ 1 - p`, together with
the
complement symmetry `klBer (1 - a) (1 - b) = klBer a b`; the degenerate thresholds `a ≥ 1`
(`a = 1` leaves the single count `k = m`, of mass `p^m ≤ b^m`; `a > 1` is an empty tail) and the
degenerate reference `b = a` (total mass `1 = exp(-m · klBer a a)`) are handled inside the proof. -/
theorem upperTail_le_exp_neg_mul_klBer (m : ℕ) (p a b : ℝ)
    (hba : b ≤ a) (hpb : p ≤ b) (hp0 : 0 ≤ p) (hb0 : 0 < b) :
    (∑ k ∈ Finset.range (m + 1),
        if a ≤ (k : ℝ) / m then
          (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)
        else 0) ≤
      Real.exp (-(m : ℝ) * Math.Concentration.BernoulliKL.klBer a b) := by
  classical
  -- Trivial case `m = 0`: the single (empty) trial contributes mass `≤ 1 = exp 0`.
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    refine le_trans (b := (1 : ℝ)) ?_ ?_
    · simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton]
      split <;> simp
    · simp
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hmpos
  rcases lt_trichotomy a 1 with ha1 | ha1 | ha1
  · -- `a < 1`: reflect the index `k ↦ m - k` and apply the lower tail at `(1-p, 1-a, 1-b)`.
    rcases lt_or_eq_of_le hba with hba_lt | hba_eq
    · have hsub :
          (∑ k ∈ Finset.range (m + 1),
              if a ≤ (k : ℝ) / m then
                (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)
              else 0)
        = (∑ j ∈ Finset.range (m + 1),
              if (j : ℝ) / m ≤ 1 - a then
                (m.choose j : ℝ) * (1 - p) ^ j * (1 - (1 - p)) ^ (m - j)
              else 0) := by
        rw [← Finset.sum_range_reflect]
        refine Finset.sum_congr rfl ?_
        intro k hk
        have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        simp only [Nat.add_sub_cancel]
        -- `(m - k)/m = 1 - k/m`.
        have hdiv : ((m - k : ℕ) : ℝ) / m = 1 - (k : ℝ) / m := by
          have h1 : ((m - k : ℕ) : ℝ) / m + (k : ℝ) / m = 1 := by
            rw [← add_div, ← Nat.cast_add, Nat.sub_add_cancel hkm, div_self hmR.ne']
          linarith
        have hcond : a ≤ ((m - k : ℕ) : ℝ) / m ↔ (k : ℝ) / m ≤ 1 - a := by
          rw [hdiv]; constructor <;> intro h <;> linarith
        -- Reflect the indicator, the binomial coefficient and the exponents.
        simp only [hcond, Nat.choose_symm hkm, Nat.sub_sub_self hkm]
        by_cases hc : (k : ℝ) / m ≤ 1 - a
        · rw [ite_eq_left hc, ite_eq_left hc]; ring
        · rw [ite_eq_right hc, ite_eq_right hc]
      rw [hsub]
      refine le_trans (lowerTail_le_exp_neg_mul_klBer m (1 - p) (1 - a) (1 - b)
        (by linarith) (by linarith) (by linarith) (by linarith)) ?_
      rw [Math.Concentration.BernoulliKL.klBer_compl]
    · -- `b = a`: the tail is at most the total binomial mass `1 = exp(-m · klBer a a)`.
      subst hba_eq
      have hle : (∑ k ∈ Finset.range (m + 1),
            if b ≤ (k : ℝ) / m then
              (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)
            else 0)
          ≤ ∑ k ∈ Finset.range (m + 1),
              (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) := by
        apply Finset.sum_le_sum
        intro k hk
        have hw : 0 ≤ (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) :=
          mul_nonneg (mul_nonneg (by exact_mod_cast Nat.zero_le _) (pow_nonneg hp0 _))
            (pow_nonneg (by linarith) _)
        by_cases hc : b ≤ (k : ℝ) / m
        · rw [ite_eq_left hc]
        · rw [ite_eq_right hc]; exact hw
      refine hle.trans ?_
      have htotal : (∑ k ∈ Finset.range (m + 1),
            (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)) = 1 := by
        simpa using binomial_tilt_sum_eq p 1 m
      rw [htotal, Math.Concentration.BernoulliKL.klBer_self]
      simp
  · -- `a = 1`: only the count `k = m` passes; mass `p^m ≤ b^m = exp(-m · klBer 1 b)`.
    subst ha1
    have hkl : Math.Concentration.BernoulliKL.klBer 1 b = -Real.log b := by
      rw [Math.Concentration.BernoulliKL.klBer, sub_self, zero_div, Real.log_zero, zero_mul,
        Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hb0.ne', Real.log_one]
      ring
    rw [Finset.sum_eq_single m]
    · have hm1 : ((1 : ℝ) ≤ (m : ℝ) / m) := by
        rw [div_self hmR.ne']
      rw [ite_eq_left hm1,
        show (m.choose m : ℝ) * p ^ m * (1 - p) ^ (m - m) = p ^ m from by simp, hkl,
        show (-(m : ℝ) * -Real.log b) = (m : ℝ) * Real.log b from by ring,
        Real.exp_nat_mul, Real.exp_log hb0]
      exact pow_le_pow_left₀ hp0 hpb m
    · intro k hk hkm
      have hk_le : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hneg : ¬ ((1 : ℝ) ≤ (k : ℝ) / m) := by
        rw [not_le]
        have hlt : k < m := Nat.lt_of_le_of_ne hk_le hkm
        rw [div_lt_one hmR]
        exact_mod_cast hlt
      rw [ite_eq_right hneg]
    · intro h; simp at h
  · -- `a > 1`: every count satisfies `k/m ≤ 1 < a`, so the tail is empty.
    have hzero : (∑ k ∈ Finset.range (m + 1),
        if a ≤ (k : ℝ) / m then
          (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)
        else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro k hk
      have hk_le : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hneg : ¬ (a ≤ (k : ℝ) / m) := by
        rw [not_le]
        calc (k : ℝ) / m ≤ 1 := by
              rw [div_le_one hmR]; exact_mod_cast hk_le
          _ < a := ha1
      rw [ite_eq_right hneg]
    rw [hzero]
    exact (Real.exp_pos _).le

end Math.Concentration.BinomialKLTail
