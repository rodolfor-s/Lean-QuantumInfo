import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Moments.SubGaussian
import QCryptLean.Math.Concentration.BernoulliKL
import QCryptLean.Math.Concentration.BernoulliKLToolkit
import QCryptLean.Math.Concentration.BinomialKLTail

/-!
# Binomial Hoeffding — Chernoff/MGF bound for the binomial distribution

This file proves the two-tail Hoeffding bound for the binomial distribution, in
finite-combinatorial form:

  `∑ k ∈ range (n+1), (if |k/n - Q| ≤ δ then 0 else C(n,k) p^k (1-p)^(n-k))
     ≤ 2 * exp (-n δ² / 2)`

under the half-margin annulus hypothesis `p ∈ [Q - δ/2, Q]`.

## Approach

The one-sided Hoeffding-rate tails `binomial_upper_tail` and `binomial_lower_tail` are
**corollaries of the KL-rate Chernoff bounds** in
`Math.Concentration.BinomialKLTail` (`upperTail_le_exp_neg_mul_klBer`,
`lowerTail_le_exp_neg_mul_klBer`) combined with
Pinsker's quadratic lower bound `klBer a b ≥ 2 (a - b)²` for the Bernoulli relative entropy
(`BernoulliKL.two_mul_sq_le_klBer`, Cover–Thomas, *Elements of Information Theory*,
Lemma 11.6.1): the KL-rate exponent dominates the Hoeffding rate `2 ε²`. The degenerate
thresholds (`p = 0`, `p = 1`, thresholds outside `[0, 1]`) give empty or vanishing tails.

The MGF/Chernoff machinery below (following the template of
`Math.Concentration.HypergeometricTail.hypergeometric_choose_upper_tail`) proves the centred
MGF bound `binomial_centeredMGF_le`, which the tail corollaries no longer use but which is
retained as a statement of independent interest:

1. **Single-Bernoulli MGF (Hoeffding's lemma)**: for `0 ≤ p ≤ 1` and any `t : ℝ`,
   `p · exp(t(1-p)) + (1-p) · exp(-tp) ≤ exp(t²/8)`.  We obtain this from
   Mathlib's `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`
   applied to the canonical `ProbabilityTheory.bernoulliMeasure` measure.
2. **Binomial centred MGF identity**: the centred MGF
   `∑_k C(n,k) p^k (1-p)^(n-k) exp(t(k - np))` equals the n-th power of the
   single-Bernoulli centred MGF (via `add_pow`).
3. **Binomial centred MGF bound**: combining (1) and (2), the centred MGF is
   bounded by `exp(n t² / 8)`.

## Main statements

- `binomial_centeredMGF_le`: centred binomial MGF is bounded by `exp(n t²/8)`.
- `binomial_upper_tail`: single-sided upper tail `Pr[k/n ≥ p + ε] ≤ exp(-2nε²)`.
- `binomial_lower_tail`: single-sided lower tail `Pr[k/n ≤ p - ε] ≤ exp(-2nε²)`.
- `binomial_two_tail_le`: two-tail bound `≤ 2 exp(-2nε²)`.
- `binomial_failProb_le_half_margin`: final wrapper for the BB84 application,
  with the half-margin annulus hypothesis `p ∈ [Q - δ/2, Q]`.
-/

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Real

namespace Math.Concentration.BinomialHoeffding

/-! ## Step 1: Single-Bernoulli MGF (Hoeffding's lemma) -/

/-- **Hoeffding's lemma for a Bernoulli random variable.**

For any `0 ≤ p ≤ 1` and any real `t`,
  `p · exp(t·(1-p)) + (1-p) · exp(-t·p) ≤ exp(t² / 8)`.

This is the moment-generating function bound for the centered random variable
`X - p` where `X ~ Bernoulli(p)`, evaluated at `t`. -/
lemma bernoulli_centeredMGF_le (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (t : ℝ) :
    p * Real.exp (t * (1 - p)) + (1 - p) * Real.exp (-(t * p)) ≤
      Real.exp (t ^ 2 / 8) := by
  -- We use Mathlib's `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` applied
  -- to the canonical Bernoulli measure on `Bool`.
  classical
  let μ : Measure Bool := bernoulliMeasure true false ⟨p, h0, h1⟩
  have hμ_prob : IsProbabilityMeasure μ := inferInstance
  -- The random variable: 1 if true, 0 if false.
  let X : Bool → ℝ := fun b => cond b 1 0
  -- X is bounded in [0,1].
  have hX_bound : ∀ b, X b ∈ Set.Icc (0 : ℝ) 1 := by
    intro b
    cases b <;> simp [X]
  have hX_meas : Measurable X := by
    -- X : Bool → ℝ is measurable on Bool (every function from a discrete space is measurable).
    exact measurable_of_countable _
  have hX_ae : ∀ᵐ b ∂μ, X b ∈ Set.Icc (0 : ℝ) 1 := ae_of_all _ hX_bound
  -- The expectation of X under μ is p.
  have hX_int' : ∫ b, X b ∂μ = p := by
    simp [μ, integral_bernoulliMeasure, X]
  -- Apply Hoeffding's lemma from Mathlib.
  have hSubG :
      HasSubgaussianMGF (fun b => X b - p) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) μ := by
    have := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := X)
      hX_meas.aemeasurable hX_ae
    rw [hX_int'] at this
    exact this
  -- Extract the MGF bound at t.
  have hmgf := hSubG.mgf_le t
  -- Now compute the MGF concretely on Bool.
  have hParam : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal) = 1 / 4 := by
    simp only [sub_zero, nnnorm_one]; norm_num
  rw [hParam] at hmgf
  -- mgf of (X - p) at t = E[exp(t (X - p))] = p · exp(t(1-p)) + (1-p) · exp(-tp).
  have hmgf_eq :
      mgf (fun b => X b - p) μ t =
        p * Real.exp (t * (1 - p)) + (1 - p) * Real.exp (-(t * p)) := by
    simp [mgf, μ, integral_bernoulliMeasure, X, mul_neg]
  -- Convert the bound on mgf into the desired form.
  have h_target : p * Real.exp (t * (1 - p)) + (1 - p) * Real.exp (-(t * p)) ≤
      Real.exp (((1 / 4 : NNReal) : ℝ) * t ^ 2 / 2) := by
    rw [← hmgf_eq]; exact hmgf
  -- (1/4 : NNReal) : ℝ = 1/4 and (1/4) * t^2 / 2 = t^2 / 8.
  have hcoe : (((1 / 4 : NNReal) : ℝ) * t ^ 2 / 2) = t ^ 2 / 8 := by
    simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
    ring
  rw [hcoe] at h_target
  exact h_target

/-! ## Step 2: Binomial centred MGF identity -/

/-- **Binomial centred MGF identity (factorisation via the binomial theorem).**

For `0 ≤ p ≤ 1`, `t : ℝ`, and `n : ℕ`,
  `∑_k C(n,k) p^k (1-p)^(n-k) · exp(t (k - n p))
     = (p · exp(t(1-p)) + (1-p) · exp(-tp))^n`.

This is the binomial theorem applied to `x = p · exp(t(1-p))` and
`y = (1-p) · exp(-tp)`. -/
lemma binomial_centeredMGF_eq (p t : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) *
          Real.exp (t * ((k : ℝ) - (n : ℝ) * p)) =
      (p * Real.exp (t * (1 - p)) + (1 - p) * Real.exp (-(t * p))) ^ n := by
  -- Apply add_pow.
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hnk : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
    rw [Nat.cast_sub hk_le]
  -- Goal:
  --   C(n,k) * p^k * (1-p)^(n-k) * exp(t·(k - n·p))
  --     = (p · exp(t·(1-p)))^k * ((1-p) · exp(-t·p))^(n-k) * C(n,k)
  rw [mul_pow, mul_pow]
  -- The exp factors:
  -- (exp(t·(1-p)))^k = exp(k·(t·(1-p)))
  -- (exp(-t·p))^(n-k) = exp((n-k)·(-(t·p)))
  rw [show (Real.exp (t * (1 - p))) ^ k = Real.exp ((k : ℝ) * (t * (1 - p))) from by
        rw [← Real.exp_nat_mul]]
  rw [show (Real.exp (-(t * p))) ^ (n - k) = Real.exp (((n - k : ℕ) : ℝ) * (-(t * p))) from by
        rw [← Real.exp_nat_mul]]
  -- Combine the two exp factors:
  rw [show p ^ k * Real.exp ((k : ℝ) * (t * (1 - p))) *
          ((1 - p) ^ (n - k) * Real.exp (((n - k : ℕ) : ℝ) * (-(t * p)))) =
        (p ^ k * (1 - p) ^ (n - k)) *
          (Real.exp ((k : ℝ) * (t * (1 - p))) *
            Real.exp (((n - k : ℕ) : ℝ) * (-(t * p)))) from by ring]
  rw [← Real.exp_add]
  -- Simplify the combined exponent.
  rw [show (k : ℝ) * (t * (1 - p)) + ((n - k : ℕ) : ℝ) * (-(t * p)) =
        t * ((k : ℝ) - (n : ℝ) * p) from by rw [hnk]; ring]
  ring

/-! ## Step 3: Binomial centred MGF bound -/

/-- **Centred binomial MGF bound.**

For `0 ≤ p ≤ 1`, `t : ℝ`, and `n : ℕ`,
  `∑_k C(n,k) p^k (1-p)^(n-k) · exp(t (k - n p)) ≤ exp(n t² / 8)`. -/
lemma binomial_centeredMGF_le (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (t : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) *
          Real.exp (t * ((k : ℝ) - (n : ℝ) * p)) ≤
      Real.exp ((n : ℝ) * t ^ 2 / 8) := by
  rw [binomial_centeredMGF_eq]
  -- Reduce to (B(p,t))^n ≤ exp(n t²/8) where B = single Bernoulli centred MGF.
  have hB := bernoulli_centeredMGF_le p h0 h1 t
  -- B ≥ 0 since it's a sum of nonneg terms.
  have hB_nonneg : 0 ≤
      p * Real.exp (t * (1 - p)) + (1 - p) * Real.exp (-(t * p)) := by
    have hpe : 0 ≤ p * Real.exp (t * (1 - p)) :=
      mul_nonneg h0 (Real.exp_pos _).le
    have h1pe : 0 ≤ (1 - p) * Real.exp (-(t * p)) :=
      mul_nonneg (by linarith) (Real.exp_pos _).le
    linarith
  calc (p * Real.exp (t * (1 - p)) + (1 - p) * Real.exp (-(t * p))) ^ n
      ≤ (Real.exp (t ^ 2 / 8)) ^ n :=
        pow_le_pow_left₀ hB_nonneg hB n
    _ = Real.exp ((n : ℝ) * (t ^ 2 / 8)) := by
        rw [← Real.exp_nat_mul]
    _ = Real.exp ((n : ℝ) * t ^ 2 / 8) := by
        congr 1; ring

/-! ## Step 4: Single-sided tail bounds via Chernoff -/

/-- **Binomial upper tail (Hoeffding rate).**

For `n : ℕ`, `0 ≤ p ≤ 1`, and `0 < ε`,
  `∑_k I[(k:ℝ)/n ≥ p + ε] · C(n,k) p^k (1-p)^(n-k) ≤ exp(-2n ε²)`.

Derived from the KL-rate Chernoff bound `BinomialKLTail.upperTail_le_exp_neg_mul_klBer` and
Pinsker's
quadratic lower bound `two_mul_sq_le_klBer` for the Bernoulli relative entropy: at
threshold
`p + ε` with reference rate `p` the tail mass is at most `exp(-n · klBer (p+ε) p)`, and
`klBer (p+ε) p ≥ 2 ε²` (Cover–Thomas Lemma 11.6.1). The cases `p = 0` (all weights vanish) and
`p + ε > 1` (empty tail) are degenerate. -/
lemma binomial_upper_tail (n : ℕ) (hn : n ≠ 0) (p ε : ℝ)
    (h0 : 0 ≤ p) (h1 : p ≤ 1) (hε : 0 < ε) :
    ∑ k ∈ Finset.range (n + 1),
        (if (p + ε ≤ (k : ℝ) / n) then
          (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)
        else 0) ≤
      Real.exp (-2 * (n : ℝ) * ε ^ 2) := by
  classical
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  by_cases hpz : p = 0
  · -- `p = 0`: the `k = 0` term fails the threshold and all other weights vanish.
    subst hpz
    have hzero :
        ∑ k ∈ Finset.range (n + 1),
          (if (0 + ε ≤ (k : ℝ) / n) then
            (n.choose k : ℝ) * 0 ^ k * (1 - 0) ^ (n - k)
          else 0) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        simp [hε]
      · split
        · rw [zero_pow (by omega : k ≠ 0)]; ring
        · rfl
    rw [hzero]
    exact (Real.exp_pos _).le
  · rcases le_or_gt (p + ε) 1 with hpe1 | hpe1
    · -- KL-rate Chernoff tail at reference rate `p`, upgraded to the Hoeffding rate by Pinsker.
      have hppos : 0 < p := lt_of_le_of_ne' h0 hpz
      have hplt : p < 1 := by linarith
      have hkl := BinomialKLTail.upperTail_le_exp_neg_mul_klBer n p (p + ε) p
        (le_add_of_nonneg_right hε.le) (le_refl p) h0 hppos
      have hpinsker := BernoulliKL.two_mul_sq_le_klBer (a := p + ε) (b := p)
        (by linarith) hpe1 hppos hplt
      rw [show p + ε - p = ε from by ring] at hpinsker
      calc ∑ k ∈ Finset.range (n + 1),
              (if (p + ε ≤ (k : ℝ) / n) then
                (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)
              else 0)
          ≤ Real.exp (-(n : ℝ) * BernoulliKL.klBer (p + ε) p) := hkl
        _ ≤ Real.exp (-2 * (n : ℝ) * ε ^ 2) := by
            refine Real.exp_le_exp.mpr ?_
            have h0n : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
            have hmul : 2 * (n : ℝ) * ε ^ 2 ≤ (n : ℝ) * BernoulliKL.klBer (p + ε) p :=
              calc 2 * (n : ℝ) * ε ^ 2 = (n : ℝ) * (2 * ε ^ 2) := by ring
                _ ≤ (n : ℝ) * BernoulliKL.klBer (p + ε) p :=
                    mul_le_mul_of_nonneg_left hpinsker h0n
            linarith
    · -- Threshold above 1: every count satisfies `k/n ≤ 1 < p + ε`, so the tail is empty.
      have hzero :
          ∑ k ∈ Finset.range (n + 1),
            (if (p + ε ≤ (k : ℝ) / n) then
              (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)
            else 0) = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        have hk_le : (k : ℝ) ≤ (n : ℝ) :=
          mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [ite_eq_right (not_le.mpr (lt_of_le_of_lt (div_le_one hn_pos |>.mpr hk_le) hpe1))]
      rw [hzero]
      exact (Real.exp_pos _).le

/-- **Binomial lower tail (Hoeffding rate).**

For `n : ℕ`, `0 ≤ p ≤ 1`, and `0 < ε`,
  `∑_k I[(k:ℝ)/n ≤ p - ε] · C(n,k) p^k (1-p)^(n-k) ≤ exp(-2n ε²)`.

Derived from the KL-rate Chernoff bound `BinomialKLTail.lowerTail_le_exp_neg_mul_klBer` and
Pinsker's
quadratic lower bound `two_mul_sq_le_klBer` for the Bernoulli relative entropy: at
threshold
`p - ε` with reference rate `p` the tail mass is at most `exp(-n · klBer (p-ε) p)`, and
`klBer (p-ε) p ≥ 2 ε²` (Cover–Thomas Lemma 11.6.1). The cases `p = 1` (all weights except
`k = n` vanish, and that term fails the threshold) and `p - ε < 0` (empty tail) are degenerate. -/
lemma binomial_lower_tail (n : ℕ) (hn : n ≠ 0) (p ε : ℝ)
    (h0 : 0 ≤ p) (h1 : p ≤ 1) (hε : 0 < ε) :
    ∑ k ∈ Finset.range (n + 1),
        (if ((k : ℝ) / n ≤ p - ε) then
          (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)
        else 0) ≤
      Real.exp (-2 * (n : ℝ) * ε ^ 2) := by
  classical
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  by_cases hp1 : p = 1
  · -- `p = 1`: only the `k = n` term has nonzero weight, and `1 ≤ 1 - ε` fails.
    subst hp1
    have hzero :
        ∑ k ∈ Finset.range (n + 1),
          (if ((k : ℝ) / n ≤ 1 - ε) then
            (n.choose k : ℝ) * 1 ^ k * (1 - 1) ^ (n - k)
          else 0) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) with hklt | hke
      · have hw : (n.choose k : ℝ) * 1 ^ k * (1 - 1) ^ (n - k) = 0 :=
          by simp [show n - k ≠ 0 from by omega]
        split_ifs with hbad
        · exact hw
        · rfl
      · subst hke
        rw [ite_eq_right (not_le.mpr (by rw [div_self hn_pos.ne']; linarith))]
    rw [hzero]
    exact (Real.exp_pos _).le
  · rcases lt_or_ge (p - ε) 0 with hneg | hpe0
    · -- Threshold below 0: every count satisfies `k/n ≥ 0 > p - ε`, so the tail is empty.
      have hzero :
          ∑ k ∈ Finset.range (n + 1),
            (if ((k : ℝ) / n ≤ p - ε) then
              (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)
            else 0) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        have hkn : (0 : ℝ) ≤ (k : ℝ) / n := by positivity
        rw [ite_eq_right (not_le.mpr (by linarith))]
      rw [hzero]
      exact (Real.exp_pos _).le
    · -- KL-rate Chernoff tail at reference rate `p`, upgraded to the Hoeffding rate by Pinsker.
      have hplt : p < 1 := lt_of_le_of_ne h1 hp1
      have hppos : 0 < p := by linarith
      have hkl := BinomialKLTail.lowerTail_le_exp_neg_mul_klBer n p (p - ε) p
        (by linarith) (le_refl p) h1 hplt
      have hpinsker := BernoulliKL.two_mul_sq_le_klBer (a := p - ε) (b := p)
        hpe0 (by linarith) hppos hplt
      rw [show p - ε - p = -(ε : ℝ) from by ring, neg_sq] at hpinsker
      calc ∑ k ∈ Finset.range (n + 1),
              (if ((k : ℝ) / n ≤ p - ε) then
                (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)
              else 0)
          ≤ Real.exp (-(n : ℝ) * BernoulliKL.klBer (p - ε) p) := hkl
        _ ≤ Real.exp (-2 * (n : ℝ) * ε ^ 2) := by
            refine Real.exp_le_exp.mpr ?_
            have h0n : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
            have hmul : 2 * (n : ℝ) * ε ^ 2 ≤ (n : ℝ) * BernoulliKL.klBer (p - ε) p :=
              calc 2 * (n : ℝ) * ε ^ 2 = (n : ℝ) * (2 * ε ^ 2) := by ring
                _ ≤ (n : ℝ) * BernoulliKL.klBer (p - ε) p :=
                    mul_le_mul_of_nonneg_left hpinsker h0n
            linarith

/-- Monotonicity of the binomial lower-tail sum in the threshold: for
`0 ≤ p ≤ 1` and `a ≤ b`, the lower-tail sum at threshold `a` is bounded by the
lower-tail sum at threshold `b`. -/
lemma binomial_lowerTailSum_mono_threshold
    {n : ℕ} {p a b : ℝ} (hab : a ≤ b) (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1) :
    (∑ k ∈ Finset.range (n + 1),
        if (k : ℝ) / n ≤ a then
          (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)
        else 0) ≤
      ∑ k ∈ Finset.range (n + 1),
        if (k : ℝ) / n ≤ b then
          (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)
        else 0 := by
  apply Finset.sum_le_sum
  intro k _hk
  have hw_nonneg :
      0 ≤ (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) := by
    have hpk : 0 ≤ p ^ k := pow_nonneg hp_nonneg _
    have h1pk : 0 ≤ (1 - p) ^ (n - k) := pow_nonneg (by linarith) _
    positivity
  by_cases h_le : (k : ℝ) / n ≤ a
  · have h_le' : (k : ℝ) / n ≤ b := h_le.trans hab
    rw [ite_eq_left h_le, ite_eq_left h_le']
  · rw [ite_eq_right h_le]
    by_cases h_le' : (k : ℝ) / n ≤ b
    · rw [ite_eq_left h_le']; exact hw_nonneg
    · rw [ite_eq_right h_le']

/-! ## Step 5: Two-tail union bound -/

/-- **Two-tail binomial Hoeffding bound (combinatorial form).**

For `n ≠ 0`, `0 ≤ p ≤ 1`, and tail margins `ε_up, ε_lo > 0`,
  `∑_k I[k/n ≥ p + ε_up ∨ k/n ≤ p - ε_lo] · C(n,k) p^k (1-p)^(n-k)
     ≤ exp(-2n ε_lo²) + exp(-2n ε_up²)`. -/
lemma binomial_two_tail_le (n : ℕ) (hn : n ≠ 0) (p ε_up ε_lo : ℝ)
    (h0 : 0 ≤ p) (h1 : p ≤ 1) (hε_up : 0 < ε_up) (hε_lo : 0 < ε_lo) :
    ∑ k ∈ Finset.range (n + 1),
        (if ((k : ℝ) / n ≤ p - ε_lo ∨ p + ε_up ≤ (k : ℝ) / n) then
          (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)
        else 0) ≤
      Real.exp (-2 * (n : ℝ) * ε_lo ^ 2) +
        Real.exp (-2 * (n : ℝ) * ε_up ^ 2) := by
  classical
  -- Split the indicator: |k/n ≤ p - ε_lo OR p + ε_up ≤ k/n| ≤ I[lower] + I[upper].
  have hSplit : ∀ k : ℕ,
      (if ((k : ℝ) / n ≤ p - ε_lo ∨ p + ε_up ≤ (k : ℝ) / n) then
        ((n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k))
      else 0) ≤
      (if ((k : ℝ) / n ≤ p - ε_lo) then
        ((n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k))
      else 0) +
      (if (p + ε_up ≤ (k : ℝ) / n) then
        ((n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k))
      else 0) := by
    intro k
    have hw_nonneg : 0 ≤ (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) := by
      have hpk : 0 ≤ p ^ k := pow_nonneg h0 _
      have h1pk : 0 ≤ (1 - p) ^ (n - k) := pow_nonneg (by linarith) _
      positivity
    by_cases hor : ((k : ℝ) / n ≤ p - ε_lo ∨ p + ε_up ≤ (k : ℝ) / n)
    · rw [ite_eq_left hor]
      rcases hor with hlo | hup
      · rw [ite_eq_left hlo]
        by_cases hup' : (p + ε_up ≤ (k : ℝ) / n)
        · rw [ite_eq_left hup']; linarith
        · rw [ite_eq_right hup']; linarith
      · by_cases hlo' : ((k : ℝ) / n ≤ p - ε_lo)
        · rw [ite_eq_left hlo', ite_eq_left hup]; linarith
        · rw [ite_eq_right hlo', ite_eq_left hup]; linarith
    · rw [ite_eq_right hor]
      have hlo_neg : ¬ ((k : ℝ) / n ≤ p - ε_lo) := fun h => hor (Or.inl h)
      have hup_neg : ¬ (p + ε_up ≤ (k : ℝ) / n) := fun h => hor (Or.inr h)
      rw [ite_eq_right hlo_neg, ite_eq_right hup_neg]; norm_num
  calc ∑ k ∈ Finset.range (n + 1),
          (if ((k : ℝ) / n ≤ p - ε_lo ∨ p + ε_up ≤ (k : ℝ) / n) then
            (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)
          else 0)
      ≤ ∑ k ∈ Finset.range (n + 1),
          ((if ((k : ℝ) / n ≤ p - ε_lo) then
              ((n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k))
            else 0) +
           (if (p + ε_up ≤ (k : ℝ) / n) then
              ((n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k))
            else 0)) :=
        Finset.sum_le_sum (fun k _ => hSplit k)
    _ = (∑ k ∈ Finset.range (n + 1),
            (if ((k : ℝ) / n ≤ p - ε_lo) then
              ((n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k))
            else 0)) +
        (∑ k ∈ Finset.range (n + 1),
            (if (p + ε_up ≤ (k : ℝ) / n) then
              ((n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k))
            else 0)) := by
        rw [Finset.sum_add_distrib]
    _ ≤ Real.exp (-2 * (n : ℝ) * ε_lo ^ 2) +
          Real.exp (-2 * (n : ℝ) * ε_up ^ 2) := by
        gcongr
        · exact binomial_lower_tail n hn p ε_lo h0 h1 hε_lo
        · exact binomial_upper_tail n hn p ε_up h0 h1 hε_up

/-! ## Step 6: Final wrapper for the BB84 half-margin annulus -/

/-- **BB84 half-margin annulus binomial Hoeffding bound.**

For `n ≠ 0`, `Q δ : ℝ` with `0 < δ`, `p ∈ [Q − δ/2, Q]` with `0 ≤ p ≤ 1`,
the failure probability for a two-sided test at margin `δ` around `Q` is bounded by
`2 · exp(-n δ² / 2)`.

The factor `2 · exp(-n δ² / 2)` is the union bound over the two tails:
- Upper tail `k/n > Q + δ`: margin from `p` is `≥ δ` (since `p ≤ Q`). Yields `exp(-2nδ²)`.
- Lower tail `k/n < Q - δ`: margin from `p` is `≥ δ/2` (since `p ≥ Q - δ/2`). Yields
`exp(-2n·(δ/2)²) = exp(-nδ²/2)`.
- Sum: `exp(-2nδ²) + exp(-nδ²/2) ≤ 2 · exp(-nδ²/2)` since the upper-tail
  exponent is smaller. -/
theorem binomial_failProb_le_half_margin
    (n : ℕ) (hn : 0 < n) (Q δ : ℝ) (hδ : 0 < δ)
    (p : ℝ) (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1)
    (hp_lo : Q - δ / 2 ≤ p) (hp_hi : p ≤ Q) :
    ∑ k ∈ Finset.range (n + 1),
        (if |(k : ℝ) / (n : ℝ) - Q| ≤ δ then (0 : ℝ)
         else (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)) ≤
      2 * Real.exp (-(n : ℝ) * δ ^ 2 / 2) := by
  classical
  have hn_ne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  -- The PE-fail event `|k/n - Q| > δ` equals `k/n ≤ Q - δ` ∨ `Q + δ ≤ k/n`.
  -- Relative to `p`: lower margin = p - (Q - δ) ≥ δ - δ/2 = δ/2 (using p ≥ Q - δ/2);
  --                 upper margin = (Q + δ) - p ≥ δ (using p ≤ Q).
  -- So the failure event implies `k/n ≤ p - δ/2 ∨ p + δ ≤ k/n`.
  -- Bound by the two-tail combinatorial sum at margins (ε_lo, ε_up) = (δ/2, δ).
  have hδ_half : 0 < δ / 2 := by linarith
  have h_mono :
      ∀ k ∈ Finset.range (n + 1),
        (if |(k : ℝ) / (n : ℝ) - Q| ≤ δ then (0 : ℝ)
         else (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)) ≤
        (if ((k : ℝ) / n ≤ p - δ / 2 ∨ p + δ ≤ (k : ℝ) / n) then
          (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)
        else 0) := by
    intro k _hk
    have hw_nonneg : 0 ≤ (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) := by
      have hpk : 0 ≤ p ^ k := pow_nonneg hp_nonneg _
      have h1pk : 0 ≤ (1 - p) ^ (n - k) := pow_nonneg (by linarith) _
      positivity
    by_cases h_pass : |(k : ℝ) / (n : ℝ) - Q| ≤ δ
    · rw [ite_eq_left h_pass]
      split_ifs <;> [exact hw_nonneg; exact le_refl 0]
    · rw [ite_eq_right h_pass]
      -- |k/n - Q| > δ, so either k/n - Q > δ or k/n - Q < -δ.
      rw [not_le] at h_pass
      have h_or : (k : ℝ) / n - Q > δ ∨ (k : ℝ) / n - Q < -δ := by
        by_cases hsgn : 0 ≤ (k : ℝ) / n - Q
        · left; rwa [abs_of_nonneg hsgn] at h_pass
        · push Not at hsgn
          right; rw [abs_of_neg hsgn] at h_pass; linarith
      rcases h_or with hUp | hLo
      · -- k/n > Q + δ, and since p ≤ Q, k/n - p ≥ (Q + δ) - p ≥ δ, hence p + δ ≤ k/n.
        have hk_up : p + δ ≤ (k : ℝ) / n := by linarith
        rw [ite_eq_left (Or.inr hk_up)]
      · -- k/n < Q - δ, and since p ≥ Q - δ/2, p - k/n > p - (Q - δ) ≥ -δ/2 + δ = δ/2.
        -- So k/n ≤ p - δ/2.
        have hk_lo : (k : ℝ) / n ≤ p - δ / 2 := by linarith
        rw [ite_eq_left (Or.inl hk_lo)]
  -- Apply the two-tail bound.
  have hSum_le :
      ∑ k ∈ Finset.range (n + 1),
        (if |(k : ℝ) / (n : ℝ) - Q| ≤ δ then (0 : ℝ)
         else (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)) ≤
      ∑ k ∈ Finset.range (n + 1),
        (if ((k : ℝ) / n ≤ p - δ / 2 ∨ p + δ ≤ (k : ℝ) / n) then
          (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)
        else 0) := Finset.sum_le_sum h_mono
  have hTwoTail := binomial_two_tail_le n hn_ne p δ (δ / 2)
    hp_nonneg hp_le_one hδ hδ_half
  -- Now: exp(-2n·(δ/2)²) + exp(-2nδ²) ≤ 2·exp(-nδ²/2).
  -- Compute exponents:
  --   -2n·(δ/2)² = -nδ²/2,
  --   -2nδ²       = -2nδ² ≤ -nδ²/2 (since nδ² ≥ 0).
  have h_exp_half : -2 * (n : ℝ) * (δ / 2) ^ 2 = -(n : ℝ) * δ ^ 2 / 2 := by ring
  have h_exp_full_le_half :
      -2 * (n : ℝ) * δ ^ 2 ≤ -(n : ℝ) * δ ^ 2 / 2 := by
    have hnδ2 : 0 ≤ (n : ℝ) * δ ^ 2 := by positivity
    linarith
  have h_exp_combine :
      Real.exp (-2 * (n : ℝ) * (δ / 2) ^ 2) +
        Real.exp (-2 * (n : ℝ) * δ ^ 2) ≤
      2 * Real.exp (-(n : ℝ) * δ ^ 2 / 2) := by
    rw [h_exp_half, two_mul]
    have h_upper :
        Real.exp (-2 * (n : ℝ) * δ ^ 2) ≤
          Real.exp (-(n : ℝ) * δ ^ 2 / 2) :=
      Real.exp_le_exp.mpr h_exp_full_le_half
    linarith
  exact hSum_le.trans (hTwoTail.trans h_exp_combine)

end Math.Concentration.BinomialHoeffding
