import QCryptLean.Math.Concentration.BernoulliKL
import QCryptLean.Math.Concentration.BinomialHoeffding
import QCryptLean.Math.Concentration.BinomialKLTail

/-!
# Strict lower tails of the binomial distribution

`binomialLowerTail n q p = ∑_{k < q} C(n, k) p^k (1 - p)^(n - k)` is the probability that `n`
independent trials with success probability `p` produce **strictly fewer** than `q` successes,
that is, the probability of falling short of a quota of `q` successes.

## Main statements

* `binomialLowerTail_zero_quota`, `binomialLowerTail_of_lt`: a zero quota is never missed and a
  quota larger than `n` is always missed.
* `binomialLowerTail_prob_zero`, `binomialLowerTail_prob_one`: the degenerate success
  probabilities.
* `binomialLowerTail_le_exp`: Hoeffding's bound at the strict-shortfall integer endpoint: fewer than
`q`
  successes means at most `q - 1`, so
  `binomialLowerTail n q p ≤ exp (-2 (n p - q + 1)^2 / n)` whenever `q - 1 < n p`.
* `binomialLowerTail_le_exp_of_le`: the linear-slack form: if `q ≤ (p - η) n` with `0 ≤ η`, the
  tail is at most `exp (-2 η^2 n)`.
* `binomialLowerTail_le_exp_neg_mul_klBer`: the Chernoff bound with the Bernoulli relative entropy
at the
  same endpoint, `exp (-n klBer ((q - 1) / n) b)` for any reference rate `(q - 1)/n < b ≤ p`
  with `b < 1`.

The two bounds are `Math.Concentration.BinomialHoeffding.binomial_lower_tail` and
`Math.Concentration.BinomialKLTail.lowerTail_le_exp_neg_mul_klBer`, evaluated at the real threshold
`(q - 1) / n`, which identifies the strict integer event `k < q` exactly.  Using the threshold
`q / n` instead would bound the larger event `k ≤ q`.
-/

open scoped BigOperators
open Finset

namespace Math.Concentration.BinomialLowerTail

/-- The probability `P[Bin(n, p) < q]` that `n` independent trials with success probability `p`
produce strictly fewer than `q` successes. -/
noncomputable def binomialLowerTail (n q : ℕ) (p : ℝ) : ℝ :=
  ∑ k ∈ range q, (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)

/-- A zero quota is never missed. -/
@[simp]
theorem binomialLowerTail_zero_quota (n : ℕ) (p : ℝ) : binomialLowerTail n 0 p = 0 := by
  simp [binomialLowerTail]

/-- The strict lower tail as a sum over all counts `k ≤ n`: terms with `n < k < q` vanish. -/
theorem binomialLowerTail_eq_sum_range_succ (n q : ℕ) (p : ℝ) :
    binomialLowerTail n q p =
      ∑ k ∈ range (n + 1),
        if k < q then (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) else 0 := by
  rw [← Finset.sum_filter, binomialLowerTail]
  symm
  refine Finset.sum_subset (fun k hk => mem_range.mpr (mem_filter.mp hk).2) fun k hkq hk => ?_
  have hnk : n < k := by
    simp only [mem_filter, mem_range, not_and] at hk
    by_contra h
    exact hk (by omega) (mem_range.mp hkq)
  simp [Nat.choose_eq_zero_of_lt hnk]

/-- A quota larger than the number of trials is always missed. -/
theorem binomialLowerTail_of_lt {n q : ℕ} (h : n < q) (p : ℝ) : binomialLowerTail n q p = 1 := by
  rw [binomialLowerTail_eq_sum_range_succ]
  have hq : ∀ k ∈ range (n + 1), k < q := fun k hk => by
    have := mem_range.mp hk
    omega
  rw [Finset.sum_congr rfl fun k hk => ite_eq_left (hq k hk)]
  have hbinom := (add_pow p (1 - p) n).symm
  rw [add_sub_cancel, one_pow] at hbinom
  refine (Finset.sum_congr rfl fun k _ => ?_).trans hbinom
  ring

/-- A strict lower tail at a probability `p ∈ [0, 1]` is nonnegative. -/
theorem binomialLowerTail_nonneg (n q : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binomialLowerTail n q p :=
  Finset.sum_nonneg fun k _ => by
    have := sub_nonneg.mpr hp1
    positivity

/-- A larger quota is missed with at least the same probability. -/
theorem binomialLowerTail_mono {n q q' : ℕ} (hq : q ≤ q') {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binomialLowerTail n q p ≤ binomialLowerTail n q' p :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hq) fun k _ _ => by
    have := sub_nonneg.mpr hp1
    positivity

/-- A strict lower tail at a probability `p ∈ [0, 1]` is at most one. -/
theorem binomialLowerTail_le_one (n q : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binomialLowerTail n q p ≤ 1 := by
  calc binomialLowerTail n q p ≤ binomialLowerTail n (max q (n + 1)) p :=
        binomialLowerTail_mono (le_max_left _ _) hp0 hp1
    _ = 1 := binomialLowerTail_of_lt (by omega) p

/-- With success probability zero every positive quota is missed. -/
theorem binomialLowerTail_prob_zero {n q : ℕ} (hq : 0 < q) : binomialLowerTail n q 0 = 1 := by
  rw [binomialLowerTail, Finset.sum_eq_single_of_mem 0 (mem_range.mpr hq)]
  · simp
  · intro k _ hk
    simp [zero_pow hk]

/-- With success probability one every quota up to `n` is met. -/
theorem binomialLowerTail_prob_one {n q : ℕ} (hq : q ≤ n) : binomialLowerTail n q 1 = 0 := by
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk : n - k ≠ 0 := by
    have := mem_range.mp hk
    omega
  simp [zero_pow hk]

/-- For `0 < n`, the strict integer event `k < q` is the real event `k / n ≤ (q - 1) / n`. -/
private theorem lt_iff_div_le {n k q : ℕ} (hn : 0 < n) :
    k < q ↔ (k : ℝ) / n ≤ ((q : ℝ) - 1) / n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [div_le_div_iff_of_pos_right hn', le_sub_iff_add_le]
  exact_mod_cast Nat.lt_iff_add_one_le

private theorem binomialLowerTail_eq_threshold (n q : ℕ) {p : ℝ} (hn : 0 < n) :
    binomialLowerTail n q p =
      ∑ k ∈ range (n + 1),
        if (k : ℝ) / n ≤ ((q : ℝ) - 1) / n then
          (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) else 0 := by
  rw [binomialLowerTail_eq_sum_range_succ]
  exact Finset.sum_congr rfl fun k _ => if_congr (lt_iff_div_le hn) rfl rfl

/-- **Hoeffding's bound at the strict-shortfall integer endpoint.**  If `q - 1 < n p`, the
probability of
fewer than `q` successes is at most `exp (-2 (n p - q + 1)^2 / n)`.

For a positive quota, the premise puts the largest failing count `q - 1` below the mean `n p`.
A zero quota has an empty failure event. The bound is below one when `0 < n` and decays once
`n p - q + 1` grows faster than `√n`. It also holds for `n = 0`, when the premise forces `q = 0`. -/
theorem binomialLowerTail_le_exp {n q : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : (q : ℝ) - 1 < n * p) :
    binomialLowerTail n q p ≤ Real.exp (-2 * ((n : ℝ) * p - q + 1) ^ 2 / n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hq0 : q = 0 := by
      have : (q : ℝ) < 1 := by simpa using hq
      exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)
    subst hq0
    rw [binomialLowerTail_zero_quota]
    exact (Real.exp_pos _).le
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set ε : ℝ := ((n : ℝ) * p - q + 1) / n with hε_def
  have hε : 0 < ε := div_pos (by linarith) hn'
  have hthreshold : ((q : ℝ) - 1) / n = p - ε := by
    rw [hε_def]
    field_simp
    ring
  rw [binomialLowerTail_eq_threshold n q hn, hthreshold]
  refine (Math.Concentration.BinomialHoeffding.binomial_lower_tail n hn.ne' p ε hp0 hp1
    hε).trans (le_of_eq ?_)
  congr 1
  rw [hε_def]
  field_simp

/-- **Linear-slack form of Hoeffding's bound.**  If the quota lies a fraction `η ≥ 0` below the
mean, `q ≤ (p - η) n`, the probability of fewer than `q` successes is at most `exp (-2 η^2 n)`.
For fixed `η > 0` this decays exponentially in `n`. -/
theorem binomialLowerTail_le_exp_of_le {n q : ℕ} {p η : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hη : 0 ≤ η) (hq : (q : ℝ) ≤ (p - η) * n) :
    binomialLowerTail n q p ≤ Real.exp (-2 * η ^ 2 * n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hq0 : q = 0 := by exact_mod_cast le_antisymm (by simpa using hq) (Nat.cast_nonneg q)
    subst hq0
    rw [binomialLowerTail_zero_quota]
    exact (Real.exp_pos _).le
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hslack : η * n + 1 ≤ (n : ℝ) * p - q + 1 := by nlinarith
  have hηn : 0 ≤ η * n := mul_nonneg hη hn'.le
  refine (binomialLowerTail_le_exp hp0 hp1 (by nlinarith)).trans (Real.exp_le_exp.mpr ?_)
  rw [div_le_iff₀ hn']
  nlinarith

/-- **Chernoff bound with the Bernoulli relative entropy at the strict-shortfall integer endpoint.**
For a
reference rate `b < 1` with `(q - 1) / n < b ≤ p`, the probability of fewer than `q` successes is
at most `exp (-n klBer ((q - 1) / n) b)`.

Taking `b = p` gives the large-deviation exponent at the true rate; a smaller `b` gives one
bound for every `p ≥ b`, including `p = 1`.  For `n = 0` the bound is one, and for `q = 0` the
tail is zero, so in these cases the bound carries no information. -/
theorem binomialLowerTail_le_exp_neg_mul_klBer {n q : ℕ} {p b : ℝ}
    (hqb : ((q : ℝ) - 1) / n < b) (hbp : b ≤ p) (hp1 : p ≤ 1) (hb1 : b < 1) :
    binomialLowerTail n q p ≤
      Real.exp (-(n : ℝ) * Math.Concentration.BernoulliKL.klBer (((q : ℝ) - 1) / n) b) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero]
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · rw [binomialLowerTail_zero_quota]
      exact zero_le_one
    · exact (binomialLowerTail_of_lt hq p).le
  rw [binomialLowerTail_eq_threshold n q hn]
  exact Math.Concentration.BinomialKLTail.lowerTail_le_exp_neg_mul_klBer n p _ b hqb hbp hp1 hb1

end Math.Concentration.BinomialLowerTail
