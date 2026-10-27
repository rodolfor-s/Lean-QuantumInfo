import QCryptLean.Math.Concentration.HypergeometricTail.Basic
import QCryptLean.Math.Concentration.HypergeometricTail.SerflingMGF

/-!
# Hypergeometric Upper Tail — Serfling's `(N − n + 1)` variance factor

This file re-threads the finite-sum Chernoff reduction through the
Serfling MGF envelope `centeredHypergeometricMGF_le_serfling_exp` (`SerflingMGF.lean`) instead of
the
crude Hoeffding envelope, producing the hypergeometric upper-tail choose bound with the
without-replacement variance factor `(N − n + 1)/N`.

The reduction itself is unchanged from the crude upper-tail file; only the
Chernoff-optimal `t` and the resulting exponent change:

- crude form (`hypergeometric_choose_upper_tail`): `t = 4δ`, tail `exp(−2nδ²)`;
- form (this file):  `t = 4Nδ/(N − n + 1)`, tail
  `exp(−2nδ² · N/(N − n + 1))`.

Because `N/(N − n + 1) ≥ 1` for `1 ≤ n ≤ N`, the tail is uniformly at least
as strong as the crude one, with equality exactly at `n = 1`.  This factor is the
sampling calculation for the TLGR finite-key parameter-estimation deviation; see
`SerflingVarianceReduction.lean` for the model wrapper and the two-sample
`μ`-corollary.

## Main statements
- `hypergeometric_choose_upper_tail_varianceReduction`: normalized hypergeometric upper-tail
  choose sum is bounded by `exp(−2nδ² · N/(N − n + 1))`.
-/

open scoped BigOperators

namespace Math.Concentration.HypergeometricTail

/-- hypergeometric upper-tail choose bound from the centered MGF
comparison `centeredHypergeometricMGF_le_serfling_exp`.

The Chernoff parameter is optimized to `t = 4Nδ/(N − n + 1)`, giving the
without-replacement tail `exp(−2nδ² · N/(N − n + 1))` — strictly sharper than the
crude `exp(−2nδ²)` of `hypergeometric_choose_upper_tail` whenever `n > 1`. -/
lemma hypergeometric_choose_upper_tail_varianceReduction
    {N n K : ℕ} (hKN : K ≤ N) (hN : n ≤ N) (hn : n ≠ 0)
    (δ : ℝ) (hδ : 0 < δ) :
    ((∑ k ∈ Finset.range (n + 1),
        if (K : ℝ) / N + δ < (k : ℝ) / n then
          K.choose k * (N - K).choose (n - k)
        else 0 : ℕ) : ℝ) /
      N.choose n ≤
        Real.exp (-2 * (n : ℝ) * δ ^ 2 * (N : ℝ) / ((N : ℝ) - (n : ℝ) + 1)) := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hNpos : 0 < N := lt_of_lt_of_le hnpos hN
  have hN_pos_real : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hNpos
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos_real
  have hn_le_N_real : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hD_pos : (0 : ℝ) < (N : ℝ) - (n : ℝ) + 1 := by linarith
  have hD_ne : (N : ℝ) - (n : ℝ) + 1 ≠ 0 := ne_of_gt hD_pos
  let t : ℝ := 4 * (N : ℝ) * δ / ((N : ℝ) - (n : ℝ) + 1)
  have ht_pos : 0 < t := by
    apply div_pos _ hD_pos
    positivity
  have hden_nonneg : 0 ≤ (N.choose n : ℝ) := Nat.cast_nonneg _
  have htail :=
    hypergeometric_tail_sum_le_exp_neg_mul_mgf
      (N := N) (n := n) (K := K) hn δ t ht_pos
  have htail_div :
      ((∑ k ∈ Finset.range (n + 1),
        if (K : ℝ) / N + δ < (k : ℝ) / n then
          K.choose k * (N - K).choose (n - k)
        else 0 : ℕ) : ℝ) / N.choose n ≤
        (Real.exp (-t * ((n : ℝ) * δ)) *
          ∑ k ∈ Finset.range (n + 1),
            chooseWeight N n K k *
              Real.exp (t * centeredSuccessCount N n K k)) / N.choose n :=
    div_le_div_of_nonneg_right htail hden_nonneg
  have hmgf :
      (∑ k ∈ Finset.range (n + 1),
          chooseWeight N n K k *
            Real.exp (t * centeredSuccessCount N n K k)) /
        N.choose n ≤
        Real.exp (t ^ 2 * (n : ℝ) * ((N : ℝ) - (n : ℝ) + 1) / (8 * (N : ℝ))) := by
    simpa [centeredHypergeometricMGF] using
      centeredHypergeometricMGF_le_serfling_exp (N := N) (n := n) (K := K) hKN hN t
  have hmul :
      (Real.exp (-t * ((n : ℝ) * δ)) *
        ∑ k ∈ Finset.range (n + 1),
          chooseWeight N n K k *
            Real.exp (t * centeredSuccessCount N n K k)) / N.choose n ≤
        Real.exp (-t * ((n : ℝ) * δ)) *
          Real.exp (t ^ 2 * (n : ℝ) * ((N : ℝ) - (n : ℝ) + 1) / (8 * (N : ℝ))) := by
    have hC_nonneg : 0 ≤ Real.exp (-t * ((n : ℝ) * δ)) := le_of_lt (Real.exp_pos _)
    calc
      (Real.exp (-t * ((n : ℝ) * δ)) *
        ∑ k ∈ Finset.range (n + 1),
          chooseWeight N n K k *
            Real.exp (t * centeredSuccessCount N n K k)) / N.choose n
          = Real.exp (-t * ((n : ℝ) * δ)) *
              ((∑ k ∈ Finset.range (n + 1),
                chooseWeight N n K k *
                  Real.exp (t * centeredSuccessCount N n K k)) /
                N.choose n) := by ring
      _ ≤ Real.exp (-t * ((n : ℝ) * δ)) *
            Real.exp (t ^ 2 * (n : ℝ) * ((N : ℝ) - (n : ℝ) + 1) / (8 * (N : ℝ))) :=
          mul_le_mul_of_nonneg_left hmgf hC_nonneg
  have hexp :
      Real.exp (-t * ((n : ℝ) * δ)) *
          Real.exp (t ^ 2 * (n : ℝ) * ((N : ℝ) - (n : ℝ) + 1) / (8 * (N : ℝ))) =
        Real.exp (-2 * (n : ℝ) * δ ^ 2 * (N : ℝ) / ((N : ℝ) - (n : ℝ) + 1)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [t]
    field_simp
    ring
  exact htail_div.trans (hmul.trans (le_of_eq hexp))

end Math.Concentration.HypergeometricTail
