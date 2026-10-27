import QCryptLean.Math.Concentration.HypergeometricTail.Basic
import QCryptLean.Math.Concentration.HypergeometricTail.MGF

/-!
# Hypergeometric Upper Tail Bound — MGF-to-tail Chernoff inequality

This file combines the finite-sum Chernoff reduction with the centered
hypergeometric MGF comparison to prove the upper-tail choose bound used by the
finite Serfling counting core.

## Main statements
- `hypergeometric_choose_upper_tail`: normalized hypergeometric upper-tail
  choose sum is bounded by `exp (-2 * n * δ ^ 2)`.
-/

open scoped BigOperators

namespace Math.Concentration.HypergeometricTail

/-- Hypergeometric upper-tail choose bound from the centered MGF comparison. -/
lemma hypergeometric_choose_upper_tail
    {N n K : ℕ} (hKN : K ≤ N) (hN : n ≤ N) (hn : n ≠ 0)
    (δ : ℝ) (hδ : 0 < δ) :
    ((∑ k ∈ Finset.range (n + 1),
        if (K : ℝ) / N + δ < (k : ℝ) / n then
          K.choose k * (N - K).choose (n - k)
        else 0 : ℕ) : ℝ) /
      N.choose n ≤ Real.exp (-2 * n * δ ^ 2) := by
  let t : ℝ := 4 * δ
  have ht_pos : 0 < t := by
    dsimp [t]
    nlinarith
  have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
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
              Real.exp (t * centeredSuccessCount N n K k)) / N.choose n := by
    exact div_le_div_of_nonneg_right htail hden_nonneg
  have hmgf :=
    hypergeometricChooseCenteredMGF_le
      (N := N) (n := n) (K := K) hKN hN hn t ht_nonneg
  have hmul :
      (Real.exp (-t * ((n : ℝ) * δ)) *
        ∑ k ∈ Finset.range (n + 1),
          chooseWeight N n K k *
            Real.exp (t * centeredSuccessCount N n K k)) / N.choose n ≤
        Real.exp (-t * ((n : ℝ) * δ)) * Real.exp (t ^ 2 * n / 8) := by
    have hC_nonneg : 0 ≤ Real.exp (-t * ((n : ℝ) * δ)) :=
      le_of_lt (Real.exp_pos _)
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
            Real.exp (t ^ 2 * n / 8) :=
          mul_le_mul_of_nonneg_left hmgf hC_nonneg
  have hexp :
      Real.exp (-t * ((n : ℝ) * δ)) * Real.exp (t ^ 2 * n / 8) =
        Real.exp (-2 * n * δ ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [t]
    ring
  exact htail_div.trans (hmul.trans (le_of_eq hexp))

end Math.Concentration.HypergeometricTail
