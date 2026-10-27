import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# Hypergeometric Tail Basics — choose weights, centered counts, Chernoff reduction

This file contains the finite-sum primitives for the hypergeometric tail
argument: real-valued choose weights, the centered success count, and the
generic Chernoff reduction from an exponential-moment bound to a weighted tail
sum bound.

## Main definitions
- `centeredSuccessCount`: centered number of successes in a sample.
- `chooseWeight`: real-valued hypergeometric choose weight.
- `centeredHypergeometricMGF`: normalized centered hypergeometric MGF.

## Main statements
- `hypergeometric_tail_sum_le_exp_neg_mul_mgf`: finite-sum Chernoff reduction for
  the hypergeometric choose tail.
-/

open scoped BigOperators

namespace Math.Concentration.HypergeometricTail

/-- The centered success count appearing in the hypergeometric MGF. -/
noncomputable def centeredSuccessCount (N n K k : ℕ) : ℝ :=
  (k : ℝ) - (n : ℝ) * (K : ℝ) / N

/-- The real-valued hypergeometric choose weight. -/
noncomputable def chooseWeight (N n K k : ℕ) : ℝ :=
  ((K.choose k * (N - K).choose (n - k) : ℕ) : ℝ)

/-- The normalized centered hypergeometric moment-generating function. -/
noncomputable def centeredHypergeometricMGF (N n K : ℕ) (t : ℝ) : ℝ :=
  (∑ k ∈ Finset.range (n + 1),
      chooseWeight N n K k *
        Real.exp (t * centeredSuccessCount N n K k)) /
    N.choose n

/-- Hypergeometric choose weights are nonnegative after coercion to reals. -/
lemma chooseWeight_nonneg (N n K k : ℕ) :
    0 ≤ chooseWeight N n K k := by
  exact Nat.cast_nonneg _

/-- The bad empirical-frequency event implies a centered-count threshold. -/
lemma centered_threshold_lt_of_bad
    {N n K k : ℕ} (hn : n ≠ 0) (δ : ℝ)
    (hbad : (K : ℝ) / N + δ < (k : ℝ) / n) :
    (n : ℝ) * δ < centeredSuccessCount N n K k := by
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hmul : ((K : ℝ) / N + δ) * (n : ℝ) < (k : ℝ) :=
    (lt_div_iff₀ hn_pos).mp hbad
  unfold centeredSuccessCount
  ring_nf at hmul ⊢
  nlinarith

/-- A finite-sum Chernoff bound from an exponential-moment sum. -/
lemma indicator_sum_le_exp_neg_mul_mgf
    {ι : Type*} (s : Finset ι) (p : ι → Prop) [DecidablePred p]
    (w x : ι → ℝ) {a t : ℝ} (ht : 0 < t)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hp : ∀ i ∈ s, p i → a ≤ x i) :
    ∑ i ∈ s, (if p i then w i else 0) ≤
      Real.exp (-t * a) * ∑ i ∈ s, w i * Real.exp (t * x i) := by
  calc
    ∑ i ∈ s, (if p i then w i else 0)
        ≤ ∑ i ∈ s, Real.exp (-t * a) * (w i * Real.exp (t * x i)) := by
          apply Finset.sum_le_sum
          intro i hi
          by_cases hpi : p i
          · have hx_nonneg : 0 ≤ t * (x i - a) :=
              mul_nonneg (le_of_lt ht) (sub_nonneg.mpr (hp i hi hpi))
            have hexp : 1 ≤ Real.exp (t * (x i - a)) :=
              Real.one_le_exp hx_nonneg
            have hmul : w i * 1 ≤ w i * Real.exp (t * (x i - a)) :=
              mul_le_mul_of_nonneg_left hexp (hw i hi)
            have harg : t * (x i - a) = -t * a + t * x i := by ring
            have hrewrite :
                w i * Real.exp (t * (x i - a)) =
                  Real.exp (-t * a) * (w i * Real.exp (t * x i)) := by
              rw [harg, Real.exp_add]
              ring
            simpa [hpi, hrewrite]
              using hmul
          · have hnonneg :
                0 ≤ Real.exp (-t * a) * (w i * Real.exp (t * x i)) :=
              mul_nonneg (le_of_lt (Real.exp_pos _))
                (mul_nonneg (hw i hi) (le_of_lt (Real.exp_pos _)))
            simpa [hpi] using hnonneg
    _ = Real.exp (-t * a) * ∑ i ∈ s, w i * Real.exp (t * x i) := by
          rw [Finset.mul_sum]

/-- Markov/Chernoff reduction for the hypergeometric choose tail. -/
lemma hypergeometric_tail_sum_le_exp_neg_mul_mgf
    {N n K : ℕ} (hn : n ≠ 0) (δ t : ℝ) (ht : 0 < t) :
    ((∑ k ∈ Finset.range (n + 1),
        if (K : ℝ) / N + δ < (k : ℝ) / n then
          K.choose k * (N - K).choose (n - k)
        else 0 : ℕ) : ℝ) ≤
      Real.exp (-t * ((n : ℝ) * δ)) *
        ∑ k ∈ Finset.range (n + 1),
          chooseWeight N n K k *
            Real.exp (t * centeredSuccessCount N n K k) := by
  rw [Nat.cast_sum]
  have h :=
    indicator_sum_le_exp_neg_mul_mgf
      (s := Finset.range (n + 1))
      (p := fun k : ℕ => (K : ℝ) / N + δ < (k : ℝ) / n)
      (w := chooseWeight N n K)
      (x := centeredSuccessCount N n K)
      (a := (n : ℝ) * δ) (t := t) ht
      (by
        intro k _hk
        exact chooseWeight_nonneg N n K k)
      (by
        intro k _hk hbad
        exact le_of_lt (centered_threshold_lt_of_bad hn δ hbad))
  simpa [chooseWeight] using h

end Math.Concentration.HypergeometricTail
