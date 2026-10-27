import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! # Purified Distance -/


noncomputable section

open scoped BigOperators

namespace InfoTheory.SmoothMinEntropy

/-- Weighted Cauchy–Schwarz for square roots:
`(∑ wᵢ·√(uᵢvᵢ))² ≤ (∑ wᵢuᵢ)·(∑ wᵢvᵢ)`. -/
lemma sum_weight_sqrt_mul_sq_le
    (S : Finset ℕ) (w u v : ℕ → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hu : ∀ i ∈ S, 0 ≤ u i) (hv : ∀ i ∈ S, 0 ≤ v i) :
    (∑ i ∈ S, w i * Real.sqrt (u i * v i)) ^ 2 ≤
      (∑ i ∈ S, w i * u i) * (∑ i ∈ S, w i * v i) := by
  have key := Finset.sum_mul_sq_le_sq_mul_sq S
    (fun i => Real.sqrt (w i) * Real.sqrt (u i))
    (fun i => Real.sqrt (w i) * Real.sqrt (v i))
  have h1 :
      (∑ i ∈ S, Real.sqrt (w i) * Real.sqrt (u i) * (Real.sqrt (w i) * Real.sqrt (v i)))
        = ∑ i ∈ S, w i * Real.sqrt (u i * v i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [show Real.sqrt (w i) * Real.sqrt (u i) * (Real.sqrt (w i) * Real.sqrt (v i))
          = (Real.sqrt (w i)) ^ 2 * (Real.sqrt (u i) * Real.sqrt (v i)) by ring,
       Real.sq_sqrt (hw i hi), ← Real.sqrt_mul (hu i hi)]
  have h2 :
      (∑ i ∈ S, (Real.sqrt (w i) * Real.sqrt (u i)) ^ 2) = ∑ i ∈ S, w i * u i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi), Real.sq_sqrt (hu i hi)]
  have h3 :
      (∑ i ∈ S, (Real.sqrt (w i) * Real.sqrt (v i)) ^ 2) = ∑ i ∈ S, w i * v i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi), Real.sq_sqrt (hv i hi)]
  rw [h1, h2, h3] at key
  exact key

/-- Weighted termwise AM–GM summed: `2·∑ wᵢ√(uᵢvᵢ) ≤ ∑ wᵢuᵢ + ∑ wᵢvᵢ`. -/
lemma two_mul_sum_weight_sqrt_mul_le
    (S : Finset ℕ) (w u v : ℕ → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hu : ∀ i ∈ S, 0 ≤ u i) (hv : ∀ i ∈ S, 0 ≤ v i) :
    2 * (∑ i ∈ S, w i * Real.sqrt (u i * v i)) ≤
      (∑ i ∈ S, w i * u i) + (∑ i ∈ S, w i * v i) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  rw [Real.sqrt_mul (hu i hi)]
  set su := Real.sqrt (u i) with hsudef
  set sv := Real.sqrt (v i) with hsvdef
  have hsu : su ^ 2 = u i := Real.sq_sqrt (hu i hi)
  have hsv : sv ^ 2 = v i := Real.sq_sqrt (hv i hi)
  have hexp : 2 * (w i * (su * sv)) = w i * (su ^ 2 + sv ^ 2) - w i * (su - sv) ^ 2 := by ring
  rw [hexp, hsu, hsv]
  nlinarith [mul_nonneg (hw i hi) (sq_nonneg (su - sv))]

/-- The sub-normalization correction.  Given per-component generalized-fidelity
lower bounds `c ≤ aₛ + √(uₛvₛ)` (with weights summing with a slack `w₀` to one),
the weighted mixture's generalized fidelity
`∑ wₛaₛ + √((w₀+∑wₛuₛ)(w₀+∑wₛvₛ))` is at least `c`. -/
lemma weighted_mixture_fidelityGen_ge
    (S : Finset ℕ) (w a u v : ℕ → ℝ) (c w0 : ℝ)
    (hw : ∀ s ∈ S, 0 ≤ w s)
    (_ha : ∀ s ∈ S, 0 ≤ a s)
    (hu : ∀ s ∈ S, 0 ≤ u s) (hv : ∀ s ∈ S, 0 ≤ v s)
    (hw0 : 0 ≤ w0) (hc1 : c ≤ 1)
    (hsum : w0 + ∑ s ∈ S, w s = 1)
    (hcomp : ∀ s ∈ S, c ≤ a s + Real.sqrt (u s * v s)) :
    c ≤ (∑ s ∈ S, w s * a s) +
        Real.sqrt ((w0 + ∑ s ∈ S, w s * u s) * (w0 + ∑ s ∈ S, w s * v s)) := by
  set Wu := ∑ s ∈ S, w s * u s with hWu
  set Wv := ∑ s ∈ S, w s * v s with hWv
  set Wsq := ∑ s ∈ S, w s * Real.sqrt (u s * v s) with hWsq
  -- basic nonnegativities
  have hWu_nn : 0 ≤ Wu := Finset.sum_nonneg fun s hs => mul_nonneg (hw s hs) (hu s hs)
  have hWv_nn : 0 ≤ Wv := Finset.sum_nonneg fun s hs => mul_nonneg (hw s hs) (hv s hs)
  have hWsq_nn : 0 ≤ Wsq :=
    Finset.sum_nonneg fun s hs => mul_nonneg (hw s hs) (Real.sqrt_nonneg _)
  have hP_nn : 0 ≤ w0 + Wu := add_nonneg hw0 hWu_nn
  have hQ_nn : 0 ≤ w0 + Wv := add_nonneg hw0 hWv_nn
  -- the two Cauchy–Schwarz / AM–GM facts
  have hCS : Wsq ^ 2 ≤ Wu * Wv := sum_weight_sqrt_mul_sq_le S w u v hw hu hv
  have hAMGM : 2 * Wsq ≤ Wu + Wv := two_mul_sum_weight_sqrt_mul_le S w u v hw hu hv
  -- step: w0 + Wsq ≤ √((w0+Wu)(w0+Wv))
  have hstep : w0 + Wsq ≤ Real.sqrt ((w0 + Wu) * (w0 + Wv)) := by
    apply Real.le_sqrt_of_sq_le
    -- `(w0 + Wsq)² = w0² + w0·(2 Wsq) + Wsq² ≤ w0² + w0·(Wu + Wv) + Wu·Wv`
    linarith only [hCS, mul_le_mul_of_nonneg_left hAMGM hw0]
  -- weighted lower bound on ∑ w a + (w0 + Wsq)
  have hsum_le : c ≤ (∑ s ∈ S, w s * a s) + (w0 + Wsq) := by
    have hpart : (∑ s ∈ S, w s * a s) + Wsq = ∑ s ∈ S, w s * (a s + Real.sqrt (u s * v s)) := by
      rw [hWsq, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s hs; ring
    have hge : ∑ s ∈ S, w s * c ≤ ∑ s ∈ S, w s * (a s + Real.sqrt (u s * v s)) := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left (hcomp s hs) (hw s hs)
    have hwc : ∑ s ∈ S, w s * c = (∑ s ∈ S, w s) * c := by
      rw [Finset.sum_mul]
    have hsumw : ∑ s ∈ S, w s = 1 - w0 := by linarith only [hsum]
    have : (1 - w0) * c ≤ (∑ s ∈ S, w s * a s) + Wsq := by
      rw [← hsumw, ← hwc]; linarith only [hge, hpart]
    -- `c = (1 - w0)·c + w0·c` and `w0·c ≤ w0` since `c ≤ 1`
    linarith only [this, mul_le_mul_of_nonneg_left hc1 hw0]
  linarith only [hsum_le, hstep]

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
