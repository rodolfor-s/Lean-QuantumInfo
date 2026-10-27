import QCryptLean.Math.Concentration.HypergeometricTail.Basic
import QCryptLean.Math.Concentration.HypergeometricTail.MGF
import QCryptLean.Math.Concentration.HypergeometricTail.TwoPoint

/-!
# Hypergeometric MGF Bound — Serfling's `(N − n + 1)/N` variance factor

This file sharpens the centered hypergeometric moment-generating-function bound
from the Hoeffding envelope `exp (t² · n / 8)` (proved in `MGF.lean`) to the **Serfling** form

`centeredHypergeometricMGF N n K t ≤ exp (t² · n · (N − n + 1) / (8 · N))`.

The extra factor `(N − n + 1) / N ≤ 1` is the without-replacement variance
reduction: a size-`n` sample from a population of size `N` has variance proxy
`n · (N − n + 1) / N` rather than the with-replacement `n`.

## Why the form matters

For the TLGR finite-key parameter-estimation bound the sample is the `n`-round
key block drawn from an `N = n + k` population (`k` = number of test rounds).
The Serfling factor here evaluates to `(N − n + 1)/N = (k + 1)/N`.  This factor is
the *sole* source of the `(k + 1)` that appears in the **denominator** of the
downstream two-sample tail exponent `−2nk²μ²/((n+k)(k+1))`.

The full TLGR deviation `μ = √[N/(nk) · (k+1)/k · ln(1/ε)]` — with its `k²`/`(n+k)`
two-sample structure under the root — is *not* reconstructible from this
single-sample MGF alone: it is assembled downstream by converting the key-sample
deviation `keyFreq − popFreq` into the key-vs-test deviation
`keyFreq − testFreq = (N/k)(keyFreq − popFreq)`.  The exact fixed constant is
stated in Lean by `Math.Concentration.Serfling.tlgr_mu_upper_tail`, which consumes this file's
envelope through
`upper_tail_varianceReduction`.

The simplified Hoeffding form (factor `1` instead of `(k+1)/N`) drops that
`(k + 1)` — replacing it by `N = n + k` inside the exponent — degrading `μ` by a
factor `≈ √(n/k)` for `n ≫ k`, fatal for the fixed TLGR constant.  Hence this
file, not the `hypergeometricChooseCenteredMGF_le`, is the sampling
calculation for the TLGR statistics interface.

## Proof structure (Serfling 1974, Cor. 1.1 argument via TLGR §S10)

Serfling's accounting is a recursion on the *bound*, not a term-wise product.
The first-draw recurrence (`centeredHypergeometricMGF_first_draw`, provided in
`MGF.lean`) reduces `(N, n, K)` to `(N − 1, n − 1, K′)`.  Each reduction carries
a two-point factor whose support half-width is exactly `(N − n) / (N − 1)`
(`twoPoint_centeredMGF_le_width`), contributing `exp((N − n)²/(N − 1)² · t²/8)`.
The invariant `N − n` is fixed along the recursion, so the accumulated exponent
telescopes into the sum `∑ⱼ (N − n)²/(N − j)²`, and the target is the
closed-form envelope of that sum.

The key is that the per-step envelope inequality closes **exactly** by induction,
avoiding the naive argument: a term-wise product gives `(t²/8)(N − n)² ∑ⱼ 1/j²`, and
crude integral bounds on `∑ 1/j²` *overshoot at the `n = 1` edge* (where the sum
is a single term and the bound is attained with equality).  Instead
`serflingVariance_recursion_le` proves the per-step envelope step
`(N − n)²/(N − 1)² + (n − 1)(N − n + 1)/(N − 1) ≤ n (N − n + 1)/N`
whose defect equals `(N − n)(n − 1)/(N (N − 1)²) ≥ 0`; positivity is exactly
`n ≥ 1`, so the recursion never leaks — including the `n = 1` base of the tail.

The `n = 1` edge (single-draw sample) is handled uniformly by the degenerate
`n = N` / `K = 0` / `K = N` branches and the nondegenerate step: the exponent is `≥ 0` throughout,
so the MGF `= 1` degenerate cases are immediate.

## Main statements
- `twoPoint_centeredMGF_le_width`: width-parametric two-point Hoeffding bound.
- `hypergeometric_branch_offsets_mgf_le_exp`: per-step branch bound.
- `serflingVariance_recursion_le`: Serfling's per-step variance-accounting inequality.
- `centeredHypergeometricMGF_le_serfling_exp`: the Serfling MGF envelope.
-/

open scoped BigOperators

open MeasureTheory ProbabilityTheory

namespace Math.Concentration.HypergeometricTail

/-- Width-parametric two-point MGF bound: a centered two-point random variable
with support `{a, b}` (`a ≤ b`) has MGF bounded by the sub-Gaussian envelope
`exp((b − a)² · t² / 8)` for every `t`.

This is the companion of `twoPoint_centeredMGF_le`, which fixes the
half-width to `1`; here the actual width `b − a` is kept, giving the tighter
`(b − a)²` variance proxy that Serfling's recursion consumes at each draw. -/
lemma twoPoint_centeredMGF_le_width
    {p a b t : ℝ} (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1)
    (hab : a ≤ b) (hmean : p * a + (1 - p) * b = 0) :
    p * Real.exp (t * a) + (1 - p) * Real.exp (t * b) ≤
      Real.exp ((b - a) ^ 2 * t ^ 2 / 8) := by
  let X : Bool → ℝ := fun q => if q then a else b
  let μ : Measure Bool := twoPointMeasure p
  have hμprob : IsProbabilityMeasure μ :=
    isProbabilityMeasure_twoPointMeasure hp_nonneg hp_le_one
  let : IsProbabilityMeasure μ := hμprob
  have hmeas : AEMeasurable X μ := (measurable_of_finite X).aemeasurable
  have hbounded : ∀ᵐ q ∂μ, X q ∈ Set.Icc a b := by
    filter_upwards with q
    cases q <;> simp [X, hab]
  have hcenter : μ[X] = 0 := by
    change ∫ x, X x ∂μ = 0
    dsimp [μ]
    simpa [X, hmean] using
      integral_twoPointMeasure (p := p) hp_nonneg hp_le_one X
  let c : NNReal := (‖b - a‖₊ / 2) ^ 2
  have hsubg : HasSubgaussianMGF X c μ := by
    dsimp [c]
    exact hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hmeas hbounded hcenter
  have hmgf : ProbabilityTheory.mgf X μ t ≤ Real.exp ((c : ℝ) * t ^ 2 / 2) :=
    hsubg.mgf_le t
  have hleft :
      p * Real.exp (t * a) + (1 - p) * Real.exp (t * b) =
        ProbabilityTheory.mgf X μ t := by
    simpa [μ, X] using
      (mgf_twoPointMeasure (p := p) (a := a) (b := b) (t := t)
        hp_nonneg hp_le_one).symm
  have hdiff_nonneg : 0 ≤ b - a := sub_nonneg.mpr hab
  have hc_eq : (c : ℝ) = (b - a) ^ 2 / 4 := by
    dsimp [c]
    rw [abs_of_nonneg hdiff_nonneg]
    ring
  have hexp_eq : (c : ℝ) * t ^ 2 / 2 = (b - a) ^ 2 * t ^ 2 / 8 := by
    rw [hc_eq]; ring
  calc
    p * Real.exp (t * a) + (1 - p) * Real.exp (t * b)
        = ProbabilityTheory.mgf X μ t := hleft
    _ ≤ Real.exp ((c : ℝ) * t ^ 2 / 2) := hmgf
    _ = Real.exp ((b - a) ^ 2 * t ^ 2 / 8) := by rw [hexp_eq]

/-- per-step branch bound.  The first-draw success/failure offsets have a
two-point MGF bounded by the width-`(N − n)/(N − 1)` Hoeffding envelope

`exp((N − n)²/(N − 1)² · t²/8)`,

sharpening `hypergeometric_branch_offsets_mgf_le` (which uses the crude
`width ≤ 1` bound `exp(t²/8)`). -/
lemma hypergeometric_branch_offsets_mgf_le_exp
    {N n K : ℕ} (hKN : K ≤ N) (hKpos : 0 < K) (hK_lt_N : K < N)
    (hn_lt_N : n < N) (t : ℝ) :
    ((N - K : ℕ) : ℝ) / N *
        Real.exp (t * (-(K : ℝ) * ((N : ℝ) - n) /
          ((N : ℝ) * ((N : ℝ) - 1)))) +
      (K : ℝ) / N *
        Real.exp (t * (((N : ℝ) - K) * ((N : ℝ) - n) /
          ((N : ℝ) * ((N : ℝ) - 1)))) ≤
      Real.exp (((N : ℝ) - n) ^ 2 / ((N : ℝ) - 1) ^ 2 * t ^ 2 / 8) := by
  let p : ℝ := ((N - K : ℕ) : ℝ) / N
  let a : ℝ := -(K : ℝ) * ((N : ℝ) - n) /
    ((N : ℝ) * ((N : ℝ) - 1))
  let b : ℝ := ((N : ℝ) - K) * ((N : ℝ) - n) /
    ((N : ℝ) * ((N : ℝ) - 1))
  have hNpos : 0 < N := lt_of_lt_of_le hKpos hKN
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hN_pos_real : 0 < (N : ℝ) := Nat.cast_pos.mpr hNpos
  have hN_gt_one : 1 < N := lt_of_le_of_lt (Nat.succ_le_of_lt hKpos) hK_lt_N
  have hN_gt_one_real : (1 : ℝ) < N := by exact_mod_cast hN_gt_one
  have hNm1_pos : 0 < (N : ℝ) - 1 := sub_pos.mpr hN_gt_one_real
  have hNm1_ne : ((N : ℝ) - 1) ≠ 0 := ne_of_gt hNm1_pos
  have hKN_cast : ((N - K : ℕ) : ℝ) = (N : ℝ) - K := Nat.cast_sub hKN
  have hp_nonneg : 0 ≤ p := by
    dsimp [p]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg N)
  have hp_le_one : p ≤ 1 := by
    dsimp [p]
    rw [hKN_cast]
    exact (div_le_one hN_pos_real).mpr
      (sub_le_self (N : ℝ) (Nat.cast_nonneg K))
  have hdiff : b - a = ((N : ℝ) - n) / ((N : ℝ) - 1) := by
    dsimp [a, b]
    field_simp [hN_ne, hNm1_ne]
    ring
  have hab : a ≤ b := by
    have hn_le_N_real : (n : ℝ) ≤ N := by exact_mod_cast le_of_lt hn_lt_N
    have hdiff_nonneg : 0 ≤ b - a := by
      rw [hdiff]
      exact div_nonneg (sub_nonneg.mpr hn_le_N_real) (le_of_lt hNm1_pos)
    exact sub_nonneg.mp hdiff_nonneg
  have hmean : p * a + (1 - p) * b = 0 := by
    dsimp [p, a, b]
    rw [hKN_cast]
    field_simp [hN_ne, hNm1_ne]
    ring
  have hp_compl : 1 - p = (K : ℝ) / N := by
    dsimp [p]
    rw [hKN_cast]
    field_simp [hN_ne]
    ring
  have htwo :=
    twoPoint_centeredMGF_le_width
      (p := p) (a := a) (b := b) (t := t)
      hp_nonneg hp_le_one hab hmean
  rw [hp_compl, hdiff, div_pow] at htwo
  simpa [p, a, b] using htwo

/-- Serfling's per-step variance-accounting inequality.  With `nr = n`,
`Nr = N` (as reals, `1 ≤ n ≤ N`, `2 ≤ N`) the two-point step contributes
`(Nr − nr)²/(Nr − 1)²` on top of the inductive envelope
`(nr − 1)(Nr − nr + 1)/(Nr − 1)`, and their sum stays under the target
`nr (Nr − nr + 1)/Nr`.

The defect is `(Nr − nr)(nr − 1)/(Nr (Nr − 1)²) ≥ 0`; the sign is exactly
`nr ≥ 1` and `nr ≤ Nr`, so the recursion closes with no slack lost at the
`nr = 1` base. -/
lemma serflingVariance_recursion_le
    {Nr nr : ℝ} (hn1 : 1 ≤ nr) (hnN : nr ≤ Nr) (hN2 : 2 ≤ Nr) :
    (Nr - nr) ^ 2 / (Nr - 1) ^ 2 + (nr - 1) * (Nr - nr + 1) / (Nr - 1) ≤
      nr * (Nr - nr + 1) / Nr := by
  have hNr_pos : 0 < Nr := by linarith
  have hNr1_pos : 0 < Nr - 1 := by linarith
  have hNr_ne : Nr ≠ 0 := ne_of_gt hNr_pos
  have hNr1_ne : Nr - 1 ≠ 0 := ne_of_gt hNr1_pos
  have key :
      nr * (Nr - nr + 1) / Nr -
          ((Nr - nr) ^ 2 / (Nr - 1) ^ 2 +
            (nr - 1) * (Nr - nr + 1) / (Nr - 1)) =
        (Nr - nr) * (nr - 1) / (Nr * (Nr - 1) ^ 2) := by
    field_simp
    ring
  have hden_nonneg : 0 ≤ Nr * (Nr - 1) ^ 2 :=
    mul_nonneg (le_of_lt hNr_pos) (sq_nonneg _)
  have hdefect_nonneg : 0 ≤ (Nr - nr) * (nr - 1) / (Nr * (Nr - 1) ^ 2) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) hden_nonneg
  linarith [key, hdefect_nonneg]

/-- The exponent `t² · n · (N − n + 1) / (8 N)` is nonnegative whenever
`n ≤ N`.  This discharges every degenerate branch (where the MGF equals `1`). -/
lemma serflingExponent_nonneg {N n : ℕ} (hN : n ≤ N) (t : ℝ) :
    0 ≤ t ^ 2 * (n : ℝ) * ((N : ℝ) - (n : ℝ) + 1) / (8 * (N : ℝ)) := by
  have hn_le : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  apply div_nonneg
  · exact mul_nonneg (mul_nonneg (sq_nonneg t) (Nat.cast_nonneg n)) (by linarith)
  · positivity

/-- Nondegenerate induction step for the centered hypergeometric MGF
bound.  Both sub-MGFs are bounded by the envelope at `(N − 1, n − 1)`; the
two-point branch factor plus `serflingVariance_recursion_le` closes the step at
`(N, n)`. -/
lemma centeredHypergeometricMGF_le_serfling_exp_of_recursion
    {N n K : ℕ} (hKN : K ≤ N) (hKpos : 0 < K) (hK_lt_N : K < N)
    (hnpos : 0 < n) (hn_lt_N : n < N) (t : ℝ)
    (hsuccess :
      centeredHypergeometricMGF (N - 1) (n - 1) (K - 1) t ≤
        Real.exp (t ^ 2 * ((n : ℝ) - 1) * ((N : ℝ) - (n : ℝ) + 1) /
          (8 * ((N : ℝ) - 1))))
    (hfailure :
      centeredHypergeometricMGF (N - 1) (n - 1) K t ≤
        Real.exp (t ^ 2 * ((n : ℝ) - 1) * ((N : ℝ) - (n : ℝ) + 1) /
          (8 * ((N : ℝ) - 1)))) :
    centeredHypergeometricMGF N n K t ≤
      Real.exp (t ^ 2 * (n : ℝ) * ((N : ℝ) - (n : ℝ) + 1) / (8 * (N : ℝ))) := by
  let successOffset : ℝ := ((N : ℝ) - K) * ((N : ℝ) - n) /
    ((N : ℝ) * ((N : ℝ) - 1))
  let failureOffset : ℝ := -(K : ℝ) * ((N : ℝ) - n) /
    ((N : ℝ) * ((N : ℝ) - 1))
  let Einner : ℝ := t ^ 2 * ((n : ℝ) - 1) * ((N : ℝ) - (n : ℝ) + 1) /
    (8 * ((N : ℝ) - 1))
  let W : ℝ := ((N : ℝ) - n) ^ 2 / ((N : ℝ) - 1) ^ 2 * t ^ 2 / 8
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hnpos
  have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast le_of_lt hn_lt_N
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by
    have : 2 ≤ N := by omega
    exact_mod_cast this
  have hE_nonneg : 0 ≤ Real.exp Einner := (Real.exp_pos _).le
  have hsuccess_term :
      (K : ℝ) / N * Real.exp (t * successOffset) *
          centeredHypergeometricMGF (N - 1) (n - 1) (K - 1) t ≤
        (K : ℝ) / N * Real.exp (t * successOffset) * Real.exp Einner := by
    have hcoef_nonneg : 0 ≤ (K : ℝ) / N * Real.exp (t * successOffset) :=
      mul_nonneg (div_nonneg (Nat.cast_nonneg K) (Nat.cast_nonneg N))
        (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_left hsuccess hcoef_nonneg
  have hfailure_term :
      ((N - K : ℕ) : ℝ) / N * Real.exp (t * failureOffset) *
          centeredHypergeometricMGF (N - 1) (n - 1) K t ≤
        ((N - K : ℕ) : ℝ) / N * Real.exp (t * failureOffset) *
          Real.exp Einner := by
    have hcoef_nonneg : 0 ≤ ((N - K : ℕ) : ℝ) / N * Real.exp (t * failureOffset) :=
      mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg N))
        (Real.exp_pos _).le
    exact mul_le_mul_of_nonneg_left hfailure hcoef_nonneg
  have hbranch :
      ((N - K : ℕ) : ℝ) / N * Real.exp (t * failureOffset) +
          (K : ℝ) / N * Real.exp (t * successOffset) ≤
        Real.exp W :=
    hypergeometric_branch_offsets_mgf_le_exp
      (N := N) (n := n) (K := K) hKN hKpos hK_lt_N hn_lt_N t
  have hrec :=
    centeredHypergeometricMGF_first_draw
      (N := N) (n := n) (K := K) hKN hKpos hK_lt_N hnpos hn_lt_N t
  have harith :
      Einner + W ≤
        t ^ 2 * (n : ℝ) * ((N : ℝ) - (n : ℝ) + 1) / (8 * (N : ℝ)) := by
    have hbase := serflingVariance_recursion_le (Nr := (N : ℝ)) (nr := (n : ℝ)) hn1 hnN hN2
    have ht8 : (0 : ℝ) ≤ t ^ 2 / 8 := by positivity
    have hstep := mul_le_mul_of_nonneg_left hbase ht8
    have hNm1_ne : ((N : ℝ) - 1) ≠ 0 := by
      have : (0 : ℝ) < (N : ℝ) - 1 := by linarith
      exact ne_of_gt this
    have hN_ne : (N : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (N : ℝ) := by linarith
      exact ne_of_gt this
    have hEW :
        Einner + W =
          t ^ 2 / 8 *
            (((N : ℝ) - n) ^ 2 / ((N : ℝ) - 1) ^ 2 +
              ((n : ℝ) - 1) * ((N : ℝ) - (n : ℝ) + 1) / ((N : ℝ) - 1)) := by
      dsimp [Einner, W]; field_simp; ring
    have htgt :
        t ^ 2 / 8 * ((n : ℝ) * ((N : ℝ) - (n : ℝ) + 1) / (N : ℝ)) =
          t ^ 2 * (n : ℝ) * ((N : ℝ) - (n : ℝ) + 1) / (8 * (N : ℝ)) := by
      field_simp
    rw [hEW, ← htgt]
    exact hstep
  calc
    centeredHypergeometricMGF N n K t
        = (K : ℝ) / N * Real.exp (t * successOffset) *
            centeredHypergeometricMGF (N - 1) (n - 1) (K - 1) t +
          ((N - K : ℕ) : ℝ) / N * Real.exp (t * failureOffset) *
            centeredHypergeometricMGF (N - 1) (n - 1) K t := by
          simpa [successOffset, failureOffset] using hrec
    _ ≤ (K : ℝ) / N * Real.exp (t * successOffset) * Real.exp Einner +
          ((N - K : ℕ) : ℝ) / N * Real.exp (t * failureOffset) *
            Real.exp Einner :=
        add_le_add hsuccess_term hfailure_term
    _ = Real.exp Einner *
          (((N - K : ℕ) : ℝ) / N * Real.exp (t * failureOffset) +
            (K : ℝ) / N * Real.exp (t * successOffset)) := by ring
    _ ≤ Real.exp Einner * Real.exp W :=
        mul_le_mul_of_nonneg_left hbranch hE_nonneg
    _ = Real.exp (Einner + W) := (Real.exp_add Einner W).symm
    _ ≤ Real.exp (t ^ 2 * (n : ℝ) * ((N : ℝ) - (n : ℝ) + 1) / (8 * (N : ℝ))) :=
        Real.exp_le_exp.mpr harith

/-- The Serfling MGF envelope for the centered hypergeometric distribution.

For a size-`n` sample (`n ≤ N`) with `K ≤ N` marked elements, the normalized
centered MGF is bounded by the without-replacement sub-Gaussian envelope with the
variance factor `(N − n + 1)/N`:

`centeredHypergeometricMGF N n K t ≤ exp(t² · n · (N − n + 1) / (8 N))`.

This is strictly sharper than the Hoeffding form
`hypergeometricChooseCenteredMGF_le` (factor `1` in place of `(N − n + 1)/N`)
and is the sampling calculation for the TLGR finite-key parameter-estimation
bound; see the module docstring.  The bound holds for every real `t`. -/
lemma centeredHypergeometricMGF_le_serfling_exp
    {N n K : ℕ} (hKN : K ≤ N) (hN : n ≤ N) (t : ℝ) :
    centeredHypergeometricMGF N n K t ≤
      Real.exp (t ^ 2 * (n : ℝ) * ((N : ℝ) - (n : ℝ) + 1) / (8 * (N : ℝ))) := by
  classical
  revert N K
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro N K hKN hN
      by_cases hn0 : n = 0
      · subst hn0
        have hmgf1 : centeredHypergeometricMGF N 0 K t = 1 := by
          unfold centeredHypergeometricMGF
          rw [hypergeometricCenteredMGF_sum_of_n_eq_zero N K t]
          simp
        rw [hmgf1]
        exact Real.one_le_exp (serflingExponent_nonneg hN t)
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      by_cases hK0 : K = 0
      · subst hK0
        have hmgf1 : centeredHypergeometricMGF N n 0 t = 1 := by
          unfold centeredHypergeometricMGF
          rw [hypergeometricCenteredMGF_sum_of_zero_success N n t]
          exact div_self (by exact_mod_cast (Nat.choose_pos hN).ne')
        rw [hmgf1]
        exact Real.one_le_exp (serflingExponent_nonneg hN t)
      have hKpos : 0 < K := Nat.pos_of_ne_zero hK0
      by_cases hKN_eq : K = N
      · have hmgf1 : centeredHypergeometricMGF N n K t = 1 := by
          unfold centeredHypergeometricMGF
          rw [hKN_eq, hypergeometricCenteredMGF_sum_of_success_eq_population hN hn0 t]
          exact div_self (by exact_mod_cast (Nat.choose_pos hN).ne')
        rw [hmgf1]
        exact Real.one_le_exp (serflingExponent_nonneg hN t)
      have hK_lt_N : K < N := lt_of_le_of_ne hKN hKN_eq
      by_cases hnN : n = N
      · have hmgf1 : centeredHypergeometricMGF N n K t = 1 := by
          unfold centeredHypergeometricMGF
          rw [hnN, hypergeometricCenteredMGF_sum_of_sample_eq_population hKN (by omega : N ≠ 0) t]
          simp
        rw [hmgf1]
        exact Real.one_le_exp (serflingExponent_nonneg hN t)
      have hn_lt_N : n < N := lt_of_le_of_ne hN hnN
      have hn_pred_lt : n - 1 < n := by omega
      have hKN_success : K - 1 ≤ N - 1 := Nat.sub_le_sub_right hKN 1
      have hn_success : n - 1 ≤ N - 1 := Nat.sub_le_sub_right hN 1
      have hKN_failure : K ≤ N - 1 := by omega
      have hconv :
          ∀ M : ℕ,
            centeredHypergeometricMGF (N - 1) (n - 1) M t ≤
              Real.exp (t ^ 2 * ((n - 1 : ℕ) : ℝ) *
                (((N - 1 : ℕ) : ℝ) - ((n - 1 : ℕ) : ℝ) + 1) /
                  (8 * ((N - 1 : ℕ) : ℝ))) →
            centeredHypergeometricMGF (N - 1) (n - 1) M t ≤
              Real.exp (t ^ 2 * ((n : ℝ) - 1) * ((N : ℝ) - (n : ℝ) + 1) /
                (8 * ((N : ℝ) - 1))) := by
        intro M hM
        refine hM.trans (le_of_eq (congrArg Real.exp ?_))
        rw [Nat.cast_sub (show 1 ≤ n by omega),
          Nat.cast_sub (show 1 ≤ N by omega), Nat.cast_one]
        ring
      have hsuccess :=
        hconv (K - 1)
          (ih (n - 1) hn_pred_lt (N := N - 1) (K := K - 1) hKN_success hn_success)
      have hfailure :=
        hconv K
          (ih (n - 1) hn_pred_lt (N := N - 1) (K := K) hKN_failure hn_success)
      exact centeredHypergeometricMGF_le_serfling_exp_of_recursion
        (N := N) (n := n) (K := K) hKN hKpos hK_lt_N hnpos hn_lt_N t
        hsuccess hfailure

end Math.Concentration.HypergeometricTail
