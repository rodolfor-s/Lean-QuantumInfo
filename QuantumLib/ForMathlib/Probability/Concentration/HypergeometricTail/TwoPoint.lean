import Mathlib.Probability.Moments.SubGaussian

/-!
# Two-Point MGF Bound — Bernoulli measure, integration, Hoeffding comparison

This file contains the two-point probability measure and MGF comparison used in
the first-draw recurrence for the hypergeometric MGF bound.

## Main definitions
- `twoPointMeasure`: measure on `Bool` with mass `p` at `true` and `1 - p`
  at `false`.

## Main statements
- `mgf_twoPointMeasure`: MGF of a two-point random variable as a two-term
  exponential average.
- `twoPoint_centeredMGF_le`: Hoeffding bound for a centered two-point random
  variable with diameter at most one.
-/

open MeasureTheory ProbabilityTheory

namespace Math.Concentration.HypergeometricTail

/-- The two-point measure on `Bool` with `ENNReal.ofReal p` at `true` and
`ENNReal.ofReal (1 - p)` at `false`. -/
noncomputable def twoPointMeasure (p : ℝ) : Measure Bool :=
  ENNReal.ofReal p • Measure.dirac true +
    ENNReal.ofReal (1 - p) • Measure.dirac false

/-- The two-point measure is a probability measure when `0 ≤ p ≤ 1`. -/
lemma isProbabilityMeasure_twoPointMeasure
    {p : ℝ} (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1) :
    IsProbabilityMeasure (twoPointMeasure p) := by
  refine ⟨?_⟩
  have hp_compl_nonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp_le_one
  simp only [twoPointMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply_of_mem, Set.mem_univ, mul_one]
  rw [← ENNReal.ofReal_add hp_nonneg hp_compl_nonneg]
  ring_nf
  simp

/-- Integrating against the two-point measure is the weighted average of the
values at `true` and `false`. -/
lemma integral_twoPointMeasure
    {p : ℝ} (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1) (f : Bool → ℝ) :
    ∫ q, f q ∂twoPointMeasure p = p * f true + (1 - p) * f false := by
  have hp_compl_nonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp_le_one
  have hi_true : Integrable f (ENNReal.ofReal p • Measure.dirac true) := by
    exact (integrable_dirac (a := true) (f := f) (by simp)).smul_measure
      ENNReal.ofReal_ne_top
  have hi_false : Integrable f (ENNReal.ofReal (1 - p) • Measure.dirac false) := by
    exact (integrable_dirac (a := false) (f := f) (by simp)).smul_measure
      ENNReal.ofReal_ne_top
  rw [twoPointMeasure, integral_add_measure hi_true hi_false]
  simp [ENNReal.toReal_ofReal hp_nonneg, ENNReal.toReal_ofReal hp_compl_nonneg]

/-- The MGF of a two-point random variable is the corresponding two-term
weighted exponential average. -/
lemma mgf_twoPointMeasure
    {p a b t : ℝ} (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1) :
    ProbabilityTheory.mgf (fun q : Bool => if q then a else b)
        (twoPointMeasure p) t =
      p * Real.exp (t * a) + (1 - p) * Real.exp (t * b) := by
  rw [ProbabilityTheory.mgf]
  simpa using
    integral_twoPointMeasure (p := p) hp_nonneg hp_le_one
      (fun q : Bool => Real.exp (t * if q then a else b))

/-- If an interval has diameter at most one, its Hoeffding variance proxy gives
an exponent bounded by `t ^ 2 / 8`. -/
lemma interval_half_diameter_subgaussian_exponent_le
    {a b t : ℝ} (hab : a ≤ b) (hdiam : b - a ≤ 1) :
    ((((‖b - a‖₊ / 2) ^ 2 : NNReal) : ℝ) * t ^ 2 / 2) ≤
      t ^ 2 / 8 := by
  let c : NNReal := (‖b - a‖₊ / 2) ^ 2
  change (c : ℝ) * t ^ 2 / 2 ≤ t ^ 2 / 8
  have hdiff_nonneg : 0 ≤ b - a := sub_nonneg.mpr hab
  have hsq_le : (b - a) ^ 2 ≤ 1 := by
    simpa [pow_two] using
      mul_le_mul hdiam hdiam hdiff_nonneg (by norm_num : (0 : ℝ) ≤ 1)
  have hc_le : (c : ℝ) ≤ 1 / 4 := by
    calc
      (c : ℝ) = (b - a) ^ 2 / 4 := by
        dsimp [c]
        rw [abs_of_nonneg hdiff_nonneg]
        ring
      _ ≤ 1 / 4 :=
        div_le_div_of_nonneg_right hsq_le (by norm_num : (0 : ℝ) ≤ 4)
  have hmul := mul_le_mul_of_nonneg_right hc_le (sq_nonneg t)
  calc
    (c : ℝ) * t ^ 2 / 2 ≤ (1 / 4 * t ^ 2) / 2 :=
      div_le_div_of_nonneg_right hmul (by norm_num : (0 : ℝ) ≤ 2)
    _ = t ^ 2 / 8 := by ring

/-- Hoeffding's two-point MGF comparison for a centered random variable whose
support has diameter at most one. -/
lemma twoPoint_centeredMGF_le
    {p a b t : ℝ} (hp_nonneg : 0 ≤ p) (hp_le_one : p ≤ 1)
    (hab : a ≤ b) (hdiam : b - a ≤ 1)
    (hmean : p * a + (1 - p) * b = 0) (_ht : 0 ≤ t) :
    p * Real.exp (t * a) + (1 - p) * Real.exp (t * b) ≤
      Real.exp (t ^ 2 / 8) := by
  let X : Bool → ℝ := fun q => if q then a else b
  let μ : Measure Bool := twoPointMeasure p
  have hμprob : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact isProbabilityMeasure_twoPointMeasure hp_nonneg hp_le_one
  let : IsProbabilityMeasure μ := hμprob
  have hmeas : AEMeasurable X μ := by
    exact (measurable_of_finite X).aemeasurable
  have hbounded : ∀ᵐ q ∂μ, X q ∈ Set.Icc a b := by
    filter_upwards with q
    cases q <;> simp [X, hab]
  have hcenter : μ[X] = 0 := by
    change ∫ x, X x ∂μ = 0
    dsimp [μ]
    simpa [X, hmean] using
      integral_twoPointMeasure (p := p) hp_nonneg hp_le_one X
  let c : NNReal := (‖b - a‖₊ / 2) ^ 2
  have hsubg :
      HasSubgaussianMGF X c μ := by
    dsimp [c]
    exact hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hmeas hbounded hcenter
  have hmgf :
      ProbabilityTheory.mgf X μ t ≤
        Real.exp ((c : ℝ) * t ^ 2 / 2) :=
    hsubg.mgf_le t
  have hleft :
      p * Real.exp (t * a) + (1 - p) * Real.exp (t * b) =
        ProbabilityTheory.mgf X μ t := by
    simpa [μ, X] using
      (mgf_twoPointMeasure (p := p) (a := a) (b := b) (t := t)
        hp_nonneg hp_le_one).symm
  have hexponent_le :
      (c : ℝ) * t ^ 2 / 2 ≤ t ^ 2 / 8 := by
    simpa [c] using
      interval_half_diameter_subgaussian_exponent_le
        (a := a) (b := b) (t := t) hab hdiam
  calc
    p * Real.exp (t * a) + (1 - p) * Real.exp (t * b)
        = ProbabilityTheory.mgf X μ t := hleft
    _ ≤ Real.exp ((c : ℝ) * t ^ 2 / 2) := hmgf
    _ ≤ Real.exp (t ^ 2 / 8) := Real.exp_le_exp.mpr hexponent_le

end Math.Concentration.HypergeometricTail
