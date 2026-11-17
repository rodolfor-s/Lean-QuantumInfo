import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian

/-!
# Sampling Bounds — Hoeffding's inequality, two-test union bound

Concentration inequalities for random sampling used in QKD security proofs.

## Main statements
- `hoeffding_sampling_bound`: Hoeffding's inequality for bounded i.i.d. samples
- `one_sub_two_mul_hoeffdingBound_le_measureReal_inter`: Union bound for two simultaneous sampling
tests
- `hoeffdingBound_decreasing_in_n`: Monotonicity of the Hoeffding bound in sample size
-/

open MeasureTheory ProbabilityTheory Set Finset

namespace Math.Concentration.SamplingBounds

/-! ## Helper Lemmas -/

/-- Characterization of |x| > ε in terms of two one-sided inequalities. -/
lemma _root_.Real.lt_abs_iff_lt_or_lt_neg {x ε : ℝ} : |x| > ε ↔ x > ε ∨ x < -ε := by
  constructor
  · intro h
    by_cases hx : x ≥ 0
    · left; rwa [abs_of_nonneg hx] at h
    · right; push Not at hx; rw [abs_of_neg hx] at h; linarith
  · intro h
    rcases h with h | h
    · have h1 : |x| ≥ x := le_abs_self x; linarith
    · have h1 : |x| ≥ -x := neg_le_abs x; linarith

/-- Upper tail bound for sum of centered [0,1]-bounded independent random variables.
    Uses sub-Gaussian concentration from Mathlib. -/
lemma sum_subgaussian_upper_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : n ≠ 0) (samples : Fin n → Ω → ℝ)
    (hMeas : ∀ i, AEMeasurable (samples i) P)
    (hBounded : ∀ i, ∀ᵐ ω ∂P, samples i ω ∈ Set.Icc 0 1)
    (hIndep : iIndepFun samples P)
    (trueRate : ℝ)
    (hMean : ∀ i, ∫ ω, samples i ω ∂P = trueRate)
    (δ : ℝ) (hδ : δ > 0) :
    P.real {ω | n * δ ≤ ∑ i : Fin n, (samples i ω - trueRate)} ≤
      Real.exp (-2 * δ^2 * n) := by
  -- Define centered variables Y_i = X_i - trueRate
  let Y : Fin n → Ω → ℝ := fun i ω => samples i ω - trueRate
  -- Y_i are independent (composition with measurable subtraction)
  have hIndepY : iIndepFun Y P := by
    have h : iIndepFun (fun i => (fun x => x - trueRate) ∘ samples i) P := by
      apply iIndepFun.comp hIndep
      intro i
      exact measurable_sub_const trueRate
    exact h
  -- Each Y_i is sub-Gaussian with parameter ((1-0)/2)² = 1/4
  have hSubG : ∀ i : Fin n, HasSubgaussianMGF (Y i) ((‖(1:ℝ) - 0‖₊ / 2) ^ 2) P := by
    intro i
    have h := hasSubgaussianMGF_of_mem_Icc (hMeas i) (hBounded i)
    rw [hMean i] at h
    exact h
  -- Apply the sum bound from Mathlib
  have hBound := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hIndepY
    (s := Finset.univ) (c := fun _ => (‖(1:ℝ) - 0‖₊ / 2) ^ 2)
    (fun i _ => hSubG i) (ε := n * δ) (by positivity)
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at hBound
  have hSetEq : {ω | n * δ ≤ ∑ i, Y i ω} =
      {ω | n * δ ≤ ∑ i : Fin n, (samples i ω - trueRate)} := rfl
  rw [← hSetEq]
  have hParam : ((‖(1:ℝ) - 0‖₊ / 2) ^ 2 : NNReal) = 1/4 := by
    simp only [sub_zero, nnnorm_one]; norm_num
  rw [hParam] at hBound
  -- Simplify the exponent: -(n*δ)²/(2*n*(1/4)) = -(n*δ)²/(n/2) = -2nδ²
  calc P.real {ω | n * δ ≤ ∑ i, Y i ω}
      ≤ Real.exp (-(↑n * δ) ^ 2 / (2 * ((↑n : ℝ) * ((1:NNReal) / 4 : NNReal).toReal))) := hBound
    _ = Real.exp (-2 * δ ^ 2 * ↑n) := by
        congr 1
        simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
        have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
        field_simp
        ring

/-- Lower tail bound for sum of centered [0,1]-bounded independent random variables.
    Uses HasSubgaussianMGF.neg to handle the negative direction. -/
lemma sum_subgaussian_lower_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : n ≠ 0) (samples : Fin n → Ω → ℝ)
    (hMeas : ∀ i, AEMeasurable (samples i) P)
    (hBounded : ∀ i, ∀ᵐ ω ∂P, samples i ω ∈ Set.Icc 0 1)
    (hIndep : iIndepFun samples P)
    (trueRate : ℝ)
    (hMean : ∀ i, ∫ ω, samples i ω ∂P = trueRate)
    (δ : ℝ) (hδ : δ > 0) :
    P.real {ω | n * δ ≤ -(∑ i : Fin n, (samples i ω - trueRate))} ≤
      Real.exp (-2 * δ^2 * n) := by
  let Y : Fin n → Ω → ℝ := fun i ω => samples i ω - trueRate
  have hIndepY : iIndepFun Y P := by
    have h : iIndepFun (fun i => (fun x => x - trueRate) ∘ samples i) P := by
      apply iIndepFun.comp hIndep
      intro i
      exact measurable_sub_const trueRate
    exact h
  have hSubG : ∀ i : Fin n, HasSubgaussianMGF (Y i) ((‖(1:ℝ) - 0‖₊ / 2) ^ 2) P := by
    intro i
    have h := hasSubgaussianMGF_of_mem_Icc (hMeas i) (hBounded i)
    rw [hMean i] at h
    exact h
  -- The negated variables -Y_i are also sub-Gaussian with the same parameter
  have hSubGNeg : ∀ i : Fin n, HasSubgaussianMGF (fun ω => -Y i ω) ((‖(1:ℝ) - 0‖₊ / 2) ^ 2) P :=
    fun i => (hSubG i).neg
  -- -Y_i are also independent
  have hIndepNegY : iIndepFun (fun i ω => -Y i ω) P := by
    have h : iIndepFun (fun i => (fun x => -x) ∘ Y i) P := by
      apply iIndepFun.comp hIndepY
      intro i
      exact measurable_neg
    exact h
  -- Apply the sum bound to -Y_i
  have hBound := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hIndepNegY
    (s := Finset.univ) (c := fun _ => (‖(1:ℝ) - 0‖₊ / 2) ^ 2)
    (fun i _ => hSubGNeg i) (ε := n * δ) (by positivity)
  have hSumNeg : ∀ ω, ∑ i : Fin n, (-Y i ω) = -(∑ i : Fin n, Y i ω) := by
    intro ω; rw [← Finset.sum_neg_distrib]
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at hBound
  have hSetEq : {ω | n * δ ≤ ∑ i, -Y i ω} =
      {ω | n * δ ≤ -(∑ i : Fin n, (samples i ω - trueRate))} := by
    ext ω; simp only [Set.mem_ofPred_eq, hSumNeg]; rfl
  rw [← hSetEq]
  have hParam : ((‖(1:ℝ) - 0‖₊ / 2) ^ 2 : NNReal) = 1/4 := by
    simp only [sub_zero, nnnorm_one]; norm_num
  rw [hParam] at hBound
  calc P.real {ω | n * δ ≤ ∑ i, -Y i ω}
      ≤ Real.exp (-(↑n * δ) ^ 2 / (2 * ((↑n : ℝ) * ((1:NNReal) / 4 : NNReal).toReal))) := hBound
    _ = Real.exp (-2 * δ ^ 2 * ↑n) := by
        congr 1
        simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
        have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
        field_simp
        ring

/-! ## Main Hoeffding Inequality -/

/-- **Hoeffding's Inequality for Sampling**

    When estimating an error rate by sampling, the probability that the observed
    sample mean deviates from the true population mean by more than δ is bounded
    by 2·exp(-2nδ²), where n is the sample size.

    **Statement**: Given n independent [0,1]-bounded random variables with common
    mean μ (the true error rate), the probability that the sample average deviates
    from μ by more than δ satisfies:

      P(|X̄ - μ| > δ) ≤ 2·exp(-2nδ²)

    **Proof**: Uses Mathlib's sub-Gaussian concentration bounds. Each [0,1]-bounded
    centered variable is sub-Gaussian with parameter 1/4. The sum of n such
    independent variables has tail bound exp(-2ε²/n). Setting ε = n*δ gives
    exp(-2nδ²) for each tail, and the union bound gives 2·exp(-2nδ²).

    **Parameters**:
    - `Ω` : sample space
    - `P` : probability measure on Ω
    - `n` : sample size (number of qubits sampled)
    - `samples` : random variables representing each sample (0 = no error, 1 = error)
    - `hMeas` : each sample is almost everywhere measurable
    - `hBounded` : each sample is bounded in [0,1]
    - `hIndep` : the samples are independent
    - `trueRate` : the true error rate (population mean)
    - `hMean` : each sample has expectation equal to trueRate
    - `δ` : deviation tolerance -/
theorem hoeffding_sampling_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : n ≠ 0)
    (samples : Fin n → Ω → ℝ)
    (hMeas : ∀ i, AEMeasurable (samples i) P)
    (hBounded : ∀ i, ∀ᵐ ω ∂P, samples i ω ∈ Set.Icc 0 1)
    (hIndep : iIndepFun samples P)
    (trueRate : ℝ)
    (hMean : ∀ i, ∫ ω, samples i ω ∂P = trueRate)
    (δ : ℝ) (hδ : δ > 0) :
    P.real {ω | |((∑ i : Fin n, samples i ω) / n) - trueRate| > δ} ≤
      2 * Real.exp (-2 * δ^2 * n) := by
  -- Define centered variables Y_i = X_i - trueRate
  let Y : Fin n → Ω → ℝ := fun i ω => samples i ω - trueRate
  -- The centered sum equals (sum - n*trueRate)
  have hSumY : ∀ ω, ∑ i : Fin n, Y i ω = (∑ i : Fin n, samples i ω) - n * trueRate := by
    intro ω
    simp only [Y, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hn' : (n : ℝ) > 0 := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hn'' : (n : ℝ) ≠ 0 := ne_of_gt hn'
  -- Rewrite the event in terms of centered sum
  have hEvent : ∀ ω, |((∑ i : Fin n, samples i ω) / n) - trueRate| > δ ↔
                     |(∑ i : Fin n, Y i ω)| > n * δ := by
    intro ω
    rw [hSumY]
    constructor
    · intro h
      have h1 : |(∑ i, samples i ω) / n - trueRate| > δ := h
      rw [show (∑ i, samples i ω) / n - trueRate = (∑ i, samples i ω - n * trueRate) / n by
        field_simp] at h1
      rw [abs_div, abs_of_pos hn', gt_iff_lt, lt_div_iff₀ hn'] at h1
      rw [gt_iff_lt, mul_comm]
      exact h1
    · intro h
      have h1 : |∑ i, samples i ω - n * trueRate| > n * δ := h
      rw [show (∑ i, samples i ω) / n - trueRate = (∑ i, samples i ω - n * trueRate) / n by
        field_simp]
      rw [abs_div, abs_of_pos hn', gt_iff_lt, lt_div_iff₀ hn']
      rw [gt_iff_lt, mul_comm] at h1
      exact h1
  -- Rewrite using hEvent
  have hSetEq : {ω | |((∑ i : Fin n, samples i ω) / n) - trueRate| > δ} =
                {ω | |(∑ i : Fin n, Y i ω)| > n * δ} := by
    ext ω; simp only [Set.mem_ofPred_eq]; exact hEvent ω
  rw [hSetEq]
  -- Decompose into upper and lower tails
  have hDecomp : {ω | |(∑ i : Fin n, Y i ω)| > n * δ} =
                 {ω | (∑ i : Fin n, Y i ω) > n * δ} ∪
                 {ω | (∑ i : Fin n, Y i ω) < -(n * δ)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    exact Real.lt_abs_iff_lt_or_lt_neg
  rw [hDecomp]
  -- Apply union bound and tail bounds
  calc P.real ({ω | (∑ i, Y i ω) > n * δ} ∪ {ω | (∑ i, Y i ω) < -(n * δ)})
      ≤ P.real {ω | (∑ i, Y i ω) > n * δ} + P.real {ω | (∑ i, Y i ω) < -(n * δ)} := by
        exact measureReal_union_le _ _
    _ ≤ P.real {ω | n * δ ≤ ∑ i, Y i ω} + P.real {ω | n * δ ≤ -(∑ i, Y i ω)} := by
        apply add_le_add
        · apply MeasureTheory.measureReal_mono
          · intro ω h; simp only [Set.mem_ofPred_eq] at h ⊢; exact le_of_lt h
          · exact measure_ne_top P _
        · apply MeasureTheory.measureReal_mono
          · intro ω h; simp only [Set.mem_ofPred_eq] at h ⊢; linarith
          · exact measure_ne_top P _
    _ ≤ Real.exp (-2 * δ^2 * n) + Real.exp (-2 * δ^2 * n) := by
        apply add_le_add
        · -- Upper tail: convert Y back to samples - trueRate
          have hUpper := sum_subgaussian_upper_tail P n hn samples hMeas hBounded hIndep
              trueRate hMean δ hδ
          convert hUpper using 2
        · -- Lower tail
          have hLower := sum_subgaussian_lower_tail P n hn samples hMeas hBounded hIndep
              trueRate hMean δ hδ
          convert hLower using 2
    _ = 2 * Real.exp (-2 * δ^2 * n) := by ring

/-! ## Hoeffding Bound Utilities -/

/-- The Hoeffding bound value for given sample size and tolerance.
    This is the failure probability bound: 2·exp(-2nδ²). -/
noncomputable def hoeffdingBound (n : ℕ) (δ : ℝ) : ℝ := 2 * Real.exp (-2 * δ^2 * n)

theorem hoeffdingBound_pos (n : ℕ) (δ : ℝ) : 0 < hoeffdingBound n δ := by
  unfold hoeffdingBound
  apply mul_pos
  · norm_num
  · exact Real.exp_pos _

theorem hoeffdingBound_le_two (n : ℕ) (δ : ℝ) : hoeffdingBound n δ ≤ 2 := by
  unfold hoeffdingBound
  have h : Real.exp (-2 * δ^2 * n) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    apply mul_nonpos_of_nonpos_of_nonneg
    · apply mul_nonpos_of_nonpos_of_nonneg
      · linarith
      · exact sq_nonneg δ
    · exact Nat.cast_nonneg n
  linarith [Real.exp_pos (-2 * δ^2 * n)]

theorem hoeffdingBound_decreasing_in_n (δ : ℝ) :
    Antitone (fun n => hoeffdingBound n δ) := by
  intro m n hmn
  unfold hoeffdingBound
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonpos_left
    · exact Nat.cast_le.mpr hmn
    · apply mul_nonpos_of_nonpos_of_nonneg
      · linarith
      · exact sq_nonneg δ
  · norm_num

/-! ## IID Sample Structure -/

/-- An i.i.d. sampling test: `n` independent [0,1]-bounded random variables with common mean `μ`.
    Bundles a sample function with measurability, boundedness, independence, and mean hypotheses. -/
structure IIDSample {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ) (μ : ℝ) where
  /-- The sample random variables -/
  samples : Fin n → Ω → ℝ
  /-- Each sample is a.e.-measurable -/
  aeMeasurable : ∀ i, AEMeasurable (samples i) P
  /-- Each sample takes values in [0,1] a.e. -/
  bounded : ∀ i, ∀ᵐ ω ∂P, samples i ω ∈ Set.Icc 0 1
  /-- The samples are mutually independent -/
  indep : iIndepFun samples P
  /-- Each sample has expectation μ -/
  mean_eq : ∀ i, ∫ ω, samples i ω ∂P = μ

/-- The sample mean: `(1/n) ∑ᵢ Xᵢ(ω)`. -/
noncomputable def IIDSample.sampleMean {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {n : ℕ} {μ : ℝ} (S : IIDSample P n μ) (ω : Ω) : ℝ :=
  (∑ i : Fin n, S.samples i ω) / n

/-! ## Complement and Union Bounds for Probability Measures -/

/-- For any set S in a probability space, P(Sᶜ) ≥ 1 - P(S).
    Uses only subadditivity, avoiding measurability requirements. -/
lemma one_sub_measureReal_le_compl {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (S : Set Ω) :
    P.real Sᶜ ≥ 1 - P.real S := by
  have h1 : P.real (S ∪ Sᶜ) ≤ P.real S + P.real Sᶜ := measureReal_union_le S Sᶜ
  have h2 : S ∪ Sᶜ = Set.univ := Set.union_compl_self S
  rw [h2, probReal_univ] at h1
  linarith

/-- **Two-test union bound via Hoeffding's inequality.**

    Given two sets of i.i.d. [0,1]-bounded samples with true means `trueRate₁`
    and `trueRate₂`, the probability that BOTH sample means are within δ of their
    respective true means is at least `1 - 2 · hoeffdingBound(n, δ)`.

    Note: Cross-independence between the two sample sets is NOT required — the
    proof uses only the union bound `P(A ∪ B) ≤ P(A) + P(B)`, which holds for
    arbitrary events. Each set need only be internally i.i.d.

    This is the key statistical tool for BB84: with high probability, both the
    bit-flip and phase-flip error rate estimates are simultaneously accurate. -/
theorem one_sub_two_mul_hoeffdingBound_le_measureReal_inter
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : n ≠ 0)
    -- First sampling test
    (samples₁ : Fin n → Ω → ℝ)
    (hMeas₁ : ∀ i, AEMeasurable (samples₁ i) P)
    (hBounded₁ : ∀ i, ∀ᵐ ω ∂P, samples₁ i ω ∈ Set.Icc 0 1)
    (hIndep₁ : iIndepFun samples₁ P)
    (trueRate₁ : ℝ)
    (hMean₁ : ∀ i, ∫ ω, samples₁ i ω ∂P = trueRate₁)
    -- Second sampling test
    (samples₂ : Fin n → Ω → ℝ)
    (hMeas₂ : ∀ i, AEMeasurable (samples₂ i) P)
    (hBounded₂ : ∀ i, ∀ᵐ ω ∂P, samples₂ i ω ∈ Set.Icc 0 1)
    (hIndep₂ : iIndepFun samples₂ P)
    (trueRate₂ : ℝ)
    (hMean₂ : ∀ i, ∫ ω, samples₂ i ω ∂P = trueRate₂)
    -- Tolerance
    (δ : ℝ) (hδ : δ > 0) :
    P.real {ω |
      |(∑ i : Fin n, samples₁ i ω) / ↑n - trueRate₁| ≤ δ ∧
      |(∑ i : Fin n, samples₂ i ω) / ↑n - trueRate₂| ≤ δ} ≥
    1 - 2 * hoeffdingBound n δ := by
  -- Define the "bad" events where each test deviates by more than δ
  set bad₁ := {ω | |(∑ i : Fin n, samples₁ i ω) / ↑n - trueRate₁| > δ}
  set bad₂ := {ω | |(∑ i : Fin n, samples₂ i ω) / ↑n - trueRate₂| > δ}
  -- The "good" event is the complement of their union
  have hSetEq : {ω | |(∑ i : Fin n, samples₁ i ω) / ↑n - trueRate₁| ≤ δ ∧
      |(∑ i : Fin n, samples₂ i ω) / ↑n - trueRate₂| ≤ δ} = (bad₁ ∪ bad₂)ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_union, bad₁, bad₂,
      Set.mem_ofPred_eq, not_or, not_lt]
  rw [hSetEq]
  -- Apply complement bound, union bound, and two Hoeffding applications
  calc P.real (bad₁ ∪ bad₂)ᶜ
      ≥ 1 - P.real (bad₁ ∪ bad₂) := one_sub_measureReal_le_compl P _
    _ ≥ 1 - (P.real bad₁ + P.real bad₂) := by
        have := measureReal_union_le (μ := P) bad₁ bad₂
        linarith
    _ ≥ 1 - (hoeffdingBound n δ + hoeffdingBound n δ) := by
        have h₁ := hoeffding_sampling_bound P n hn samples₁ hMeas₁ hBounded₁ hIndep₁
          trueRate₁ hMean₁ δ hδ
        have h₂ := hoeffding_sampling_bound P n hn samples₂ hMeas₂ hBounded₂ hIndep₂
          trueRate₂ hMean₂ δ hδ
        unfold hoeffdingBound
        linarith
    _ = 1 - 2 * hoeffdingBound n δ := by ring

/-- Structured version of `one_sub_two_mul_hoeffdingBound_le_measureReal_inter`: given two
`IIDSample`s,
    both sample means are within δ of their true means with probability
    ≥ 1 - 2·hoeffdingBound(n, δ). -/
theorem IIDSample.one_sub_two_mul_hoeffdingBound_le_measureReal_inter {Ω : Type*} [MeasurableSpace
    Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {n : ℕ} {μ₁ μ₂ : ℝ}
    (test₁ : IIDSample P n μ₁) (test₂ : IIDSample P n μ₂)
    (hn : n ≠ 0) (δ : ℝ) (hδ : δ > 0) :
    P.real {ω |
      |test₁.sampleMean ω - μ₁| ≤ δ ∧
      |test₂.sampleMean ω - μ₂| ≤ δ} ≥
    1 - 2 * hoeffdingBound n δ :=
  Math.Concentration.SamplingBounds.one_sub_two_mul_hoeffdingBound_le_measureReal_inter P n hn
    test₁.samples test₁.aeMeasurable test₁.bounded test₁.indep _ test₁.mean_eq
    test₂.samples test₂.aeMeasurable test₂.bounded test₂.indep _ test₂.mean_eq δ hδ

end Math.Concentration.SamplingBounds
