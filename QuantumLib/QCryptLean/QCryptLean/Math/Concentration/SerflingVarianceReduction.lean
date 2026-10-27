import QCryptLean.Math.Concentration.HypergeometricTail.SerflingUpperTail
import QCryptLean.Math.Concentration.Serfling
import QCryptLean.Math.Concentration.SerflingFinite
import QCryptLean.Math.Probability.SamplingConcentration

/-!
# Serfling Sampling Bound with Finite-Population Variance Reduction and the TLGR `μ`-Corollary

This file lifts the hypergeometric upper-tail calculation
(`hypergeometric_choose_upper_tail_varianceReduction`) through the finite counting reduction
and the uniform-injection model, giving the one-sided Serfling bound
with the without-replacement variance factor `(N − n + 1)/N`, and then specializes
it to the two-sample deviation fixed by TLGR (arXiv:1103.4130).

The counting reductions of `SerflingFinite.lean` and `Serfling.lean` are
*constant-agnostic* — they carry any tail bound on the normalized hypergeometric choose sum
through unchanged — so the siblings here reuse their exact structure, differing only in
the RHS constant.

## The TLGR split

A population of `N = n + k` bits is partitioned by a uniform injection into an
`n`-element **key** sample (the image of `sampleFn`) and its `k`-element
**test/complement** sample.  Writing `keyFreq = empiricalFreqOf`,
`testFreq = complementFreq`, `popFreq = populationFreq`, the exact partition
identity (`freq_conservation`)

`n · keyFreq + k · testFreq = N · popFreq`

is equivalent to `keyFreq − testFreq = (N/k)(keyFreq − popFreq)`, so the two-sample
event `keyFreq ≥ testFreq + μ` coincides with the single-sample event
`keyFreq ≥ popFreq + μk/N`.  Feeding `δ = μk/N` into the key-sample tail
(`N − n + 1 = k + 1`) produces TLGR's fixed bound
`exp(−2nk²μ² / ((n+k)(k+1)))`.

## Main statements
- `finite_powersetCard_upper_tail_varianceReduction`,
  `finite_injection_upper_tail_varianceReduction`: finite counting core.
- `upper_tail_varianceReduction`: one-sided model bound (strict deviation).
- `upper_tail_varianceReduction_le`: one-sided model bound for the `≥`/`≤`
  (non-strict) event, obtained from the strict bound by a limit argument.
- `complementFreq`, `freq_conservation`: test-sample frequency and the exact
  key/test/population conservation identity.
- `tlgr_mu_upper_tail`: the fixed TLGR two-sample deviation bound
  `Pr[keyFreq ≥ testFreq + μ] ≤ exp(−2nk²μ² / ((n+k)(k+1)))`.

## References
- Serfling, R.J. (1974). "Probability Inequalities for the Sum in Sampling without
  Replacement." *The Annals of Statistics* 2(1), 39–48 (Cor. 1.1).
- Tomamichel, Lim, Gisin, Renner (2012). "Tight finite-key analysis for quantum
  cryptography." *Nature Communications* 3, 634 (arXiv:1103.4130), Lemma 3 & (S10).
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal
open Math.Probability.SamplingConcentration

namespace Math.Concentration.Serfling

/-- Serfling upper tail with finite-population correction after reducing injections to unordered
image
subsets: among `n`-element subsets of `Fin N`, the fraction whose success count
exceeds the population success rate by `δ` is bounded by the without-replacement tail `exp(−2nδ² ·
N/(N − n + 1))`. -/
lemma finite_powersetCard_upper_tail_varianceReduction
    {N n : ℕ} (hN : n ≤ N) (hn : n ≠ 0)
    (seq : Fin N → Bool) (δ : ℝ) (hδ : 0 < δ) :
    ((Finset.univ.filter (fun s : Set.powersetCard (Fin N) n =>
      (populationSuccessCount seq : ℝ) / N + δ <
        (((s : Finset (Fin N)).filter (fun i : Fin N => seq i)).card : ℝ) /
          n)).card : ℝ) /
      Nat.card (Set.powersetCard (Fin N) n) ≤
        Real.exp (-2 * (n : ℝ) * δ ^ 2 * (N : ℝ) / ((N : ℝ) - (n : ℝ) + 1)) := by
  rw [card_powersetCard_bad_eq_hypergeom_sum]
  rw [Set.powersetCard.card]
  simp only [Nat.card_fin]
  exact Math.Concentration.HypergeometricTail.hypergeometric_choose_upper_tail_varianceReduction
    (populationSuccessCount_le seq) hN hn δ hδ

/-- The finite combinatorial core of Serfling's upper-tail inequality for
the uniform type of injections `Fin n ↪ Fin N`. -/
theorem finite_injection_upper_tail_varianceReduction
    {N n : ℕ} (hN : n ≤ N) (hn : n ≠ 0)
    (seq : Fin N → Bool) (δ : ℝ) (hδ : 0 < δ) :
    ((Finset.univ.filter (fun f : Fin n ↪ Fin N =>
      populationFreq seq + δ < empiricalFreqOf seq f)).card : ℝ) /
      Fintype.card (Fin n ↪ Fin N) ≤
        Real.exp (-2 * (n : ℝ) * δ ^ 2 * (N : ℝ) / ((N : ℝ) - (n : ℝ) + 1)) := by
  -- An injection is bad exactly when its unordered image subset is bad.
  have hfilter :
      Finset.univ.filter (fun f : Fin n ↪ Fin N =>
        populationFreq seq + δ < empiricalFreqOf seq f) =
      Finset.univ.filter (fun f : Fin n ↪ Fin N =>
        (populationSuccessCount seq : ℝ) / N + δ <
          ((((Set.powersetCard.ofFinEmb n (Fin N) f : Set.powersetCard (Fin N) n) :
            Finset (Fin N)).filter (fun i : Fin N => seq i)).card : ℝ) / n) :=
    Finset.filter_congr fun f _ => (badImageSubset_ofFinEmb_iff seq δ f).symm
  -- Each image subset is the image of exactly `n!` injections, so `n!` cancels.
  have hfac : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [hfilter, card_filter_preimage_ofFinEmb_eq_factorial_mul N n
      (fun s => (populationSuccessCount seq : ℝ) / N + δ <
        (((s : Finset (Fin N)).filter (fun i : Fin N => seq i)).card : ℝ) / n),
    card_fin_embedding_eq_factorial_mul_powersetCard, Nat.cast_mul, Nat.cast_mul,
    mul_div_mul_left _ _ hfac]
  exact finite_powersetCard_upper_tail_varianceReduction hN hn seq δ hδ

/-- **Serfling Upper-Tail Bound with Finite-Population Correction.**

Same uniform-injection model as `upper_tail`, but with the without-replacement variance factor `(N −
n + 1)/N`: the probability that the
empirical frequency exceeds the population frequency by more than `δ` is at most
`exp(−2nδ² · N/(N − n + 1))`.  Since `N/(N − n + 1) ≥ 1`, this is uniformly at
least as strong as `upper_tail`, with equality only at `n = 1`. -/
theorem upper_tail_varianceReduction
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {N n : ℕ} (hN : n ≤ N) (hn : n ≠ 0)
    (seq : Fin N → Bool)
    (sampleFn : Ω → Fin n ↪ Fin N)
    (hUniform : ∀ (f : Fin n ↪ Fin N),
      P {ω | sampleFn ω = f} = (Fintype.card (Fin n ↪ Fin N) : ℝ≥0∞)⁻¹)
    (δ : ℝ) (hδ : 0 < δ) :
    P.real {ω | populationFreq seq + δ < empiricalFreqOf seq (sampleFn ω)} ≤
      Real.exp (-2 * (n : ℝ) * δ ^ 2 * (N : ℝ) / ((N : ℝ) - (n : ℝ) + 1)) := by
  classical
  exact (measureReal_uniform_preimage_le_card_filter P sampleFn hUniform
    (fun f : Fin n ↪ Fin N => populationFreq seq + δ < empiricalFreqOf seq f)).trans
      (finite_injection_upper_tail_varianceReduction hN hn seq δ hδ)

/-- **Serfling Upper-Tail Bound with Finite-Population Correction, non-strict deviation.**

The `≤`-form of `upper_tail_varianceReduction`: the probability that the empirical
frequency is *at least* `δ` above the population frequency is at most
`exp(−2nδ² · N/(N − n + 1))`.  Obtained from the strict bound by taking a limit
`δ' ↑ δ` (the strict bound holds for every `δ' ∈ (0, δ)`, and the RHS is
continuous in `δ`).  This is the form consumed by `tlgr_mu_upper_tail`,
where the TLGR event is a non-strict `≥`. -/
theorem upper_tail_varianceReduction_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N n : ℕ} (hN : n ≤ N) (hn : n ≠ 0)
    (seq : Fin N → Bool)
    (sampleFn : Ω → Fin n ↪ Fin N)
    (hUniform : ∀ (f : Fin n ↪ Fin N),
      P {ω | sampleFn ω = f} = (Fintype.card (Fin n ↪ Fin N) : ℝ≥0∞)⁻¹)
    (δ : ℝ) (hδ : 0 < δ) :
    P.real {ω | populationFreq seq + δ ≤ empiricalFreqOf seq (sampleFn ω)} ≤
      Real.exp (-2 * (n : ℝ) * δ ^ 2 * (N : ℝ) / ((N : ℝ) - (n : ℝ) + 1)) := by
  classical
  have hmono : ∀ δ' : ℝ, 0 < δ' → δ' < δ →
      P.real {ω | populationFreq seq + δ ≤ empiricalFreqOf seq (sampleFn ω)} ≤
        Real.exp (-2 * (n : ℝ) * δ' ^ 2 * (N : ℝ) / ((N : ℝ) - (n : ℝ) + 1)) := by
    intro δ' hδ'pos hδ'lt
    have hsub :
        {ω | populationFreq seq + δ ≤ empiricalFreqOf seq (sampleFn ω)} ⊆
          {ω | populationFreq seq + δ' < empiricalFreqOf seq (sampleFn ω)} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      linarith
    calc
      P.real {ω | populationFreq seq + δ ≤ empiricalFreqOf seq (sampleFn ω)}
          ≤ P.real {ω | populationFreq seq + δ' < empiricalFreqOf seq (sampleFn ω)} :=
            measureReal_mono hsub (measure_ne_top P _)
      _ ≤ Real.exp (-2 * (n : ℝ) * δ' ^ 2 * (N : ℝ) / ((N : ℝ) - (n : ℝ) + 1)) :=
            upper_tail_varianceReduction P hN hn seq sampleFn hUniform δ' hδ'pos
  have hcont : Continuous
      (fun x : ℝ =>
        Real.exp (-2 * (n : ℝ) * x ^ 2 * (N : ℝ) / ((N : ℝ) - (n : ℝ) + 1))) := by
    fun_prop
  have htendsto :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.exp (-2 * (n : ℝ) * x ^ 2 * (N : ℝ) / ((N : ℝ) - (n : ℝ) + 1)))
        (nhdsWithin δ (Set.Iio δ))
        (nhds (Real.exp (-2 * (n : ℝ) * δ ^ 2 * (N : ℝ) / ((N : ℝ) - (n : ℝ) + 1)))) :=
    (hcont.tendsto δ).mono_left nhdsWithin_le_nhds
  have hev :
      ∀ᶠ x in nhdsWithin δ (Set.Iio δ),
        P.real {ω | populationFreq seq + δ ≤ empiricalFreqOf seq (sampleFn ω)} ≤
          Real.exp (-2 * (n : ℝ) * x ^ 2 * (N : ℝ) / ((N : ℝ) - (n : ℝ) + 1)) := by
    filter_upwards [Ioo_mem_nhdsLT hδ] with x hx
    exact hmono x hx.1 hx.2
  exact ge_of_tendsto htendsto hev

/-- Success frequency among the `N − n` population positions **not** covered by
the sample (the complementary "test" sample).  This is the honest complement of
`empiricalFreqOf`: the sum of `seq` over `(Finset.univ.map sample)ᶜ`, normalized
by the complement size `N − n`. -/
noncomputable def complementFreq {N n : ℕ} (seq : Fin N → Bool)
    (sample : Fin n ↪ Fin N) : ℝ :=
  (∑ i ∈ (Finset.univ.map sample)ᶜ, if seq i then (1 : ℝ) else 0) / ((N : ℝ) - n)

/-- **Key/test/population frequency conservation.**

For a sample `sample : Fin n ↪ Fin N` (with `1 ≤ n < N`) the successes split
exactly between the sample and its complement:

`n · empiricalFreqOf + (N − n) · complementFreq = N · populationFreq`.

Equivalently `keyFreq − testFreq = (N/k)(keyFreq − popFreq)` with `k = N − n`. -/
lemma freq_conservation {N n : ℕ} (seq : Fin N → Bool) (sample : Fin n ↪ Fin N)
    (hn : n ≠ 0) (hnN : n < N) :
    (n : ℝ) * empiricalFreqOf seq sample +
        ((N : ℝ) - n) * complementFreq seq sample =
      (N : ℝ) * populationFreq seq := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hlt : (n : ℝ) < N := by exact_mod_cast hnN
  have hNn' : (N : ℝ) - n ≠ 0 := by
    have : (0 : ℝ) < (N : ℝ) - n := by linarith
    exact ne_of_gt this
  have cancel : ∀ a b : ℝ, a ≠ 0 → a * (b / a) = b := by
    intro a b ha
    rw [mul_comm]
    exact div_mul_cancel₀ b ha
  have hsum :
      (∑ i : Fin n, if seq (sample i) then (1 : ℝ) else 0) +
        (∑ i ∈ (Finset.univ.map sample)ᶜ, if seq i then (1 : ℝ) else 0) =
      ∑ i : Fin N, if seq i then (1 : ℝ) else 0 := by
    rw [← Finset.sum_map Finset.univ sample (fun i => if seq i then (1 : ℝ) else 0)]
    exact Finset.sum_add_sum_compl (Finset.univ.map sample)
      (fun i => if seq i then (1 : ℝ) else 0)
  unfold empiricalFreqOf complementFreq populationFreq
  rw [cancel _ _ hn', cancel _ _ hNn', cancel _ _ hN']
  exact hsum

/-- **TLGR fixed two-sample deviation bound** (arXiv:1103.4130, Lemma 3 / (S10)).

In the model where a population of `N = n + k` bits is split by a uniform
injection into an `n`-element key sample and its `k`-element test complement, the
probability that the key-sample success frequency exceeds the test-sample
frequency by at least `μ` is bounded by

`Pr[keyFreq ≥ testFreq + μ] ≤ exp(−2 n k² μ² / ((n + k)(k + 1)))`.

The `(k + 1)` denominator is the Serfling factor `N − n + 1` for the
`n`-element key sample; the `k²`/`(n+k)` structure comes from converting the
single-sample deviation `keyFreq − popFreq` to the two-sample deviation
`keyFreq − testFreq = (N/k)(keyFreq − popFreq)` via `freq_conservation`.  This is
the exact fixed constant behind TLGR's `μ = √[N/(nk) · (k+1)/k · ln(1/ε)]`. -/
theorem tlgr_mu_upper_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0)
    (seq : Fin (n + k) → Bool)
    (sampleFn : Ω → Fin n ↪ Fin (n + k))
    (hUniform : ∀ (f : Fin n ↪ Fin (n + k)),
      P {ω | sampleFn ω = f} = (Fintype.card (Fin n ↪ Fin (n + k)) : ℝ≥0∞)⁻¹)
    (μ : ℝ) (hμ : 0 < μ) :
    P.real {ω | empiricalFreqOf seq (sampleFn ω) ≥
        complementFreq seq (sampleFn ω) + μ} ≤
      Real.exp (-2 * (n : ℝ) * (k : ℝ) ^ 2 * μ ^ 2 /
        (((n : ℝ) + (k : ℝ)) * ((k : ℝ) + 1))) := by
  classical
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have hNk_pos : (0 : ℝ) < (n : ℝ) + k := add_pos hn_pos hk_pos
  have hNk_ne : (n : ℝ) + k ≠ 0 := ne_of_gt hNk_pos
  have hk1_ne : (k : ℝ) + 1 ≠ 0 := (add_pos hk_pos one_pos).ne'
  -- The single-sample deviation `δ` matching the two-sample deviation `μ`.
  set δ : ℝ := μ * (k : ℝ) / ((n : ℝ) + k) with hδdef
  have hδpos : 0 < δ := div_pos (mul_pos hμ hk_pos) hNk_pos
  have hδk : δ * ((n : ℝ) + k) = μ * k := div_mul_cancel₀ _ hNk_ne
  have hEvent :
      {ω | empiricalFreqOf seq (sampleFn ω) ≥ complementFreq seq (sampleFn ω) + μ} =
        {ω | populationFreq seq + δ ≤ empiricalFreqOf seq (sampleFn ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, ge_iff_le]
    have hcons := freq_conservation seq (sampleFn ω) hn (by omega : n < n + k)
    push_cast at hcons
    set e := empiricalFreqOf seq (sampleFn ω) with he
    set c := complementFreq seq (sampleFn ω) with hc
    set p := populationFreq seq with hp
    have hcons2 : (n : ℝ) * e + (k : ℝ) * c = ((n : ℝ) + k) * p := by
      linear_combination hcons
    have hid : ((n : ℝ) + k) * (e - (p + δ)) = (k : ℝ) * (e - (c + μ)) := by
      linear_combination hcons2 - hδk
    -- Both events say that the two sides of `hid` are nonnegative.
    constructor
    · intro h
      have h' : 0 ≤ ((n : ℝ) + k) * (e - (p + δ)) := by
        rw [hid]; exact mul_nonneg hk_pos.le (sub_nonneg.mpr h)
      exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hNk_pos).mp h')
    · intro h
      have h' : 0 ≤ (k : ℝ) * (e - (c + μ)) := by
        rw [← hid]; exact mul_nonneg hNk_pos.le (sub_nonneg.mpr h)
      exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hk_pos).mp h')
  rw [hEvent]
  refine (upper_tail_varianceReduction_le P (Nat.le_add_right n k) hn seq sampleFn
    hUniform δ hδpos).trans (le_of_eq ?_)
  congr 1
  rw [hδdef]
  push_cast
  field_simp
  ring

end Math.Concentration.Serfling
