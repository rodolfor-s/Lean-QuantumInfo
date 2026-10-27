import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import QCryptLean.Math.Concentration.SamplingBounds
import QCryptLean.Math.Concentration.SerflingFinite
import QCryptLean.Math.Probability.SamplingConcentration

/-!
# Serfling (1974) Sampling-Without-Replacement Concentration Inequality

Concentration inequalities for the empirical frequency of a sample drawn uniformly
at random **without replacement** from a finite binary population.

## Main statements

- `upper_tail`: one-sided upper tail — the empirical frequency exceeds the
  population frequency by more than δ with probability at most `exp(-2nδ²)`.
- `lower_tail`: one-sided lower tail — the empirical frequency is below the
  population frequency by more than δ with probability at most `exp(-2nδ²)`.
- `two_sided`: two-sided deviation — `exp(-2nδ²)` bound with a factor of 2.

## Setup

A **population** is a binary sequence `seq : Fin N → Bool` with population frequency
`populationFreq seq = (#{i | seq i = true}) / N`.

A **without-replacement sample** of size `n` is modelled by a probability space `(Ω, P)`
equipped with a random injection `sampleFn : Ω → Fin n ↪ Fin N` whose distribution
is the uniform measure over all `n`-element subsets of `Fin N` (equivalently, all
injections `Fin n ↪ Fin N` divided by `n!`).

The empirical frequency of the sample is
`empiricalFreqOf seq (sampleFn ω) = (#{i | seq (sampleFn ω i) = true}) / n`.

## Bound

The textbook one-sided Serfling bound is `exp(-2nδ² / (1 - (n-1)/N))`.  The
simplified form used here — `exp(-2nδ²)` — follows from `(1 - (n-1)/N) ≤ 1`, which
gives the weaker but cleaner inequality `exp(-2nδ²/(1-(n-1)/N)) ≤ exp(-2nδ²)`.
This simplified form suffices for the BB84 PE step (Renner §6.2 lem:PEsec).

## References

- Serfling, R.J. (1974). "Probability Inequalities for the Sum in Sampling without
  Replacement." *The Annals of Statistics* 2(1), 39–48.
- Renner, R. (2005). "Security of Quantum Key Distribution." PhD thesis, ETH Zürich,
  §6.4 and lem:PEsec (arXiv:quant-ph/0512258).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open Math.Probability.SamplingConcentration

namespace Math.Concentration.Serfling

/-!
## Serfling Concentration Inequalities
-/

/-- A uniform random variable on a finite type assigns any predicate event at most
the corresponding finite counting fraction.  The statement is an inequality rather
than equality so it does not require measurability of the fibers. -/
lemma measureReal_uniform_preimage_le_card_filter
    {Ω α : Type*} [MeasurableSpace Ω] [Fintype α]
    (P : Measure Ω) (X : Ω → α)
    (hUniform : ∀ a : α, P {ω | X ω = a} = (Fintype.card α : ℝ≥0∞)⁻¹)
    (p : α → Prop) [DecidablePred p] :
    P.real {ω | p (X ω)} ≤
      ((Finset.univ.filter p).card : ℝ) / Fintype.card α := by
  classical
  let s : Finset α := Finset.univ.filter p
  have hEvent : {ω | p (X ω)} = ⋃ a ∈ s, {ω | X ω = a} := by
    ext ω
    simp [s]
  have hFiberReal : ∀ a : α, P.real {ω | X ω = a} =
      ((Fintype.card α : ℝ)⁻¹) := by
    intro a
    simp [Measure.real, hUniform a, ENNReal.toReal_inv]
  calc
    P.real {ω | p (X ω)}
        = P.real (⋃ a ∈ s, {ω | X ω = a}) := by rw [hEvent]
    _ ≤ ∑ a ∈ s, P.real {ω | X ω = a} := by
        exact MeasureTheory.measureReal_biUnion_finset_le s (fun a => {ω | X ω = a})
    _ = ∑ a ∈ s, ((Fintype.card α : ℝ)⁻¹) := by
        apply Finset.sum_congr rfl
        intro a _ha
        exact hFiberReal a
    _ = (s.card : ℝ) * ((Fintype.card α : ℝ)⁻¹) := by simp
    _ = ((Finset.univ.filter p).card : ℝ) / Fintype.card α := by
        simp [s, div_eq_mul_inv]

/-- **Serfling Upper-Tail Bound** (1974).

    For a binary population `seq : Fin N → Bool` with population frequency
    `populationFreq seq`, and a random sample `sampleFn : Ω → Fin n ↪ Fin N`
    drawn uniformly without replacement, the probability that the empirical
    frequency exceeds the population frequency by more than δ is at most
    `exp(-2nδ²)`.

    This is the simplified Serfling bound obtained from the exact bound
    `exp(-2nδ² / (1 - (n-1)/N))` by the inequality `1 - (n-1)/N ≤ 1`. -/
theorem upper_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {N n : ℕ} (hN : n ≤ N) (hn : n ≠ 0)
    (seq : Fin N → Bool)
    (sampleFn : Ω → Fin n ↪ Fin N)
    (hUniform : ∀ (f : Fin n ↪ Fin N),
      P {ω | sampleFn ω = f} = (Fintype.card (Fin n ↪ Fin N) : ℝ≥0∞)⁻¹)
    (δ : ℝ) (hδ : 0 < δ) :
    P.real {ω | populationFreq seq + δ < empiricalFreqOf seq (sampleFn ω)} ≤
      Real.exp (-2 * n * δ ^ 2) := by
  classical
  exact (measureReal_uniform_preimage_le_card_filter P sampleFn hUniform
    (fun f : Fin n ↪ Fin N => populationFreq seq + δ < empiricalFreqOf seq f)).trans
      (finite_injection_serfling_upper_tail hN hn seq δ hδ)

/-- **Serfling Lower-Tail Bound** (1974).

    For a binary population `seq : Fin N → Bool` with population frequency
    `populationFreq seq`, and a random sample `sampleFn : Ω → Fin n ↪ Fin N`
    drawn uniformly without replacement, the probability that the empirical
    frequency falls more than δ below the population frequency is at most
    `exp(-2nδ²)`. -/
theorem lower_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {N n : ℕ} (hN : n ≤ N) (hn : n ≠ 0)
    (seq : Fin N → Bool)
    (sampleFn : Ω → Fin n ↪ Fin N)
    (hUniform : ∀ (f : Fin n ↪ Fin N),
      P {ω | sampleFn ω = f} = (Fintype.card (Fin n ↪ Fin N) : ℝ≥0∞)⁻¹)
    (δ : ℝ) (hδ : 0 < δ) :
    P.real {ω | empiricalFreqOf seq (sampleFn ω) < populationFreq seq - δ} ≤
      Real.exp (-2 * n * δ ^ 2) := by
  classical
  have hN_ne : N ≠ 0 := fun hN0 => by
    subst N
    exact hn (Nat.eq_zero_of_le_zero hN)
  let seqCompl : Fin N → Bool := fun i => !seq i
  have hUpper := upper_tail P hN hn seqCompl sampleFn hUniform δ hδ
  have hEvent :
      {ω | empiricalFreqOf seq (sampleFn ω) < populationFreq seq - δ} =
        {ω | populationFreq seqCompl + δ < empiricalFreqOf seqCompl (sampleFn ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [populationFreq_not seq hN_ne, empiricalFreqOf_not seq (sampleFn ω) hn]
    constructor <;> intro h <;> linarith
  rw [hEvent]
  exact hUpper

/-- **Serfling Two-Sided Bound** (1974).

    The probability that the empirical frequency deviates from the population
    frequency by more than δ in either direction is at most `2 · exp(-2nδ²)`.

    Follows from the upper and lower tail bounds via the union bound. -/
theorem two_sided
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {N n : ℕ} (hN : n ≤ N) (hn : n ≠ 0)
    (seq : Fin N → Bool)
    (sampleFn : Ω → Fin n ↪ Fin N)
    (hUniform : ∀ (f : Fin n ↪ Fin N),
      P {ω | sampleFn ω = f} = (Fintype.card (Fin n ↪ Fin N) : ℝ≥0∞)⁻¹)
    (δ : ℝ) (hδ : 0 < δ) :
    P.real {ω | δ < |empiricalFreqOf seq (sampleFn ω) - populationFreq seq|} ≤
      2 * Real.exp (-2 * n * δ ^ 2) := by
  classical
  let upper : Set Ω := {ω | populationFreq seq + δ < empiricalFreqOf seq (sampleFn ω)}
  let lower : Set Ω := {ω | empiricalFreqOf seq (sampleFn ω) < populationFreq seq - δ}
  have hDecomp :
      {ω | δ < |empiricalFreqOf seq (sampleFn ω) - populationFreq seq|} =
        upper ∪ lower := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, upper, lower]
    constructor
    · intro h
      rcases (lt_abs.mp h) with hpos | hneg
      · left
        linarith
      · right
        linarith
    · intro h
      apply lt_abs.mpr
      rcases h with h | h
      · left
        linarith
      · right
        linarith
  rw [hDecomp]
  calc
    P.real (upper ∪ lower) ≤ P.real upper + P.real lower := by
      exact measureReal_union_le upper lower
    _ ≤ Real.exp (-2 * n * δ ^ 2) + Real.exp (-2 * n * δ ^ 2) := by
      apply add_le_add
      · exact upper_tail P hN hn seq sampleFn hUniform δ hδ
      · exact lower_tail P hN hn seq sampleFn hUniform δ hδ
    _ = 2 * Real.exp (-2 * n * δ ^ 2) := by ring

end Math.Concentration.Serfling
