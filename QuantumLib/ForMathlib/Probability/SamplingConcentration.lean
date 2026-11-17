import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Sampling Concentration — Population and Empirical Frequency Definitions

Definitions of population frequency and empirical frequency for a binary population
sequence `seq : Fin N → Bool` and a random test sample `sampleFn : Ω → Fin n ↪ Fin N`
drawn without replacement. These definitions support the BB84 PE false-pass bounds
in `PEConcentration.lean`.

## Setup

A population is a binary sequence `seq : Fin N → Bool` with population
frequency `populationFreq seq = (∑ i, if seq i then 1 else 0) / N`.
A test sample of size `n` is modeled by a probability space `(Ω, P)` together
with a random variable `sampleFn : Ω → Fin n ↪ Fin N` whose distribution is
uniform over all injections (sampling without replacement).

## References

- Serfling, R.J. (1974). "Probability Inequalities for the Sum in Sampling
  without Replacement." *The Annals of Statistics* 2(1), 39–48.
- Tomamichel (2016), §6.5.3, application to BB84 PE step.
- Renner (2005), §6.4.
-/

open MeasureTheory Set Finset

namespace Math.Probability.SamplingConcentration

/-- The population frequency of a binary sequence: fraction of `true` entries. -/
noncomputable def populationFreq {N : ℕ} (seq : Fin N → Bool) : ℝ :=
  (∑ i, if seq i then (1 : ℝ) else 0) / N

/-- The empirical frequency of a test sample: fraction of `true` entries
among the `n` sampled positions. -/
noncomputable def empiricalFreqOf {N n : ℕ} (seq : Fin N → Bool)
    (sample : Fin n ↪ Fin N) : ℝ :=
  (∑ i, if seq (sample i) then (1 : ℝ) else 0) / n

/-- Complementing every bit complements the population frequency. -/
lemma populationFreq_not {N : ℕ} (seq : Fin N → Bool) (hN : N ≠ 0) :
    populationFreq (fun i => !seq i) = 1 - populationFreq seq := by
  classical
  unfold populationFreq
  let a : ℝ := ∑ i : Fin N, if !seq i then (1 : ℝ) else 0
  let b : ℝ := ∑ i : Fin N, if seq i then (1 : ℝ) else 0
  have hsum : a + b = N := by
    dsimp [a, b]
    rw [← Finset.sum_add_distrib]
    trans ∑ _i : Fin N, (1 : ℝ)
    · apply Finset.sum_congr rfl
      intro i _hi
      by_cases h : seq i <;> simp [h]
    · simp
  have ha : a = (N : ℝ) - b := by linarith
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  calc
    a / (N : ℝ) = ((N : ℝ) - b) / (N : ℝ) := by rw [ha]
    _ = (N : ℝ) / (N : ℝ) - b / (N : ℝ) := by rw [sub_div]
    _ = 1 - b / (N : ℝ) := by rw [div_self hN']

/-- Complementing every bit complements the empirical frequency. -/
lemma empiricalFreqOf_not {N n : ℕ} (seq : Fin N → Bool) (sample : Fin n ↪ Fin N)
    (hn : n ≠ 0) :
    empiricalFreqOf (fun i => !seq i) sample = 1 - empiricalFreqOf seq sample := by
  classical
  unfold empiricalFreqOf
  let a : ℝ := ∑ i : Fin n, if !seq (sample i) then (1 : ℝ) else 0
  let b : ℝ := ∑ i : Fin n, if seq (sample i) then (1 : ℝ) else 0
  have hsum : a + b = n := by
    dsimp [a, b]
    rw [← Finset.sum_add_distrib]
    trans ∑ _i : Fin n, (1 : ℝ)
    · apply Finset.sum_congr rfl
      intro i _hi
      by_cases h : seq (sample i) <;> simp [h]
    · simp
  have ha : a = (n : ℝ) - b := by linarith
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  calc
    a / (n : ℝ) = ((n : ℝ) - b) / (n : ℝ) := by rw [ha]
    _ = (n : ℝ) / (n : ℝ) - b / (n : ℝ) := by rw [sub_div]
    _ = 1 - b / (n : ℝ) := by rw [div_self hn']

end Math.Probability.SamplingConcentration
