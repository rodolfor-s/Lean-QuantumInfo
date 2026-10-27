import QCryptLean.Math.Concentration.BinomialHoeffding
import QCryptLean.Math.Concentration.BinomialPassSum

/-!
# Completeness direction of the binomial PE-pass mass

`Math.Concentration.BinomialPassSum.binomialPassSum_le_hoeffding` is the **soundness** direction of
the parameter-estimation band: a true rate sitting a margin `η` outside the band `|k/m − Q| ≤ δ`
passes with mass at most `exp(−2mη²)`.  This file supplies the **completeness** direction, needed by
the honest run: a true rate sitting exactly at the band centre `p = Q` **fails** the band with mass
at most `2·exp(−2mδ²)`, the two-sided Hoeffding bound.

Both directions are used by a sifted two-basis parameter-estimation test: soundness bounds the
accept mass of an attacked component, completeness bounds the abort mass of the honest
QBER-`Q` channel.

## Main statements
- `binomialWeight_sum_eq_one`: `∑_k C(m,k) p^k (1−p)^(m−k) = 1` (binomial normalisation).
- `one_sub_binomialPassSum_le_two_hoeffding`: `1 − binomialPassSum m Q δ Q ≤ 2·exp(−2mδ²)`.

The two-tail calculation is `Math.Concentration.BinomialHoeffding.binomial_two_tail_le`; this file
only
turns "outside the band" into "in one of the two tails at margin `δ`" and complements against the
normalisation.

Source: Hoeffding 1963; Renner 2005 (`arXiv:quant-ph/0512258v2`) §6.5 (the robustness/completeness
side of the parameter-estimation test).
-/

namespace Math.Concentration.BinomialPassSum

open scoped BigOperators

/-- **Binomial normalisation.** The binomial weights at rate `p` sum to one over `k ∈ {0, …, m}`.

Read off the centred-MGF identity `binomial_centeredMGF_eq` at `t = 0`, where the right-hand side
collapses to `(p + (1 − p))^m = 1`. -/
theorem binomialWeight_sum_eq_one (m : ℕ) (p : ℝ) :
    ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) = 1 := by
  have h := Math.Concentration.BinomialHoeffding.binomial_centeredMGF_eq p 0 m
  simpa using h

/-- **Completeness bound on the PE-pass mass (two-sided Hoeffding).**

At a true per-trial rate sitting exactly at the band centre (`p = Q`), the binomial mass that
**fails** the parameter-estimation band `|k/m − Q| ≤ δ` is at most `2·exp(−2mδ²)`:

`1 − binomialPassSum m Q δ Q ≤ 2·exp(−2·m·δ²)`.

Failing the band means `k/m > Q + δ` or `k/m < Q − δ`, i.e. landing in one of the two Hoeffding
tails at margin `δ`; `binomial_two_tail_le` charges `exp(−2mδ²)` to each.  Complementing against
`binomialWeight_sum_eq_one` turns the fail bound into the pass lower bound.

This is the honest-run counterpart of `binomialPassSum_le_hoeffding` (which bounds the pass mass
from ABOVE at a rate far outside the band). -/
theorem one_sub_binomialPassSum_le_two_hoeffding (m : ℕ) (hm : m ≠ 0) (Q δ : ℝ)
    (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) (hδ : 0 < δ) :
    1 - binomialPassSum m Q δ Q ≤ 2 * Real.exp (-2 * (m : ℝ) * δ ^ 2) := by
  classical
  set w : ℕ → ℝ := fun k => (m.choose k : ℝ) * Q ^ k * (1 - Q) ^ (m - k) with hw
  have hw_nonneg : ∀ k, 0 ≤ w k := by
    intro k
    have h1 : 0 ≤ Q ^ k := pow_nonneg hQ0 _
    have h2 : 0 ≤ (1 - Q) ^ (m - k) := pow_nonneg (by linarith) _
    simp only [hw]
    positivity
  -- The pass mass and the fail mass add up to the total mass `1`.
  have hsplit : binomialPassSum m Q δ Q +
      (∑ k ∈ Finset.range (m + 1), if |(k : ℝ) / m - Q| ≤ δ then 0 else w k) =
      ∑ k ∈ Finset.range (m + 1), w k := by
    unfold binomialPassSum
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hw]
    split_ifs <;> ring
  rw [binomialWeight_sum_eq_one m Q] at hsplit
  -- Failing the band puts `k/m` in one of the two Hoeffding tails at margin `δ`.
  have hdom : (∑ k ∈ Finset.range (m + 1), if |(k : ℝ) / m - Q| ≤ δ then 0 else w k) ≤
      ∑ k ∈ Finset.range (m + 1),
        if ((k : ℝ) / m ≤ Q - δ ∨ Q + δ ≤ (k : ℝ) / m) then w k else 0 := by
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hband : |(k : ℝ) / m - Q| ≤ δ
    · rw [ite_eq_left hband]
      split_ifs
      · exact hw_nonneg k
      · exact le_refl 0
    · rw [ite_eq_right hband]
      have htail : (k : ℝ) / m ≤ Q - δ ∨ Q + δ ≤ (k : ℝ) / m := by
        rcases lt_or_ge ((k : ℝ) / m) Q with hlt | hge
        · left
          have : -((k : ℝ) / m - Q) ≤ δ → |(k : ℝ) / m - Q| ≤ δ := by
            intro h
            rw [abs_of_nonpos (by linarith)]
            exact h
          have hneg : ¬ (-((k : ℝ) / m - Q) ≤ δ) := fun h => hband (this h)
          push Not at hneg
          linarith
        · right
          have : (k : ℝ) / m - Q ≤ δ → |(k : ℝ) / m - Q| ≤ δ := by
            intro h
            rw [abs_of_nonneg (by linarith)]
            exact h
          have hpos : ¬ ((k : ℝ) / m - Q ≤ δ) := fun h => hband (this h)
          push Not at hpos
          linarith
      rw [ite_eq_left htail]
  have htwo := Math.Concentration.BinomialHoeffding.binomial_two_tail_le m hm Q δ δ hQ0 hQ1 hδ hδ
  have hsum : (∑ k ∈ Finset.range (m + 1),
      if ((k : ℝ) / m ≤ Q - δ ∨ Q + δ ≤ (k : ℝ) / m) then w k else 0) ≤
      2 * Real.exp (-2 * (m : ℝ) * δ ^ 2) := by
    simp only [hw]
    linarith [htwo]
  linarith [hdom.trans hsum]

end Math.Concentration.BinomialPassSum
