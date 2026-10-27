import QCryptLean.Math.Concentration.BinomialHoeffding
import QCryptLean.Math.Concentration.BinomialPassSum
import QCryptLean.Math.Concentration.BinomialPassSumCompleteness

/-!
# Completeness of the binomial PE-pass mass at a shifted true rate

`Math.Concentration.BinomialPassSum.one_sub_binomialPassSum_le_two_hoeffding` bounds the
band-fail mass **only at the band centre**, `p = Q`.  A de Finetti component that merely *lies in*
the parameter-estimation band carries a true per-trial rate `p` somewhere inside it, not exactly at
its centre, so the centre-only bound says nothing about it.  This file supplies the band-uniform
completeness bound: a true rate anywhere in the shrunken band `|p − Q| ≤ δ − η` fails the band
`|k/m − Q| ≤ δ` with mass at most `2·exp(−2mη²)`, an exponent that does **not** degrade as `p`
moves across the shrunken band.

## Main statements

- `one_sub_binomialPassSum_le_two_hoeffding_of_mem_band`: `|p − Q| ≤ δ − η` implies
  `1 − binomialPassSum m Q δ p ≤ 2·exp(−2mη²)`, uniformly in `p` over the shrunken band.
- `one_sub_binomialPassSum_le_two_hoeffding_of_halfBand`: the half-band instance `η = δ/2`,
  `|p − Q| ≤ δ/2` implies `1 − binomialPassSum m Q δ p ≤ 2·exp(−m·δ²/2)`.
- `one_sub_two_hoeffding_le_binomialPassSum_of_halfBand`: the same as an explicit **lower** bound on
  the pass mass, the direction a positive accept-weight argument consumes.

The centre-only bound `one_sub_binomialPassSum_le_two_hoeffding` is the `η = δ` case (the shrunken
band `|p − Q| ≤ 0` pins `p = Q`); nothing here weakens it.

The calculation is the same as in the centre-only file: `binomial_two_tail_le` at the tails
`k/m ≤ p − η` and `p + η ≤ k/m` **around the true rate `p`**, not around `Q`.  Only the
indicator-domination step changes: outside the band `|k/m − Q| ≤ δ`, the empirical fraction is at
distance more than `δ − |p − Q| ≥ η` from `p`.

Source: Hoeffding 1963; Renner (2005), `arXiv:quant-ph/0512258v2`, §6.5 (robustness/completeness
side of the parameter-estimation test).
-/

namespace Math.Concentration.BinomialPassSum

open scoped BigOperators

/-- **Band-uniform completeness bound on the PE-pass mass.**

If the true per-trial rate `p ∈ [0,1]` lies in the band `|k/m − Q| ≤ δ` shrunk by a margin `η > 0`
(that is `|p − Q| ≤ δ − η`), then the binomial mass that **fails** the band is at most
`2·exp(−2mη²)`:

`1 − binomialPassSum m Q δ p ≤ 2·exp(−2·m·η²)`.

The exponent depends on `p` only through the hypothesis, so the bound is uniform in `p` over the
shrunken band — this is what distinguishes it from `one_sub_binomialPassSum_le_two_hoeffding`,
which holds only at the exact centre `p = Q`.

Mechanism: failing the band means `k/m > Q + δ` or `k/m < Q − δ`; combined with
`Q − (δ − η) ≤ p ≤ Q + (δ − η)` this puts `k/m` in one of the two Hoeffding tails **at the true
rate** `p`, at margin `η` on each side, and `binomial_two_tail_le` charges `exp(−2mη²)` to each.
Complementing against `binomialWeight_sum_eq_one` turns the fail bound into the pass bound. -/
theorem one_sub_binomialPassSum_le_two_hoeffding_of_mem_band (m : ℕ) (hm : m ≠ 0) (Q δ η p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hη : 0 < η) (hband : |p - Q| ≤ δ - η) :
    1 - binomialPassSum m Q δ p ≤ 2 * Real.exp (-2 * (m : ℝ) * η ^ 2) := by
  classical
  obtain ⟨hlo, hhi⟩ := abs_le.mp hband
  set w : ℕ → ℝ := fun k => (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k) with hw
  have hw_nonneg : ∀ k, 0 ≤ w k := by
    intro k
    have h1 : 0 ≤ p ^ k := pow_nonneg hp0 _
    have h2 : 0 ≤ (1 - p) ^ (m - k) := pow_nonneg (by linarith) _
    simp only [hw]
    positivity
  -- The pass mass and the fail mass add up to the total mass `1`.
  have hsplit : binomialPassSum m Q δ p +
      (∑ k ∈ Finset.range (m + 1), if |(k : ℝ) / m - Q| ≤ δ then 0 else w k) =
      ∑ k ∈ Finset.range (m + 1), w k := by
    unfold binomialPassSum
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hw]
    split_ifs <;> ring
  rw [binomialWeight_sum_eq_one m p] at hsplit
  -- Failing the band at centre `Q` puts `k/m` in a Hoeffding tail at margin `η` around `p`.
  have hdom : (∑ k ∈ Finset.range (m + 1), if |(k : ℝ) / m - Q| ≤ δ then 0 else w k) ≤
      ∑ k ∈ Finset.range (m + 1),
        if ((k : ℝ) / m ≤ p - η ∨ p + η ≤ (k : ℝ) / m) then w k else 0 := by
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hband' : |(k : ℝ) / m - Q| ≤ δ
    · rw [ite_eq_left hband']
      split_ifs
      · exact hw_nonneg k
      · exact le_refl 0
    · rw [ite_eq_right hband']
      have htail : (k : ℝ) / m ≤ p - η ∨ p + η ≤ (k : ℝ) / m := by
        rcases lt_or_ge ((k : ℝ) / m) Q with hlt | hge
        · left
          have hcontra : -((k : ℝ) / m - Q) ≤ δ → |(k : ℝ) / m - Q| ≤ δ := by
            intro h
            rw [abs_of_nonpos (by linarith)]
            exact h
          have hneg : ¬ (-((k : ℝ) / m - Q) ≤ δ) := fun h => hband' (hcontra h)
          push Not at hneg
          linarith
        · right
          have hcontra : (k : ℝ) / m - Q ≤ δ → |(k : ℝ) / m - Q| ≤ δ := by
            intro h
            rw [abs_of_nonneg (by linarith)]
            exact h
          have hpos : ¬ ((k : ℝ) / m - Q ≤ δ) := fun h => hband' (hcontra h)
          push Not at hpos
          linarith
      rw [ite_eq_left htail]
  have htwo := Math.Concentration.BinomialHoeffding.binomial_two_tail_le m hm p η η hp0 hp1 hη hη
  have hsum : (∑ k ∈ Finset.range (m + 1),
      if ((k : ℝ) / m ≤ p - η ∨ p + η ≤ (k : ℝ) / m) then w k else 0) ≤
      2 * Real.exp (-2 * (m : ℝ) * η ^ 2) := by
    simp only [hw]
    linarith [htwo]
  linarith [hdom.trans hsum]

/-- **Half-band completeness bound on the PE-pass mass.**

The `η = δ/2` instance of `one_sub_binomialPassSum_le_two_hoeffding_of_mem_band`: a true per-trial
rate within `δ/2` of the band centre fails the band `|k/m − Q| ≤ δ` with mass at most
`2·exp(−m·δ²/2)`.

Half of the band width is spent buying the margin, so the exponent is a quarter of the centre-only
one (`2mδ²` at `p = Q`); what is bought is that the bound holds **uniformly** for every `p` in the
half-band rather than at the single point `p = Q`. -/
theorem one_sub_binomialPassSum_le_two_hoeffding_of_halfBand (m : ℕ) (hm : m ≠ 0) (Q δ p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 < δ) (hband : |p - Q| ≤ δ / 2) :
    1 - binomialPassSum m Q δ p ≤ 2 * Real.exp (-((m : ℝ) * δ ^ 2) / 2) := by
  have h := one_sub_binomialPassSum_le_two_hoeffding_of_mem_band m hm Q δ (δ / 2) p hp0 hp1
    (by linarith) (by linarith [hband])
  have hexp : -2 * (m : ℝ) * (δ / 2) ^ 2 = -((m : ℝ) * δ ^ 2) / 2 := by ring
  rwa [hexp] at h

/-- **Half-band lower bound on the PE-pass mass.**

The pass-mass form of `one_sub_binomialPassSum_le_two_hoeffding_of_halfBand`: for a true per-trial
rate within `δ/2` of the band centre,

`binomialPassSum m Q δ p ≥ 1 − 2·exp(−m·δ²/2)`.

This is the direction a positive accept-weight argument consumes: it certifies that a component
sitting anywhere in the half-band contributes at least a constant share of its mass to the accept
event, uniformly in its position within the half-band. -/
theorem one_sub_two_hoeffding_le_binomialPassSum_of_halfBand (m : ℕ) (hm : m ≠ 0) (Q δ p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 < δ) (hband : |p - Q| ≤ δ / 2) :
    1 - 2 * Real.exp (-((m : ℝ) * δ ^ 2) / 2) ≤ binomialPassSum m Q δ p := by
  linarith [one_sub_binomialPassSum_le_two_hoeffding_of_halfBand m hm Q δ p hp0 hp1 hδ hband]

end Math.Concentration.BinomialPassSum
