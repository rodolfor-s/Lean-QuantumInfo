import QCryptLean.Math.Concentration.BernoulliKL
import QCryptLean.Math.Concentration.BinomialLowerTail
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Disintegration
import QCryptLean.QKD.BB84.Sampling.MatchedCounts

/-!
# Quantitative bounds on the BB84 quota-failure probability

The exact quota-failure mass `selectionFailureMass N nK mZ mX pA pB` of the raw control law lies
between the larger and the sum of the two binomial shortfall probabilities `P[K_Z < nK + mZ]` and
`P[K_X < mX]` of the matched raw-round counts, from the Sampling.MatchedCounts module.  This
module states that sandwich with the real strict lower tail `binomialLowerTail` and bounds the
failure probability by concentration inequalities.

Write `p_Z = (matchedProb pA pB .z).toReal` and `p_X = (matchedProb pA pB .x).toReal` for the
per-round probabilities that both parties choose Z, respectively X.

## Main statements

* `selectionFailureMass_toReal_le_add`, `max_le_selectionFailureMass_toReal`: the union bound
  and a lower bound giving a factor-two comparison with the exact failure probability.
* `selectionFailureMass_toReal_le_exp`: Hoeffding's bound at the strict-shortfall integer endpoints,
  `exp (-2 (N p_Z - (nK + mZ) + 1)^2 / N) + exp (-2 (N p_X - mX + 1)^2 / N)`.
* `selectionFailureMass_toReal_le_two_exp`: if both quotas lie a fraction `η ≥ 0` below the
  expected matched counts, the failure probability is at most `2 exp (-2 η^2 N)`.
* `selectionFailureMass_toReal_le_exp_klBer`: the bound with Bernoulli relative-entropy exponents.

## When the bounds are informative

Every statement holds for arbitrary basis laws, subject to its stated premises. For positive
quotas, the Hoeffding and relative-entropy bounds require the largest failing counts,
`nK + mZ - 1` and `mX - 1`, to lie below the expected matched counts `N p_Z` and `N p_X`.
A zero quota has an empty shortfall event. The bounds are small when
both slacks are large compared with `√N`: at quotas a fixed fraction `η > 0` below `p_Z N` and
`p_X N` the failure probability is at most `2 exp (-2 η^2 N)`, which is below one once
`2 η^2 N > log 2` and decays exponentially in `N`.  For quotas near the expected counts the
bounds exceed one, and once a largest failing count reaches its expected count the premises
fail; the exact law then decides.  For example a positive X quota fails surely when `p_X = 0`
(`max_le_selectionFailureMass_toReal`, `binomialLowerTail_prob_zero`).
-/

open scoped ENNReal BigOperators
open Finset
open Math.Concentration.BinomialLowerTail

noncomputable section

namespace QKD.BB84.Sampling

open QKD.BB84.Measurement

/-- The real matched probability is the product of the two real basis probabilities. -/
theorem matchedProb_toReal (pA pB : PMF Basis) (θ : Basis) :
    (matchedProb pA pB θ).toReal = (pA θ).toReal * (pB θ).toReal :=
  ENNReal.toReal_mul

/-- Independent uniform basis choices match in a given basis with probability `1/4`. -/
@[simp] theorem matchedProb_uniformOfFintype_toReal (θ : Measurement.Basis) :
    (matchedProb (PMF.uniformOfFintype Measurement.Basis)
      (PMF.uniformOfFintype Measurement.Basis) θ).toReal = 1 / 4 := by
  rw [matchedProb_toReal]
  norm_num [PMF.uniformOfFintype_apply, Measurement.card_basis, ENNReal.toReal_inv]

/-- The real matched probability is nonnegative. -/
theorem matchedProb_toReal_nonneg (pA pB : PMF Basis) (θ : Basis) :
    0 ≤ (matchedProb pA pB θ).toReal :=
  ENNReal.toReal_nonneg

/-- The real matched probability is at most one. -/
theorem matchedProb_toReal_le_one (pA pB : PMF Basis) (θ : Basis) :
    (matchedProb pA pB θ).toReal ≤ 1 := by
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top (matchedProb_le_one pA pB θ)

/-- A matched shortfall mass is finite. -/
theorem matchedShortfallMass_ne_top (N q : ℕ) (pA pB : PMF Basis) (θ : Basis) :
    matchedShortfallMass N q pA pB θ ≠ ∞ := by
  refine ENNReal.sum_ne_top.mpr fun k _ => ?_
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (ENNReal.pow_ne_top (matchedProb_ne_top pA pB θ))) (ENNReal.pow_ne_top ?_)
  exact ENNReal.sub_ne_top ENNReal.one_ne_top

/-- The matched shortfall mass is the real strict binomial lower tail at the matched
probability. -/
theorem matchedShortfallMass_toReal (N q : ℕ) (pA pB : PMF Basis) (θ : Basis) :
    (matchedShortfallMass N q pA pB θ).toReal =
      binomialLowerTail N q (matchedProb pA pB θ).toReal := by
  rw [matchedShortfallMass, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le (matchedProb_le_one pA pB θ) ENNReal.one_ne_top,
      ENNReal.toReal_one, ENNReal.toReal_natCast]
  · intro k _
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.pow_ne_top (matchedProb_ne_top pA pB θ))) (ENNReal.pow_ne_top ?_)
    exact ENNReal.sub_ne_top ENNReal.one_ne_top

/-- The quota-failure mass is finite: it is at most one. -/
theorem selectionFailureMass_ne_top (N nK mZ mX : ℕ) (pA pB : PMF Basis) :
    selectionFailureMass N nK mZ mX pA pB ≠ ∞ := by
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  rw [← selectionSuccessMass_add_failureMass N nK mZ mX pA pB]
  exact le_add_self

/-- **Union bound**: the quota-failure probability is at most the sum of the matched-Z and
matched-X shortfall probabilities. -/
theorem selectionFailureMass_toReal_le_add (N nK mZ mX : ℕ) (pA pB : PMF Basis) :
    (selectionFailureMass N nK mZ mX pA pB).toReal ≤
      binomialLowerTail N (nK + mZ) (matchedProb pA pB .z).toReal +
        binomialLowerTail N mX (matchedProb pA pB .x).toReal := by
  rw [← matchedShortfallMass_toReal, ← matchedShortfallMass_toReal,
    ← ENNReal.toReal_add (matchedShortfallMass_ne_top _ _ _ _ _)
      (matchedShortfallMass_ne_top _ _ _ _ _)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨matchedShortfallMass_ne_top _ _ _ _ _,
    matchedShortfallMass_ne_top _ _ _ _ _⟩) (selectionFailureMass_le_add N nK mZ mX pA pB)

/-- **Lower bound for the union event**: each shortfall alone already fails, so the failure
probability is at least the larger of the two shortfall probabilities. -/
theorem max_le_selectionFailureMass_toReal (N nK mZ mX : ℕ) (pA pB : PMF Basis) :
    max (binomialLowerTail N (nK + mZ) (matchedProb pA pB .z).toReal)
        (binomialLowerTail N mX (matchedProb pA pB .x).toReal) ≤
      (selectionFailureMass N nK mZ mX pA pB).toReal := by
  rw [← matchedShortfallMass_toReal, ← matchedShortfallMass_toReal]
  exact max_le
    (ENNReal.toReal_mono (selectionFailureMass_ne_top N nK mZ mX pA pB)
      (matchedShortfallMass_z_le_selectionFailureMass N nK mZ mX pA pB))
    (ENNReal.toReal_mono (selectionFailureMass_ne_top N nK mZ mX pA pB)
      (matchedShortfallMass_x_le_selectionFailureMass N nK mZ mX pA pB))

/-- **Hoeffding's bound on the quota-failure probability.**  If
`nK + mZ - 1 < N p_Z` and `mX - 1 < N p_X`, then the failure
probability is at most `exp (-2 (N p_Z - (nK + mZ) + 1)^2 / N) + exp (-2 (N p_X - mX + 1)^2 / N)`.

For a positive quota `q`, the largest failing count is `q - 1`, giving the `+ 1` in the
bound. A zero quota has an empty shortfall event. -/
theorem selectionFailureMass_toReal_le_exp {N nK mZ mX : ℕ} {pA pB : PMF Basis}
    (hZ : (nK + mZ : ℝ) - 1 < N * (matchedProb pA pB .z).toReal)
    (hX : (mX : ℝ) - 1 < N * (matchedProb pA pB .x).toReal) :
    (selectionFailureMass N nK mZ mX pA pB).toReal ≤
      Real.exp (-2 * (N * (matchedProb pA pB .z).toReal - (nK + mZ) + 1) ^ 2 / N) +
        Real.exp (-2 * (N * (matchedProb pA pB .x).toReal - mX + 1) ^ 2 / N) := by
  refine (selectionFailureMass_toReal_le_add N nK mZ mX pA pB).trans (add_le_add ?_ ?_)
  · have h := binomialLowerTail_le_exp (n := N) (q := nK + mZ)
      (matchedProb_toReal_nonneg pA pB .z) (matchedProb_toReal_le_one pA pB .z)
      (by push_cast; exact hZ)
    push_cast at h
    exact h
  · exact binomialLowerTail_le_exp (matchedProb_toReal_nonneg pA pB .x)
      (matchedProb_toReal_le_one pA pB .x) hX

/-- **Linear-slack bound on the quota-failure probability.**  If both quotas lie a fraction
`η ≥ 0` below the expected matched counts, `nK + mZ ≤ (p_Z - η) N` and `mX ≤ (p_X - η) N`, the
failure probability is at most `2 exp (-2 η^2 N)`.  For fixed `η > 0` this decays exponentially
in `N`, and it is below one once `2 η^2 N > log 2`. -/
theorem selectionFailureMass_toReal_le_two_exp {N nK mZ mX : ℕ} {pA pB : PMF Basis} {η : ℝ}
    (hη : 0 ≤ η) (hZ : (nK + mZ : ℝ) ≤ ((matchedProb pA pB .z).toReal - η) * N)
    (hX : (mX : ℝ) ≤ ((matchedProb pA pB .x).toReal - η) * N) :
    (selectionFailureMass N nK mZ mX pA pB).toReal ≤ 2 * Real.exp (-2 * η ^ 2 * N) := by
  refine (selectionFailureMass_toReal_le_add N nK mZ mX pA pB).trans ?_
  rw [two_mul]
  refine add_le_add ?_ ?_
  · exact binomialLowerTail_le_exp_of_le (matchedProb_toReal_nonneg pA pB .z)
      (matchedProb_toReal_le_one pA pB .z) hη (by push_cast; exact hZ)
  · exact binomialLowerTail_le_exp_of_le (matchedProb_toReal_nonneg pA pB .x)
      (matchedProb_toReal_le_one pA pB .x) hη hX

/-- **Relative-entropy bound on the quota-failure probability.**  If
`(nK + mZ - 1) / N < p_Z < 1` and
`(mX - 1) / N < p_X < 1`, the failure probability is at most
`exp (-N klBer ((nK + mZ - 1) / N) p_Z) + exp (-N klBer ((mX - 1) / N) p_X)`.

For positive quotas and `N > 0`, the fractions are the largest failing counts divided by `N`.
A matched probability equal to one is covered by `binomialLowerTail_prob_one` or, uniformly in
`p ≥ b`, by the reference-rate form `binomialLowerTail_le_exp_neg_mul_klBer`.  A zero quota
contributes a
zero shortfall, for which the corresponding exponential carries no information. -/
theorem selectionFailureMass_toReal_le_exp_klBer {N nK mZ mX : ℕ} {pA pB : PMF Basis}
    (hZ : ((nK + mZ : ℝ) - 1) / N < (matchedProb pA pB .z).toReal)
    (hZ1 : (matchedProb pA pB .z).toReal < 1)
    (hX : ((mX : ℝ) - 1) / N < (matchedProb pA pB .x).toReal)
    (hX1 : (matchedProb pA pB .x).toReal < 1) :
    (selectionFailureMass N nK mZ mX pA pB).toReal ≤
      Real.exp (-(N : ℝ) * Math.Concentration.BernoulliKL.klBer (((nK + mZ : ℝ) - 1) / N)
          (matchedProb pA pB .z).toReal) +
        Real.exp (-(N : ℝ) * Math.Concentration.BernoulliKL.klBer (((mX : ℝ) - 1) / N)
          (matchedProb pA pB .x).toReal) := by
  refine (selectionFailureMass_toReal_le_add N nK mZ mX pA pB).trans (add_le_add ?_ ?_)
  · have h := binomialLowerTail_le_exp_neg_mul_klBer (n := N) (q := nK + mZ)
      (by push_cast; exact hZ) le_rfl hZ1.le hZ1
    push_cast at h
    exact h
  · exact binomialLowerTail_le_exp_neg_mul_klBer hX le_rfl hX1.le hX1

end QKD.BB84.Sampling
