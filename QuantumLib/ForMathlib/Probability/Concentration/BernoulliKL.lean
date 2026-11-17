import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Bernoulli KL divergence — a quadratic lower bound on the small-`b` admissible box

This file proves the elementary analytic inequality

  `4·δ² ≤ klBer (Q + δ) (Q + 2δ)`,  where  `klBer a b := a·log(a/b) + (1 - a)·log((1 - a)/(1 - b))`,

on the admissible box `0 < Q`, `0 < δ`, `Q + 2δ < 0.11`.  This is the KL exponent that
sharpens the binomial Hoeffding rate `2δ²` to `4δ²` when the true rate `b = Q + 2δ` stays
small (`b < 1/8 ⇒ b(1 - b) < 1/8`).  The proof is elementary (no calculus on `klBer` itself):

1. `log_one_add_le_mul_add_div`: the Padé `[2,1]` upper bound `log(1 + x) ≤ x(x + 2)/(2(x + 1))` for
   `x ≥ 0`, proved by monotonicity of `g(x) = x(x + 2)/(2(x + 1)) − log(1 + x)` (`g(0) = 0`,
   `g'(x) = x²/(2(x + 1)²) ≥ 0`).
2. The first KL term `(Q + δ)·log((Q + δ)/(Q + 2δ)) = −(Q + δ)·log(1 + (Q + δ − …)/…)` is lower
   bounded via the Padé upper bound; the second term via Mathlib's Padé lower bound
   `Real.le_log_one_add_of_nonneg : 2x/(x + 2) ≤ log(1 + x)`.
3. The two bounds sum to the closed form `(b − a)²(2 + (b − a))/(2b(2(1 − b) + (b − a)))`
   (`sq_mul_add_div_le_klBer`), which dominates `c·(b − a)²` whenever `2cb ≤ 1`
   (`mul_sq_le_klBer`).

The free-deviation form `four_mul_sq_le_klBer_add` separates the accept-test window `δ` from
the
phase-error deviation `dev`: it bounds `4·dev² ≤ klBer (Q + δ) (Q + δ + dev)` on the box
`0 < Q`, `0 < dev`, `Q + δ + dev < 0.11` (Nahar et al., arXiv:2403.11851, Lemma 9 Eq. 44, §V.C);
`four_mul_sq_le_klBer_add_two_mul` is its `dev = δ` instance.

References: standard Chernoff/large-deviations exponent for the binomial lower tail
(Cover–Thomas, *Elements of Information Theory*, §11.1; the binomial method-of-types bound);
Renner (2005), `arXiv:quant-ph/0512258v2`, §5 (parameter estimation concentration).
-/

namespace Math.Concentration.BernoulliKL

open Real

/-- **Bernoulli KL divergence.**  `klBer a b = a·log(a/b) + (1 - a)·log((1 - a)/(1 - b))`. -/
noncomputable def klBer (a b : ℝ) : ℝ :=
  a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b))

/-- The Bernoulli KL divergence vanishes when both arguments agree. -/
@[simp] theorem klBer_self (a : ℝ) : klBer a a = 0 := by
  by_cases ha : a = 0
  · simp [klBer, ha]
  by_cases ha1 : 1 - a = 0
  · simp [klBer, ha, ha1]
  simp [klBer, ha, ha1]

/-- **Complement symmetry of the Bernoulli KL divergence.**  `klBer (1 - a) (1 - b) = klBer a b`:
flipping both arguments leaves the divergence unchanged. -/
theorem klBer_compl (a b : ℝ) : klBer (1 - a) (1 - b) = klBer a b := by
  simp only [klBer, show 1 - (1 - a) = a from by ring, show 1 - (1 - b) = b from by ring]
  ring

/-- **Gibbs' inequality for the Bernoulli KL.**  `0 ≤ klBer a b` for `a, b ∈ (0,1)`
(elementary, via `log x ≤ x − 1`, `Real.log_le_sub_one_of_pos`). -/
theorem klBer_nonneg (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1) :
    0 ≤ klBer a b := by
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have h1b : (0 : ℝ) < 1 - b := by linarith
  have hba : (0 : ℝ) < b / a := div_pos hb0 ha0
  have hba' : (0 : ℝ) < (1 - b) / (1 - a) := div_pos h1b h1a
  have k1 : a * (Real.log b - Real.log a) ≤ b - a := by
    have h := Real.log_le_sub_one_of_pos hba
    rw [Real.log_div hb0.ne' ha0.ne'] at h
    have h2 := mul_le_mul_of_nonneg_left h ha0.le
    have : a * (b / a - 1) = b - a := by field_simp
    linarith [this ▸ h2]
  have k2 : (1 - a) * (Real.log (1 - b) - Real.log (1 - a)) ≤ (1 - b) - (1 - a) := by
    have h := Real.log_le_sub_one_of_pos hba'
    rw [Real.log_div h1b.ne' h1a.ne'] at h
    have h2 := mul_le_mul_of_nonneg_left h h1a.le
    have : (1 - a) * ((1 - b) / (1 - a) - 1) = (1 - b) - (1 - a) := by field_simp
    linarith [this ▸ h2]
  unfold klBer
  rw [Real.log_div ha0.ne' hb0.ne', Real.log_div h1a.ne' h1b.ne']
  nlinarith [k1, k2]

/-- **Padé `[2,1]` upper bound on `log`.**  For `x ≥ 0`,
`log(1 + x) ≤ x(x + 2)/(2(x + 1))`.  Proved by monotonicity of
`g(x) = x(x + 2)/(2(x + 1)) − log(1 + x)` on `[0, ∞)` (`g(0) = 0`, `g' ≥ 0`). -/
theorem log_one_add_le_mul_add_div (x : ℝ) (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ x * (x + 2) / (2 * (x + 1)) := by
  set g : ℝ → ℝ := fun t => t * (t + 2) / (2 * (t + 1)) - Real.log (1 + t) with hg
  have hg0 : g 0 = 0 := by simp [hg]
  have hderiv : ∀ t : ℝ, 0 < t → HasDerivAt g (t ^ 2 / (2 * (t + 1) ^ 2)) t := by
    intro t ht
    have h1 : HasDerivAt (fun t => t * (t + 2) / (2 * (t + 1)))
        (((1 * (t + 2) + t * 1) * (2 * (t + 1)) - t * (t + 2) * (2 * 1)) / (2 * (t + 1)) ^ 2) t :=
            by
      apply HasDerivAt.div
      · exact (hasDerivAt_id t).mul (by simpa using (hasDerivAt_id t).add_const 2)
      · simpa using ((hasDerivAt_id t).add_const 1).const_mul 2
      · positivity
    have h2 : HasDerivAt (fun t => Real.log (1 + t)) (1 / (1 + t)) t := by
      have := (Real.hasDerivAt_log (show (1 : ℝ) + t ≠ 0 by positivity)).comp t
        ((hasDerivAt_id t).const_add 1)
      simpa only [Function.comp_def, mul_one, one_div] using this
    apply (h1.sub h2).congr_deriv
    field_simp
    ring
  have hmono : MonotoneOn g (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · apply ContinuousOn.sub
      · apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · intro t ht
          simp only [Set.mem_Ici] at ht
          positivity
      · apply ContinuousOn.comp Real.continuousOn_log
        · fun_prop
        · intro t ht
          simp only [Set.mem_Ici] at ht
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro h; linarith
    · intro t ht
      rw [interior_Ici] at ht
      simp only [Set.mem_Ioi] at ht
      exact (hderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      simp only [Set.mem_Ioi] at ht
      rw [(hderiv t ht).deriv]
      positivity
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  rw [hg0] at this
  simp only [hg] at this
  linarith

/-- **Padé lower bound on the first Bernoulli-KL term.**  For `0 < a ≤ b`,
`-(b - a)(b + a)/(2b) ≤ a·log(a/b)`.  This is `log_one_add_le_mul_add_div` at `x = (b - a)/a`, where
`1 + x = b/a` and `x(x + 2)/(2(x + 1)) = (b - a)(b + a)/(2ab)`. -/
theorem neg_pade_le_mul_log_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    -((b - a) * (b + a) / (2 * b)) ≤ a * Real.log (a / b) := by
  have hb : b ≠ 0 := (ha.trans_le hab).ne'
  have hpu := log_one_add_le_mul_add_div ((b - a) / a) (div_nonneg (sub_nonneg.2 hab) ha.le)
  have h1x : 1 + (b - a) / a = b / a := by rw [one_add_div ha.ne', add_sub_cancel]
  have hval : (b - a) / a * ((b - a) / a + 2) / (2 * ((b - a) / a + 1)) =
      (b - a) * (b + a) / (2 * b) / a := by
    rw [div_add' _ _ _ ha.ne', div_add_one ha.ne', sub_add_cancel]
    field_simp
    ring
  -- `hpu : log(b/a) · a ≤ (b - a)(b + a)/(2b)`, and `a·log(a/b) = -(log(b/a) · a)`.
  rw [h1x, hval, le_div_iff₀ ha] at hpu
  rw [← inv_div b a, Real.log_inv, mul_neg, neg_le_neg_iff, mul_comm]
  exact hpu

/-- **Padé lower bound on the second Bernoulli-KL term.**  For `a ≤ b < 1`,
`(1 - a)·2(b - a)/((b - a) + 2(1 - b)) ≤ (1 - a)·log((1 - a)/(1 - b))`.  This is Mathlib's
`Real.le_log_one_add_of_nonneg` (`2x/(x + 2) ≤ log(1 + x)`) at `x = (b - a)/(1 - b)`, where
`1 + x = (1 - a)/(1 - b)`. -/
theorem mul_pade_le_mul_log_one_sub_div {a b : ℝ} (hab : a ≤ b) (hb : b < 1) :
    (1 - a) * (2 * (b - a) / ((b - a) + 2 * (1 - b))) ≤
      (1 - a) * Real.log ((1 - a) / (1 - b)) := by
  have h1b : 0 < 1 - b := sub_pos.2 hb
  have hpl := Real.le_log_one_add_of_nonneg (div_nonneg (sub_nonneg.2 hab) h1b.le)
  have h1x : 1 + (b - a) / (1 - b) = (1 - a) / (1 - b) := by
    rw [one_add_div h1b.ne', sub_add_sub_cancel]
  have hval : 2 * ((b - a) / (1 - b)) / ((b - a) / (1 - b) + 2) =
      2 * (b - a) / ((b - a) + 2 * (1 - b)) := by
    rw [div_add' _ _ _ h1b.ne', mul_div_assoc', div_div_div_cancel_right₀ h1b.ne']
  rw [h1x, hval] at hpl
  exact mul_le_mul_of_nonneg_left hpl (by linarith)

/-- **Padé bracket for the Bernoulli KL.**  For `0 < a ≤ b < 1`,
`(b - a)²(2 + (b - a)) / (2b(2(1 - b) + (b - a))) ≤ klBer a b`: the sum of the two Padé
bounds `neg_pade_le_mul_log_div` and `mul_pade_le_mul_log_one_sub_div`, in closed form. -/
theorem sq_mul_add_div_le_klBer {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    (b - a) ^ 2 * (2 + (b - a)) / (2 * b * (2 * (1 - b) + (b - a))) ≤ klBer a b := by
  have hb0 : 0 < b := ha.trans_le hab
  have hD : 0 < (b - a) + 2 * (1 - b) := by linarith
  have hsum : -((b - a) * (b + a) / (2 * b)) + (1 - a) * (2 * (b - a) / ((b - a) + 2 * (1 - b)))
      = (b - a) ^ 2 * (2 + (b - a)) / (2 * b * (2 * (1 - b) + (b - a))) := by
    rw [add_comm (2 * (1 - b)) (b - a)]
    field_simp
    ring
  rw [← hsum, klBer]
  exact add_le_add (neg_pade_le_mul_log_div ha hab) (mul_pade_le_mul_log_one_sub_div hab hb)

/-- **Quadratic KL lower bound.**  For `0 < a ≤ b < 1` and `2·c·b ≤ 1`,
`c·(b - a)² ≤ klBer a b`.  From `sq_mul_add_div_le_klBer`: with `D = 2(1 - b) + (b - a)`,
`c·2b·D ≤ D ≤ 2 + (b - a)`. -/
theorem mul_sq_le_klBer {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1)
    (hcb : 2 * c * b ≤ 1) :
    c * (b - a) ^ 2 ≤ klBer a b := by
  refine le_trans ?_ (sq_mul_add_div_le_klBer ha hab hb)
  have hb0 : 0 < b := ha.trans_le hab
  have hD : 0 < 2 * (1 - b) + (b - a) := by linarith
  rw [le_div_iff₀ (by positivity)]
  have hkey : c * (2 * b * (2 * (1 - b) + (b - a))) ≤ 2 + (b - a) :=
    calc c * (2 * b * (2 * (1 - b) + (b - a)))
        = (2 * c * b) * (2 * (1 - b) + (b - a)) := by ring
      _ ≤ 1 * (2 * (1 - b) + (b - a)) := mul_le_mul_of_nonneg_right hcb hD.le
      _ ≤ 2 + (b - a) := by linarith
  calc c * (b - a) ^ 2 * (2 * b * (2 * (1 - b) + (b - a)))
      = (b - a) ^ 2 * (c * (2 * b * (2 * (1 - b) + (b - a)))) := by ring
    _ ≤ (b - a) ^ 2 * (2 + (b - a)) := mul_le_mul_of_nonneg_left hkey (sq_nonneg _)

/-- **Quadratic KL lower bound on the admissible box, free deviation.**  For `0 < Q`, `0 < δ`,
`0 < dev`, `Q + δ + dev < 0.11`,
`4·dev² ≤ klBer (Q + δ) (Q + δ + dev)`.

Here `δ` is the accept-test window and `dev` the phase-error deviation between the window edge
`Q + δ` and the rate the entropy floor is charged at (Nahar et al., arXiv:2403.11851, Lemma 9
Eq. 44 and §V.C).  The factor `4` (twice the Pinsker constant `2`) is recovered because the
reference rate `b = Q + δ + dev < 0.11` keeps `b(1 - b) < 1/8`.  Proof:
`mul_sq_le_klBer` at
`c = 4` (the Padé bracket `sq_mul_add_div_le_klBer`, whose quadratic form dominates
`4·dev²`
since `8b ≤ 1`).  Pinsker's inequality itself — the same quadratic form at the constant `2` on
the whole unit box — is `Math.Concentration.BernoulliKL.two_mul_sq_le_klBer` in
`BernoulliKLToolkit.lean` (Cover–Thomas, Lemma 11.6.1). -/
theorem four_mul_sq_le_klBer_add (Q δ dev : ℝ) (hQ : 0 < Q) (hδ : 0 < δ) (hdev : 0 < dev)
    (hb : Q + δ + dev < (0.11 : ℝ)) :
    4 * dev ^ 2 ≤ klBer (Q + δ) (Q + δ + dev) := by
  have h := mul_sq_le_klBer (a := Q + δ) (b := Q + δ + dev) (c := 4)
    (by linarith) (by linarith) (by linarith) (by linarith)
  rwa [show Q + δ + dev - (Q + δ) = dev by ring] at h

/-- **Quadratic KL lower bound on the admissible box.**  For `0 < Q`, `0 < δ`,
`Q + 2δ < 0.11`,
`4·δ² ≤ klBer (Q + δ) (Q + 2δ)`.

The deviation coincides with the window (`dev = δ`), so this is `four_mul_sq_le_klBer_add`
at
`dev = δ`. -/
theorem four_mul_sq_le_klBer_add_two_mul (Q δ : ℝ) (hQ : 0 < Q) (hδ : 0 < δ)
    (hb : Q + 2 * δ < (0.11 : ℝ)) :
    4 * δ ^ 2 ≤ klBer (Q + δ) (Q + 2 * δ) := by
  have h := four_mul_sq_le_klBer_add Q δ δ hQ hδ hδ (by linarith)
  rwa [show Q + δ + δ = Q + 2 * δ by ring] at h

end Math.Concentration.BernoulliKL
