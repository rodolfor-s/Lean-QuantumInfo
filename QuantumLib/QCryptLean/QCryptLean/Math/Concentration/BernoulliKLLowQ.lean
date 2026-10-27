import QCryptLean.Math.Concentration.BernoulliKL

/-!
# Bernoulli KL divergence — the small-error-rate quadratic lower bound

This file proves the sharpened analytic inequality

  `12.5·δ² ≤ klBer (Q + δ) (Q + 2δ)`,

on the tighter small-error-rate window `0 < Q`, `0 < δ`, `Q + 2δ ≤ 1/25`.  It mirrors the
`four_mul_sq_le_klBer_add_two_mul` (window `Q + 2δ < 0.11`, constant `4`): both are the quadratic
form of
the same two-term Padé bracket (`sq_mul_add_div_le_klBer`, via
`mul_sq_le_klBer`).  Only the
window literal `0.11 → 1/25` and the final constant `4 → 12.5` change.  The constant
`12.5 = 1/(2·(1/25))` is the quadratic-form
value `(b − a)²/(2b) = δ²/(2(Q + 2δ)) ≥ δ²/(2·(1/25)) = 12.5·δ²` at the window boundary; the KL
divergence exceeds it, with slack `0.52·δ²`.

References: standard Chernoff/large-deviations exponent for the binomial lower tail
(Cover–Thomas, *Elements of Information Theory*, §11.1); Renner (2005),
`arXiv:quant-ph/0512258v2`, §5.
-/

namespace Math.Concentration.BernoulliKL

open Real

/-- **quadratic KL lower bound on the small-error-rate window.**  For `0 < Q`, `0 < δ`,
`Q + 2δ ≤ 1/25`,
`12.5·δ² ≤ klBer (Q + δ) (Q + 2δ)`.

The constant `12.5 = 1/(2·(1/25))` is recovered because the reference rate `b = Q + 2δ ≤ 1/25`
caps the quadratic form `(b − a)²/(2b) = δ²/(2b) ≥ δ²/(2·(1/25)) = 12.5·δ²`.  Proof:
`mul_sq_le_klBer` at `c = 12.5` (the Padé bracket `sq_mul_add_div_le_klBer`),
exactly as
`four_mul_sq_le_klBer_add_two_mul`; only the window literal and final constant change. -/
theorem twelve_point_five_mul_sq_le_klBer_of_le (Q δ : ℝ) (hQ : 0 < Q) (hδ : 0 < δ)
    (hb : Q + 2 * δ ≤ (1 : ℝ) / 25) :
    (12.5 : ℝ) * δ ^ 2 ≤ klBer (Q + δ) (Q + 2 * δ) := by
  -- `mul_sq_le_klBer` with `a = Q + δ`, `b = Q + 2δ`, `c = 12.5`: `2·12.5·b = 25·b ≤
  -- 1`.
  have h := mul_sq_le_klBer (a := Q + δ) (b := Q + 2 * δ) (c := 12.5)
    (by linarith) (by linarith) (by linarith) (by norm_num; linarith)
  rwa [show Q + 2 * δ - (Q + δ) = δ by ring] at h

/-- **KL-constant lemma at the raised `θ = 9δ/4` tilt.**  For `0 < Q`, `0 < δ`, `Q + 2δ ≤ 1/25`,
`8·δ² ≤ klBer (Q + δ) (Q + 13δ/4)`.

Proved by the same Padé bracket as `twelve_point_five_mul_sq_le_klBer_of_le`
(`mul_sq_le_klBer` at `c = 128/81`), with
the reference tilt `b = Q + 13δ/4`. Here `b − a = 9δ/4`, so the quadratic form
`(b − a)²/(2b) = (81δ²/16)/(2b)`; with `b ≤ 1/25 + 5δ/4 ≤ 0.065` this is `≳ 39·δ²`, comfortably
above the claimed `8·δ²`. -/
theorem eight_mul_sq_le_klBer_of_le (Q δ : ℝ) (hQ : 0 < Q) (hδ : 0 < δ)
    (hLowQ : Q + 2 * δ ≤ (1 : ℝ) / 25) :
    (8 : ℝ) * δ ^ 2 ≤ klBer (Q + δ) (Q + 13 * δ / 4) := by
  -- `mul_sq_le_klBer` with `a = Q + δ`, `b = Q + 13δ/4`, `c = 128/81`: here `b - a =
  -- 9δ/4`,
  -- so `c·(b - a)² = 8·δ²`, and `2·c·b = 256·b/81 ≤ 1` since `b ≤ 1/25 + 5δ/4 ≤ 0.065`.
  have h := mul_sq_le_klBer (a := Q + δ) (b := Q + 13 * δ / 4) (c := 128 / 81)
    (by linarith) (by linarith) (by linarith) (by linarith)
  rwa [show (128 / 81 : ℝ) * (Q + 13 * δ / 4 - (Q + δ)) ^ 2 = 8 * δ ^ 2 by ring] at h

end Math.Concentration.BernoulliKL
