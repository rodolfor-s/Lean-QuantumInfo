import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.RtFunction

/-!
# Bennett's `h`, its Bernstein lower bound, and the exact-tilt factor

The scalar layer behind the *exact* Chernoff tilt for Renner's `r_t` estimate.

Renner's `lem:rtbound` (`arXiv:quant-ph/0512258v2`, `main.tex:10487`) relaxes
`rennerRt(t,z) = z^t − t·log z − 1` to the quadratic envelope `κ·(t·log z)²` before optimising the
tilt.  The relaxation is not needed: writing `v = t·log z` and `φ(v) = e^v − v − 1`, the
entropy-cancelled exponent `φ(v) − v·w` is minimised at `v = log(1 + w)`, where it takes the
value `−h(w)` **exactly** (`bennett_tilt_identity`), with

`h(w) = (1 + w)·log(1 + w) − w`

Bennett's function (Bennett 1962, *J. Amer. Statist. Assoc.* 57, 33–45; the same `h` as in
Boucheron–Lugosi–Massart, *Concentration Inequalities*, §2.7–2.8).  `h` has no elementary
inverse, so the tilt is transported to a closed form through Bernstein's rational minorant
`h(w) ≥ 3w²/(6 + 2w)` (`three_mul_sq_div_le_bennettH`, BLM Exercise 2.8), whose inversion against a
prescribed exponent is the positive root of `w² − (a/3)·w − a = 0`, namely

`bennettFactor a = a/6 + √(a + a²/36)`.

## Main statements

* `two_mul_div_le_log_one_add` — the Padé(1,1) minorant `2w/(2 + w) ≤ log(1 + w)` on `w ≥ 0`.
* `three_mul_sq_div_le_bennettH` — `3w²/(6 + 2w) ≤ h(w)` on `w ≥ 0`.
* `bennett_tilt_identity` — `φ(log(1+w)) − log(1+w)·w = −h(w)`, an identity, not a bound.
* `bennettFactor_sq` — `bennettFactor a` solves `w² = (a/3)·w + a`.
* `bennettFactor_le_one_of_le_three_quarters` / `one_le_bennettFactor_of_three_quarters_le` —
  the exact regime split `a ≤ 3/4 ↔ bennettFactor a ≤ 1`.
* `bennettFactor_le_two_mul_of_eq_four_mul_log_two_mul_sq` — the dominance
  `bennettFactor a ≤ 2·f` at `a = 4·log 2·f²`, valid on the whole regime `a ≤ 3/4`.
-/

open Real

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-! ## The Padé(1,1) minorant of `log` -/

/-- `0 ≤ log(1 + w) + 1/(1 + w) − 1` for `w ≥ 0`: the derivative of the Padé gap.

This follows from `Real.one_sub_inv_le_log_of_pos` at `1 + w`. -/
private lemma log_one_add_add_inv_sub_one_nonneg {w : ℝ} (hw : 0 ≤ w) :
    0 ≤ Real.log (1 + w) + (1 + w)⁻¹ - 1 := by
  have hpos : (0 : ℝ) < 1 + w := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hpos
  linarith

/-- The Padé gap `(2 + w)·log(1 + w) − 2w` is nonnegative for `w ≥ 0`. -/
private lemma padeGap_nonneg {w : ℝ} (hw : 0 ≤ w) :
    0 ≤ (2 + w) * Real.log (1 + w) - 2 * w := by
  set f : ℝ → ℝ := fun x => (2 + x) * Real.log (1 + x) - 2 * x with hf
  have hderiv : ∀ x : ℝ, 0 < 1 + x →
      HasDerivAt f (Real.log (1 + x) + (2 + x) / (1 + x) - 2) x := by
    intro x hx
    have hlog : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x := by
      have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
        simpa using (hasDerivAt_id x).const_add (1 : ℝ)
      simpa only [Function.comp_def, mul_one, one_div] using (Real.hasDerivAt_log hx.ne').comp x h1
    have hlin : HasDerivAt (fun y : ℝ => 2 + y) 1 x := by
      simpa using (hasDerivAt_id x).const_add (2 : ℝ)
    have hmul := hlin.mul hlog
    have h2 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
      simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
    have := hmul.sub h2
    apply this.congr_deriv
    field_simp
  have hmono : MonotoneOn f (Set.Ici (0 : ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici _) ?cont ?diff ?sign
    · refine ContinuousOn.sub (ContinuousOn.mul (by fun_prop) ?_) (by fun_prop)
      refine ContinuousOn.log (by fun_prop) ?_
      intro x hx
      have : (0 : ℝ) ≤ x := hx
      positivity
    · intro x hx
      rw [interior_Ici] at hx
      exact (hderiv x (by linarith [hx.out])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : (0 : ℝ) < x := hx.out
      have hx1 : (0 : ℝ) < 1 + x := by linarith
      rw [(hderiv x hx1).deriv]
      have hkey := log_one_add_add_inv_sub_one_nonneg hx0.le
      have hsplit : (2 + x) / (1 + x) = 1 + (1 + x)⁻¹ := by
        field_simp
        ring
      rw [hsplit]
      linarith
  have h0 : f 0 = 0 := by simp [hf]
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hw) hw
  rw [h0] at this
  exact this

/-- **The Padé(1,1) minorant of the logarithm**: `2w/(2 + w) ≤ log(1 + w)` for `w ≥ 0`.

The two sides agree to second order at `w = 0`; the gap `(2 + w)·log(1 + w) − 2w` has
nonnegative derivative `log(1 + w) + 1/(1 + w) − 1` and vanishes at `w = 0`. -/
theorem two_mul_div_le_log_one_add {w : ℝ} (hw : 0 ≤ w) :
    2 * w / (2 + w) ≤ Real.log (1 + w) := by
  have hpos : (0 : ℝ) < 2 + w := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith [padeGap_nonneg hw]

/-! ## Bennett's `h` and its Bernstein minorant -/

/-- **Bennett's function** `h(w) = (1 + w)·log(1 + w) − w`.

This is the exact value of the entropy-cancelled Chernoff exponent at the optimal tilt
(`bennett_tilt_identity`); Renner's quadratic relaxation replaces it by `w²/2 · (1 + o(1))`
after a further envelope step. -/
noncomputable def bennettH (w : ℝ) : ℝ := (1 + w) * Real.log (1 + w) - w

/-- The Bennett–Bernstein gap `(6 + 2w)·h(w) − 3w²` is nonnegative on `w ≥ 0`.

Its derivative is `4·((2 + w)·log(1 + w) − 2w)`, the Padé gap, and it vanishes at `w = 0`. -/
private lemma bennettBernsteinGap_nonneg {w : ℝ} (hw : 0 ≤ w) :
    0 ≤ (6 + 2 * w) * bennettH w - 3 * w ^ 2 := by
  set g : ℝ → ℝ := fun x => (6 + 2 * x) * ((1 + x) * Real.log (1 + x) - x) - 3 * x ^ 2 with hg
  have hderiv : ∀ x : ℝ, 0 < 1 + x →
      HasDerivAt g (4 * ((2 + x) * Real.log (1 + x) - 2 * x)) x := by
    intro x hx
    have hlog : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x := by
      have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
        simpa using (hasDerivAt_id x).const_add (1 : ℝ)
      simpa only [Function.comp_def, mul_one, one_div] using (Real.hasDerivAt_log hx.ne').comp x h1
    have honeadd : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
      simpa using (hasDerivAt_id x).const_add (1 : ℝ)
    have hsix : HasDerivAt (fun y : ℝ => 6 + 2 * y) 2 x := by
      simpa using ((hasDerivAt_id x).const_mul (2 : ℝ)).const_add (6 : ℝ)
    have hinner : HasDerivAt (fun y : ℝ => (1 + y) * Real.log (1 + y) - y)
        (Real.log (1 + x) + (1 + x) * (1 / (1 + x)) - 1) x := by
      have := (honeadd.mul hlog).sub (hasDerivAt_id x)
      exact this.congr_deriv (by rw [one_mul])
    have hsq : HasDerivAt (fun y : ℝ => 3 * y ^ 2) (3 * (2 * x)) x := by
      simpa using ((hasDerivAt_pow 2 x).const_mul (3 : ℝ))
    have := (hsix.mul hinner).sub hsq
    apply this.congr_deriv
    field_simp
    ring
  have hmono : MonotoneOn g (Set.Ici (0 : ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici _) ?cont ?diff ?sign
    · refine ContinuousOn.sub (ContinuousOn.mul (by fun_prop) (ContinuousOn.sub
        (ContinuousOn.mul (by fun_prop) ?_) (by fun_prop))) (by fun_prop)
      refine ContinuousOn.log (by fun_prop) ?_
      intro x hx
      have : (0 : ℝ) ≤ x := hx
      positivity
    · intro x hx
      rw [interior_Ici] at hx
      exact (hderiv x (by linarith [hx.out])).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : (0 : ℝ) < x := hx.out
      rw [(hderiv x (by linarith)).deriv]
      have := padeGap_nonneg hx0.le
      linarith
  have h0 : g 0 = 0 := by simp [hg]
  have hmain := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hw) hw
  rw [h0] at hmain
  simpa [hg, bennettH] using hmain

/-- **Bennett ≥ Bernstein**: `3w²/(6 + 2w) ≤ h(w)` for `w ≥ 0`.

Bernstein's rational minorant of Bennett's function (Boucheron–Lugosi–Massart,
*Concentration Inequalities*, Exercise 2.8).  Equality holds to third order at `w = 0`; at
`w = 1` the margin is `h(1) − 3/8 = 2·log 2 − 1 − 0.375 = 0.011294…`.

This is the step that makes the exact Chernoff tilt invertible in closed form: `h` itself has
no elementary inverse, whereas `3w²/(6 + 2w) = c` is a quadratic in `w`. -/
theorem three_mul_sq_div_le_bennettH {w : ℝ} (hw : 0 ≤ w) :
    3 * w ^ 2 / (6 + 2 * w) ≤ bennettH w := by
  have hpos : (0 : ℝ) < 6 + 2 * w := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith [bennettBernsteinGap_nonneg hw]

/-- `0 ≤ h(w)` for `w ≥ 0`. -/
theorem bennettH_nonneg {w : ℝ} (hw : 0 ≤ w) : 0 ≤ bennettH w := by
  have hpos : (0 : ℝ) < 6 + 2 * w := by linarith
  have hbern : (0 : ℝ) ≤ 3 * w ^ 2 / (6 + 2 * w) := by positivity
  linarith [three_mul_sq_div_le_bennettH hw]

/-! ## The exact tilt identity -/

/-- **The exact Chernoff tilt identity.**  For `w > −1`, at the tilt `v = log(1 + w)`,

`exp v − v − 1 − v·w = −h(w)`.

This is an *identity*, not an inequality: `v ↦ φ(v) − v·w` with `φ(v) = e^v − v − 1` has
derivative `e^v − 1 − w`, which vanishes exactly at `v = log(1 + w)`, and the minimum value is
`−h(w)`.  Renner's `InfoTheory.SmoothMinEntropy.AEP.IID.optimalTilt` instead minimises the quadratic
*envelope*
`κ·v² − v·w`, which is why it lands at a different tilt. -/
theorem bennett_tilt_identity {w : ℝ} (hw : -1 < w) :
    Real.exp (Real.log (1 + w)) - Real.log (1 + w) - 1 - Real.log (1 + w) * w
      = -bennettH w := by
  have hpos : (0 : ℝ) < 1 + w := by linarith
  rw [Real.exp_log hpos, bennettH]
  ring

/-! ## The closed-form tilt factor -/

/-- **The Bennett tilt factor**: the positive root of `w² − (a/3)·w − a = 0`,

`bennettFactor a = a/6 + √(a + a²/36)`.

`a` is the prescribed Bernstein exponent budget: `bennettFactor a` is the unique `w ≥ 0` with
`3w²/(6 + 2w) = a/2`.  (Clearing denominators: `6w² = a(6 + 2w)`, i.e. `w² = (a/3)w + a`.) -/
noncomputable def bennettFactor (a : ℝ) : ℝ := a / 6 + Real.sqrt (a + a ^ 2 / 36)

/-- `bennettFactor` is nonnegative on `a ≥ 0`. -/
theorem bennettFactor_nonneg {a : ℝ} (ha : 0 ≤ a) : 0 ≤ bennettFactor a := by
  unfold bennettFactor
  positivity

/-- **The defining quadratic**: `bennettFactor a ^ 2 = (a/3)·bennettFactor a + a`. -/
theorem bennettFactor_sq {a : ℝ} (ha : 0 ≤ a) :
    bennettFactor a ^ 2 = a / 3 * bennettFactor a + a := by
  have hrad : (0 : ℝ) ≤ a + a ^ 2 / 36 := by positivity
  have hsq : Real.sqrt (a + a ^ 2 / 36) ^ 2 = a + a ^ 2 / 36 := Real.sq_sqrt hrad
  unfold bennettFactor
  nlinarith [hsq]

/-- **The Bernstein-exponent identity**: `3·w²/(6 + 2w) = a/2` at `w = bennettFactor a`.

This is the equation `bennettFactor` was built to solve: the Bernstein exponent at the tilt
factor is exactly half the budget `a`. -/
theorem three_mul_sq_div_bennettFactor {a : ℝ} (ha : 0 ≤ a) :
    3 * bennettFactor a ^ 2 / (6 + 2 * bennettFactor a) = a / 2 := by
  have hnn := bennettFactor_nonneg ha
  have hpos : (0 : ℝ) < 6 + 2 * bennettFactor a := by linarith
  rw [div_eq_iff (ne_of_gt hpos), bennettFactor_sq ha]
  ring

/-- **The regime condition, forward direction**: `a ≤ 3/4` forces `bennettFactor a ≤ 1`.

`w ≤ 1` is exactly the admissibility condition `v = log(1 + w) ≤ log 2` of Renner's `lem:rtbound`.
-/
theorem bennettFactor_le_one_of_le_three_quarters {a : ℝ} (ha : 0 ≤ a) (h : a ≤ 3 / 4) :
    bennettFactor a ≤ 1 := by
  have hrad : (0 : ℝ) ≤ a + a ^ 2 / 36 := by positivity
  have hb : (0 : ℝ) ≤ 1 - a / 6 := by linarith
  have hsq : a + a ^ 2 / 36 ≤ (1 - a / 6) ^ 2 := by nlinarith
  have := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq hb] at this
  unfold bennettFactor
  linarith

/-- **The regime condition, complementary direction**: `3/4 ≤ a` forces `1 ≤ bennettFactor a`.

Off the regime the tilt factor exceeds `1`, which is what makes the small-block branch of the
AEP trivial: the correction `log₂ μ · bennettFactor a` then exceeds `log₂ μ` itself. -/
theorem one_le_bennettFactor_of_three_quarters_le {a : ℝ} (h : 3 / 4 ≤ a) :
    1 ≤ bennettFactor a := by
  have ha : (0 : ℝ) ≤ a := by linarith
  have hrad : (0 : ℝ) ≤ a + a ^ 2 / 36 := by positivity
  by_cases h6 : (6 : ℝ) ≤ a
  · have : Real.sqrt (a + a ^ 2 / 36) ≥ 0 := Real.sqrt_nonneg _
    unfold bennettFactor
    linarith
  · push Not at h6
    have hb : (0 : ℝ) ≤ 1 - a / 6 := by linarith
    have hsq : (1 - a / 6) ^ 2 ≤ a + a ^ 2 / 36 := by nlinarith
    have := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq hb] at this
    unfold bennettFactor
    linarith

/-- **Uniform dominance of the exact tilt over Renner's clamped tilt.**

At `a = 4·log 2·f²` with `f ≥ 0`, and on the whole regime `bennettFactor a ≤ 1`,

`bennettFactor a ≤ 2·f`.

`2·f` is Renner's factor: his `δ = 2·log₂ μ · noiseFactor`, ours is
`log₂ μ · bennettFactor a`, so this inequality is exactly `δ_Bennett ≤ δ_Renner` at the same
`μ`.  The proof is the defining quadratic: `w² = (a/3)w + a ≤ a·(1/3 + 1) ≤ a/log 2 = 4f²`
using `w ≤ 1` and `log 2 ≤ 3/4`.  The dominance in fact survives up to
`w ≤ 3·(1/log 2 − 1) = 1.328…`, well beyond the regime bound `w ≤ 1`. -/
theorem bennettFactor_le_two_mul_of_eq_four_mul_log_two_mul_sq
    {a f : ℝ} (hf : 0 ≤ f) (ha : a = 4 * Real.log 2 * f ^ 2)
    (hw : bennettFactor a ≤ 1) :
    bennettFactor a ≤ 2 * f := by
  have hl2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl2 : Real.log 2 < 3 / 4 := by
    have := Real.log_two_lt_d9
    linarith
  have ha_nonneg : (0 : ℝ) ≤ a := by rw [ha]; positivity
  have hnn := bennettFactor_nonneg ha_nonneg
  have hsq := bennettFactor_sq ha_nonneg
  -- `w² = (a/3)w + a ≤ (4/3)·a`, and `(4/3)·a = (16/3)·log 2·f² ≤ 4f²`.
  have hstep : bennettFactor a ^ 2 ≤ 4 * f ^ 2 := by
    have h1 : a / 3 * bennettFactor a ≤ a / 3 := by nlinarith
    have h2 : (4 : ℝ) / 3 * a ≤ 4 * f ^ 2 := by
      rw [ha]; nlinarith [sq_nonneg f]
    linarith [hsq, h1, h2]
  nlinarith [hstep, hnn, hf]

/-- **The dominance is strict.**

At `a = 4·log 2·f²` with `f > 0`, and on the regime `bennettFactor a ≤ 1`,

`bennettFactor a < 2·f`.

The strictness is `log 2 < 3/4`: the defining quadratic gives `w² ≤ (4/3)·a = (16/3)·log 2·f²`
and `(16/3)·log 2 = 3.6968… < 4`.  So the exact tilt is a genuine improvement over Renner's
clamped tilt, not a re-parameterisation. -/
theorem bennettFactor_lt_two_mul_of_eq_four_mul_log_two_mul_sq
    {a f : ℝ} (hf : 0 < f) (ha : a = 4 * Real.log 2 * f ^ 2)
    (hw : bennettFactor a ≤ 1) :
    bennettFactor a < 2 * f := by
  have hl2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hl2 : Real.log 2 < 3 / 4 := by
    have := Real.log_two_lt_d9
    linarith
  have ha_pos : (0 : ℝ) < a := by rw [ha]; positivity
  have hnn := bennettFactor_nonneg ha_pos.le
  have hsq := bennettFactor_sq ha_pos.le
  have hstep : bennettFactor a ^ 2 < 4 * f ^ 2 := by
    have h1 : a / 3 * bennettFactor a ≤ a / 3 := by nlinarith
    have h2 : (4 : ℝ) / 3 * a < 4 * f ^ 2 := by
      rw [ha]; nlinarith [sq_nonneg f, hf]
    linarith [hsq, h1, h2]
  nlinarith [hstep, hnn, hf]

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
