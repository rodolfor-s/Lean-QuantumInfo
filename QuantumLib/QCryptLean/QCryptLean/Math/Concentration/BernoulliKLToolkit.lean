import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import QCryptLean.Math.Concentration.BernoulliKL

/-!
# Bernoulli-KL toolkit

Analytic control lemmas for the Bernoulli KL divergence
`klBer a b = a·log(a/b) + (1 - a)·log((1 - a)/(1 - b))` defined in `BernoulliKL.lean`:

* `klBer_antitone_left`   : `θ ↦` monotonicity in the first argument below the second;
* `quadratic_taylor_le_klBer`      : a strong-convexity quadratic lower bound in the second
argument;
* `klBer_lipschitz_left`  : Lipschitz control in the first argument;
* `klBer_transfer_left`   : exact closed form for the first-argument difference of `klBer` at a
                            common tilt;
* `klBer_tangent_fst`     : tangent-plus-remainder identity for `klBer` on the open unit interval;
* `mul_log_div_add_sub_le_klBer`      : elementary lower bound `s·log(s/a) + a - s ≤ klBer s a` for
`a, s < 1`;
* `two_mul_sq_le_klBer`   : **Pinsker's inequality** `2·(a - b)² ≤ klBer a b` for `0 ≤ a
≤ 1`,
                            `0 < b < 1` (endpoint variants
                            `two_mul_sq_le_klBer_zero_left`,
                            `two_mul_sq_le_klBer_of_pos_of_lt_one`).

All bounds are stated with the window endpoints and the curvature/Lipschitz constants as explicit
parameters (not baked-in numbers), matching the surrounding concentration infrastructure.
Pinsker's inequality follows Cover–Thomas, *Elements of Information Theory*, Lemma 11.6.1,
specialised to two points.
-/

namespace Math.Concentration.BernoulliKL

open Real

/-- Derivative of `a ↦ klBer a θ` at an interior point `a` with `0 < a < 1` and `0 < θ < 1`:
`d/da klBer a θ = log (a / θ) - log ((1 - a) / (1 - θ))`. -/
private theorem hasDerivAt_klBer_fst {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    HasDerivAt (fun a => klBer a θ)
      (Real.log (a / θ) - Real.log ((1 - a) / (1 - θ))) a := by
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hne_a : a ≠ 0 := ne_of_gt ha0
  have hne_θ : θ ≠ 0 := ne_of_gt hθ0
  have hne_1a : (1 : ℝ) - a ≠ 0 := ne_of_gt h1a
  have hne_1θ : (1 : ℝ) - θ ≠ 0 := by linarith
  have haθ_ne : a / θ ≠ 0 := div_ne_zero hne_a hne_θ
  have h1aθ_ne : (1 - a) / (1 - θ) ≠ 0 := div_ne_zero hne_1a hne_1θ
  -- First summand: a * log (a / θ).
  have hlog1 : HasDerivAt (fun a : ℝ => Real.log (a / θ)) (1 / a) a := by
    have := (Real.hasDerivAt_log haθ_ne).comp a ((hasDerivAt_id a).div_const θ)
    simp only [id] at this
    apply this.congr_deriv
    field_simp
  have hterm1 : HasDerivAt (fun a : ℝ => a * Real.log (a / θ))
      (Real.log (a / θ) + 1) a := by
    have := (hasDerivAt_id a).mul hlog1
    simp only [id] at this
    apply this.congr_deriv
    field_simp
  -- Second summand: (1 - a) * log ((1 - a) / (1 - θ)).
  have hlog2 : HasDerivAt (fun a : ℝ => Real.log ((1 - a) / (1 - θ)))
      (-(1 / (1 - a))) a := by
    have hinner : HasDerivAt (fun a : ℝ => (1 - a) / (1 - θ)) (-1 / (1 - θ)) a := by
      have := ((hasDerivAt_id a).const_sub 1).div_const (1 - θ)
      simpa using this
    have := (Real.hasDerivAt_log h1aθ_ne).comp a hinner
    apply this.congr_deriv
    rw [inv_div]
    field_simp
  have hterm2 : HasDerivAt (fun a : ℝ => (1 - a) * Real.log ((1 - a) / (1 - θ)))
      (-Real.log ((1 - a) / (1 - θ)) - 1) a := by
    have := ((hasDerivAt_id a).const_sub 1).mul hlog2
    simp only [id] at this
    apply this.congr_deriv
    field_simp
    ring
  have hsum := hterm1.add hterm2
  refine hsum.congr_deriv ?_
  ring

/-- **`klBer` is antitone in the first argument below the second.**
For `0 < a₁ ≤ a₂ ≤ θ < 1`, `klBer a₂ θ ≤ klBer a₁ θ`. -/
theorem klBer_antitone_left {a₁ a₂ θ : ℝ}
    (h0 : 0 < a₁) (h12 : a₁ ≤ a₂) (h2θ : a₂ ≤ θ) (hθ : θ < 1) :
    klBer a₂ θ ≤ klBer a₁ θ := by
  have hθ0 : 0 < θ := lt_of_lt_of_le h0 (le_trans h12 h2θ)
  -- Every point of `[a₁, a₂]` satisfies `0 < a < 1`.
  have hmem : ∀ a ∈ Set.Icc a₁ a₂, 0 < a ∧ a < 1 := by
    intro a ha
    rw [Set.mem_Icc] at ha
    exact ⟨lt_of_lt_of_le h0 ha.1, lt_of_le_of_lt (le_trans ha.2 h2θ) hθ⟩
  have hderiv : ∀ a ∈ Set.Icc a₁ a₂,
      HasDerivAt (fun a => klBer a θ)
        (Real.log (a / θ) - Real.log ((1 - a) / (1 - θ))) a := by
    intro a ha
    obtain ⟨hpos, hlt⟩ := hmem a ha
    exact hasDerivAt_klBer_fst hθ0 hθ hpos hlt
  have hcont : ContinuousOn (fun a => klBer a θ) (Set.Icc a₁ a₂) :=
    fun a ha => (hderiv a ha).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun a => klBer a θ) (interior (Set.Icc a₁ a₂)) := by
    intro a ha
    have ha' : a ∈ Set.Icc a₁ a₂ := interior_subset ha
    exact (hderiv a ha').differentiableAt.differentiableWithinAt
  have hnonpos : ∀ a ∈ interior (Set.Icc a₁ a₂), deriv (fun a => klBer a θ) a ≤ 0 := by
    intro a ha
    have ha' : a ∈ Set.Icc a₁ a₂ := interior_subset ha
    obtain ⟨hpos, hlt⟩ := hmem a ha'
    rw [Set.mem_Icc] at ha'
    rw [(hderiv a (by rw [Set.mem_Icc]; exact ha')).deriv]
    have h1a : 0 < 1 - a := by linarith
    -- log (a/θ) ≤ 0 since a ≤ θ; log ((1-a)/(1-θ)) ≥ 0 since 1-a ≥ 1-θ.
    have hle1 : Real.log (a / θ) ≤ 0 := by
      apply Real.log_nonpos (by positivity)
      rw [div_le_one hθ0]
      linarith [ha'.2, h2θ]
    have hle2 : 0 ≤ Real.log ((1 - a) / (1 - θ)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by linarith), one_mul]
      linarith [ha'.2, h2θ]
    linarith
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc a₁ a₂) hcont hdiff hnonpos
  exact hanti (Set.mem_Icc.mpr ⟨le_rfl, h12⟩)
    (Set.mem_Icc.mpr ⟨h12, le_rfl⟩) h12

/-- The `klBer`-in-first-argument derivative, rewritten as a single logarithm:
`log (a / θ) − log ((1 − a) / (1 − θ)) = log (a (1 − θ) / (θ (1 − a)))`. -/
private theorem klBer_fst_deriv_eq {a θ : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    Real.log (a / θ) - Real.log ((1 - a) / (1 - θ))
      = Real.log (a * (1 - θ) / (θ * (1 - a))) := by
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  rw [← Real.log_div (by positivity) (by positivity)]
  congr 1
  field_simp

/-- **`klBer` is Lipschitz in the first argument.**
For `0 < a₁ ≤ a₂ < 1` and `0 < θ < 1`, if the derivative log is bounded by `L` throughout
`[a₁, a₂]`, then `|klBer a₂ θ − klBer a₁ θ| ≤ L (a₂ − a₁)`. -/
theorem klBer_lipschitz_left {a₁ a₂ θ L : ℝ}
    (h0 : 0 < a₁) (h12 : a₁ ≤ a₂) (ha2 : a₂ < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hL : ∀ a ∈ Set.Icc a₁ a₂, |Real.log (a * (1 - θ) / (θ * (1 - a)))| ≤ L) :
    |klBer a₂ θ - klBer a₁ θ| ≤ L * (a₂ - a₁) := by
  have hmem : ∀ a ∈ Set.Icc a₁ a₂, 0 < a ∧ a < 1 := by
    intro a ha
    rw [Set.mem_Icc] at ha
    exact ⟨lt_of_lt_of_le h0 ha.1, lt_of_le_of_lt ha.2 ha2⟩
  -- Derivative within the set.
  have hderiv : ∀ a ∈ Set.Icc a₁ a₂,
      HasDerivWithinAt (fun a => klBer a θ)
        (Real.log (a * (1 - θ) / (θ * (1 - a)))) (Set.Icc a₁ a₂) a := by
    intro a ha
    obtain ⟨hpos, hlt⟩ := hmem a ha
    have hd := hasDerivAt_klBer_fst hθ0 hθ1 hpos hlt
    rw [klBer_fst_deriv_eq hpos hlt hθ0 hθ1] at hd
    exact hd.hasDerivWithinAt
  have hbound : ∀ a ∈ Set.Icc a₁ a₂,
      ‖Real.log (a * (1 - θ) / (θ * (1 - a)))‖ ≤ L := by
    intro a ha
    rw [Real.norm_eq_abs]
    exact hL a ha
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (convex_Icc a₁ a₂)
    (Set.mem_Icc.mpr ⟨le_rfl, h12⟩) (Set.mem_Icc.mpr ⟨h12, le_rfl⟩)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ a₂ - a₁)] at hmain
  exact hmain

/-- Derivative of `θ ↦ klBer a θ` at an interior point `θ` with `0 < θ < 1`
(and `0 < a < 1`): `d/dθ klBer a θ = -(a / θ) + (1 - a) / (1 - θ)`. -/
private theorem hasDerivAt_klBer_snd {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    HasDerivAt (fun θ => klBer a θ)
      (-(a / θ) + (1 - a) / (1 - θ)) θ := by
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hne_θ : θ ≠ 0 := ne_of_gt hθ0
  have hne_1θ : (1 : ℝ) - θ ≠ 0 := ne_of_gt h1θ
  have haθ_ne : a / θ ≠ 0 := div_ne_zero (ne_of_gt ha0) hne_θ
  have h1aθ_ne : (1 - a) / (1 - θ) ≠ 0 := div_ne_zero (ne_of_gt h1a) hne_1θ
  -- First summand: a * log (a / θ).
  have hlog1 : HasDerivAt (fun θ : ℝ => Real.log (a / θ)) (-(1 / θ)) θ := by
    have hinv : HasDerivAt (fun θ : ℝ => θ⁻¹) (-1 / θ ^ 2) θ := by
      exact (hasDerivAt_id θ).inv hne_θ
    have hinner : HasDerivAt (fun θ : ℝ => a / θ) (a * (-1 / θ ^ 2)) θ := by
      have := hinv.const_mul a
      simpa [div_eq_mul_inv] using this
    have := (Real.hasDerivAt_log haθ_ne).comp θ hinner
    apply this.congr_deriv
    field_simp
  have hterm1 : HasDerivAt (fun θ : ℝ => a * Real.log (a / θ)) (-(a / θ)) θ := by
    have := hlog1.const_mul a
    apply this.congr_deriv
    field_simp
  -- Second summand: (1 - a) * log ((1 - a) / (1 - θ)).
  have hlog2 : HasDerivAt (fun θ : ℝ => Real.log ((1 - a) / (1 - θ))) (1 / (1 - θ)) θ := by
    have hinner : HasDerivAt (fun θ : ℝ => (1 - a) / (1 - θ)) ((1 - a) / (1 - θ) ^ 2) θ := by
      have hd : HasDerivAt (fun θ : ℝ => 1 - θ) (-1) θ := by
        simpa using (hasDerivAt_id θ).const_sub 1
      have hinv : HasDerivAt (fun θ : ℝ => (1 - θ)⁻¹) (-(-1) / (1 - θ) ^ 2) θ :=
        hd.inv hne_1θ
      have := hinv.const_mul (1 - a)
      simpa [div_eq_mul_inv] using this
    have := (Real.hasDerivAt_log h1aθ_ne).comp θ hinner
    apply this.congr_deriv
    rw [inv_div]
    field_simp
  have hterm2 : HasDerivAt (fun θ : ℝ => (1 - a) * Real.log ((1 - a) / (1 - θ)))
      ((1 - a) / (1 - θ)) θ := by
    have := hlog2.const_mul (1 - a)
    apply this.congr_deriv
    field_simp
  have hsum := hterm1.add hterm2
  exact hsum

/-- Second derivative of `θ ↦ klBer a θ`:
`d/dθ (-(a/θ) + (1-a)/(1-θ)) = a / θ ^ 2 + (1 - a) / (1 - θ) ^ 2`. -/
private theorem hasDerivAt_klBer_snd' {a : ℝ} {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    HasDerivAt (fun θ => -(a / θ) + (1 - a) / (1 - θ))
      (a / θ ^ 2 + (1 - a) / (1 - θ) ^ 2) θ := by
  have h1θ : (0 : ℝ) < 1 - θ := by linarith
  have hne_θ : θ ≠ 0 := ne_of_gt hθ0
  have hne_1θ : (1 : ℝ) - θ ≠ 0 := ne_of_gt h1θ
  -- d/dθ (-(a/θ)) = a / θ^2.
  have h1 : HasDerivAt (fun θ : ℝ => -(a / θ)) (a / θ ^ 2) θ := by
    have hinv : HasDerivAt (fun θ : ℝ => θ⁻¹) (-1 / θ ^ 2) θ := by
      exact (hasDerivAt_id θ).inv hne_θ
    have hd : HasDerivAt (fun θ : ℝ => a / θ) (a * (-1 / θ ^ 2)) θ := by
      have := hinv.const_mul a
      simpa [div_eq_mul_inv] using this
    have := hd.neg
    apply this.congr_deriv
    field_simp
  -- d/dθ ((1-a)/(1-θ)) = (1-a) / (1-θ)^2.
  have h2 : HasDerivAt (fun θ : ℝ => (1 - a) / (1 - θ)) ((1 - a) / (1 - θ) ^ 2) θ := by
    have hd : HasDerivAt (fun θ : ℝ => 1 - θ) (-1) θ := by
      simpa using (hasDerivAt_id θ).const_sub 1
    have hinv : HasDerivAt (fun θ : ℝ => (1 - θ)⁻¹) (-(-1) / (1 - θ) ^ 2) θ :=
      hd.inv hne_1θ
    have := hinv.const_mul (1 - a)
    simpa [div_eq_mul_inv] using this
  exact h1.add h2

/-- **Strong-convexity quadratic lower bound on `klBer` in the second argument.**
For `0 < a < 1`, a window `[θLo, θHi] ⊆ (0, 1)`, and any `θ, θ₀` in the window, if `κ` is at most
the minimal curvature `a / θHi² + (1 - a) / (1 - θLo)²`, then the tangent line at `θ₀` plus the
quadratic correction `κ/2 (θ − θ₀)²` lies below `klBer a θ`. -/
theorem quadratic_taylor_le_klBer {a θ θ₀ θLo θHi κ : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hLo : 0 < θLo) (hHi : θHi < 1)
    (hθ : θ ∈ Set.Icc θLo θHi) (hθ₀ : θ₀ ∈ Set.Icc θLo θHi)
    (hκ : κ ≤ a / θHi ^ 2 + (1 - a) / (1 - θLo) ^ 2) :
    klBer a θ₀ + (-(a / θ₀) + (1 - a) / (1 - θ₀)) * (θ - θ₀) + κ / 2 * (θ - θ₀) ^ 2
      ≤ klBer a θ := by
  rw [Set.mem_Icc] at hθ hθ₀
  -- membership on the window ⇒ `0 < s < 1`
  have hmem : ∀ s ∈ Set.Icc θLo θHi, 0 < s ∧ s < 1 := by
    intro s hs
    rw [Set.mem_Icc] at hs
    exact ⟨lt_of_lt_of_le hLo hs.1, lt_of_le_of_lt hs.2 hHi⟩
  -- `g'` in second argument.
  set p : ℝ → ℝ := fun s => -(a / s) + (1 - a) / (1 - s) with hp
  -- curvature lower bound: `p'(s) = a/s² + (1-a)/(1-s)² ≥ κ` on the window
  have hcurv : ∀ s ∈ Set.Icc θLo θHi, κ ≤ a / s ^ 2 + (1 - a) / (1 - s) ^ 2 := by
    intro s hs
    obtain ⟨hs0, hs1⟩ := hmem s hs
    rw [Set.mem_Icc] at hs
    have hsq1 : a / θHi ^ 2 ≤ a / s ^ 2 := by
      apply div_le_div_of_nonneg_left ha0.le (by positivity)
      gcongr
      exact hs.2
    have hsq2 : (1 - a) / (1 - θLo) ^ 2 ≤ (1 - a) / (1 - s) ^ 2 := by
      apply div_le_div_of_nonneg_left (by linarith) (by
        have : 0 < 1 - s := by linarith
        positivity)
      have h1s : (0 : ℝ) ≤ 1 - s := by linarith
      have hle : 1 - s ≤ 1 - θLo := by linarith only [hs.1]
      gcongr
    linarith only [hκ, hsq1, hsq2]
  -- `p` is `κ`-strongly monotone across the window (integrated curvature bound)
  have hp_deriv : ∀ s ∈ interior (Set.Icc θLo θHi),
      HasDerivAt p (a / s ^ 2 + (1 - a) / (1 - s) ^ 2) s := by
    intro s hs
    have hs' : s ∈ Set.Icc θLo θHi := interior_subset hs
    obtain ⟨hs0, hs1⟩ := hmem s hs'
    exact hasDerivAt_klBer_snd' hs0 hs1
  have hp_cont : ContinuousOn p (Set.Icc θLo θHi) := by
    intro s hs
    obtain ⟨hs0, hs1⟩ := hmem s hs
    exact (hasDerivAt_klBer_snd' hs0 hs1).continuousAt.continuousWithinAt
  have hp_diff : DifferentiableOn ℝ p (interior (Set.Icc θLo θHi)) := by
    intro s hs
    exact (hp_deriv s hs).differentiableAt.differentiableWithinAt
  have hp_deriv_ge : ∀ s ∈ interior (Set.Icc θLo θHi), κ ≤ deriv p s := by
    intro s hs
    rw [(hp_deriv s hs).deriv]
    exact hcurv s (interior_subset hs)
  have hstrong : ∀ x ∈ Set.Icc θLo θHi, ∀ y ∈ Set.Icc θLo θHi, x ≤ y →
      κ * (y - x) ≤ p y - p x :=
    Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc θLo θHi)
      hp_cont hp_diff hp_deriv_ge
  -- ψ s := klBer a s − p(θ₀)·s − κ/2·(s − θ₀)²; ψ has min at θ₀ over the window.
  have hθ₀mem : θ₀ ∈ Set.Icc θLo θHi := Set.mem_Icc.mpr hθ₀
  have hθmem : θ ∈ Set.Icc θLo θHi := Set.mem_Icc.mpr hθ
  set ψ : ℝ → ℝ := fun s => klBer a s - p θ₀ * s - κ / 2 * (s - θ₀) ^ 2 with hψ
  -- ψ has derivative `p s − p θ₀ − κ (s − θ₀)`.
  have hψ_deriv : ∀ s ∈ Set.Icc θLo θHi,
      HasDerivAt ψ (p s - p θ₀ - κ * (s - θ₀)) s := by
    intro s hs
    obtain ⟨hs0, hs1⟩ := hmem s hs
    have hk : HasDerivAt (fun s => klBer a s) (p s) s := hasDerivAt_klBer_snd ha0 ha1 hs0 hs1
    have hlin : HasDerivAt (fun s : ℝ => p θ₀ * s) (p θ₀) s := by
      simpa using (hasDerivAt_id s).const_mul (p θ₀)
    have hquad : HasDerivAt (fun s : ℝ => κ / 2 * (s - θ₀) ^ 2) (κ * (s - θ₀)) s := by
      have hbase : HasDerivAt (fun s : ℝ => (s - θ₀) ^ 2) (2 * (s - θ₀)) s := by
        have := ((hasDerivAt_id s).sub_const θ₀).pow 2
        exact this.congr_deriv (by norm_num)
      have := hbase.const_mul (κ / 2)
      apply this.congr_deriv
      ring
    have := (hk.sub hlin).sub hquad
    exact this
  have hψ_cont : ContinuousOn ψ (Set.Icc θLo θHi) :=
    fun s hs => (hψ_deriv s hs).continuousAt.continuousWithinAt
  -- ψ is antitone on `[θLo, θ₀]` and monotone on `[θ₀, θHi]`.
  have hkey : ψ θ₀ ≤ ψ θ := by
    rcases le_total θ₀ θ with hle | hle
    · -- monotone on [θ₀, θHi]
      have hmono : MonotoneOn ψ (Set.Icc θ₀ θHi) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc θ₀ θHi)
        · exact hψ_cont.mono (Set.Icc_subset_Icc hθ₀.1 le_rfl)
        · intro s hs
          rw [interior_Icc, Set.mem_Ioo] at hs
          have hs' : s ∈ Set.Icc θLo θHi :=
            Set.mem_Icc.mpr ⟨le_trans hθ₀.1 hs.1.le, hs.2.le⟩
          exact (hψ_deriv s hs').differentiableAt.differentiableWithinAt
        · intro s hs
          rw [interior_Icc, Set.mem_Ioo] at hs
          have hs' : s ∈ Set.Icc θLo θHi :=
            Set.mem_Icc.mpr ⟨le_trans hθ₀.1 hs.1.le, hs.2.le⟩
          rw [(hψ_deriv s hs').deriv]
          have := hstrong θ₀ hθ₀mem s hs' hs.1.le
          linarith
      exact hmono (Set.mem_Icc.mpr ⟨le_rfl, hθ₀.2⟩)
        (Set.mem_Icc.mpr ⟨hle, hθ.2⟩) hle
    · -- antitone on [θLo, θ₀]
      have hanti : AntitoneOn ψ (Set.Icc θLo θ₀) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc θLo θ₀)
        · exact hψ_cont.mono (Set.Icc_subset_Icc le_rfl hθ₀.2)
        · intro s hs
          rw [interior_Icc, Set.mem_Ioo] at hs
          have hs' : s ∈ Set.Icc θLo θHi :=
            Set.mem_Icc.mpr ⟨hs.1.le, le_trans hs.2.le hθ₀.2⟩
          exact (hψ_deriv s hs').differentiableAt.differentiableWithinAt
        · intro s hs
          rw [interior_Icc, Set.mem_Ioo] at hs
          have hs' : s ∈ Set.Icc θLo θHi :=
            Set.mem_Icc.mpr ⟨hs.1.le, le_trans hs.2.le hθ₀.2⟩
          rw [(hψ_deriv s hs').deriv]
          have := hstrong s hs' θ₀ hθ₀mem hs.2.le
          linarith
      exact hanti (Set.mem_Icc.mpr ⟨hθ.1, hle⟩)
        (Set.mem_Icc.mpr ⟨hθ₀.1, le_rfl⟩) hle
  -- Unfold `ψ θ₀ ≤ ψ θ` into the target.
  simp only [hψ] at hkey
  nlinarith only [hkey]

/-- **(C′-transfer) the exact `a₁ → a₂` transfer closed form.**  At a common tilt `θ`, the
first-argument difference of `klBer` collapses the `log θ`/`log(1−θ)` slots into a single slope
term:
`klBer a₁ θ − klBer a₂ θ = (η a₁ − η a₂) − (a₁ − a₂)·(log θ − log(1−θ))`, with the
neg-binary-entropy
`η x = x·log x + (1−x)·log(1−x)` written explicitly.  Requires `0 < aᵢ < 1`, `0 < θ < 1` (all logs
split); proved by `ring` after `log_div` expansion. -/
theorem klBer_transfer_left (a₁ a₂ θ : ℝ)
    (ha1 : 0 < a₁) (ha1' : a₁ < 1) (ha2 : 0 < a₂) (ha2' : a₂ < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    klBer a₁ θ - klBer a₂ θ
      = ((a₁ * Real.log a₁ + (1 - a₁) * Real.log (1 - a₁))
          - (a₂ * Real.log a₂ + (1 - a₂) * Real.log (1 - a₂)))
        - (a₁ - a₂) * (Real.log θ - Real.log (1 - θ)) := by
  have hθne : θ ≠ 0 := ne_of_gt hθ0
  have h1θne : (1 : ℝ) - θ ≠ 0 := by linarith
  unfold klBer
  rw [Real.log_div (ne_of_gt ha1) hθne,
    Real.log_div (by linarith : (1 : ℝ) - a₁ ≠ 0) h1θne,
    Real.log_div (ne_of_gt ha2) hθne,
    Real.log_div (by linarith : (1 : ℝ) - a₂ ≠ 0) h1θne]
  ring

/-- Tangent-plus-remainder identity for Bernoulli KL divergence on the open unit interval. -/
theorem klBer_tangent_fst (a s θ : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (hs0 : 0 < s) (hs1 : s < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    klBer a θ - klBer s θ
      = (s - a) * ((Real.log θ - Real.log (1 - θ)) - (Real.log a - Real.log (1 - a)))
        - klBer s a := by
  unfold klBer
  rw [Real.log_div (ne_of_gt ha0) (ne_of_gt hθ0),
    Real.log_div (by linarith : (1:ℝ) - a ≠ 0) (by linarith : (1:ℝ) - θ ≠ 0),
    Real.log_div (ne_of_gt hs0) (ne_of_gt hθ0),
    Real.log_div (by linarith : (1:ℝ) - s ≠ 0) (by linarith : (1:ℝ) - θ ≠ 0),
    Real.log_div (ne_of_gt hs0) (ne_of_gt ha0),
    Real.log_div (by linarith : (1:ℝ) - s ≠ 0) (by linarith : (1:ℝ) - a ≠ 0)]
  ring

/-- Elementary lower bound for Bernoulli KL divergence, for `a, s < 1`.

Only `1 - a` and `1 - s` need to be positive; no lower bound on `a` or `s` is used. -/
theorem mul_log_div_add_sub_le_klBer (a s : ℝ) (ha1 : a < 1) (hs1 : s < 1) :
    s * Real.log (s / a) + a - s ≤ klBer s a := by
  have h1s : (0 : ℝ) < 1 - s := by linarith
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have hx : (0 : ℝ) < (1 - a) / (1 - s) := by positivity
  have hlog := Real.log_le_sub_one_of_pos hx
  rw [Real.log_div (by linarith) (by linarith)] at hlog
  have hprod : (1 - s) * (Real.log (1 - a) - Real.log (1 - s)) ≤ (1 - s) * ((1 - a) / (1 - s) - 1)
      :=
    mul_le_mul_of_nonneg_left hlog h1s.le
  have hrw : (1 - s) * ((1 - a) / (1 - s) - 1) = s - a := by field_simp; ring
  rw [hrw] at hprod
  have hlogdiv : Real.log ((1 - s) / (1 - a)) = Real.log (1 - s) - Real.log (1 - a) :=
    Real.log_div (by linarith) (by linarith)
  unfold klBer
  rw [hlogdiv]
  nlinarith [hprod]

/-- Endpoint case of Pinsker: for `0 < b < 1`, `2·b² ≤ klBer 0 b = -log(1 - b)`.
Proof: `x ↦ -log(1 - x) - 2x²` has derivative `(1 - 2x)²/(1 - x) ≥ 0` on `[0, 1)`,
so it is monotone with value `0` at `x = 0`. -/
theorem two_mul_sq_le_klBer_zero_left {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    2 * b ^ 2 ≤ klBer 0 b := by
  -- `klBer 0 b = -log(1 - b)`: the `0 * log (0 / b)` term vanishes since `Real.log 0 = 0`.
  have hkl : klBer 0 b = -Real.log (1 - b) := by simp [klBer]
  -- φ x = -log(1 - x) - 2x²; φ' x = (1 - 2x)² / (1 - x) ≥ 0 on [0, b] ⊂ [0, 1), φ 0 = 0.
  set φ : ℝ → ℝ := fun x => -Real.log (1 - x) - 2 * x ^ 2 with hφ
  have hderiv : ∀ x ∈ Set.Icc 0 b, HasDerivAt φ ((1 - 2 * x) ^ 2 / (1 - x)) x := by
    intro x hx
    rw [Set.mem_Icc] at hx
    have hx1 : (1 : ℝ) - x ≠ 0 := sub_ne_zero_of_ne (by linarith)
    have hlog : HasDerivAt (fun x : ℝ => -Real.log (1 - x)) (1 / (1 - x)) x := by
      have hcomp := (Real.hasDerivAt_log hx1).comp x ((hasDerivAt_id x).const_sub 1)
      exact hcomp.neg.congr_deriv (by simp)
    have hquad : HasDerivAt (fun x : ℝ => 2 * x ^ 2) (4 * x) x := by
      exact (((hasDerivAt_id x).pow 2).const_mul 2).congr_deriv (by simp only [id_eq]; ring)
    exact (hlog.sub hquad).congr_deriv (by field_simp; ring)
  have hcont : ContinuousOn φ (Set.Icc 0 b) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ φ (interior (Set.Icc 0 b)) := fun x hx =>
    (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
  have hnonneg : ∀ x ∈ interior (Set.Icc 0 b), 0 ≤ deriv φ x := by
    intro x hx
    obtain ⟨-, hx2⟩ := interior_subset hx
    rw [(hderiv x (interior_subset hx)).deriv]
    exact div_nonneg (sq_nonneg _) (by linarith)
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc 0 b) hcont hdiff hnonneg
  have hval : φ 0 ≤ φ b :=
    hmono (Set.mem_Icc.mpr ⟨le_rfl, hb0.le⟩) (Set.mem_Icc.mpr ⟨hb0.le, le_rfl⟩) hb0.le
  simp only [hφ] at hval
  simp at hval
  linarith [hkl, hval]

/-- **Pinsker's inequality for the Bernoulli KL divergence, interior points.**
For `0 < a < 1` and `0 < b < 1`, `2·(a - b)² ≤ klBer a b`.
Proof (Cover–Thomas Lemma 11.6.1, two-point form): `f a = klBer a b - 2(a - b)²` has
derivative `g a = log(a/b) - log((1 - a)/(1 - b))` with `g b = 0` and
`g' a = 1/a + 1/(1 - a) > 0`, so `g < 0` on `(0, b)` and `g > 0` on `(b, 1)`: `f` is antitone
then monotone, with minimum `f b = 0`. -/
theorem two_mul_sq_le_klBer_of_pos_of_lt_one {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hb0 : 0 < b) (hb1 : b < 1) : 2 * (a - b) ^ 2 ≤ klBer a b := by
  -- ψ s = klBer s b − 2(s − b)² has derivative g s with g b = 0 and g' ≥ 0 on (0, 1)
  -- (since g' = 1/s + 1/(1-s) − 4 and s(1−s) ≤ 1/4), so ψ decreases on (0, b) and
  -- increases on (b, 1), with minimum ψ b = 0.
  set C : ℝ := Real.log (1 - b) - Real.log b with hC
  set ψ : ℝ → ℝ := fun s => klBer s b - 2 * (s - b) ^ 2 with hψ
  set g : ℝ → ℝ := fun s => Real.log s - Real.log (1 - s) + C - 4 * (s - b) with hg
  have hbne : (1 : ℝ) - b ≠ 0 := sub_ne_zero_of_ne (by linarith)
  -- Derivative of ψ is g at every point of (0, 1).
  have hψderiv : ∀ s, 0 < s → s < 1 → HasDerivAt ψ (g s) s := by
    intro s hs0 hs1
    have hsk : HasDerivAt (fun s => klBer s b)
        (Real.log (s / b) - Real.log ((1 - s) / (1 - b))) s :=
      hasDerivAt_klBer_fst hb0 hb1 hs0 hs1
    have hquad : HasDerivAt (fun s : ℝ => 2 * (s - b) ^ 2) (4 * (s - b)) s := by
      have h1 : HasDerivAt (fun s : ℝ => (s - b) ^ 2) (2 * (s - b)) s := by
        exact (((hasDerivAt_id s).sub_const b).pow 2).congr_deriv (by norm_num)
      have := h1.const_mul 2
      apply this.congr_deriv
      ring
    have hexp : Real.log (s / b) - Real.log ((1 - s) / (1 - b))
        = Real.log s - Real.log (1 - s) + C := by
      rw [hC, Real.log_div (ne_of_gt hs0) (ne_of_gt hb0),
        Real.log_div (show (1 : ℝ) - s ≠ 0 by linarith) hbne]
      ring
    rw [hψ]
    exact (hsk.sub hquad).congr_deriv (by rw [hexp])
  -- Derivative of g is `1/s + 1/(1-s) − 4 ≥ 0`: g is increasing on (0, 1).
  have hgderiv : ∀ s, 0 < s → s < 1 → HasDerivAt g (1 / s + 1 / (1 - s) - 4) s := by
    intro s hs0 hs1
    have hchain : HasDerivAt (fun s : ℝ => Real.log s - Real.log (1 - s) + C - 4 * (s - b))
        (1 / s + 1 / (1 - s) - 4) s := by
      have h1 : HasDerivAt (fun s : ℝ => Real.log s) (1 / s) s := by
        simpa using Real.hasDerivAt_log (ne_of_gt hs0)
      have h2 : HasDerivAt (fun s : ℝ => Real.log (1 - s)) (-(1 / (1 - s))) s := by
        simpa only [Function.comp_def, mul_neg, mul_one, one_div]
          using (Real.hasDerivAt_log (sub_ne_zero_of_ne (by linarith))).comp s
          ((hasDerivAt_id s).const_sub 1)
      have h4 : HasDerivAt (fun s : ℝ => 4 * (s - b)) 4 s := by
        simpa using ((hasDerivAt_id s).sub_const b).const_mul 4
      refine (((h1.sub h2).add (hasDerivAt_const s C)).sub h4).congr_deriv ?_
      ring
    rw [hg]
    exact hchain
  -- `g` is monotone on every compact subinterval of (0, 1).
  have hgmono : ∀ x y, 0 < x → x ≤ y → y < 1 → MonotoneOn g (Set.Icc x y) := by
    intro x y hx0 hxy hy1
    have hmem : ∀ s ∈ Set.Icc x y, 0 < s ∧ s < 1 := by
      intro s hs
      rw [Set.mem_Icc] at hs
      exact ⟨lt_of_lt_of_le hx0 hs.1, lt_of_le_of_lt hs.2 hy1⟩
    apply monotoneOn_of_deriv_nonneg (convex_Icc x y)
      (fun s hs => (hgderiv s (hmem s hs).1 (hmem s hs).2).continuousAt.continuousWithinAt)
      (fun s hs =>
        (hgderiv s (hmem s (interior_subset hs)).1
          (hmem s (interior_subset hs)).2).differentiableAt.differentiableWithinAt)
    intro s hs
    rw [interior_Icc, Set.mem_Ioo] at hs
    rw [(hgderiv s (lt_of_lt_of_le hx0 hs.1.le) (lt_of_le_of_lt hs.2.le hy1)).deriv]
    have hpos : (0 : ℝ) < s * (1 - s) := mul_pos (by linarith) (by linarith)
    have hbound : s * (1 - s) ≤ 1 / 4 := by nlinarith [sq_nonneg (s - 1 / 2)]
    have h4 : (4 : ℝ) * (s * (1 - s)) ≤ 1 := by
      simpa using mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 4)
    have h5 : (4 : ℝ) ≤ 1 / s + 1 / (1 - s) := by
      rw [div_add_div _ _ (ne_of_gt (by linarith : (0 : ℝ) < s))
        (ne_of_gt (by linarith : (0 : ℝ) < 1 - s)),
        le_div_iff₀ (mul_pos (by linarith) (by linarith))]
      simp only [one_mul, mul_one, sub_add_cancel]
      exact h4
    linarith
  have hgb : g b = 0 := by simp [hg, hC]
  have hψb : ψ b = 0 := by simp [hψ, klBer]
  rcases le_total b a with hba | hab
  · -- `a ≥ b`: ψ is monotone on `[b, a]`, so ψ b ≤ ψ a.
    have hmono : MonotoneOn ψ (Set.Icc b a) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc b a)
      · intro s hs
        exact (hψderiv s (lt_of_lt_of_le hb0 hs.1)
          (lt_of_le_of_lt hs.2 ha1)).continuousAt.continuousWithinAt
      · intro s hs
        have hs' : s ∈ Set.Icc b a := interior_subset hs
        exact (hψderiv s (lt_of_lt_of_le hb0 hs'.1)
          (lt_of_le_of_lt hs'.2 ha1)).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Icc, Set.mem_Ioo] at hs
        rw [(hψderiv s (lt_of_lt_of_le hb0 hs.1.le)
          (lt_of_le_of_lt hs.2.le ha1)).deriv]
        have hgs := hgmono b a hb0 hba ha1 (Set.mem_Icc.mpr ⟨le_rfl, hba⟩)
          (Set.mem_Icc.mpr ⟨hs.1.le, hs.2.le⟩) hs.1.le
        linarith [hgb, hgs]
    have hval := hmono (Set.mem_Icc.mpr ⟨le_rfl, hba⟩) (Set.mem_Icc.mpr ⟨hba, le_rfl⟩) hba
    rw [hψb] at hval
    simp only [hψ] at hval
    linarith
  · -- `a ≤ b`: ψ is antitone on `[a, b]` (g ≤ g b = 0 there), so ψ b ≤ ψ a.
    have hanti : AntitoneOn ψ (Set.Icc a b) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
      · intro s hs
        exact (hψderiv s (lt_of_lt_of_le ha0 hs.1)
          (lt_of_le_of_lt hs.2 hb1)).continuousAt.continuousWithinAt
      · intro s hs
        have hs' : s ∈ Set.Icc a b := interior_subset hs
        exact (hψderiv s (lt_of_lt_of_le ha0 hs'.1)
          (lt_of_le_of_lt hs'.2 hb1)).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Icc, Set.mem_Ioo] at hs
        rw [(hψderiv s (lt_of_lt_of_le ha0 hs.1.le)
          (lt_of_le_of_lt hs.2.le hb1)).deriv]
        have hgs := hgmono a b ha0 hab hb1 (Set.mem_Icc.mpr ⟨hs.1.le, hs.2.le⟩)
          (Set.mem_Icc.mpr ⟨hab, le_rfl⟩) hs.2.le
        linarith [hgb, hgs]
    have hval := hanti (Set.mem_Icc.mpr ⟨le_rfl, hab⟩) (Set.mem_Icc.mpr ⟨hab, le_rfl⟩) hab
    rw [hψb] at hval
    simp only [hψ] at hval
    linarith

/-- **Pinsker's inequality for the Bernoulli KL divergence.**
For `0 ≤ a ≤ 1` and `0 < b < 1`, `2·(a - b)² ≤ klBer a b`
(Cover–Thomas, *Elements of Information Theory*, Lemma 11.6.1, specialised to two points).
The endpoint cases `a = 0` and `a = 1` follow from `two_mul_sq_le_klBer_zero_left` and
`klBer_compl`. -/
theorem two_mul_sq_le_klBer {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 < b) (hb1 :
    b < 1) :
    2 * (a - b) ^ 2 ≤ klBer a b := by
  rcases eq_or_lt_of_le ha0 with rfl | hai
  · have h : 2 * (0 - b) ^ 2 ≤ klBer 0 b := by
      simpa using two_mul_sq_le_klBer_zero_left hb0 hb1
    exact h
  rcases le_iff_eq_or_lt.1 ha1 with rfl | hlt
  · -- `a = 1`: `klBer 1 b = klBer 0 (1 - b)` by `klBer_compl`.
    have hcompl : klBer 1 b = klBer 0 (1 - b) := by
      simpa using klBer_compl (a := 0) (b := 1 - b)
    have h := two_mul_sq_le_klBer_zero_left (by linarith : (0 : ℝ) < 1 - b)
      (by linarith : 1 - b < 1)
    rwa [← hcompl] at h
  · exact two_mul_sq_le_klBer_of_pos_of_lt_one hai hlt hb0 hb1

end Math.Concentration.BernoulliKL
