import QCryptLean.Math.Analysis.AMGM

/-! # Bhattacharyya -/


namespace Real

/-- Bhattacharyya-type inequality: for `a, b ∈ [0, 1]`,
    `√(a · b) + √((1 - a) · (1 - b)) ≤ 1`. -/
lemma sqrt_mul_add_sqrt_one_sub_mul_one_sub_le_one
    {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    Real.sqrt (a * b) + Real.sqrt ((1 - a) * (1 - b)) ≤ 1 := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  have h1a : 0 ≤ 1 - a := sub_nonneg.mpr ha1
  have h1b : 0 ≤ 1 - b := sub_nonneg.mpr hb1
  have hab : 0 ≤ a * b := mul_nonneg ha0 hb0
  have h1a1b : 0 ≤ (1 - a) * (1 - b) := mul_nonneg h1a h1b
  set x := Real.sqrt (a * b) with hx_def
  set y := Real.sqrt ((1 - a) * (1 - b)) with hy_def
  have hx : 0 ≤ x := Real.sqrt_nonneg _
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = a * b := by
    rw [hx_def, sq]; exact Real.mul_self_sqrt hab
  have hy2 : y ^ 2 = (1 - a) * (1 - b) := by
    rw [hy_def, sq]; exact Real.mul_self_sqrt h1a1b
  -- AM–GM applied to u = a(1-b), v = b(1-a).
  set u := a * (1 - b) with hu_def
  set v := b * (1 - a) with hv_def
  have hu : 0 ≤ u := mul_nonneg ha0 h1b
  have hv : 0 ≤ v := mul_nonneg hb0 h1a
  have key : 2 * Real.sqrt (u * v) ≤ u + v := two_mul_sqrt_mul_le_add hu hv
  have huv_eq : u * v = (a * b) * ((1 - a) * (1 - b)) := by
    simp only [hu_def, hv_def]; ring
  have hxy : x * y = Real.sqrt (u * v) := by
    rw [hx_def, hy_def, huv_eq]
    exact (Real.sqrt_mul hab _).symm
  have hsq : (x + y) ^ 2 ≤ 1 := by
    have hexpand : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * (x * y) := by ring
    rw [hexpand, hx2, hy2, hxy]
    have huv_sum : u + v = a + b - 2 * a * b := by
      simp only [hu_def, hv_def]; ring
    -- `ab + (1 - a)(1 - b) + (u + v) = 1`, and `2√(uv) ≤ u + v`.
    have hone : a * b + (1 - a) * (1 - b) + (a + b - 2 * a * b) = 1 := by ring
    linarith only [key, huv_sum, hone]
  exact (sq_le_one_iff₀ (add_nonneg hx hy)).mp hsq

/-- **Tensor-product complement bound** (AM-GM consequence used by the
    fidelity super-multiplicativity proof).

    For `p, q, p', q' ∈ [0, 1]`,
    `√(p·q·(1-p')·(1-q')) + √((1-p)·(1-q)) ≤ √((1 - p·p')·(1 - q·q'))`.

    Proof: square both sides, expand `(1 - p·p')(1 - q·q')` via the identity
    `(1 - p·p')(1 - q·q') = (1-p)(1-q) + p·q·(1-p')(1-q') + p·(1-p')(1-q) + q·(1-p)(1-q')`,
    and apply AM-GM `2·√(α·β) ≤ α + β` to `α := p·(1-p')(1-q)` and
    `β := q·(1-p)(1-q')` whose product equals the inner sqrt argument. -/
lemma sqrt_mul_add_sqrt_le_sqrt_mul
    {p q p' q' : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hp' : p' ∈ Set.Icc (0 : ℝ) 1) (hq' : q' ∈ Set.Icc (0 : ℝ) 1) :
    Real.sqrt (p * q * (1 - p') * (1 - q')) + Real.sqrt ((1 - p) * (1 - q)) ≤
      Real.sqrt ((1 - p * p') * (1 - q * q')) := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hq0, hq1⟩ := hq
  obtain ⟨hp'0, hp'1⟩ := hp'
  obtain ⟨hq'0, hq'1⟩ := hq'
  have h1p : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have h1q : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have h1p' : 0 ≤ 1 - p' := sub_nonneg.mpr hp'1
  have h1q' : 0 ≤ 1 - q' := sub_nonneg.mpr hq'1
  have hpp'_le : p * p' ≤ 1 := (mul_le_of_le_one_left hp'0 hp1).trans hp'1
  have hqq'_le : q * q' ≤ 1 := (mul_le_of_le_one_left hq'0 hq1).trans hq'1
  have h1pp' : 0 ≤ 1 - p * p' := sub_nonneg.mpr hpp'_le
  have h1qq' : 0 ≤ 1 - q * q' := sub_nonneg.mpr hqq'_le
  have h_prod_nn : 0 ≤ (1 - p * p') * (1 - q * q') := mul_nonneg h1pp' h1qq'
  set u := Real.sqrt (p * q * (1 - p') * (1 - q')) with hu_def
  set v := Real.sqrt ((1 - p) * (1 - q)) with hv_def
  have hu_nn : 0 ≤ u := Real.sqrt_nonneg _
  have hv_nn : 0 ≤ v := Real.sqrt_nonneg _
  have huv_nn : 0 ≤ u + v := add_nonneg hu_nn hv_nn
  have h_u_arg_nn : 0 ≤ p * q * (1 - p') * (1 - q') := by positivity
  have h_v_arg_nn : 0 ≤ (1 - p) * (1 - q) := by positivity
  have hu_sq : u ^ 2 = p * q * (1 - p') * (1 - q') := by
    rw [hu_def, sq]; exact Real.mul_self_sqrt h_u_arg_nn
  have hv_sq : v ^ 2 = (1 - p) * (1 - q) := by
    rw [hv_def, sq]; exact Real.mul_self_sqrt h_v_arg_nn
  -- `u * v = √(p·q·(1-p)·(1-q)·(1-p')·(1-q'))`.
  have h_uv_eq : u * v = Real.sqrt (p * q * (1 - p) * (1 - q) * (1 - p') * (1 - q')) := by
    rw [hu_def, hv_def, ← Real.sqrt_mul h_u_arg_nn]
    congr 1; ring
  -- AM-GM with `α := p·(1-p')·(1-q)`, `β := q·(1-p)·(1-q')`.
  have hα_nn : 0 ≤ p * (1 - p') * (1 - q) := by positivity
  have hβ_nn : 0 ≤ q * (1 - p) * (1 - q') := by positivity
  have hAB := Real.two_mul_sqrt_mul_le_add hα_nn hβ_nn
  -- The inner sqrt argument collapses to the same one as in `h_uv_eq`.
  have hsqrt_collapse :
      Real.sqrt (p * (1 - p') * (1 - q) * (q * (1 - p) * (1 - q'))) =
        Real.sqrt (p * q * (1 - p) * (1 - q) * (1 - p') * (1 - q')) := by
    congr 1; ring
  -- Tensor-complement factorization identity.
  have hfactor : (1 - p * p') * (1 - q * q') =
      (1 - p) * (1 - q) + p * q * (1 - p') * (1 - q')
        + (p * (1 - p') * (1 - q) + q * (1 - p) * (1 - q')) := by ring
  -- `(u + v)² ≤ (1 - p·p')(1 - q·q')`.
  have h_sq : (u + v) ^ 2 ≤ (1 - p * p') * (1 - q * q') := by
    have hexpand : (u + v) ^ 2 = u ^ 2 + v ^ 2 + 2 * (u * v) := by ring
    rw [hexpand, hu_sq, hv_sq, h_uv_eq, ← hsqrt_collapse, hfactor]
    linarith [hAB]
  have h_step := Real.sqrt_le_sqrt h_sq
  rwa [Real.sqrt_sq huv_nn] at h_step

/-- Coordinate form of the Bhattacharyya inversion used for purified-distance
weight floors.

The variables are first-quadrant coordinates on two unit circles, with
`(c,s)` representing the purified-distance radius and `(a,b)`, `(x,y)` the two
weights.  If the Bhattacharyya overlap is at least `c` and `s^2 < a^2`, then
the second weight coordinate is above the squared threshold. -/
lemma bhattacharyya_floor_sq_le_sq_of_coord
    {a b c s x y : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hab : a ^ 2 + b ^ 2 = 1)
    (hcs : c ^ 2 + s ^ 2 = 1)
    (hxy : x ^ 2 + y ^ 2 = 1)
    (hs_lt_a : s ^ 2 < a ^ 2)
    (hB : c ≤ a * x + b * y) :
    (a * c - b * s) ^ 2 ≤ x ^ 2 := by
  have ha_sq_le_one : a ^ 2 ≤ 1 := by
    linarith only [sq_nonneg b, hab]
  have hbs_sq_lt_ac_sq : (b * s) ^ 2 < (a * c) ^ 2 := by
    -- `(ac)² - (bs)² = a²(1 - s²) - (1 - a²)s² = a² - s² > 0`.
    have hdiff : (a * c) ^ 2 - (b * s) ^ 2 = a ^ 2 - s ^ 2 := by
      linear_combination a ^ 2 * hcs - s ^ 2 * hab
    linarith only [hdiff, hs_lt_a]
  have ht_pos : 0 < a * c - b * s := by
    have hbs_lt_ac : b * s < a * c :=
      (sq_lt_sq₀ (mul_nonneg hb hs) (mul_nonneg ha hc)).mp hbs_sq_lt_ac_sq
    exact sub_pos.mpr hbs_lt_ac
  have ht_nonneg : 0 ≤ a * c - b * s := le_of_lt ht_pos
  have htx : a * c - b * s ≤ x := by
    by_contra hnot
    push Not at hnot
    have hx_lt_t : x < a * c - b * s := hnot
    have hbs_nonneg : 0 ≤ b * s := mul_nonneg hb hs
    have hx_lt_ac : x < a * c := by
      linarith only [hx_lt_t, hbs_nonneg]
    have hax_le_c : a * x ≤ c :=
      calc a * x ≤ a * (a * c) := mul_le_mul_of_nonneg_left (le_of_lt hx_lt_ac) ha
        _ = a ^ 2 * c := by ring
        _ ≤ c := mul_le_of_le_one_left hc ha_sq_le_one
    have hc_sub_ax_nonneg : 0 ≤ c - a * x := sub_nonneg.mpr hax_le_c
    -- On the three unit circles, `(c - ax)² - (by)²` factors through `x ∓ (ac ± bs)`.
    have hfactor :
        (c - a * x) ^ 2 - (b * y) ^ 2 =
          (x - (a * c - b * s)) * (x - (a * c + b * s)) := by
      linear_combination (s ^ 2 - y ^ 2) * hab + (1 - a ^ 2) * hcs - (1 - a ^ 2) * hxy
    have hleft_neg : x - (a * c - b * s) < 0 := sub_neg.mpr hx_lt_t
    have hright_neg : x - (a * c + b * s) < 0 := by
      linarith only [hx_lt_t, hbs_nonneg]
    have hdiff_pos : 0 < (c - a * x) ^ 2 - (b * y) ^ 2 := by
      rw [hfactor]
      exact mul_pos_of_neg_of_neg hleft_neg hright_neg
    have hby_sq_lt : (b * y) ^ 2 < (c - a * x) ^ 2 := by
      linarith only [hdiff_pos]
    have hby_nonneg : 0 ≤ b * y := mul_nonneg hb hy
    have hby_lt : b * y < c - a * x :=
      (sq_lt_sq₀ hby_nonneg hc_sub_ax_nonneg).mp hby_sq_lt
    have : a * x + b * y < c := by
      linarith only [hby_lt]
    linarith only [hB, this]
  exact (sq_le_sq₀ ht_nonneg hx).mpr htx

/-- The Bhattacharyya scalar bound behind the purified-distance contraction: for base
overlap `F` bounded by the geometric mean of the block weights `a, b`, and ancilla weight
`t`, the generalized fidelity does not decrease when both weights are scaled by `t` and the
overlap by `t`.  Reduces to `Real.sqrt_mul_add_sqrt_one_sub_mul_one_sub_le_one`. -/
theorem add_sqrt_le_scale_add_sqrt
    {a b t F : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hF_nn : 0 ≤ F) (hF_le : F ≤ Real.sqrt (a * b)) :
    F + Real.sqrt ((1 - a) * (1 - b)) ≤
      t * F + Real.sqrt ((1 - a * t) * (1 - b * t)) := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  obtain ⟨ht0, ht1⟩ := ht
  have hbha : Real.sqrt (a * b) + Real.sqrt ((1 - a) * (1 - b)) ≤ 1 :=
    Real.sqrt_mul_add_sqrt_one_sub_mul_one_sub_le_one ⟨ha0, ha1⟩ ⟨hb0, hb1⟩
  set u := Real.sqrt ((1 - a) * (1 - b)) with hu_def
  set w := Real.sqrt (a * b) with hw_def
  have hu_nn : 0 ≤ u := Real.sqrt_nonneg _
  have hw_nn : 0 ≤ w := hF_nn.trans hF_le
  have hu2 : u ^ 2 = (1 - a) * (1 - b) := by
    rw [hu_def, sq]; exact Real.mul_self_sqrt (mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1))
  have hw2 : w ^ 2 = a * b := by
    rw [hw_def, sq]; exact Real.mul_self_sqrt (mul_nonneg ha0 hb0)
  have huw1 : u + w ≤ 1 := by linarith only [hbha]
  have hstar : u + (1 - t) * w ≤ Real.sqrt ((1 - a * t) * (1 - b * t)) := by
    have hlhs_nn : 0 ≤ u + (1 - t) * w := add_nonneg hu_nn (mul_nonneg (sub_nonneg.mpr ht1) hw_nn)
    -- `1 - t ≥ 0`, and `(u + w)² ≤ 1` since `0 ≤ u + w ≤ 1`
    have hprod : 0 ≤ (1 - t) * (1 - (u + w) ^ 2) :=
      mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr (pow_le_one₀ (add_nonneg hu_nn hw_nn) huw1))
    have hident : (1 - a * t) * (1 - b * t) - (u + (1 - t) * w) ^ 2
        = (1 - t) * (1 - (u + w) ^ 2) := by
      linear_combination (-t) * hu2 + (t * (1 - t)) * hw2
    have hsq_le : (u + (1 - t) * w) ^ 2 ≤ (1 - a * t) * (1 - b * t) := by
      linarith only [hident, hprod]
    calc u + (1 - t) * w
        = Real.sqrt ((u + (1 - t) * w) ^ 2) := (Real.sqrt_sq hlhs_nn).symm
      _ ≤ Real.sqrt ((1 - a * t) * (1 - b * t)) := Real.sqrt_le_sqrt hsq_le
  have hwF : (1 - t) * F ≤ (1 - t) * w := mul_le_mul_of_nonneg_left hF_le (sub_nonneg.mpr ht1)
  linarith only [hstar, hwF]

end Real
