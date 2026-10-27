import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Two-term AM–GM in square-root form, with a free weight

For nonnegative reals `a, b` the AM–GM inequality `2 √(a b) ≤ a + b` has a weighted form: for
every weight `ε > 0`,

  `2 √(a b) ≤ ε a + ε⁻¹ b`,

which is the unweighted inequality for `ε a` and `ε⁻¹ b` (equivalently, Mathlib's
`two_mul_le_add_mul_sq` at `√a` and `√b`). The bound is optimal. For `a, b > 0` the weight
`ε = √(b / a)` gives equality, so `2 √(a b)` is the least value of `ε a + ε⁻¹ b` over positive
weights. For `a, b ≥ 0` it is still the greatest lower bound, but when exactly one of `a, b`
vanishes that infimum `0` is not attained by any positive weight.

This is the scalar step of a weighted Young or Cauchy–Schwarz estimate: a quantity bounded by
`ε a + ε⁻¹ b` for every `ε > 0` is bounded by `2 √(a b)`.

## Main statements

- `Real.two_mul_sqrt_mul_le_add`: `2 √(u v) ≤ u + v` for `u, v ≥ 0`.
- `Real.sqrt_sub_mul_add_sqrt_mul_le`: superadditivity of the geometric mean,
  `√((α - u)(β - v)) + √(u v) ≤ √(α β)` for `0 ≤ u ≤ α`, `0 ≤ v ≤ β`.
- `Real.two_mul_sqrt_mul_le_mul_add_inv_mul`: the weighted form, for every `ε > 0`.
- `Real.sqrt_div_mul_add_inv_mul_eq`: equality at the weight `√(b / a)`.
- `Real.isLeast_mul_add_inv_mul`, `Real.isGLB_mul_add_inv_mul`: `2 √(a b)` is the least value of
  `ε a + ε⁻¹ b` over `ε > 0` when `a, b > 0`, and its infimum when `a, b ≥ 0`.
- `Real.exists_pos_mul_add_inv_mul_le_iff`, `Real.exists_pos_mul_add_inv_mul_lt_iff`: a positive
  weight brings `ε a + ε⁻¹ b` under a bound `S` exactly when `2 √(a b)` is under `S`; the
  non-strict form needs `a, b > 0`, the strict form holds for `a, b ≥ 0`.
-/

namespace Real

/-- **AM–GM for square roots**: for nonnegative reals `u, v`, `2 √(u v) ≤ u + v`. -/
lemma two_mul_sqrt_mul_le_add {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    2 * √(u * v) ≤ u + v := by
  have hsqd : 0 ≤ (√u - √v) ^ 2 := sq_nonneg _
  have hu_sq : √u ^ 2 = u := Real.sq_sqrt hu
  have hv_sq : √v ^ 2 = v := Real.sq_sqrt hv
  have hsm : √u * √v = √(u * v) := (Real.sqrt_mul hu _).symm
  nlinarith [hsqd, hu_sq, hv_sq, hsm]

/-- **Superadditivity of the geometric mean**: for `0 ≤ u ≤ α` and `0 ≤ v ≤ β`,
`√((α - u)(β - v)) + √(u v) ≤ √(α β)`. Splitting both factors of a geometric mean into two
nonnegative parts can only lower the sum of the partial geometric means; the cross term is
controlled by `two_mul_sqrt_mul_le_add`. -/
lemma sqrt_sub_mul_add_sqrt_mul_le
    {α β u v : ℝ} (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (huα : u ≤ α) (hvβ : v ≤ β) :
    √((α - u) * (β - v)) + √(u * v) ≤ √(α * β) := by
  have hαu : 0 ≤ α - u := by linarith
  have hβv : 0 ≤ β - v := by linarith
  apply Real.le_sqrt_of_sq_le
  have e1 : √((α - u) * (β - v)) ^ 2 = (α - u) * (β - v) :=
    Real.sq_sqrt (mul_nonneg hαu hβv)
  have e2 : √(u * v) ^ 2 = u * v := Real.sq_sqrt (mul_nonneg hu0 hv0)
  -- cross term: `2 √((α-u)(β-v)) √(uv) = 2 √(((α-u)v) (u(β-v))) ≤ (α-u)v + u(β-v)`
  have hxy : √((α - u) * (β - v)) * √(u * v) = √(((α - u) * v) * (u * (β - v))) := by
    rw [← Real.sqrt_mul (mul_nonneg hαu hβv)]
    ring_nf
  have hcross : 2 * (√((α - u) * (β - v)) * √(u * v)) ≤ (α - u) * v + u * (β - v) := by
    rw [hxy]
    exact two_mul_sqrt_mul_le_add (mul_nonneg hαu hv0) (mul_nonneg hu0 hβv)
  have hexpand : (√((α - u) * (β - v)) + √(u * v)) ^ 2 =
      (α - u) * (β - v) + u * v + 2 * (√((α - u) * (β - v)) * √(u * v)) := by
    rw [add_sq, e1, e2]
    ring
  rw [hexpand]
  nlinarith [hcross]

/-- **AM–GM with a free weight**: for `a, b ≥ 0` and every weight `ε > 0`,
`2 √(a b) ≤ ε a + ε⁻¹ b`. -/
lemma two_mul_sqrt_mul_le_mul_add_inv_mul {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 < ε) :
    2 * √(a * b) ≤ ε * a + ε⁻¹ * b := by
  have h := two_mul_sqrt_mul_le_add (mul_nonneg hε.le ha) (mul_nonneg (inv_nonneg.2 hε.le) hb)
  rwa [mul_mul_mul_comm, mul_inv_cancel₀ hε.ne', one_mul] at h

/-- `√(y / x) · x = √(x y)` for `x > 0`: the weight `√(y / x)` scales `x` to the geometric mean. -/
private lemma sqrt_div_mul_eq_sqrt_mul {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y) :
    √(y / x) * x = √(x * y) :=
  calc √(y / x) * x = √(y / x) * √(x * x) := by rw [Real.sqrt_mul_self hx.le]
    _ = √(y / x * (x * x)) := (Real.sqrt_mul (div_nonneg hy hx.le) _).symm
    _ = √(x * y) := by rw [← mul_assoc, div_mul_cancel₀ y hx.ne', mul_comm]

/-- **The optimal weight.** For `a, b > 0` the weight `ε = √(b / a)` makes both terms of the
weighted AM–GM bound equal to `√(a b)`, so the bound is attained:
`√(b / a) · a + (√(b / a))⁻¹ · b = 2 √(a b)`. -/
lemma sqrt_div_mul_add_inv_mul_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    √(b / a) * a + (√(b / a))⁻¹ * b = 2 * √(a * b) := by
  rw [← Real.sqrt_inv, inv_div, sqrt_div_mul_eq_sqrt_mul ha hb.le,
    sqrt_div_mul_eq_sqrt_mul hb ha.le, mul_comm b a, two_mul]

/-- For `a, b > 0`, `2 √(a b)` is the least value of `ε a + ε⁻¹ b` over positive weights `ε`,
attained at `ε = √(b / a)`. -/
theorem isLeast_mul_add_inv_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsLeast ((fun ε => ε * a + ε⁻¹ * b) '' Set.Ioi 0) (2 * √(a * b)) :=
  ⟨⟨√(b / a), Real.sqrt_pos.2 (div_pos hb ha), sqrt_div_mul_add_inv_mul_eq ha hb⟩,
    by
      rintro _ ⟨ε, hε, rfl⟩
      exact two_mul_sqrt_mul_le_mul_add_inv_mul ha.le hb.le hε⟩

/-- For `a, b ≥ 0`, `2 √(a b)` is the infimum of `ε a + ε⁻¹ b` over positive weights `ε`.
When exactly one of `a, b` vanishes this infimum `0` is not attained. -/
theorem isGLB_mul_add_inv_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IsGLB ((fun ε => ε * a + ε⁻¹ * b) '' Set.Ioi 0) (2 * √(a * b)) := by
  refine ⟨?_, fun L hL => ?_⟩
  · rintro _ ⟨ε, hε, rfl⟩
    exact two_mul_sqrt_mul_le_mul_add_inv_mul ha hb hε
  rcases ha.eq_or_lt with rfl | ha'
  · -- `a = 0`: the values `ε⁻¹ b` become arbitrarily small as `ε` grows.
    rw [zero_mul, Real.sqrt_zero, mul_zero]
    by_contra! hL0
    have h := hL ⟨(b + 1) / L, div_pos (by linarith) hL0, rfl⟩
    have hlt : ((b + 1) / L)⁻¹ * b < L := by
      rw [inv_div, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  rcases hb.eq_or_lt with rfl | hb'
  · -- `b = 0`: the values `ε a` become arbitrarily small as `ε` shrinks.
    rw [mul_zero, Real.sqrt_zero, mul_zero]
    by_contra! hL0
    have h := hL ⟨L / (a + 1), div_pos hL0 (by linarith), rfl⟩
    have hlt : L / (a + 1) * a + (L / (a + 1))⁻¹ * 0 < L := by
      rw [mul_zero, add_zero, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  exact hL (isLeast_mul_add_inv_mul ha' hb').1

/-- For `a, b > 0`, some positive weight brings `ε a + ε⁻¹ b` under `S` exactly when the
geometric mean `2 √(a b)` is under `S`. With `a = 0 < b` and `S = 0` the right side holds but
no positive weight satisfies the left, so the weakening to `a, b ≥ 0` is false. -/
theorem exists_pos_mul_add_inv_mul_le_iff {a b S : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∃ ε, 0 < ε ∧ ε * a + ε⁻¹ * b ≤ S) ↔ 2 * √(a * b) ≤ S :=
  ⟨fun ⟨_, hε, h⟩ => (two_mul_sqrt_mul_le_mul_add_inv_mul ha.le hb.le hε).trans h,
    fun h => ⟨√(b / a), Real.sqrt_pos.2 (div_pos hb ha),
      (sqrt_div_mul_add_inv_mul_eq ha hb).trans_le h⟩⟩

/-- For `a, b ≥ 0`, some positive weight brings `ε a + ε⁻¹ b` strictly under `S` exactly when
`2 √(a b) < S`. -/
theorem exists_pos_mul_add_inv_mul_lt_iff {a b S : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∃ ε, 0 < ε ∧ ε * a + ε⁻¹ * b < S) ↔ 2 * √(a * b) < S := by
  rw [isGLB_lt_iff (isGLB_mul_add_inv_mul ha hb), Set.exists_mem_image]
  rfl

end Real
