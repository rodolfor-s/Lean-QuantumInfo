import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Quadratic forms of orthogonal projections are `2`-Lipschitz on the unit ball

A self-adjoint idempotent continuous linear map `A` on a complex Hilbert space is a contraction,
and its quadratic form `x ↦ re ⟪x, A x⟫` is `2`-Lipschitz on the closed unit ball.  Both are
textbook facts; they are recorded here because the CKR band-mass argument needs the constant `2`
explicitly (a cruder entrywise bound loses several orders in the resulting sample-size threshold).

## Main statements

- `Math.ProjectionQuadraticForm.norm_apply_le`: `‖A z‖ ≤ ‖z‖`.
- `Math.ProjectionQuadraticForm.abs_re_inner_sub_le`: the `2`-Lipschitz bound.
-/

open RCLike ContinuousLinearMap

noncomputable section

namespace Math.ProjectionQuadraticForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- For a self-adjoint idempotent `A`, `⟪A z, A z⟫ = ⟪z, A z⟫`. -/
theorem inner_apply_apply (A : E →L[ℂ] E) (hsa : star A = A) (hidem : A * A = A) (z : E) :
    (inner ℂ (A z) (A z) : ℂ) = inner ℂ z (A z) := by
  have hadj : ContinuousLinearMap.adjoint A = A := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hsa
  have h := ContinuousLinearMap.adjoint_inner_right A z (A z)
  rw [hadj] at h
  rw [← h]
  congr 1
  have : A (A z) = (A * A) z := rfl
  rw [this, hidem]

/-- **A self-adjoint idempotent is a contraction.** -/
theorem norm_apply_le (A : E →L[ℂ] E) (hsa : star A = A) (hidem : A * A = A) (z : E) :
    ‖A z‖ ≤ ‖z‖ := by
  have hkey : ‖A z‖ ^ 2 = (inner ℂ z (A z) : ℂ).re := by
    rw [← inner_apply_apply A hsa hidem z]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) (A z)).symm
  have hcs : (inner ℂ z (A z) : ℂ).re ≤ ‖z‖ * ‖A z‖ := by
    refine le_trans (Complex.re_le_norm _) ?_
    exact norm_inner_le_norm (𝕜 := ℂ) z (A z)
  have hsq : ‖A z‖ ^ 2 ≤ ‖z‖ * ‖A z‖ := hkey ▸ hcs
  rcases eq_or_lt_of_le (norm_nonneg (A z)) with hz | hz
  · rw [← hz]; exact norm_nonneg z
  · nlinarith [hsq, hz]

/-- **The quadratic form of a self-adjoint idempotent is `2`-Lipschitz on the unit ball.** -/
theorem abs_re_inner_sub_le (A : E →L[ℂ] E) (hsa : star A = A) (hidem : A * A = A)
    {x y : E} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |(inner ℂ x (A x) : ℂ).re - (inner ℂ y (A y) : ℂ).re| ≤ 2 * ‖x - y‖ := by
  have hsplit : (inner ℂ x (A x) : ℂ) - inner ℂ y (A y)
      = inner ℂ (x - y) (A x) + inner ℂ y (A (x - y)) := by
    rw [map_sub, inner_sub_left, inner_sub_right]
    ring
  have hre : (inner ℂ x (A x) : ℂ).re - (inner ℂ y (A y) : ℂ).re
      = (inner ℂ (x - y) (A x) : ℂ).re + (inner ℂ y (A (x - y)) : ℂ).re := by
    rw [← Complex.sub_re, hsplit, Complex.add_re]
  rw [hre]
  refine le_trans (abs_add_le _ _) ?_
  have h1 : |(inner ℂ (x - y) (A x) : ℂ).re| ≤ ‖x - y‖ := by
    refine le_trans (Complex.abs_re_le_norm _) ?_
    refine le_trans (norm_inner_le_norm (𝕜 := ℂ) (x - y) (A x)) ?_
    have := norm_apply_le A hsa hidem x
    nlinarith [norm_nonneg (x - y), norm_nonneg (A x), norm_nonneg x]
  have h2 : |(inner ℂ y (A (x - y)) : ℂ).re| ≤ ‖x - y‖ := by
    refine le_trans (Complex.abs_re_le_norm _) ?_
    refine le_trans (norm_inner_le_norm (𝕜 := ℂ) y (A (x - y))) ?_
    have := norm_apply_le A hsa hidem (x - y)
    nlinarith [norm_nonneg y, norm_nonneg (A (x - y)), norm_nonneg (x - y)]
  linarith

end Math.ProjectionQuadraticForm

end
