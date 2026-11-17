import Mathlib.Basic.Complex.BigOperators

/-!
# Rank-one Gram rigidity

A sum of vector outer products with rank at most one has pairwise vanishing minors.
-/

open scoped BigOperators

noncomputable section

namespace Matrix

/-- **Rank-one Gram rigidity.**  If the outer-product sum of a finite family of vectors equals a
*single* outer product, then every `2×2` minor of the family vanishes:
`u x α * u y β = u y α * u x β` for all members `x, y` and all coordinates `α, β`.

This is the linear-algebra core of the obstruction and has no quantum content.  The proof is the
`2×2` minor identity `∑_{z,w} |u z α · u w β − u w α · u z β|² = 2·(M α α · M β β − M α β · M β α)`
for `M = ∑ₓ uₓ uₓᴴ`, whose right-hand side vanishes when `M` is a single outer product. -/
theorem outerSum_eq_outer_minor {κ ι : Type*} [Fintype κ]
    (u : κ → ι → ℂ) (v : ι → ℂ)
    (h : ∀ α γ : ι, ∑ x, u x α * star (u x γ) = v α * star (v γ)) :
    ∀ (x y : κ) (α β : ι), u x α * u y β = u y α * u x β := by
  intro x y α β
  set P : κ → κ → ℂ := fun z w => u z α * u w β - u w α * u z β with hP
  -- The `2×2` minor identity, termwise.
  have hexp : ∀ z w : κ, P z w * star (P z w)
      = (u z α * star (u z α)) * (u w β * star (u w β))
        + (u w α * star (u w α)) * (u z β * star (u z β))
        - (u z α * star (u z β)) * (u w β * star (u w α))
        - (u w α * star (u w β)) * (u z β * star (u z α)) := by
    intro z w
    simp only [hP, star_sub, star_mul']
    ring
  -- Summing the identity over the second index and using `h` on the inner sums.
  have hinner : ∀ z : κ, ∑ w : κ, P z w * star (P z w)
      = (u z α * star (u z α)) * (v β * star (v β))
        + (v α * star (v α)) * (u z β * star (u z β))
        - (u z α * star (u z β)) * (v β * star (v α))
        - (v α * star (v β)) * (u z β * star (u z α)) := by
    intro z
    simp_rw [hexp]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul,
      h α α, h β β, h α β, h β α]
  -- Summing over the first index and using `h` again makes the whole double sum vanish.
  have hsum0 : ∑ z : κ, ∑ w : κ, P z w * star (P z w) = 0 := by
    simp_rw [hinner]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum,
      h α α, h β β, h α β, h β α]
    ring
  -- A vanishing sum of squared norms has vanishing terms.
  have hcast : ∑ z : κ, ∑ w : κ, ((Complex.normSq (P z w) : ℝ) : ℂ) = 0 := by
    rw [← hsum0]
    simp only [Complex.star_def, Complex.mul_conj]
  have hreal : ∑ z : κ, ∑ w : κ, Complex.normSq (P z w) = 0 := by exact_mod_cast hcast
  have hz : ∑ w : κ, Complex.normSq (P x w) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun z _ => Finset.sum_nonneg fun w _ => Complex.normSq_nonneg _)).1 hreal x
      (Finset.mem_univ x)
  have hzw : Complex.normSq (P x y) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => Complex.normSq_nonneg _)).1 hz y
      (Finset.mem_univ y)
  have hPxy : P x y = 0 := Complex.normSq_eq_zero.1 hzw
  exact sub_eq_zero.1 hPxy

end Matrix
