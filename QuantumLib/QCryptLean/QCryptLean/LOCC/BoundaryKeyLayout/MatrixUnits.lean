import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.BoundaryKeyLayout.Basic
import QCryptLean.LOCC.BoundaryKeyLayout.Hom

/-!
# Boundary key resources on matrix units

The ideal resource on diagonal matrix units and its naturality along injective
morphisms of boundary key layouts.
-/

open scoped Matrix BigOperators

noncomputable section

open Quantum.Operators (Op)

namespace LOCC.BoundaryKeyLayout

variable {P : Type} [Fintype P] [DecidableEq P]

/-- **The ideal key resource on a diagonal matrix unit.** At a complete exit `e`, the ideal sends
the rank-one projector onto the output with key coordinates `(a, b)` and retained coordinate `u`
to the uniform mixture, over the shared key `k`, of the projectors onto the output with key
coordinates `(k, k)` and the same retained coordinate. -/
theorem ideal_single_coordinates {B : Boundary P} (L : BoundaryKeyLayout B) (e : B.Exit)
    (a b : (L.disposition e).Key) (u : L.Residual e) :
    L.ideal (Matrix.single (⟨e, (L.coordinates e).symm (a, b, u)⟩ : B.space)
        ⟨e, (L.coordinates e).symm (a, b, u)⟩ (1 : ℂ)) =
      ((((Fintype.card (L.disposition e).Key : ℝ))⁻¹ : ℝ) : ℂ) •
        ∑ k, Matrix.single (⟨e, (L.coordinates e).symm (k, k, u)⟩ : B.space)
          ⟨e, (L.coordinates e).symm (k, k, u)⟩ (1 : ℂ) := by
  classical
  ext ⟨f, p⟩ ⟨g, q⟩
  by_cases hfg : f = g
  · subst hfg
    rcases hp : L.coordinates f p with ⟨a₁, b₁, u₁⟩
    rcases hq : L.coordinates f q with ⟨a₂, b₂, u₂⟩
    obtain rfl : p = (L.coordinates f).symm (a₁, b₁, u₁) := by
      rw [← hp, Equiv.symm_apply_apply]
    obtain rfl : q = (L.coordinates f).symm (a₂, b₂, u₂) := by
      rw [← hq, Equiv.symm_apply_apply]
    rw [L.ideal_coordinate_entry]
    by_cases hfe : f = e
    · subst hfe
      simp only [Matrix.single_apply, Matrix.smul_apply, Matrix.sum_apply, Sigma.mk.inj_iff,
        heq_eq_eq, true_and, Equiv.apply_eq_iff_eq, Prod.mk.injEq, smul_eq_mul]
      by_cases hk : a₁ = b₁ ∧ a₂ = b₂ ∧ a₁ = a₂
      · obtain ⟨rfl, rfl, rfl⟩ := hk
        rw [ite_eq_left ⟨rfl, rfl, rfl⟩]
        simp [Finset.sum_ite_eq, ite_and, eq_comm]
      · rw [ite_eq_right hk]
        symm
        refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k _ => ite_eq_right ?_)
        rintro ⟨⟨rfl, rfl, -⟩, ⟨h₂, h₂', -⟩⟩
        exact hk ⟨rfl, h₂.symm.trans h₂', h₂⟩
    · have hne : ∀ (r r' : (L.disposition e).Key × (L.disposition e).Key × L.Residual e)
          (s s' : (L.disposition f).Key × (L.disposition f).Key × L.Residual f),
          Matrix.single (⟨e, (L.coordinates e).symm r⟩ : B.space)
            ⟨e, (L.coordinates e).symm r'⟩ (1 : ℂ)
            (⟨f, (L.coordinates f).symm s⟩ : B.space)
            (⟨f, (L.coordinates f).symm s'⟩ : B.space) = 0 := by
        intro r r' s s'
        rw [Matrix.single_apply, ite_eq_right]
        rintro ⟨h, -⟩
        exact hfe (congrArg Sigma.fst h).symm
      simp only [hne, Finset.sum_const_zero, mul_zero, ite_self, Matrix.smul_apply,
        Matrix.sum_apply, smul_zero]
  · rw [L.ideal_crossExit_zero _ hfg]
    symm
    simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.single_apply]
    refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun k _ => ite_eq_right ?_)
    rintro ⟨h, h'⟩
    exact hfg ((congrArg Sigma.fst h).symm.trans (congrArg Sigma.fst h'))

namespace Hom

/-- **The ideal key resource transports diagonal matrix units along an injective morphism.** If
the source ideal sends the projector onto `x` to a weighted sum of projectors, the target ideal
sends the projector onto the image of `x` to the same weighted sum of the image projectors. -/
theorem ideal_single_of_injective {B₂ B₁ : Boundary P} {L₂ : BoundaryKeyLayout B₂}
    {L₁ : BoundaryKeyLayout B₁} (φ : Hom L₂ L₁) (hφ : Function.Injective φ)
    {ι : Type} [Fintype ι] (x : B₂.space) (c : ℂ) (y : ι → B₂.space)
    (h : L₂.ideal (Matrix.single x x (1 : ℂ)) =
      c • ∑ i, Matrix.single (y i) (y i) (1 : ℂ)) :
    L₁.ideal (Matrix.single (φ x) (φ x) (1 : ℂ)) =
      c • ∑ i, Matrix.single (φ (y i)) (φ (y i)) (1 : ℂ) := by
  classical
  have hM : ∀ z w, (z ∉ Set.range φ ∨ w ∉ Set.range φ) →
      Matrix.single (φ x) (φ x) (1 : ℂ) z w = 0 := by
    rintro z w (hz | hw)
    · rw [Matrix.single_apply, ite_eq_right]
      rintro ⟨rfl, -⟩
      exact hz ⟨x, rfl⟩
    · rw [Matrix.single_apply, ite_eq_right]
      rintro ⟨-, rfl⟩
      exact hw ⟨x, rfl⟩
  have hM' : ∀ z w, (z ∉ Set.range φ ∨ w ∉ Set.range φ) →
      (c • ∑ i, Matrix.single (φ (y i)) (φ (y i)) (1 : ℂ)) z w = 0 := by
    rintro z w hzw
    simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.single_apply]
    refine smul_eq_zero_of_right _ (Finset.sum_eq_zero fun i _ => ite_eq_right ?_)
    rintro ⟨rfl, rfl⟩
    rcases hzw with hz | hw
    · exact hz ⟨y i, rfl⟩
    · exact hw ⟨y i, rfl⟩
  rw [φ.ideal_eq_iff hM hM']
  have hsub : ∀ z : B₂.space,
      (Matrix.single (φ z) (φ z) (1 : ℂ)).submatrix φ φ = Matrix.single z z 1 := by
    intro z
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.single_apply, hφ.eq_iff]
  rw [hsub, h]
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.single_apply,
    hφ.eq_iff]

end Hom

end LOCC.BoundaryKeyLayout

end
