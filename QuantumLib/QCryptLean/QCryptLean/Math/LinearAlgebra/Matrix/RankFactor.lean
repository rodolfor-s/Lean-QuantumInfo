import QCryptLean.Math.SpectralTheory.Matrix

/-!
# Positive matrix factors on a rank-bounded register

Only the positive-eigenvalue support is embedded into the requested environment.
The construction works for empty types and never enumerates a quantum register.
-/

noncomputable section
namespace Matrix
open scoped ComplexOrder
variable {X R : Type*} [Fintype X] [Fintype R]

open scoped Classical in
/-- A positive matrix has a rectangular Gram factor on every sufficiently large register. -/
theorem PosSemidef.exists_factor_of_rank_le {A : Matrix X X ℂ} (hA : A.PosSemidef)
    (h : A.rank ≤ Fintype.card R) : ∃ V : Matrix X R ℂ, V * Vᴴ = A := by
  classical
  let H := hA.isHermitian
  let U := H.eigenvectorUnitary
  let w : X → X → ℂ := fun i x => (Real.sqrt (H.eigenvalues i) : ℂ) * U.val x i
  have hfull : A = ∑ i, vecMulVec (w i) (star (w i)) := by
    conv_lhs => rw [H.spectral_theorem, Unitary.conjStarAlgAut_apply]
    ext x y
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.sum_apply,
      Matrix.star_apply, vecMulVec_apply, Pi.star_apply, Function.comp_apply,
      RCLike.ofReal_eq_complex_ofReal]
    apply Finset.sum_congr rfl
    intro i _
    have hs : (Real.sqrt (H.eigenvalues i) : ℂ) * (Real.sqrt (H.eigenvalues i) : ℂ) =
        (H.eigenvalues i : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hA.eigenvalues_nonneg i)]
    dsimp only [w, U]
    rw [star_mul, show star ((Real.sqrt (H.eigenvalues i) : ℝ) : ℂ) =
      ((Real.sqrt (H.eigenvalues i) : ℝ) : ℂ) from Complex.conj_ofReal _]
    calc
      _ = ((Real.sqrt (H.eigenvalues i) : ℂ) * (Real.sqrt (H.eigenvalues i) : ℂ)) *
          (H.eigenvectorUnitary.val x i * star (H.eigenvectorUnitary.val y i)) := by rw [hs]; ring
      _ = _ := by ring
  let S := {i : X // H.eigenvalues i ≠ 0}
  let B : Matrix X S ℂ := fun x i => w i.val x
  have hB : B * Bᴴ = A := by
    conv_rhs => rw [hfull]
    have hz (i : X) (hi : H.eigenvalues i = 0) : vecMulVec (w i) (star (w i)) = 0 := by
      ext x y
      simp [w, hi, vecMulVec_apply, Pi.star_apply]
    have hf : (∑ i : X, vecMulVec (w i) (star (w i))) =
        ∑ i ∈ Finset.univ.filter (fun i => H.eigenvalues i ≠ 0),
          vecMulVec (w i) (star (w i)) := by
      symm
      apply Finset.sum_filter_of_ne
      intro i _ hne hi
      exact hne (hz i hi)
    rw [hf, Finset.sum_subtype (p := fun i => H.eigenvalues i ≠ 0)
      (F := inferInstance) (Finset.univ.filter (fun i => H.eigenvalues i ≠ 0))
      (fun i => by simp) (fun i => vecMulVec (w i) (star (w i)))]
    ext x y
    simp only [Matrix.sum_apply, B, vecMulVec_apply, Pi.star_apply]
    rfl
  have hc : Fintype.card S ≤ Fintype.card R := by
    simpa only [H.rank_eq_card_non_zero_eigs] using h
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hc
  let J : Matrix R S ℂ := fun r i => if r = e i then 1 else 0
  have hJ : Jᴴ * J = 1 := by
    ext i j
    simp only [Matrix.mul_apply, conjTranspose_apply]
    simp [J, one_apply, apply_ite,
      e.injective.eq_iff, eq_comm]
  refine ⟨B * Jᴴ, ?_⟩
  rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc Jᴴ J, hJ, Matrix.one_mul, hB]

end Matrix
