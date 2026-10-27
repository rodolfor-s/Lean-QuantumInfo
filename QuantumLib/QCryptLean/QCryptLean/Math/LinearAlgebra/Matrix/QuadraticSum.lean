import QCryptLean.Math.SpectralTheory.Matrix

/-! # A finite-sum Cauchy bound for positive matrix quadratic forms -/
namespace Matrix
open scoped ComplexOrder MatrixOrder
variable {X I : Type*} [Fintype X] [Fintype I]

/-- A positive quadratic form of a sum is bounded by the number of terms times their forms. -/
theorem PosSemidef.re_dotProduct_sum_le {A : Matrix X X ℂ} (hA : A.PosSemidef)
    (v : I → X → ℂ) :
    (star (∑ i, v i) ⬝ᵥ A *ᵥ (∑ i, v i)).re ≤
      (Fintype.card I : ℝ) * ∑ i, (star (v i) ⬝ᵥ A *ᵥ v i).re := by
  classical
  let S := CFC.sqrt A
  have hS : S.IsHermitian := (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hsq : S * S = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hq (x : X → ℂ) : (star x ⬝ᵥ A *ᵥ x).re = ∑ z, Complex.normSq ((S *ᵥ x) z) := by
    have he : star x ⬝ᵥ A *ᵥ x = star (S *ᵥ x) ⬝ᵥ S *ᵥ x := by
      rw [star_mulVec, hS.eq, ← dotProduct_mulVec, mulVec_mulVec, hsq]
    rw [he]
    simp only [dotProduct, Complex.re_sum, Pi.star_apply, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  have hc (f : I → ℂ) : Complex.normSq (∑ i, f i) ≤
      (Fintype.card I : ℝ) * ∑ i, Complex.normSq (f i) := by
    calc
      _ = ‖∑ i, f i‖ ^ 2 := Complex.normSq_eq_norm_sq _
      _ ≤ (∑ i, ‖f i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (∑ _ : I, (1 : ℝ) ^ 2) * ∑ i, ‖f i‖ ^ 2 := by
        simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : I => (1 : ℝ))
          (fun i => ‖f i‖)
      _ = _ := by simp [Complex.normSq_eq_norm_sq]
  simp_rw [hq]
  simp only [mulVec_sum, Finset.sum_apply]
  calc
    _ ≤ ∑ z : X, (Fintype.card I : ℝ) * ∑ i, Complex.normSq ((S *ᵥ v i) z) :=
      Finset.sum_le_sum fun z _ => hc (fun i => (S *ᵥ v i) z)
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

end Matrix
