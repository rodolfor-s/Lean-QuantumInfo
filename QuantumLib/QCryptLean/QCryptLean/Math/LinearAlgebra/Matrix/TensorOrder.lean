import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct

/-! # Order monotonicity of dependent tensor families

The star order is scoped locally. Expanding a finite product of positive sums
also covers the empty tensor family and empty component registers.
-/
namespace Matrix
open scoped ComplexOrder MatrixOrder
variable {I : Type*} [Fintype I] {X : I → Type*} [∀ i, Finite (X i)]

/-- Dependent tensor products preserve order between positive matrix families. -/
theorem piTensorProduct_mono {A B : ∀ i, Matrix (X i) (X i) ℂ}
    (hA : ∀ i, (A i).PosSemidef) (h : ∀ i, A i ≤ B i) :
    piTensorProduct A ≤ piTensorProduct B := by
  classical
  let F : (i : I) → Bool → Matrix (X i) (X i) ℂ :=
    fun i b => if b then B i - A i else A i
  have hF (i : I) (b : Bool) : (F i b).PosSemidef := by
    cases b
    · exact hA i
    · exact Matrix.le_iff.mp (h i)
  have he : piTensorProduct B = ∑ b : I → Bool, piTensorProduct (fun i => F i (b i)) := by
    ext x y
    simp only [piTensorProduct_apply, Matrix.sum_apply]
    rw [← Fintype.prod_sum (fun (i : I) (b : Bool) => F i b (x i) (y i))]
    apply Finset.prod_congr rfl
    intro i _
    simp [F, Matrix.sub_apply]
  have hz : piTensorProduct (fun i => F i ((fun _ : I => false) i)) =
      piTensorProduct A := by simp [F]
  rw [he, Matrix.le_iff]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (fun _ : I => false)), hz,
    add_sub_cancel_left]
  exact posSemidef_sum _ (fun b _ => PosSemidef.piTensorProduct (fun i => hF i (b i)))

open scoped Kronecker

/-- Tensor products preserve order between positive matrices. -/
theorem kronecker_mono {X Y 𝕜 : Type*} [RCLike 𝕜] [Finite X] [Finite Y]
    {A B : Matrix X X 𝕜} {C D : Matrix Y Y 𝕜}
    (hA : A.PosSemidef) (hC : C.PosSemidef) (hAB : A ≤ B) (hCD : C ≤ D) :
    A ⊗ₖ C ≤ B ⊗ₖ D := by
  have hd := Matrix.le_iff.mp hAB
  have hD : D.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (hC.nonneg.trans hCD)
  apply Matrix.le_iff.mpr
  have h := (hd.kronecker hD).add (hA.kronecker (Matrix.le_iff.mp hCD))
  convert h using 1
  ext i j
  change B i.1 j.1 * D i.2 j.2 - A i.1 j.1 * C i.2 j.2 =
    (B i.1 j.1 - A i.1 j.1) * D i.2 j.2 + A i.1 j.1 * (D i.2 j.2 - C i.2 j.2)
  ring

end Matrix
