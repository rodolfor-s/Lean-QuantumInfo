import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.SpectralTheory.MatrixCFC

/-! # Real functional-calculus powers of dependent tensor families

The local matrix star order supplies positive functional calculus. No norm instance
is selected or exported.
-/
noncomputable section
namespace Matrix
open Unitary Math.SpectralTheory
open scoped ComplexOrder MatrixOrder
variable {I : Type*} {X : I → Type*} [Fintype I] [DecidableEq I]
  [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)]

open Classical in
/-- Real powers factor over positive dependent tensor families, including the empty family. -/
theorem PosSemidef.rpow_piTensorProduct (A : ∀ i, Matrix (X i) (X i) ℂ)
    (hA : ∀ i, (A i).PosSemidef) (r : ℝ) :
    (Matrix.piTensorProduct A) ^ r = Matrix.piTensorProduct (fun i => A i ^ r) := by
  classical
  let U (i : I) := (hA i).isHermitian.eigenvectorUnitary
  let V : unitaryGroup ((i : I) → X i) ℂ :=
    ⟨Matrix.piTensorProduct (fun i => (U i).val), mem_unitaryGroup_iff'.mpr (by
      rw [Matrix.star_eq_conjTranspose, conjTranspose_piTensorProduct, piTensorProduct_mul]
      simp only [← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self,
        piTensorProduct_one])⟩
  let d (x : (i : I) → X i) : ℝ := ∏ i, (hA i).isHermitian.eigenvalues (x i)
  have hd : Matrix.piTensorProduct (fun i => diagonal
      (fun x => ((hA i).isHermitian.eigenvalues x : ℂ))) =
        diagonal (fun x => (d x : ℂ)) := by
    rw [piTensorProduct_diagonal]
    congr 1
    funext x
    exact (Complex.ofReal_prod _ _).symm
  have he : Matrix.piTensorProduct A = conjStarAlgAut ℂ _ V (diagonal (fun x => (d x : ℂ))) := by
    rw [Unitary.conjStarAlgAut_apply]
    change Matrix.piTensorProduct A = Matrix.piTensorProduct (fun i => (U i).val) *
      diagonal (fun x => (d x : ℂ)) * (Matrix.piTensorProduct (fun i => (U i).val))ᴴ
    rw [← hd, conjTranspose_piTensorProduct, piTensorProduct_mul, piTensorProduct_mul]
    apply congrArg Matrix.piTensorProduct
    funext i
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using (hA i).isHermitian.spectral_theorem
  rw [CFC.rpow_eq_cfc_real (PosSemidef.piTensorProduct hA).nonneg,
    he, cfc_conjStarAlgAut _ (isHermitian_diagonal_ofReal d) V,
    cfc_diagonal_ofReal]
  have hd' : diagonal (fun x => ((d x ^ r : ℝ) : ℂ)) =
      Matrix.piTensorProduct (fun i => diagonal
        (fun x => (((hA i).isHermitian.eigenvalues x ^ r : ℝ) : ℂ))) := by
    rw [piTensorProduct_diagonal]
    congr 1
    funext x
    rw [show d x ^ r = ∏ i, (hA i).isHermitian.eigenvalues (x i) ^ r from
      (Real.finsetProd_rpow _ _ (fun i _ => (hA i).eigenvalues_nonneg (x i)) r).symm]
    exact Complex.ofReal_prod _ _
  rw [hd', Unitary.conjStarAlgAut_apply]
  change Matrix.piTensorProduct (fun i => (U i).val) * _ *
    (Matrix.piTensorProduct (fun i => (U i).val))ᴴ = _
  rw [conjTranspose_piTensorProduct, piTensorProduct_mul, piTensorProduct_mul]
  apply congrArg Matrix.piTensorProduct
  funext i
  exact ((hA i).cfcRpow_eq_conjStarAlgAut_diagonal r).symm

end Matrix
