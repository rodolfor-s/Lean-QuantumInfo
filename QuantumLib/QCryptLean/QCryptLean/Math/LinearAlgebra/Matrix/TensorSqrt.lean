import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.LinearAlgebra.PartialTrace.Sandwich
import QCryptLean.Math.SpectralTheory.Matrix

/-! # Positive square roots of local tensor factors

Only the local matrix star order is used; no matrix norm instance is selected.
-/
namespace Matrix
noncomputable section
open scoped ComplexOrder MatrixOrder Kronecker
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]

open Classical in
/-- Taking a positive square root commutes with adjoining an identity register. -/
theorem PosSemidef.sqrt_kronecker_one {A : Matrix X X ℂ} (hA : A.PosSemidef) :
    CFC.sqrt (A ⊗ₖ (1 : Matrix Y Y ℂ)) = CFC.sqrt A ⊗ₖ (1 : Matrix Y Y ℂ) := by
  classical
  have hS : (CFC.sqrt A ⊗ₖ (1 : Matrix Y Y ℂ)).PosSemidef :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).kronecker PosSemidef.one
  apply CFC.sqrt_unique
  · rw [← mul_kronecker_mul, CFC.sqrt_mul_sqrt_self A hA.nonneg, Matrix.one_mul]
  · exact hS.nonneg

open Classical in
/-- A local square-root filter preserves commutation with another matrix. -/
theorem PosSemidef.commute_sqrt_kronecker_one {A : Matrix X X ℂ} {B : Matrix (X × Y) (X × Y) ℂ}
    (hA : A.PosSemidef) (h : _root_.Commute (A ⊗ₖ (1 : Matrix Y Y ℂ)) B) :
    _root_.Commute (CFC.sqrt A ⊗ₖ (1 : Matrix Y Y ℂ)) B := by
  classical
  rw [← hA.sqrt_kronecker_one]
  exact h.cfcₙ_nnreal NNReal.sqrt

omit [Fintype X] [Fintype Y] [DecidableEq Y] in
open Classical in
/-- Positive square roots factor over dependent tensor families. -/
theorem PosSemidef.sqrt_piTensorProduct {I : Type*} {D : I → Type*}
    [Fintype I] [DecidableEq I] [∀ i, Fintype (D i)]
    (A : ∀ i, Matrix (D i) (D i) ℂ) (hA : ∀ i, (A i).PosSemidef) :
    CFC.sqrt (Matrix.piTensorProduct A) = Matrix.piTensorProduct (fun i => CFC.sqrt (A i)) := by
  classical
  apply CFC.sqrt_unique
  · rw [piTensorProduct_mul]
    exact congrArg Matrix.piTensorProduct (funext fun i => CFC.sqrt_mul_sqrt_self _ (hA i).nonneg)
  · exact (PosSemidef.piTensorProduct fun i =>
      nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (A i))).nonneg

end
end Matrix
