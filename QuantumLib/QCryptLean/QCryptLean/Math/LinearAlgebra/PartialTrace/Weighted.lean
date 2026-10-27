import Mathlib.Analysis.Matrix.Order
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Cyclic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Positivity
import QCryptLean.Math.SpectralTheory.Matrix

/-! # Weighted partial traces and compression of the discarded register -/
namespace Matrix
open scoped Kronecker
variable {X Y Z R : Type*}

/-- A rectangular sandwich on the discarded factor moves cyclically to the right. -/
theorem partialTraceLeft_kronecker_sandwich_cycle [CommSemiring R]
    [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq Y]
    (A : Matrix Z X R) (B : Matrix X Z R) (M : Matrix (X × Y) (X × Y) R) :
    partialTraceLeft ((A ⊗ₖ (1 : Matrix Y Y R)) * M * (B ⊗ₖ (1 : Matrix Y Y R))) =
      partialTraceLeft (M * ((B * A) ⊗ₖ (1 : Matrix Y Y R))) := by
  ext i j
  have hl : partialTraceLeft ((A ⊗ₖ (1 : Matrix Y Y R)) * M *
      (B ⊗ₖ (1 : Matrix Y Y R))) i j =
      (A * (of fun x y => M (x, i) (y, j)) * B).trace := by
    simp [partialTraceLeft, trace, diag, mul_apply, kroneckerMap_apply,
      Fintype.sum_prod_type, one_apply, apply_ite]
  have hr : partialTraceLeft (M * ((B * A) ⊗ₖ (1 : Matrix Y Y R))) i j =
      ((of fun x y => M (x, i) (y, j)) * (B * A)).trace := by
    simp [partialTraceLeft, trace, diag, mul_apply, kroneckerMap_apply,
      Fintype.sum_prod_type, one_apply, apply_ite]
  rw [hl, hr, trace_mul_cycle, trace_mul_comm]

noncomputable section
open scoped ComplexOrder MatrixOrder
variable [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

omit [DecidableEq X] in
/-- Multiplying a positive joint matrix by a positive weight on the discarded factor
has a positive marginal, even though the product need not itself be Hermitian. -/
theorem PosSemidef.partialTraceLeft_mul_kronecker {M : Matrix (X × Y) (X × Y) ℂ}
    {P : Matrix X X ℂ} (hM : M.PosSemidef) (hP : P.PosSemidef) :
    (Matrix.partialTraceLeft (M * (P ⊗ₖ (1 : Matrix Y Y ℂ)))).PosSemidef := by
  classical
  have hs : (CFC.sqrt P).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)
  have h := (hM.mul_mul_conjTranspose_same
    (CFC.sqrt P ⊗ₖ (1 : Matrix Y Y ℂ))).partialTraceLeft
  rw [conjTranspose_kronecker, conjTranspose_one, hs.isHermitian.eq,
    partialTraceLeft_kronecker_sandwich_cycle, CFC.sqrt_mul_sqrt_self P hP.nonneg] at h
  exact h

/-- Compressing a discarded register by a contraction decreases its marginal. -/
theorem PosSemidef.partialTraceLeft_compression_le [Fintype Z]
    {M : Matrix (X × Y) (X × Y) ℂ} (hM : M.PosSemidef)
    (V : Matrix X Z ℂ) (hV : (1 - V * Vᴴ).PosSemidef) :
    Matrix.partialTraceLeft ((Vᴴ ⊗ₖ (1 : Matrix Y Y ℂ)) * M *
      (V ⊗ₖ (1 : Matrix Y Y ℂ))) ≤ Matrix.partialTraceLeft M := by
  rw [Matrix.le_iff, partialTraceLeft_kronecker_sandwich_cycle]
  have h := hM.partialTraceLeft_mul_kronecker hV
  have he : (1 - V * Vᴴ) ⊗ₖ (1 : Matrix Y Y ℂ) =
      1 - (V * Vᴴ) ⊗ₖ (1 : Matrix Y Y ℂ) := by
    rw [← one_kronecker_one (α := ℂ)]
    ext p q
    simp only [kroneckerMap_apply, Matrix.sub_apply, sub_mul]
  rwa [he, Matrix.mul_sub, Matrix.mul_one, partialTraceLeft_sub] at h

end
end Matrix
