import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Sandwich
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.CovariantBound
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceNormFinite
import QCryptLean.Quantum.Operators.Basic

/-! # Classical records of finite conjugation averages

The record is an actual product factor; no enumeration is used.
-/
noncomputable section
namespace Quantum.Channels
open Matrix Quantum.Operators Quantum.Metrics
open scoped Kronecker ComplexOrder
variable {X Y R I : Type*} [Fintype X] [Fintype Y] [Fintype R] [Fintype I]
  [DecidableEq R] [DecidableEq I]

omit [Fintype X] [Fintype Y] [Fintype R] in
/-- Uniformly record a finite family of conjugations on the signal register. -/
def recordedConjugation (U : I → Op X) (A : Op (X × R)) : Op (X × (R × I)) :=
  reindex (Equiv.prodAssoc X R I) (Equiv.prodAssoc X R I)
    (blockDiagonal (fun i => (Fintype.card I : ℂ)⁻¹ •
      ((U i ⊗ₖ (1 : Op R)) * A * (U i ⊗ₖ (1 : Op R))ᴴ)))

omit [Fintype Y] in
/-- The recorded conjugation average preserves positivity. -/
theorem recordedConjugation_posSemidef (U : I → Op X) (A : Op (X × R))
    (hA : A.PosSemidef) : (recordedConjugation U A).PosSemidef := by
  apply (Matrix.posSemidef_blockDiagonal (fun i =>
    (hA.mul_mul_conjTranspose_same (U i ⊗ₖ (1 : Op R))).smul
      (inv_nonneg.mpr (by positivity)))).submatrix

omit [Fintype Y] in
/-- Forgetting the reference and record leaves the conjugation average of the marginal. -/
theorem partialTraceRight_recordedConjugation (U : I → Op X) (A : Op (X × R)) :
    partialTraceRight (recordedConjugation U A) = (Fintype.card I : ℂ)⁻¹ •
      ∑ i, U i * partialTraceRight A * (U i)ᴴ := by
  have he : partialTraceRight (recordedConjugation U A) = (Fintype.card I : ℂ)⁻¹ •
      ∑ i, partialTraceRight ((U i ⊗ₖ (1 : Op R)) * A * (U i ⊗ₖ (1 : Op R))ᴴ) := by
    ext x y
    simp only [partialTraceRight_apply, recordedConjugation, reindex_apply, submatrix_apply,
      Equiv.prodAssoc_symm_apply, blockDiagonal_apply, ite_true, Matrix.smul_apply,
      smul_eq_mul, Matrix.sum_apply, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [conjTranspose_kronecker, conjTranspose_one, partialTraceRight_kronecker_one_sandwich]

omit [Fintype Y] in
/-- Amplification acts separately on every recorded diagonal block. -/
theorem mapTensorId_recordedConjugation (Δ : Operation X Y) (U : I → Op X)
    (A : Op (X × R)) :
    mapTensorId Δ (R × I) (recordedConjugation U A) =
      reindex (Equiv.prodAssoc Y R I) (Equiv.prodAssoc Y R I)
        (blockDiagonal (fun i => mapTensorId Δ R ((Fintype.card I : ℂ)⁻¹ •
          ((U i ⊗ₖ (1 : Op R)) * A * (U i ⊗ₖ (1 : Op R))ᴴ)))) := by
  ext ⟨y, r, i⟩ ⟨z, s, j⟩
  let M (i : I) : Op (X × R) := (Fintype.card I : ℂ)⁻¹ •
    ((U i ⊗ₖ (1 : Op R)) * A * (U i ⊗ₖ (1 : Op R))ᴴ)
  change Δ (fun x w => if i = j then M i (x, r) (w, s) else 0) y z =
    if i = j then Δ (fun x w => M i (x, r) (w, s)) y z else 0
  split_ifs
  · rfl
  · exact congrFun (congrFun (map_zero Δ) y) z

/-- The output trace norm of a recorded average is the average of output trace norms. -/
theorem traceNorm_mapTensorId_recordedConjugation (Δ : Operation X Y) (U : I → Op X)
    (A : Op (X × R)) :
    traceNorm (mapTensorId Δ (R × I) (recordedConjugation U A)) =
      (Fintype.card I : ℝ)⁻¹ * ∑ i, traceNorm (mapTensorId Δ R
        ((U i ⊗ₖ (1 : Op R)) * A * (U i ⊗ₖ (1 : Op R))ᴴ)) := by
  rw [mapTensorId_recordedConjugation, traceNorm_reindex, traceNorm_blockDiagonal]
  simp only [map_smul, traceNorm_smul, norm_inv, Complex.norm_natCast, Finset.mul_sum]

end Quantum.Channels
