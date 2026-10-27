import QCryptLean.Math.LinearAlgebra.Matrix.EntryIntegral
import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Weighted

/-! # Weighted right marginals and rank-one sandwiches -/
namespace Matrix
open scoped Kronecker
variable {X Y R : Type*} [Fintype X] [Fintype Y]

/-- A weight on the discarded right register moves cyclically through partial trace. -/
theorem partialTraceRight_one_kronecker_mul_cycle [CommSemiring R] [DecidableEq X]
    (P : Matrix Y Y R) (M : Matrix (X × Y) (X × Y) R) :
    partialTraceRight (((1 : Matrix X X R) ⊗ₖ P) * M) =
      partialTraceRight (M * ((1 : Matrix X X R) ⊗ₖ P)) := by
  ext i j
  simp only [partialTraceRight_apply, mul_apply, Fintype.sum_prod_type,
    kroneckerMap_apply, one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, mul_ite, mul_zero, Finset.sum_ite_eq']
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact mul_comm _ _

open scoped ComplexOrder in
/-- A positive weight on the discarded right register gives a positive marginal. -/
theorem PosSemidef.partialTraceRight_one_kronecker_mul [DecidableEq X]
    {M : Matrix (X × Y) (X × Y) ℂ} {P : Matrix Y Y ℂ}
    (hM : M.PosSemidef) (hP : P.PosSemidef) :
    (Matrix.partialTraceRight (((1 : Matrix X X ℂ) ⊗ₖ P) * M)).PosSemidef := by
  classical
  rw [partialTraceRight_one_kronecker_mul_cycle]
  have h := (hM.submatrix Prod.swap).partialTraceLeft_mul_kronecker hP
  have he : Matrix.reindex (Equiv.prodComm X Y) (Equiv.prodComm X Y)
      (M * ((1 : Matrix X X ℂ) ⊗ₖ P)) =
      M.submatrix Prod.swap Prod.swap * (P ⊗ₖ (1 : Matrix X X ℂ)) := by
    have he := (reindexAlgEquiv ℂ ℂ (Equiv.prodComm X Y)).map_mul
      M ((1 : Matrix X X ℂ) ⊗ₖ P)
    change Matrix.reindex _ _ _ = Matrix.reindex _ _ _ * Matrix.reindex _ _ _ at he
    rw [he, reindex_prodComm_kronecker]
    rfl
  change (Matrix.partialTraceLeft (Matrix.reindex (Equiv.prodComm X Y) (Equiv.prodComm X Y)
    (M * ((1 : Matrix X X ℂ) ⊗ₖ P)))).PosSemidef
  rw [he]
  exact h

omit [Fintype Y] in
/-- Sandwiching by a rank-one matrix reduces to a scalar trace product. -/
theorem vecMulVec_sandwich_eq_trace_smul [CommSemiring R]
    (u v : X → R) (M : Matrix X X R) :
    vecMulVec u v * M * vecMulVec u v =
      (vecMulVec u v * M).trace • vecMulVec u v := by
  rw [vecMulVec_mul, trace_vecMulVec, vecMulVec_mul_vecMulVec]
  ext i j
  simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [dotProduct_comm u]
  ring

omit [Fintype X] in
open MeasureTheory in
/-- A right marginal commutes with entrywise integration. -/
theorem partialTraceRight_entryIntegral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {M : Ω → Matrix (X × Y) (X × Y) ℂ}
    (hint : ∀ i j, Integrable (fun ω => M ω i j) μ) :
    partialTraceRight (of fun i j => ∫ ω, M ω i j ∂μ) =
      of fun i j => ∫ ω, partialTraceRight (M ω) i j ∂μ := by
  ext i j
  exact (integral_finsetSum _ (fun y _ => hint (i,y) (j,y))).symm

end Matrix
