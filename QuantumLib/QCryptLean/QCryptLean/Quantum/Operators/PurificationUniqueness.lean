import QCryptLean.Math.LinearAlgebra.Matrix.UnitaryGram
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification

/-!
# Native purification uniqueness on arbitrary reference types

Reshaping a ket is simply evaluating it at a pair. Equal marginals are equal row
Gram matrices. The reference map is the transpose of the native right-coisometry
factor, not its adjoint. No normalization hypothesis is needed.
-/

noncomputable section

namespace Quantum.Operators

open Matrix
open scoped Kronecker

variable {X R S : Type*} [Fintype X] [Fintype R] [Fintype S]

open scoped Classical in
/-- Two equal-marginal vectors differ by an isometry on a sufficiently large reference. -/
theorem Ket.exists_reference_isometry_of_partialTraceRight_eq
    (v : Ket (X × R)) (w : Ket (X × S))
    (h : partialTraceRight v.projector = partialTraceRight w.projector)
    (hdim : Fintype.card R ≤ Fintype.card S) :
    ∃ V : Matrix S R ℂ, Vᴴ * V = 1 ∧ w = ((1 : Op X) ⊗ₖ V) * v := by
  classical
  let M : Matrix X R ℂ := fun x r => v.vec (x, r)
  let N : Matrix X S ℂ := fun x s => w.vec (x, s)
  have hg : M * Mᴴ = N * Nᴴ := by
    rw [← Ket.partialTraceRight_vectorize, ← Ket.partialTraceRight_vectorize]
    exact h
  obtain ⟨W, hW, hN⟩ := Matrix.exists_coisometry_of_rowGram_eq M N hg hdim
  refine ⟨Wᵀ, ?_, ?_⟩
  · have he : (Wᵀ)ᴴ * Wᵀ = (W * Wᴴ)ᵀ := by rw [transpose_mul]; rfl
    rw [he, hW, transpose_one]
  · ext p
    have he := congrFun (congrFun hN p.1) p.2
    rw [Matrix.mul_apply] at he
    change w.vec p = (((1 : Op X) ⊗ₖ Wᵀ) *ᵥ v.vec) p
    simpa [M, N, Matrix.mul_apply, mulVec, dotProduct, kroneckerMap_apply,
      Fintype.sum_prod_type, one_apply, mul_comm] using he

end Quantum.Operators
