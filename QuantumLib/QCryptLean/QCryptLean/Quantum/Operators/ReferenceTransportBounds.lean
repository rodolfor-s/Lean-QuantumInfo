import QCryptLean.Math.LinearAlgebra.Matrix.UnitaryGram
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.RankPurification
import QCryptLean.Quantum.Operators.ReferenceTransport
import QCryptLean.Quantum.Operators.StateOperations

/-! # Reference Transport Bounds -/


noncomputable section

namespace Quantum.Operators

open Matrix
open scoped MatrixOrder ComplexOrder Kronecker

variable {X R : Type*} [Fintype X] [Fintype R] [DecidableEq X] [DecidableEq R]
variable {d r : ℕ}

/-- Square-ancilla pure extensions are reference-unitary transports of the canonical one. -/
theorem DensityOp.exists_reference_unitary (ρ : DensityOp X) (τ : DensityOp (X × X))
    (hpure : τ.IsPure) (hmarg : τ.partialTraceRight = ρ) :
    ∃ U : UnitaryOp X, τ.toOp = rightTensorUnitaryConj U ρ.purification.toOp := by
  classical
  obtain ⟨v, hv⟩ := DensityOp.IsPure.exists_normKet τ hpure
  let V : Op X := fun i j => v.vec (i, j)
  let S := CFC.sqrt ρ.toOp
  have hV : V * Vᴴ = ρ.toOp := by
    change Matrix.partialTraceRight v.toKet.projector = _
    change v.toDensityOp.partialTraceRight.toOp = _
    rw [hv, hmarg]
  have hS : S * Sᴴ = ρ.toOp := ρ.posSemidef.eq_cfcSqrt_mul_conjTranspose.symm
  obtain ⟨W, hW, he⟩ := Matrix.exists_coisometry_of_rowGram_eq S V (hS.trans hV.symm) le_rfl
  have hu : W ∈ Matrix.unitaryGroup X ℂ := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    convert hW using 1
    ext i j
    simp only [Matrix.one_apply]
    split_ifs <;> rfl
  let U : UnitaryOp X := Matrix.UnitaryGroup.transpose ⟨W, hu⟩
  have hk : v.toKet.vec = (1 ⊗ₖ U.val) *ᵥ ρ.purificationKet.vec := by
    ext ⟨i, j⟩
    have hij := congrFun (congrFun he i) j
    change V i j = _
    rw [hij]
    simp [DensityOp.toPosSemidefOp, U, S, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type,
      kroneckerMap_apply, Matrix.one_apply, DensityOp.purificationKet,
      PosSemidefOp.purificationKet, Ket.vectorize, mul_comm]
  refine ⟨U, ?_⟩
  rw [← hv]
  change vecMulVec v.vec (star v.vec) =
    (1 ⊗ₖ U.val) * vecMulVec ρ.purificationKet.vec (star ρ.purificationKet.vec) * (1 ⊗ₖ U.val)ᴴ
  rw [hk, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  congr 1
  exact Matrix.star_mulVec _ _

/-- The reference marginal of any square-ancilla purification is a conjugate transpose. -/
theorem DensityOp.exists_reference_marginal_eq_unitary_conj
    (ρ : DensityOp X) (τ : DensityOp (X × X))
    (hpure : τ.IsPure) (hmarg : τ.partialTraceRight = ρ) :
    ∃ U : UnitaryOp X, Matrix.partialTraceLeft τ.toOp = U.val * ρ.toOpᵀ * U.valᴴ := by
  obtain ⟨U, hU⟩ := ρ.exists_reference_unitary τ hpure hmarg
  exact ⟨U, hU ▸ partialTraceLeft_rightTensorUnitaryConj_purification ρ U⟩

end Quantum.Operators
