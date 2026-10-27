import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.StateOperations

/-! # Purification -/


namespace Quantum.Operators

open Matrix
open scoped ComplexOrder MatrixOrder

variable {X Y : Type*}

/-- Purify a family of vectors by storing its label in an ancilla register. -/
def purifyVectorFamily (v : Y → Ket X) : Ket (X × Y) := ⟨fun p => (v p.2).vec p.1⟩

/-- Vectorize a rectangular matrix with the column register as ancilla. -/
def Ket.vectorize (A : Matrix X Y ℂ) : Ket (X × Y) := ⟨fun p => A p.1 p.2⟩

/-- Tracing out the label register sums the family projectors. -/
theorem partialTraceRight_purifyVectorFamily [Fintype Y] (v : Y → Ket X) :
    Matrix.partialTraceRight (purifyVectorFamily v).projector = ∑ y, (v y).projector := by
  ext x x'
  rw [Matrix.sum_apply]
  rfl

/-- Inner products of family purifications sum the component inner products. -/
theorem purifyVectorFamily_inner [Fintype X] [Fintype Y] (v w : Y → Ket X) :
    ((purifyVectorFamily v).dag * purifyVectorFamily w : ℂ) = ∑ y, ((v y).dag * w y : ℂ) := by
  change (∑ p : X × Y, star ((v p.2).vec p.1) * (w p.2).vec p.1) = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- The system marginal of a vectorized matrix is its left Gram matrix. -/
theorem Ket.partialTraceRight_vectorize [Fintype Y] (A : Matrix X Y ℂ) :
    Matrix.partialTraceRight (Ket.vectorize A).projector = A * Aᴴ := rfl


/-- Vectorization turns the Hilbert--Schmidt trace pairing into the ket inner product. -/
theorem Ket.vectorize_inner [Fintype X] [Fintype Y] (A B : Matrix X Y ℂ) :
    ((Ket.vectorize A).dag * Ket.vectorize B : ℂ) = (Aᴴ * B).trace := by
  change (∑ p : X × Y, star (A p.1 p.2) * B p.1 p.2) = _
  simp only [Fintype.sum_prod_type, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  exact Finset.sum_comm

/-- The ancilla marginal is the transpose of the right Gram matrix. -/
theorem Ket.partialTraceLeft_vectorize [Fintype X] (A : Matrix X Y ℂ) :
    Matrix.partialTraceLeft (Ket.vectorize A).projector = (Aᴴ * A)ᵀ := by
  ext y y'
  exact Finset.sum_congr rfl (fun x _ => mul_comm _ _)

/-- A normalized vector defines an idempotent density operator. -/
theorem NormKet.isPure_toDensityOp [Fintype X] (v : NormKet X) : v.toDensityOp.IsPure := by
  change vecMulVec v.vec (star v.vec) * vecMulVec v.vec (star v.vec) = _
  rw [vecMulVec_mul_vecMulVec]
  change vecMulVec v.vec ((v.toKet.dag * v.toKet : ℂ) • star v.vec) = _
  rw [v.normalized, one_smul]
  rfl

variable [Fintype X]

/-- The square-root purification ket, independent of any enumeration. -/
noncomputable def PosSemidefOp.purificationKet (A : PosSemidefOp X) : Ket (X × X) := by
  classical
  exact Ket.vectorize (CFC.sqrt A.val)

/-- The square-root purification has the original positive operator as its system marginal. -/
theorem PosSemidefOp.partialTraceRight_purificationKet (A : PosSemidefOp X) :
    Matrix.partialTraceRight A.purificationKet.projector = A.val := by
  classical
  exact (Ket.partialTraceRight_vectorize _).trans A.property.eq_cfcSqrt_mul_conjTranspose.symm

/-- The ancilla marginal of a square-root purification is the transpose. -/
theorem PosSemidefOp.partialTraceLeft_purificationKet (A : PosSemidefOp X) :
    Matrix.partialTraceLeft A.purificationKet.projector = A.valᵀ := by
  classical
  rw [purificationKet, Ket.partialTraceLeft_vectorize]
  rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A.val)).isHermitian.eq,
    CFC.sqrt_mul_sqrt_self A.val A.property.nonneg]

/-- Purification preserves the trace of a positive operator. -/
theorem PosSemidefOp.trace_purificationKet (A : PosSemidefOp X) :
    A.purificationKet.projector.trace = A.val.trace := by
  rw [← Matrix.trace_partialTraceRight, A.partialTraceRight_purificationKet]

/-- A density state's square-root purification is a normalized vector. -/
noncomputable def DensityOp.purificationKet (ρ : DensityOp X) : NormKet (X × X) where
  toKet := ρ.toPosSemidefOp.purificationKet
  normalized := by
    rw [Ket.IsNormalized, ← Ket.trace_projector,
      PosSemidefOp.trace_purificationKet]
    exact ρ.trace_one

/-- The pure state associated with the square-root purification. -/
noncomputable def DensityOp.purification (ρ : DensityOp X) : DensityOp (X × X) :=
  ρ.purificationKet.toDensityOp

/-- Canonical purification returns the input when its ancilla is discarded. -/
@[simp] theorem DensityOp.partialTraceRight_purification (ρ : DensityOp X) :
    ρ.purification.partialTraceRight = ρ := by
  apply DensityOp.ext
  exact ρ.toPosSemidefOp.partialTraceRight_purificationKet

/-- The other marginal of the canonical purification is the transposed state. -/
@[simp] theorem DensityOp.partialTraceLeft_purification (ρ : DensityOp X) :
    ρ.purification.partialTraceLeft = ρ.transpose := by
  apply DensityOp.ext
  exact ρ.toPosSemidefOp.partialTraceLeft_purificationKet

/-- Canonical purification is pure. -/
theorem DensityOp.isPure_purification (ρ : DensityOp X) : ρ.purification.IsPure :=
  ρ.purificationKet.isPure_toDensityOp

/-- Every density state has a pure extension on a copy of its register. -/
theorem DensityOp.exists_isPure_partialTraceRight_eq (ρ : DensityOp X) :
    ∃ ψ : DensityOp (X × X), ψ.IsPure ∧ ψ.partialTraceRight = ρ :=
  ⟨ρ.purification, ρ.isPure_purification, ρ.partialTraceRight_purification⟩

/-- Square-root purification also preserves sub-normalization, including zero states. -/
noncomputable def SubDensityOp.purification (ρ : SubDensityOp X) : SubDensityOp (X × X) where
  toOp := ρ.toPosSemidefOp.purificationKet.projector
  posSemidef := Ket.posSemidef_projector _
  trace_le_one := by
    rw [PosSemidefOp.trace_purificationKet]
    exact ρ.trace_le_one

/-- Discarding a sub-density purification's ancilla returns the input state. -/
@[simp] theorem SubDensityOp.partialTraceRight_purification (ρ : SubDensityOp X) :
    ρ.purification.partialTraceRight = ρ := by
  apply SubDensityOp.ext
  exact ρ.toPosSemidefOp.partialTraceRight_purificationKet

end Quantum.Operators
