import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Cyclic
import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Topology
import QCryptLean.Quantum.Symmetry.EmbeddedEntanglement

/-! # Purification into an embedded reference register -/
noncomputable section
namespace Quantum.Operators
open Matrix
open scoped Kronecker MatrixOrder ComplexOrder
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- Purify into an embedded reference basis, then apply a reference unitary. -/
def DensityOp.embeddedPurificationKet (ρ : DensityOp X) (e : X ↪ Y)
    (U : unitaryGroup Y ℂ) : NormKet (X × Y) where
  toKet := ((CFC.sqrt ρ.toOp) ⊗ₖ U.val) * embeddedMaxEntangled e
  normalized := by
    have hU : U.valᴴ * U.val = 1 := Unitary.coe_star_mul_self U
    rw [Ket.IsNormalized, ← Ket.trace_projector, Ket.projector_mul,
      ← trace_partialTraceRight, conjTranspose_kronecker,
      partialTraceRight_kronecker_sandwich_of_mul_eq_one _ _ _ _ _
        hU, partialTraceRight_embeddedMaxEntangled,
      Matrix.mul_one, ← ρ.posSemidef.eq_cfcSqrt_mul_conjTranspose]
    exact ρ.trace_one

/-- The pure density operator obtained from an embedded square-root purification. -/
def DensityOp.embeddedPurification (ρ : DensityOp X) (e : X ↪ Y)
    (U : unitaryGroup Y ℂ) : DensityOp (X × Y) :=
  (ρ.embeddedPurificationKet e U).toDensityOp

/-- The matrix of an embedded purification is the corresponding entangled sandwich. -/
theorem DensityOp.embeddedPurification_toOp (ρ : DensityOp X) (e : X ↪ Y)
    (U : unitaryGroup Y ℂ) :
    (ρ.embeddedPurification e U).toOp =
      ((CFC.sqrt ρ.toOp) ⊗ₖ U.val) * (embeddedMaxEntangled e).projector *
        ((CFC.sqrt ρ.toOp) ⊗ₖ U.val)ᴴ :=
  Ket.projector_mul _ _

/-- Discarding the embedded reference recovers the original state. -/
@[simp] theorem DensityOp.partialTraceRight_embeddedPurification (ρ : DensityOp X)
    (e : X ↪ Y) (U : unitaryGroup Y ℂ) :
    (ρ.embeddedPurification e U).partialTraceRight = ρ := by
  have hU : U.valᴴ * U.val = 1 := Unitary.coe_star_mul_self U
  apply DensityOp.ext
  change Matrix.partialTraceRight (ρ.embeddedPurification e U).toOp = _
  rw [ρ.embeddedPurification_toOp, conjTranspose_kronecker,
    partialTraceRight_kronecker_sandwich_of_mul_eq_one _ _ _ _ _
      hU, partialTraceRight_embeddedMaxEntangled,
    Matrix.mul_one]
  exact ρ.posSemidef.eq_cfcSqrt_mul_conjTranspose.symm

/-- Embedded square-root purifications are pure states. -/
theorem DensityOp.isPure_embeddedPurification (ρ : DensityOp X) (e : X ↪ Y)
    (U : unitaryGroup Y ℂ) : (ρ.embeddedPurification e U).IsPure :=
  NormKet.isPure_toDensityOp _

/-- Embedded purification depends continuously on the reference unitary. -/
theorem DensityOp.continuous_embeddedPurification (ρ : DensityOp X) (e : X ↪ Y) :
    Continuous (ρ.embeddedPurification e) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun U : unitaryGroup Y ℂ => (ρ.embeddedPurification e U).toOp)
  simp only [ρ.embeddedPurification_toOp]
  have h : Continuous (fun U : unitaryGroup Y ℂ => (CFC.sqrt ρ.toOp) ⊗ₖ U.val) := by
    apply continuous_pi; intro i
    apply continuous_pi; intro j
    exact continuous_const.mul ((continuous_apply j.2).comp
      ((continuous_apply i.2).comp continuous_subtype_val))
  exact (h.matrix_mul continuous_const).matrix_mul h.matrix_conjTranspose

end Quantum.Operators
