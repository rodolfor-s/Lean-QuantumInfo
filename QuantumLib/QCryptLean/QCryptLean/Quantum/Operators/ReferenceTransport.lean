import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Cyclic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Sandwich
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.Purification

/-! # Unitary transport of the reference factor of a purification -/

namespace Quantum.Operators

open Matrix
open scoped Kronecker

variable {X R : Type*} [Fintype X] [Fintype R] [DecidableEq X] [DecidableEq R]

/-- Conjugate only the reference register by a unitary. -/
def rightTensorUnitaryConj (U : UnitaryOp R) (A : Op (X × R)) : Op (X × R) :=
  (1 ⊗ₖ U.val) * A * (1 ⊗ₖ U.val)ᴴ

/-- Reference transport leaves the system marginal unchanged. -/
theorem partialTraceRight_rightTensorUnitaryConj (U : UnitaryOp R) (A : Op (X × R)) :
    partialTraceRight (rightTensorUnitaryConj U A) = partialTraceRight A := by
  unfold rightTensorUnitaryConj
  rw [conjTranspose_kronecker, conjTranspose_one]
  exact partialTraceRight_one_kronecker_sandwich_of_mul_eq_one _ _ _ U.property.1

/-- Reference transport conjugates the reference marginal. -/
theorem partialTraceLeft_rightTensorUnitaryConj (U : UnitaryOp R) (A : Op (X × R)) :
    partialTraceLeft (rightTensorUnitaryConj U A) = U.val * partialTraceLeft A * U.valᴴ := by
  unfold rightTensorUnitaryConj
  rw [conjTranspose_kronecker, conjTranspose_one, partialTraceLeft_one_kronecker_sandwich]

/-- A transported canonical purification has reference marginal in the transpose's orbit. -/
theorem partialTraceLeft_rightTensorUnitaryConj_purification
    (ρ : DensityOp X) (U : UnitaryOp X) :
    partialTraceLeft (rightTensorUnitaryConj U ρ.purification.toOp) =
      U.val * ρ.toOpᵀ * U.valᴴ := by
  rw [partialTraceLeft_rightTensorUnitaryConj]
  exact congrArg (fun A => U.val * A * U.valᴴ)
    (congrArg DensityOp.toOp ρ.partialTraceLeft_purification)

/-- The reference marginal is unchanged precisely when its unitary transport commutes. -/
theorem partialTraceLeft_rightTensorUnitaryConj_purification_eq_iff
    (ρ : DensityOp X) (U : UnitaryOp X) :
    partialTraceLeft (rightTensorUnitaryConj U ρ.purification.toOp) = ρ.toOpᵀ ↔
      Commute U.val ρ.toOpᵀ := by
  rw [partialTraceLeft_rightTensorUnitaryConj_purification]
  have hL : U.valᴴ * U.val = 1 := U.property.1
  have hR : U.val * U.valᴴ = 1 := U.property.2
  constructor
  · intro h
    have he := congrArg (fun A => A * U.val) h
    change U.val * ρ.toOpᵀ = ρ.toOpᵀ * U.val
    simpa only [Matrix.mul_assoc, hL, Matrix.mul_one] using he
  · intro h
    rw [h.eq, Matrix.mul_assoc, hR, Matrix.mul_one]

end Quantum.Operators
