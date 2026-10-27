import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification

/-! # Unnormalized maximal entanglement on a product register -/

namespace Quantum.Operators

open Matrix
open scoped ComplexOrder

variable (X : Type*) [DecidableEq X]

/-- The unnormalized maximally entangled ket is the vectorized identity. -/
def maxEntangledKet : Ket (X × X) := Ket.vectorize (1 : Op X)

/-- The unnormalized maximally entangled positive operator. -/
def maxEntangledOp : Op (X × X) := (maxEntangledKet X).projector

/-- Maximal entanglement has an entry exactly when both index pairs agree. -/
theorem maxEntangledOp_apply (p q : X × X) :
    maxEntangledOp X p q = if p.1 = p.2 ∧ q.1 = q.2 then 1 else 0 := by
  change (if p.1 = p.2 then (1 : ℂ) else 0) *
    star (if q.1 = q.2 then (1 : ℂ) else 0) = _
  split_ifs <;> simp_all

/-- The maximally entangled operator is positive, including on an empty register. -/
theorem posSemidef_maxEntangledOp [Finite X] : (maxEntangledOp X).PosSemidef :=
  (maxEntangledKet X).posSemidef_projector

/-- Its system marginal is the identity, with no nonemptiness hypothesis. -/
theorem partialTraceRight_maxEntangledOp [Fintype X] :
    partialTraceRight (maxEntangledOp X) = 1 := by
  rw [maxEntangledOp, maxEntangledKet, Ket.partialTraceRight_vectorize,
    conjTranspose_one, one_mul]

open scoped Kronecker in
/-- A maximally entangled sandwich evaluates the system trace. -/
theorem maxEntangledOp_sandwich [Fintype X] (A : Op X) :
    maxEntangledOp X * (A ⊗ₖ (1 : Op X)) * maxEntangledOp X =
      A.trace • maxEntangledOp X := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [Matrix.mul_apply, Fintype.sum_prod_type, maxEntangledOp_apply,
    kroneckerMap_apply, Matrix.one_apply, Matrix.trace, ite_and]
  split_ifs <;> rfl

open scoped MatrixOrder ComplexOrder Kronecker in
/-- The square root of unnormalized maximal entanglement has inverse square-root scaling. -/
theorem sqrt_maxEntangledOp [Fintype X] [Nonempty X] :
    CFC.sqrt (maxEntangledOp X) = (((Real.sqrt (Fintype.card X : ℝ))⁻¹ : ℝ) : ℂ) •
      maxEntangledOp X := by
  have hn : (0 : ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
  have hsq : maxEntangledOp X * maxEntangledOp X =
      (Fintype.card X : ℂ) • maxEntangledOp X := by
    simpa only [one_kronecker_one, Matrix.mul_one, Matrix.trace_one] using
      maxEntangledOp_sandwich X (1 : Op X)
  apply CFC.sqrt_unique
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsq, smul_smul]
    have hc : (((Real.sqrt (Fintype.card X : ℝ))⁻¹ : ℝ) : ℂ) *
        (((Real.sqrt (Fintype.card X : ℝ))⁻¹ : ℝ) : ℂ) * (Fintype.card X : ℂ) = 1 := by
      have hr : (Real.sqrt (Fintype.card X : ℝ))⁻¹ *
          (Real.sqrt (Fintype.card X : ℝ))⁻¹ * (Fintype.card X : ℝ) = 1 := by
        rw [← mul_inv, Real.mul_self_sqrt hn.le, inv_mul_cancel₀ (ne_of_gt hn)]
      exact_mod_cast hr
    rw [hc, one_smul]
  · exact ((posSemidef_maxEntangledOp X).smul
      (Complex.zero_le_real.mpr (inv_nonneg.mpr (Real.sqrt_nonneg _)))).nonneg

end Quantum.Operators
