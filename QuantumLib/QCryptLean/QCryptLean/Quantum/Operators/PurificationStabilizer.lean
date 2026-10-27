import QCryptLean.Math.LinearAlgebra.Matrix.OuterProduct
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification

/-! # Purification Stabilizer -/


noncomputable section
namespace Quantum.Operators
open Matrix
open scoped Kronecker
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A paired real orthogonal symmetry of a full-rank purification fixes its
reference transport whenever the symmetry has nonzero trace. -/
theorem commute_transpose_of_paired_projector_fixed (A S W : Op X)
    (hS : IsUnit S) (hW : IsUnit W) (hc : Commute A S)
    (hA : Aᵀ * A = 1) (ht : A.trace ≠ 0)
    (hf : (A ⊗ₖ A) * (Ket.vectorize (S * Wᵀ)).projector * (A ⊗ₖ A)ᴴ =
      (Ket.vectorize (S * Wᵀ)).projector) : Commute A Wᵀ := by
  let v := (Ket.vectorize (S * Wᵀ)).vec
  have hp : vecMulVec ((A ⊗ₖ A) *ᵥ v) (star ((A ⊗ₖ A) *ᵥ v)) =
      vecMulVec v (star v) := by
    rw [star_mulVec, ← vecMulVec_mul, ← mul_vecMulVec]
    exact hf
  obtain ⟨a, ha⟩ := Matrix.exists_smul_eq_of_vecMulVec_star_eq hp
  have hm : A * (S * Wᵀ) * Aᵀ = a • (S * Wᵀ) := by
    have hv : v = Matrix.vec (S * Wᵀ)ᵀ := rfl
    rw [hv, kronecker_mulVec_vec] at ha
    ext i j
    have hij := congrFun ha (i, j)
    change ((A * (S * Wᵀ)ᵀ * Aᵀ)ᵀ) i j = a * (S * Wᵀ) i j at hij
    simpa only [transpose_mul, transpose_transpose, Matrix.mul_assoc,
      Matrix.smul_apply, smul_eq_mul] using hij
  have he : A * Wᵀ * Aᵀ = a • Wᵀ := by
    apply hS.mul_left_cancel
    calc S * (A * Wᵀ * Aᵀ) = A * (S * Wᵀ) * Aᵀ := by
           simp only [← Matrix.mul_assoc]
           rw [hc.eq.symm]
         _ = a • (S * Wᵀ) := hm
         _ = S * (a • Wᵀ) := (Matrix.mul_smul _ _ _).symm
  have he' : A * Wᵀ = a • (Wᵀ * A) := by
    have h := congrArg (· * A) he
    simpa only [Matrix.mul_assoc, hA, Matrix.mul_one, Matrix.smul_mul] using h
  obtain ⟨V, hV⟩ := ((Matrix.isUnit_transpose W).mpr hW)
  have hl : ((V⁻¹ : (Op X)ˣ) : Op X) * Wᵀ = 1 := by
    rw [← hV]; exact V.inv_mul
  have hr : Wᵀ * ((V⁻¹ : (Op X)ˣ) : Op X) = 1 := by
    rw [← hV]; exact V.mul_inv
  have he'' : ((V⁻¹ : (Op X)ˣ) : Op X) * A * Wᵀ = a • A := by
    have h := congrArg (((V⁻¹ : (Op X)ˣ) : Op X) * ·) he'
    simpa only [Matrix.mul_smul, ← Matrix.mul_assoc, hl, Matrix.one_mul] using h
  have htr := congrArg Matrix.trace he''
  rw [Matrix.trace_mul_cycle, hr,
    Matrix.one_mul, Matrix.trace_smul, smul_eq_mul] at htr
  have haone : a = 1 := by
    apply (mul_right_cancel₀ ht)
    simpa using htr.symm
  change A * Wᵀ = Wᵀ * A
  simpa only [haone, one_smul] using he'

end Quantum.Operators
