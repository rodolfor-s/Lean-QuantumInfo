import QCryptLean.Math.LinearAlgebra.Matrix.PositiveTrace
import QCryptLean.Math.SpectralTheory.Matrix

/-! # Collision trace under a positive definite reference

The matrix order is local. The weight is the CFC inverse fourth root, and no
matrix norm instance is selected.
-/
noncomputable section
namespace Matrix
open scoped ComplexOrder MatrixOrder
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Inverse-fourth-root collision is bounded by the feasible scale times the input trace. -/
theorem PosSemidef.trace_inverse_fourth_sandwich_sq_le {A B : Matrix X X ℂ}
    (hA : A.PosSemidef) (hB : B.PosDef) {t : ℝ} (ht : A ≤ (t : ℂ) • B) :
    let F := CFC.sqrt (CFC.sqrt B⁻¹)
    ((F * A * F) * (F * A * F)).trace.re ≤ t * A.trace.re := by
  let F := CFC.sqrt (CFC.sqrt B⁻¹)
  have hF : F.IsHermitian := (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian
  have hG : F * F * B * (F * F) = 1 := by
    rw [show F * F = CFC.sqrt B⁻¹ from
      CFC.sqrt_mul_sqrt_self _ (CFC.sqrt_nonneg _)]
    exact hB.sqrt_inv_mul_self_mul_sqrt_inv
  have hQ : (F * A * F).PosSemidef := by
    simpa only [hF.eq] using hA.conjTranspose_mul_mul_same F
  have hE := (le_iff.mp ht).conjTranspose_mul_mul_same F
  rw [hF.eq, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul] at hE
  have hp := (Complex.nonneg_iff.mp (hQ.trace_mul_nonneg hE)).1
  have he : ((F * A * F) * (F * B * F)).trace = A.trace := by
    calc
      _ = (F * (A * (F * F * B * F))).trace := by
        congr 1
        noncomm_ring
      _ = ((A * (F * F * B * F)) * F).trace := trace_mul_comm _ _
      _ = (A * (F * F * B * (F * F))).trace := by
        congr 1
        noncomm_ring
      _ = A.trace := by rw [hG, mul_one]
  rw [mul_sub, trace_sub, Complex.sub_re, Matrix.mul_smul, trace_smul,
    smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, he] at hp
  exact sub_nonneg.mp hp

end Matrix
