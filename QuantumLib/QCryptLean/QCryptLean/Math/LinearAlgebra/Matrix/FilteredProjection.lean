import QCryptLean.Math.LinearAlgebra.Matrix.ProjectionOrder

/-! # Trace bounds after an invertible filter on a supported positive matrix

Only the local matrix star order is used. The filter need not be Hermitian.
-/
namespace Matrix
open scoped ComplexOrder MatrixOrder
variable {X : Type*} [Fintype X]

/-- Undoing an invertible filter gives a trace cap against the filtered support projector. -/
theorem PosSemidef.le_trace_smul_filtered_projection {A P S T : Matrix X X ℂ}
    [DecidableEq X] (hA : A.PosSemidef) (hP : P.IsHermitian) (hPP : P * P = P)
    (hPA : P * A = A) (hST : S * T = 1) (hTP : Commute T P) :
    A ≤ (((T * A * Tᴴ).trace.re : ℂ) • (S * P * Sᴴ)) := by
  have hTA : P * (T * A * Tᴴ) = T * A * Tᴴ := by
    calc
      _ = (P * T) * A * Tᴴ := by simp only [Matrix.mul_assoc]
      _ = (T * P) * A * Tᴴ := by rw [hTP.eq]
      _ = _ := by rw [Matrix.mul_assoc T P, hPA]
  have h := (Matrix.le_iff.mp ((hA.mul_mul_conjTranspose_same T).le_re_trace_smul_projection
    hP hPP hTA)).mul_mul_conjTranspose_same S
  have he : S * (T * A * Tᴴ) * Sᴴ = A := by
    calc
      _ = (S * T) * A * (S * T)ᴴ := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = A := by rw [hST, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, he] at h
  exact Matrix.le_iff.mpr h

end Matrix
