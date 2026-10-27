import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.Scaling
import QCryptLean.Quantum.Operators.Algebra

/-! # Isometry -/


namespace Quantum.Metrics

open scoped ComplexOrder MatrixOrder

open Matrix Quantum.Operators

variable {X Y : Type*} [Fintype X] [Fintype Y]

open scoped Classical in
/-- Fidelity is unchanged by a common rectangular isometry. -/
theorem fidelity_isometry_conj_of_toOp_eq
    (V : Matrix Y X ℂ) (A B : PosSemidefOp X) (A' B' : PosSemidefOp Y)
    (hV : Vᴴ * V = 1) (hA : A'.val = V * A.val * Vᴴ)
    (hB : B'.val = V * B.val * Vᴴ) : fidelity A' B' = fidelity A B := by
  classical
  have hp : (sqrtPosSemidefOp A * B.val * sqrtPosSemidefOp A).PosSemidef := by
    simpa only [(isHermitian_sqrtPosSemidefOp A).eq] using
      B.property.mul_mul_conjTranspose_same (sqrtPosSemidefOp A)
  change (CFC.sqrt A.val * B.val * CFC.sqrt A.val).PosSemidef at hp
  unfold fidelity sqrtPosSemidefOp
  rw [hA, hB, A.property.sqrt_conj_of_isometry V hV]
  have he : (V * CFC.sqrt A.val * Vᴴ) * (V * B.val * Vᴴ) *
      (V * CFC.sqrt A.val * Vᴴ) = V * (CFC.sqrt A.val * B.val * CFC.sqrt A.val) * Vᴴ := by
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul]
  rw [he, hp.sqrt_conj_of_isometry V hV, Matrix.trace_mul_cycle, hV, Matrix.one_mul]

end Quantum.Metrics
