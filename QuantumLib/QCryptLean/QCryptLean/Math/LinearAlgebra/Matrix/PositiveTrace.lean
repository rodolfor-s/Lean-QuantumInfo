import QCryptLean.Math.SpectralTheory.Matrix

/-!
# Trace products of positive matrices

The square-root argument uses the local Löwner-order scope. It installs no norm
instances and works on every finite index type, including the empty type.
-/

namespace Matrix

open scoped ComplexOrder MatrixOrder

variable {X : Type*} [Fintype X]

/-- The trace of a product of two positive complex matrices is nonnegative. -/
theorem PosSemidef.trace_mul_nonneg {A B : Matrix X X ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  classical
  have h := (hA.conjTranspose_mul_mul_same (CFC.sqrt B)).trace_nonneg
  rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian.eq, trace_mul_cycle,
    CFC.sqrt_mul_sqrt_self B hB.nonneg] at h
  rwa [trace_mul_comm] at h

end Matrix
