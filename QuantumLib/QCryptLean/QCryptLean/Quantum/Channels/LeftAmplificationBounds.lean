import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.LeftAmplification
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.Contractivity
import QCryptLean.Quantum.Operators.Basic

/-! # Left Amplification Bounds -/


noncomputable section

namespace Quantum.Channels

open Matrix Quantum.Operators Quantum.Metrics
open scoped ComplexOrder

variable {X Y R : Type*} {n m r : ℕ}

/-- CP trace-nonincreasing operations contract all-operator trace norm with a left reference.
The contraction proof uses the native right-reference bound and product commutation. -/
theorem traceNorm_mapIdTensor_le [Fintype X] [Fintype Y] [Fintype R]
    (Φ : Operation X Y) (hΦ : IsCompletelyPositive Φ)
    (htr : ∀ A : Op X, A.PosSemidef → (Φ A).trace.re ≤ A.trace.re)
    (A : Op (R × X)) : traceNorm (mapIdTensor R Φ A) ≤ traceNorm A := by
  exact traceNorm_apply_le_of_isCompletelyPositive_of_trace_le (mapIdTensor R Φ)
    hΦ.mapIdTensor (trace_mapIdTensor_le Φ htr) A

end Quantum.Channels
