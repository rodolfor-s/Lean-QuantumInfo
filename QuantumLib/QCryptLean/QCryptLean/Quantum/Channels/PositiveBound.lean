import QCryptLean.Quantum.Channels.AncillaBounds
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Diamond
import QCryptLean.Quantum.Channels.DiamondBounds
import QCryptLean.Quantum.Channels.DiamondInequality
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Basic

/-! # Positive Bound -/


namespace Quantum.Channels

open Matrix Quantum.Operators Quantum.Metrics
open scoped ComplexOrder

variable {X Y R : Type*} [Fintype X] [Fintype Y] [Fintype R] {n m r : ℕ}

omit [Fintype R] in
/-- A square-reference positive-input bound bounds the all-operator diamond norm. -/
theorem diamondNorm_le_of_traceNorm_mapTensorId_le
    (Φ : Operation X Y) (hstar : ∀ A, Φ Aᴴ = (Φ A)ᴴ) (B : ℝ)
    (hPSD : ∀ A : Op (X × X), A.PosSemidef → A.trace.re ≤ 1 →
      traceNorm (mapTensorId Φ X A) ≤ B) : diamondNorm Φ ≤ B := by
  have hb : 0 ≤ B := by
    simpa only [map_zero, traceNorm_zero] using hPSD 0 PosSemidef.zero (by simp)
  apply diamondNorm_le_of_forall
  intro A hA
  exact (traceNorm_mapTensorId_le_mul_of_map_conjTranspose Φ B hstar hPSD A).trans
    (mul_le_of_le_one_right hb hA)

/-- The arbitrary-reference factor-two reduction from a square positive bound. -/
theorem traceNorm_mapTensorId_le_two_mul_of_square_posSemidef_bound
    (Φ : Operation X Y) (B : ℝ)
    (hPSD : ∀ A : Op (X × X), A.PosSemidef → A.trace.re ≤ 1 →
      traceNorm (mapTensorId Φ X A) ≤ B)
    (A : Op (X × R)) (hA : traceNorm A ≤ 1) :
    traceNorm (mapTensorId Φ R A) ≤ 2 * B := by
  have hb : 0 ≤ B := by
    simpa only [map_zero, traceNorm_zero] using hPSD 0 PosSemidef.zero (by simp)
  have hh := traceNorm_mapTensorId_add_adjoint_le Φ B hPSD A
  have hn := traceNorm_nonneg (mapTensorId Φ R Aᴴ)
  have hm := mul_le_mul_of_nonneg_left hA (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hb)
  linarith

end Quantum.Channels
