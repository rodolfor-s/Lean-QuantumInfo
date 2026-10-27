import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.PositiveBound
import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Quantum.Channels.SymmetricBound
import QCryptLean.Quantum.Channels.SymmetricSupport
import QCryptLean.Quantum.Channels.SymmetricSupportBound
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Dimension

/-! # Supported Bound -/


noncomputable section

namespace Quantum.Channels

open Matrix Quantum.Operators Quantum.Symmetry Quantum.Metrics
open scoped ComplexOrder

variable {X Y R S : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
  [Fintype Y] [Nonempty Y] [Fintype R] [Nonempty R] [Fintype S] [Nonempty S] {k : ℕ}

omit [Nonempty Y] [Nonempty R] [Nonempty S] in
/-- Supported positive-input CKR bound, with the factor-two loss and arbitrary finite ancilla. -/
theorem traceNorm_mapTensorId_le_two_mul_choose_mul_of_support (e : X ≃ Fin 4)
    (Δ : Operation (Fin k → X) Y) (A : Op ((Fin k → X) × S))
    (hA : A.PosSemidef) (htr : A.trace.re ≤ 1)
    (τ : DensityOp ((Fin k → X) × R)) (hτ : IsDeFinettiPurification τ)
    (hs : symmetricProjector X k * partialTraceRight A = partialTraceRight A) :
    traceNorm (mapTensorId Δ S A) ≤
      2 * ((k + 3).choose 3 : ℝ) * ckrTraceNorm Δ τ := by
  have hc : Fintype.card X = 4 := by simpa using Fintype.card_congr e
  have hb := traceNorm_mapTensorId_le_of_symmetric_support Δ A hA htr τ hτ hs
  rw [symmetricSubspace_dim, hc] at hb
  norm_num [Nat.add_sub_assoc] at hb
  have hn : 0 ≤ ((k + 3).choose 3 : ℝ) * ckrTraceNorm Δ τ :=
    mul_nonneg (Nat.cast_nonneg _) (traceNorm_nonneg _)
  linarith

end Quantum.Channels
