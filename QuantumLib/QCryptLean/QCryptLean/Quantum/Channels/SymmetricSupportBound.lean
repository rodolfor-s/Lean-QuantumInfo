import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Diamond
import QCryptLean.Quantum.Channels.PositiveBound
import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Quantum.Channels.PostselectionBound
import QCryptLean.Quantum.Channels.SymmetricBound
import QCryptLean.Quantum.Channels.SymmetricSupport
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Dimension

/-! # Symmetric Support Bound -/


noncomputable section

namespace Quantum.Channels

open Matrix Quantum.Operators Quantum.Symmetry Quantum.Metrics

variable {X Y R : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [Fintype R]
  {d m r k : ℕ}

/-- Exact four-level symmetric-support CKR bound. -/
theorem PermutationCovariantSymmetricSupport.diamondNorm_le_choose_mul_ckrTraceNorm
    [Nonempty X] (e : X ≃ Fin 4)
    (Δ : Operation (Fin k → X) Y) (hΔ : PermutationCovariantSymmetricSupport Δ)
    (τ : DensityOp ((Fin k → X) × R)) (hτ : IsDeFinettiPurification τ) :
    diamondNorm Δ ≤ ((k + 3).choose 3 : ℝ) * ckrTraceNorm Δ τ := by
  have hc : Fintype.card X = 4 := by simpa using Fintype.card_congr e
  apply diamondNorm_le_of_traceNorm_mapTensorId_le Δ hΔ.map_conjTranspose
  intro A hA ht
  obtain ⟨B, hB, htB, hs, he⟩ := hΔ.exists_supported_input Δ A hA ht
  have hb := traceNorm_mapTensorId_le_of_symmetric_support Δ B hB htB τ hτ hs
  rw [he, symmetricSubspace_dim, hc] at hb
  norm_num [Nat.add_sub_assoc] at hb
  exact hb

/-- The cubic bound follows natively from the exact coefficient and nonnegative norm. -/
theorem PermutationCovariantSymmetricSupport.diamondNorm_le_cube_mul_ckrTraceNorm
    [Nonempty X] (e : X ≃ Fin 4)
    (Δ : Operation (Fin k → X) Y) (hΔ : PermutationCovariantSymmetricSupport Δ)
    (τ : DensityOp ((Fin k → X) × R)) (hτ : IsDeFinettiPurification τ) :
    diamondNorm Δ ≤ (k + 1 : ℝ) ^ 3 * ckrTraceNorm Δ τ :=
  (hΔ.diamondNorm_le_choose_mul_ckrTraceNorm e Δ τ hτ).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_add_le_add_one_pow k 3)
      (ckrTraceNorm_nonneg Δ τ))

end Quantum.Channels
