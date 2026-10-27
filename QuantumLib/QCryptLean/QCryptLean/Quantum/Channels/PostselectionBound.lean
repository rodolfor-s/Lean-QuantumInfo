import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.CKRBound
import QCryptLean.Quantum.Channels.Diamond
import QCryptLean.Quantum.Channels.DiamondInequality
import QCryptLean.Quantum.Channels.PositiveBound
import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Symmetry.Dimension
import QCryptLean.Quantum.Symmetry.PairedAlgebra
import QCryptLean.Quantum.Symmetry.Purification

/-! # Postselection Bound -/


noncomputable section

namespace Quantum.Channels

open Matrix Quantum.Operators Quantum.Symmetry Quantum.Metrics

variable {X Y R : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [Fintype R]
  {d m r k : ℕ}

/-- CKR postselection with its exact paired symmetric-subspace dimension.
Native recorded-permutation reduction and paired-projector trace cap. -/
theorem diamondNorm_le_symDim_mul_ckrTraceNorm [Nonempty X]
    (Δ : Operation (Fin k → X) Y) (hΔ : PermutationCovariant Δ)
    (hstar : ∀ A, Δ Aᴴ = (Δ A)ᴴ) (τ : DensityOp ((Fin k → X) × R))
    (hτ : IsCKRDeFinettiPurification τ) :
    diamondNorm Δ ≤
      (Nat.choose (k + (Fintype.card X ^ 2 - 1)) (Fintype.card X ^ 2 - 1) : ℝ) *
        ckrTraceNorm Δ τ := by
  classical
  apply diamondNorm_le_of_traceNorm_mapTensorId_le Δ hstar
  intro A hA ht
  obtain ⟨σ, hσ, hn⟩ := hΔ.exists_invariant_purification_bound Δ A hA ht
  have hb := traceNorm_mapTensorId_le_of_paired_support Δ σ.purification.toOp
    σ.purification.posSemidef (by rw [σ.purification.trace_one, Complex.one_re])
    (purification_in_paired_symmetric_subspace σ hσ) τ hτ
  have hc : Fintype.card (X × X) = Fintype.card X ^ 2 := by simp [pow_two]
  have hpos : 0 < Fintype.card X ^ 2 := pow_pos Fintype.card_pos _
  rw [Quantum.Symmetry.symmetricSubspace_dim, hc,
    Nat.add_sub_assoc (by omega : 1 ≤ Fintype.card X ^ 2)] at hb
  exact hn.trans hb

end Quantum.Channels
