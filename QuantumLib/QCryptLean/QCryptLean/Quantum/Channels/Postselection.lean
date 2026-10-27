import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Diamond
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Paired

/-! # Postselection -/


noncomputable section

namespace Quantum.Channels

open Matrix Quantum.Operators Quantum.Symmetry Quantum.Metrics

variable {X Y R : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [Fintype R] {k : ℕ}

/-- CKR covariance: every input permutation has a channel correction on the output. -/
structure PermutationCovariant (Δ : Operation (Fin k → X) Y) : Prop where
  /-- The correction is a complex linear channel. -/
  covariance : ∀ σ : Equiv.Perm (Fin k), ∃ K : Operation Y Y, IsChannel K ∧
    ∀ A, Δ (permutationRepresentation σ * A * (permutationRepresentation σ)ᴴ) = K (Δ A)

/-- A pure extension of the mixed CKR reference on an arbitrary reference register. -/
structure IsCKRDeFinettiPurification [Nonempty X]
    (τ : DensityOp ((Fin k → X) × R)) : Prop where
  /-- The joint density operator is pure. -/
  isPure : τ.IsPure
  /-- Its system marginal is the mixed CKR reference. -/
  marginal : τ.partialTraceRight = ckrDeFinettiState X k

/-- The CKR reference trace norm with an arbitrary finite reference register. -/
def ckrTraceNorm (Δ : Operation (Fin k → X) Y) (τ : DensityOp ((Fin k → X) × R)) : ℝ :=
  traceNorm (mapTensorId Δ R τ.toOp)

omit [DecidableEq X] in
/-- Reference trace norms are nonnegative. -/
theorem ckrTraceNorm_nonneg (Δ : Operation (Fin k → X) Y)
    (τ : DensityOp ((Fin k → X) × R)) : 0 ≤ ckrTraceNorm Δ τ := traceNorm_nonneg _

end Quantum.Channels
