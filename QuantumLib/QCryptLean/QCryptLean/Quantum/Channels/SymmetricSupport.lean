import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Paired

/-!
# Symmetric-support postselection hypotheses

The ordinary Haar-pure reference differs from the mixed CKR reference. Factoring
through the symmetric projector is an additional assumption on the operation.
No matrix norm or order instance is installed.
-/

namespace Quantum.Channels

open Matrix Quantum.Operators Quantum.Symmetry

variable {X Y R : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [Fintype R] {k : ℕ}

/-- A pure extension of the normalized symmetric projector. -/
structure IsDeFinettiPurification [Nonempty X]
    (τ : DensityOp ((Fin k → X) × R)) : Prop where
  /-- The joint reference is pure. -/
  isPure : τ.IsPure
  /-- Its marginal is the ordinary Haar-pure de Finetti reference. -/
  marginal : τ.partialTraceRight = deFinettiState X k

/-- Permutation covariance with adjoint preservation and symmetric input support. -/
structure PermutationCovariantSymmetricSupport (Δ : Operation (Fin k → X) Y)
    : Prop extends PermutationCovariant Δ where
  /-- The operation preserves adjoints on all operators. -/
  map_conjTranspose : ∀ A, Δ Aᴴ = (Δ A)ᴴ
  /-- The operation depends only on the symmetric compression of its input. -/
  factors_through_sym : ∀ A, Δ (symmetricProjector X k * A * symmetricProjector X k) = Δ A

end Quantum.Channels
