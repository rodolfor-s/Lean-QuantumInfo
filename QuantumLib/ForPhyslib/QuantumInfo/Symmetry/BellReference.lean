import QuantumLib.ForPhyslib.QuantumInfo.Channels.Kraus
import QuantumLib.ForPhyslib.QuantumInfo.Operators.Basic
import QuantumLib.ForPhyslib.QuantumInfo.Symmetry.Basic
import QuantumLib.ForPhyslib.QuantumInfo.Symmetry.Bell
import QuantumLib.ForPhyslib.QuantumInfo.Symmetry.Paired

/-!
# Bell-sector de Finetti references

The reference is obtained by applying the intrinsic Pauli channel to the
normalized symmetric projector of the Boolean pair register.
-/

noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators Quantum.Channels

/-- The normalized Bell-sector de Finetti reference on a function register. -/
def bellDeFinettiDensity (k : ℕ) : DensityOp (Fin k → Bool × Bool) :=
  (isChannel_bellTwirl k).applyDensity (deFinettiState (Bool × Bool) k)

/-- The Bell-sector reference is invariant under permutations of the sites. -/
theorem isPermutationInvariant_bellDeFinettiDensity (k : ℕ) :
    IsPermutationInvariant (bellDeFinettiDensity k) := by
  intro σ
  change permutationRepresentation σ * bellTwirl k (deFinettiState (Bool × Bool) k).toOp *
    (permutationRepresentation σ)ᴴ = bellTwirl k (deFinettiState (Bool × Bool) k).toOp
  rw [← bellTwirl_perm_conj]
  apply congrArg (bellTwirl k)
  change _ * (_ • symmetricProjector _ _) * _ = _ • symmetricProjector _ _
  rw [Matrix.mul_smul, Matrix.smul_mul, permutationRepresentation_mul_symmetricProjector]
  have h := congrArg Matrix.conjTranspose
    (permutationRepresentation_mul_symmetricProjector (X := Bool × Bool) σ)
  simpa only [Matrix.conjTranspose_mul, symmetricProjector_isHermitian.eq] using
    congrArg ((Matrix.trace (symmetricProjector (Bool × Bool) k))⁻¹ • ·) h

/-- The Bell reference viewed as a subnormalized state. -/
def bellDeFinettiState (k : ℕ) : SubDensityOp (Fin k → Bool × Bool) :=
  (bellDeFinettiDensity k).toSubDensityOp

end Quantum.Symmetry
