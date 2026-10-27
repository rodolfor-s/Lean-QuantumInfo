import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Commutant

/-!
# Independent local actions and permutations

The joint action is a family indexed by a group-valued word and a site
permutation. This interface does not require callers to manipulate a semidirect
product or enumerate the quantum register.
-/

namespace Quantum.Symmetry

open Matrix Quantum.Operators

variable {X G : Type*} [Fintype X] [DecidableEq X] [Group G]

/-- Independent local group actions followed by a permutation of the sites. -/
def jointAction (ρ : G →* Op X) (k : ℕ)
    (v : (Fin k → G) × Equiv.Perm (Fin k)) : Op (Fin k → X) :=
  piTensorProduct (fun i => ρ (v.1 i)) * permutationRepresentation v.2

/-- Tensor powers constrained to the one-copy commutant. -/
def centralizerTensorPowers (ρ : G →* Op X) (k : ℕ) : Set (Op (Fin k → X)) :=
  Set.range fun A : commutant (Set.range ρ) => Op.tensorPow A.val k

end Quantum.Symmetry
