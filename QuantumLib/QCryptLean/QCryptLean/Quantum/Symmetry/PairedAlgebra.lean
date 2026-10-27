import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Dimension
import QCryptLean.Quantum.Symmetry.Paired

/-! # Paired Algebra -/


noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators
open scoped Kronecker

variable {X : Type*} [Fintype X] [DecidableEq X] {d k : ℕ}

/-- Normalizing the symmetric projector keeps exactly its occupation-type rank. -/
theorem rank_deFinettiState [Nonempty X] :
    (deFinettiState X k).toOp.rank =
      Nat.choose (k + Fintype.card X - 1) (Fintype.card X - 1) := by
  change ((symmetricProjector X k).trace⁻¹ • symmetricProjector X k).rank = _
  rw [Matrix.rank_smul_of_mem_nonZeroDivisors _
    (mem_nonZeroDivisors_iff_ne_zero.mpr (inv_ne_zero symmetricProjector_trace_ne_zero))]
  exact rank_symmetricProjector

end Quantum.Symmetry
