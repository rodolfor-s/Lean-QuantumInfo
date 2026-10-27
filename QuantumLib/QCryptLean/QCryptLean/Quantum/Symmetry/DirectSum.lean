import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Paired

/-!
# Symmetric spaces with aligned classical block labels

Local registers are dependent sums. Alignment compares their classical labels
at each site; no cumulative dimensions or decoded offsets are involved.
-/

noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators
open scoped ComplexOrder Kronecker

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (A R : I → Type*) [∀ i, Fintype (A i)] [∀ i, Fintype (R i)]
variable [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (R i)]

/-- Project onto words whose signal and reference have the same block label at every site. -/
def alignedDirectSumProjector (n : ℕ) :
    Op ((Fin n → Sigma A) × (Fin n → Sigma R)) :=
  Matrix.diagonal (fun x => if ∀ t, (x.1 t).1 = (x.2 t).1 then 1 else 0)

omit [Fintype I] [∀ i, Fintype (A i)] [∀ i, Fintype (R i)] in
/-- The alignment projector is Hermitian. -/
theorem isHermitian_alignedDirectSumProjector (n : ℕ) :
    (alignedDirectSumProjector A R n).IsHermitian := by
  rw [alignedDirectSumProjector, isHermitian_diagonal_iff]
  intro i
  split <;> simp [IsSelfAdjoint]

/-- Alignment is idempotent. -/
theorem alignedDirectSumProjector_idem (n : ℕ) :
    alignedDirectSumProjector A R n * alignedDirectSumProjector A R n =
      alignedDirectSumProjector A R n := by
  rw [alignedDirectSumProjector, diagonal_mul_diagonal]
  congr 1
  funext i
  split <;> simp

omit [Fintype I] [∀ i, Fintype (A i)] [∀ i, Fintype (R i)] in
/-- Alignment is positive because it is a nonnegative diagonal matrix. -/
theorem posSemidef_alignedDirectSumProjector (n : ℕ) :
    (alignedDirectSumProjector A R n).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  dsimp only [Pi.zero_apply]
  split <;> positivity

/-- Symmetric vectors within aligned direct sums, expressed as a compression. -/
def symmetricProjectorDirectSum (n : ℕ) :
    Op ((Fin n → Sigma A) × (Fin n → Sigma R)) :=
  alignedDirectSumProjector A R n * pairedProjectorOf (Sigma A) (Sigma R) n *
    alignedDirectSumProjector A R n

/-- The compressed symmetric projector is positive. -/
theorem posSemidef_symmetricProjectorDirectSum (n : ℕ) :
    (symmetricProjectorDirectSum A R n).PosSemidef := by
  have h := (pairedProjectorOf_posSemidef (Sigma A) (Sigma R) n).mul_mul_conjTranspose_same
    (alignedDirectSumProjector A R n)
  simpa only [symmetricProjectorDirectSum,
    (isHermitian_alignedDirectSumProjector A R n).eq] using h

/-- The compressed symmetric projector is Hermitian. -/
theorem isHermitian_symmetricProjectorDirectSum (n : ℕ) :
    (symmetricProjectorDirectSum A R n).IsHermitian :=
  (posSemidef_symmetricProjectorDirectSum A R n).isHermitian

end Quantum.Symmetry
