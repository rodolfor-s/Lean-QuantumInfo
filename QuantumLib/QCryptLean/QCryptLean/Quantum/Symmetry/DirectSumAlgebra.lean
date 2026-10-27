import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Math.LinearAlgebra.Matrix.Reindex
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Symmetry.DirectSum
import QCryptLean.Quantum.Symmetry.Paired
import QCryptLean.Quantum.Symmetry.PairedAlgebra
import QCryptLean.Quantum.Symmetry.ProjectedAlgebra

/-! # Direct Sum Algebra -/


noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators

/-- Enumerate a dependent sum from its individual component enumerations. -/
def sigmaEquiv {k : ℕ} {A : Fin k → Type*} {a : Fin k → ℕ}
    (e : ∀ i, A i ≃ Fin (a i)) : Sigma A ≃ Fin (∑ i, a i) :=
  (Equiv.sigmaCongrRight e).trans finSigmaFinEquiv

variable {k n : ℕ} {A R : Fin k → Type*} {a r : Fin k → ℕ}
variable [∀ i, Fintype (A i)] [∀ i, Fintype (R i)]
variable [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (R i)]

/-- Dimension of aligned symmetric direct sums. -/
theorem symmetricProjectorDirectSum_trace [Nonempty (Fin k)]
    [∀ i, Nonempty (A i)] [∀ i, Nonempty (R i)] :
    (symmetricProjectorDirectSum A R n).trace =
      ((n + ∑ i, Fintype.card (A i) * Fintype.card (R i) - 1).choose
        ((∑ i, Fintype.card (A i) * Fintype.card (R i)) - 1) : ℂ) := by
  classical
  let Z := Sigma A × Sigma R
  let P : Op Z := diagonal (fun z => if z.1.1 = z.2.1 then 1 else 0)
  have hP : P.IsHermitian := by
    apply isHermitian_diagonal_iff.mpr
    intro z
    split <;> simp [IsSelfAdjoint]
  have hPP : P * P = P := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext z
    split <;> simp
  have ht : P.trace = (∑ i, Fintype.card (A i) * Fintype.card (R i) : ℕ) := by
    rw [Matrix.trace_diagonal]
    change (∑ z : Sigma A × Sigma R, if z.1.1 = z.2.1 then (1 : ℂ) else 0) = _
    simp only [Fintype.sum_prod_type, Fintype.sum_sigma]
    have he (i : Fin k) : (∑ j : Fin k, ∑ _b : R j,
        if i = j then (1 : ℂ) else 0) = Fintype.card (R i) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Ne.symm hj]
      · simp
    simp_rw [he]
    simp [Nat.cast_sum, Nat.cast_mul]
  have : NeZero (∑ i, Fintype.card (A i) * Fintype.card (R i)) := ⟨ne_of_gt
    (Finset.sum_pos (fun i _ => Nat.mul_pos Fintype.card_pos Fintype.card_pos)
      Finset.univ_nonempty)⟩
  have he : reindex (pairFunctions (Sigma A) (Sigma R) n)
      (pairFunctions (Sigma A) (Sigma R) n) (Op.tensorPow P n) =
        alignedDirectSumProjector A R n := by
    rw [Op.tensorPow, piTensorProduct_diagonal, reindex_diagonal]
    congr 1
    funext z
    simp only [pairFunctions, Equiv.arrowProdEquivProdArrow,
      Finset.prod_ite_zero, Finset.prod_const_one, Finset.mem_univ, forall_const]
    rfl
  rw [symmetricProjectorDirectSum, ← he, pairedProjectorOf,
    ← Matrix.reindex_mul, ← Matrix.reindex_mul, Matrix.trace_reindex_self]
  rw [Matrix.trace_mul_cycle, ← Op.tensorPow_mul, hPP]
  exact trace_tensorPow_projection_mul_symmetricProjector P hP hPP ht

end Quantum.Symmetry
