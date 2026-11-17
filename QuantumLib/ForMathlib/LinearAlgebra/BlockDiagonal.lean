import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Block

/-!
# Off-diagonal-zero matrices are block-diagonal submatrices

A generic linear-algebra fact: if a square matrix `M` has zero entries whenever the
second components of the reindexed row/column disagree, then `M` is (the reindexing
of) a block-diagonal matrix whose blocks are the fixed-second-component submatrices.

-/

open Matrix

lemma matrix_eq_blockDiagonal_submatrix_of_offDiag_zero
    {ι κ outIdx : Type*} [DecidableEq κ]
    (M : Matrix outIdx outIdx ℂ)
    (e : outIdx ≃ ι × κ)
    (hzero : ∀ p q : outIdx, (e p).2 ≠ (e q).2 → M p q = 0) :
    M =
      (Matrix.blockDiagonal
        (fun i : κ =>
          M.submatrix (fun x : ι => e.symm (x, i))
            (fun x : ι => e.symm (x, i)))).submatrix e e := by
  ext p q
  by_cases h : (e p).2 = (e q).2
  · have hp : e.symm ((e p).1, (e q).2) = p := by
      have hpair : ((e p).1, (e q).2) = e p := by
        ext <;> simp [h]
      calc
        e.symm ((e p).1, (e q).2) = e.symm (e p) := congrArg e.symm hpair
        _ = p := e.symm_apply_apply p
    simp [Matrix.blockDiagonal_apply, h, hp]
  · simp [Matrix.blockDiagonal_apply, h, hzero p q h]
