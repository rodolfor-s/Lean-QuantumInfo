import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Block Diagonal PSD — reindexing, block-diagonal positivity, and block traces

Provides matrix reindexing facts and `Matrix.posSemidef_blockDiagonal`: if
every block `M i` is positive semidefinite, then `blockDiagonal M` is positive
semidefinite.

## Main statements

- `Matrix.trace_reindex_self`: reindexing rows and columns by one equivalence preserves trace
- `Matrix.PosSemidef.reindex`: reindexing preserves positive semidefiniteness
- `blockDiagonal_mulVec_apply`: mulVec of block diagonal decomposes block-wise
- `Matrix.posSemidef_blockDiagonal`: block diagonal of PSD blocks is PSD
-/

open Matrix Finset
open scoped ComplexOrder

/-- Reindexing a square matrix by the same equivalence on rows and columns
preserves the trace. -/
lemma Matrix.trace_reindex_self {m n : Type*} [Fintype m] [Fintype n]
    (e : m ≃ n) (M : Matrix m m ℂ) :
    (Matrix.reindex e e M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.reindex_apply]
  exact Equiv.sum_comp e.symm (fun i => M i i)

/-- Reindexing a positive semidefinite matrix by an equivalence preserves
positive semidefiniteness. -/
lemma Matrix.PosSemidef.reindex {m n : Type*} {M : Matrix m m ℂ}
    (hM : M.PosSemidef) (e : m ≃ n) :
    (Matrix.reindex e e M).PosSemidef := by
  rw [Matrix.reindex_apply]
  exact (Matrix.posSemidef_submatrix_equiv e.symm).mpr hM

variable {m o : Type*} [Fintype m] [DecidableEq m] [Fintype o] [DecidableEq o]

omit [DecidableEq m] in
/-- The mulVec of a block diagonal matrix decomposes block-wise. -/
lemma blockDiagonal_mulVec_apply
    (M : o → Matrix m m ℂ) (x : m × o → ℂ) (a : m) (k : o) :
    (blockDiagonal M *ᵥ x) (a, k) = (M k *ᵥ fun b => x (b, k)) a := by
  simp only [mulVec, dotProduct, blockDiagonal_apply, Fintype.sum_prod_type,
    ite_mul, zero_mul, sum_ite_eq, mem_univ, ↓reduceIte]

omit [Fintype m] [DecidableEq m] [Fintype o] in
/-- A block diagonal matrix with PSD blocks is PSD. -/
lemma Matrix.posSemidef_blockDiagonal [Finite m] [Finite o] {M : o → Matrix m m ℂ}
    (h : ∀ i, (M i).PosSemidef) :
    (blockDiagonal M).PosSemidef := by
  cases nonempty_fintype m; cases nonempty_fintype o
  apply PosSemidef.of_dotProduct_mulVec_nonneg
  · -- IsHermitian
    ext ⟨a, k⟩ ⟨b, k'⟩
    simp only [conjTranspose_apply, blockDiagonal_apply]
    by_cases hk : k = k'
    · subst hk; simp only [↓reduceIte]
      change star (M k b a) = M k a b
      rw [← Matrix.conjTranspose_apply]; exact congr_fun (congr_fun (h k).isHermitian a) b
    · rw [ite_eq_right hk, ite_eq_right (Ne.symm hk), star_zero]
  · -- Nonneg quadratic form
    intro x
    simp only [dotProduct, Pi.star_apply, Fintype.sum_prod_type, blockDiagonal_mulVec_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_nonneg
    intro k _
    exact (h k).dotProduct_mulVec_nonneg (fun a => x (a, k))

/-- A `fromBlocks`-style block-diagonal matrix (zero off-diagonal blocks) with PSD
    diagonal blocks is PSD. -/
lemma Matrix.PosSemidef.fromBlocks_zero
    {n l : Type*} [Finite n] [Finite l]
    {A : Matrix n n ℂ} {D : Matrix l l ℂ}
    (hA : A.PosSemidef) (hD : D.PosSemidef) :
    (Matrix.fromBlocks A 0 0 D).PosSemidef := by
  classical
  let := Fintype.ofFinite n
  let := Fintype.ofFinite l
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · -- Hermitian: conjTranspose of fromBlocks splits; zero blocks stay zero.
    change (Matrix.fromBlocks A 0 0 D)ᴴ = Matrix.fromBlocks A 0 0 D
    simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_inj]
    exact ⟨hA.isHermitian, trivial, trivial, hD.isHermitian⟩
  · intro x
    -- Expand using fromBlocks_mulVec and the sum-type dotProduct split.
    rw [Matrix.fromBlocks_mulVec, Matrix.dotProduct_block]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr,
      Matrix.zero_mulVec, add_zero, zero_add]
    have hstar_inl : (star x) ∘ Sum.inl = star (x ∘ Sum.inl) := by funext; rfl
    have hstar_inr : (star x) ∘ Sum.inr = star (x ∘ Sum.inr) := by funext; rfl
    rw [hstar_inl, hstar_inr]
    exact add_nonneg (hA.dotProduct_mulVec_nonneg _)
      (hD.dotProduct_mulVec_nonneg _)
