import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Relabelling rows and columns: the algebraic laws

`Matrix.reindex eₘ eₙ` relabels a matrix's rows by `eₘ` and its columns by `eₙ`. This module gives
its algebraic laws for independent row and column equivalences, using the corresponding
`Matrix.submatrix` laws and Mathlib's reindex equivalences.

## Main statements

* `Matrix.reindex_add`, `Matrix.reindex_smul`, `Matrix.reindex_sum`: a relabelling is additive,
  homogeneous and commutes with a finite sum. `Matrix.submatrix_sum` is the `submatrix` form of
  the last, beside Mathlib's `Matrix.submatrix_add` and `Matrix.submatrix_smul`.
* `Matrix.reindex_mul_reindex` and its square instance `Matrix.reindex_mul`: a relabelling is
  multiplicative, relabelling the contracted index consistently on both factors.
* `Matrix.reindex_trans_apply`: relabelling twice is relabelling once, by the composite.
* `Matrix.reindex_symm_reindex`, `Matrix.reindex_reindex_symm`: the inverse relabelling undoes
  the relabelling, in both orders.
-/

open scoped BigOperators

namespace Matrix

variable {l m n o α : Type*}

/-- A row/column restriction commutes with a finite sum. This is the `Matrix.submatrix` companion
of Mathlib's `Matrix.submatrix_add` and `Matrix.submatrix_smul`. -/
theorem submatrix_sum {ι : Type*} [AddCommMonoid α] (s : Finset ι) (f : ι → Matrix m n α)
    (r : l → m) (c : o → n) :
    (∑ i ∈ s, f i).submatrix r c = ∑ i ∈ s, (f i).submatrix r c := by
  ext i j
  simp [Matrix.sum_apply]

/-- A relabelling commutes with a finite sum. -/
theorem reindex_sum {ι : Type*} [AddCommMonoid α] (eₘ : m ≃ l) (eₙ : n ≃ o) (s : Finset ι)
    (f : ι → Matrix m n α) :
    reindex eₘ eₙ (∑ i ∈ s, f i) = ∑ i ∈ s, reindex eₘ eₙ (f i) :=
  submatrix_sum s f _ _

/-- A relabelling is additive. -/
theorem reindex_add [Add α] (eₘ : m ≃ l) (eₙ : n ≃ o) (A B : Matrix m n α) :
    reindex eₘ eₙ (A + B) = reindex eₘ eₙ A + reindex eₘ eₙ B :=
  congrFun₂ (submatrix_add A B) _ _

/-- A relabelling is homogeneous. -/
theorem reindex_smul {R : Type*} [SMul R α] (eₘ : m ≃ l) (eₙ : n ≃ o) (r : R)
    (A : Matrix m n α) : reindex eₘ eₙ (r • A) = r • reindex eₘ eₙ A :=
  congrFun₂ (submatrix_smul r A) _ _

/-- **A relabelling is multiplicative**, provided the contracted index is relabelled the same way
in both factors. This is Mathlib's `Matrix.submatrix_mul_equiv` at the `reindex` spelling. -/
theorem reindex_mul_reindex {m' n' o' : Type*} [Fintype n] [Fintype n'] [AddCommMonoid α] [Mul α]
    (eₘ : m ≃ m') (eₙ : n ≃ n') (eₒ : o ≃ o') (M : Matrix m n α) (N : Matrix n o α) :
    reindex eₘ eₙ M * reindex eₙ eₒ N = reindex eₘ eₒ (M * N) :=
  submatrix_mul_equiv M N _ eₙ.symm _

/-- Relabelling all indices of square-matrix multiplication by the same equivalence commutes
with multiplication. -/
theorem reindex_mul {m' : Type*} [Fintype m] [Fintype m'] [AddCommMonoid α] [Mul α]
    (e : m ≃ m') (A B : Matrix m m α) :
    reindex e e (A * B) = reindex e e A * reindex e e B :=
  (reindex_mul_reindex e e e A B).symm

/-- Relabelling twice is relabelling once, by the composite. Mathlib's `Matrix.reindex_trans` is
the same fact between the two equivalences. -/
theorem reindex_trans_apply {l₂ o₂ : Type*} (eₘ : m ≃ l) (eₙ : n ≃ o) (eₘ₂ : l ≃ l₂)
    (eₙ₂ : o ≃ o₂) (M : Matrix m n α) :
    reindex (eₘ.trans eₘ₂) (eₙ.trans eₙ₂) M = reindex eₘ₂ eₙ₂ (reindex eₘ eₙ M) :=
  rfl

/-- The inverse relabelling undoes the relabelling. -/
theorem reindex_symm_reindex (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix m n α) :
    reindex eₘ.symm eₙ.symm (reindex eₘ eₙ M) = M :=
  (reindex eₘ eₙ).symm_apply_apply M

/-- The relabelling undoes the inverse relabelling. -/
theorem reindex_reindex_symm (eₘ : m ≃ l) (eₙ : n ≃ o) (M : Matrix l o α) :
    reindex eₘ eₙ (reindex eₘ.symm eₙ.symm M) = M :=
  (reindex eₘ eₙ).apply_symm_apply M

end Matrix
