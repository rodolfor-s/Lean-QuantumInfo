import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The Schur product theorem

The **Schur product theorem**: the Hadamard (entrywise) product of two positive semidefinite
matrices is positive semidefinite. A Kronecker interpretation is: `A ⊗ₖ B` is
positive semidefinite, and `A ⊙ B` is the principal submatrix of `A ⊗ₖ B` selected by the
diagonal embedding `i ↦ (i, i)`, so it inherits positivity from
`Matrix.PosSemidef.submatrix`.

The file also collects the diagonal and trace companions of the Hadamard product that the
positivity statements are normally used with: the diagonal of `A ⊙ B` is the pointwise
product of the diagonals, so its trace is the dot product `A.diag ⬝ᵥ B.diag`, and pairing a
matrix with a diagonal one reads off a weighted diagonal sum.

## Main statements

* `Matrix.kronecker_submatrix_diag_eq_hadamard` — the Hadamard product is a principal
  submatrix of the Kronecker product; this needs only `Mul`.
* `Matrix.diag_hadamard`, `Matrix.trace_hadamard` — the diagonal and the trace of a Hadamard
  product.
* `Matrix.trace_diagonal_hadamard`, `Matrix.trace_hadamard_diagonal` — the two diagonal
  pairings `tr (diagonal d ⊙ B) = d ⬝ᵥ B.diag` and `tr (B ⊙ diagonal d) = B.diag ⬝ᵥ d`.
* `Matrix.PosSemidef.hadamard` — the Schur product theorem.
* `Matrix.PosSemidef.trace_hadamard_nonneg` — its trace corollary.
* `Matrix.PosSemidef.diag_dotProduct_nonneg` — nonnegativity of the pairing of the
  diagonals of two positive semidefinite matrices.
* `Matrix.PosSemidef.hadamard_vecMulVec_self_star` and
  `Matrix.PosSemidef.vecMulVec_self_star_hadamard` — the two cases in which one factor is the
  rank-one outer product `vecMulVec d (star d)`, with entries `dᵢ · conj dⱼ`, on the right and
  on the left respectively. This is the shape that arises when one factor comes from a single
  spectral direction.

## Relation to Mathlib

Mathlib supplies the Hadamard product itself and its ring-theoretic algebra
(`Mathlib/LinearAlgebra/Matrix/Hadamard.lean`), including the reductions
`Matrix.diagonal_hadamard : diagonal w ⊙ M = diagonal (w * M.diag)` and
`Matrix.hadamard_diagonal : M ⊙ diagonal w = diagonal (M.diag * w)`, which already settle the
positivity of a Hadamard product with a diagonal matrix through
`Matrix.posSemidef_diagonal_iff`. Mathlib also supplies `Matrix.PosSemidef.hadamard` in
`Mathlib/Analysis/Matrix/Order.lean`. This file supplies the trace formulas and rank-one
corollaries above.

## References

* I. Schur, *Bemerkungen zur Theorie der beschränkten Bilinearformen mit unendlich vielen
  Veränderlichen*, J. Reine Angew. Math. **140** (1911), 1–28.
* R. A. Horn and C. R. Johnson, *Topics in Matrix Analysis*, Chapter 5 (the Hadamard product).

## Tags

Schur product, Hadamard product, positive semidefinite, Kronecker product
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder

namespace Matrix

variable {n : Type*}

section Algebra

variable {α : Type*}

/-- The Hadamard product is the principal submatrix of the Kronecker product along the
diagonal embedding `i ↦ (i, i)`, because `(A ⊗ₖ B) (i, i) (j, j) = A i j * B i j`. -/
theorem kronecker_submatrix_diag_eq_hadamard [Mul α] (A B : Matrix n n α) :
    (A ⊗ₖ B).submatrix (fun i => (i, i)) (fun i => (i, i)) = A ⊙ B := by
  ext i j
  simp [Matrix.submatrix_apply, Matrix.hadamard_apply, Matrix.kroneckerMap_apply]

/-! ### Diagonal and trace of a Hadamard product -/

/-- The diagonal of a Hadamard product is the pointwise product of the diagonals. -/
@[simp]
theorem diag_hadamard [Mul α] (A B : Matrix n n α) : (A ⊙ B).diag = A.diag * B.diag := rfl

/-- The trace of a Hadamard product is the dot product of the diagonals. -/
theorem trace_hadamard [Fintype n] [AddCommMonoid α] [Mul α] (A B : Matrix n n α) :
    (A ⊙ B).trace = A.diag ⬝ᵥ B.diag := rfl

variable [Fintype n] [DecidableEq n] [AddCommMonoid α] [Mul α]

/-- Pairing a matrix with a diagonal one on the left reads off a weighted diagonal sum:
`tr (diagonal d ⊙ B) = d ⬝ᵥ B.diag`. -/
theorem trace_diagonal_hadamard (d : n → α) (B : Matrix n n α) :
    (diagonal d ⊙ B).trace = d ⬝ᵥ B.diag := by
  simp [Matrix.trace, dotProduct, Matrix.diag, Matrix.hadamard_apply]

/-- Pairing a matrix with a diagonal one on the right reads off a weighted diagonal sum:
`tr (B ⊙ diagonal d) = B.diag ⬝ᵥ d`. -/
theorem trace_hadamard_diagonal (B : Matrix n n α) (d : n → α) :
    (B ⊙ diagonal d).trace = B.diag ⬝ᵥ d := by
  simp [Matrix.trace, dotProduct, Matrix.diag, Matrix.hadamard_apply]

end Algebra

/-! ### Positivity -/

section PosSemidef

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The trace of a Hadamard product of positive semidefinite matrices is nonnegative.
Combined with `Matrix.trace_hadamard` this is the statement `0 ≤ A.diag ⬝ᵥ B.diag`. -/
theorem PosSemidef.trace_hadamard_nonneg [Fintype n] {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A ⊙ B).trace :=
  (hA.hadamard hB).trace_nonneg

/-- The diagonals of two positive semidefinite matrices pair nonnegatively. -/
theorem PosSemidef.diag_dotProduct_nonneg [Fintype n] {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ A.diag ⬝ᵥ B.diag := by
  rw [← Matrix.trace_hadamard]
  exact hA.trace_hadamard_nonneg hB

/-- The Hadamard product of a positive semidefinite matrix with the rank-one outer product
`vecMulVec d (star d)` is positive semidefinite. -/
theorem PosSemidef.hadamard_vecMulVec_self_star [Finite n] {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (d : n → 𝕜) : (A ⊙ vecMulVec d (star d)).PosSemidef :=
  hA.hadamard (posSemidef_vecMulVec_self_star d)

/-- The rank-one Hadamard factor on the left: `vecMulVec d (star d) ⊙ A` is positive
semidefinite for positive semidefinite `A`. -/
theorem PosSemidef.vecMulVec_self_star_hadamard [Finite n] {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (d : n → 𝕜) : (vecMulVec d (star d) ⊙ A).PosSemidef :=
  (posSemidef_vecMulVec_self_star d).hadamard hA

end PosSemidef

end Matrix
