import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! # Kronecker Sandwich -/


namespace Matrix

open scoped Kronecker

variable {V W X Y Z R : Type*} [Semiring R] [Fintype X] [Fintype Y] [Fintype Z]
  [DecidableEq Z]

/-- Multiplication on the first coordinate contracts only that coordinate. -/
theorem kronecker_one_sandwich_apply (A : Matrix W X R) (M : Matrix (X × Z) (Y × Z) R)
    (B : Matrix Y V R) (w : W) (v : V) (z z' : Z) :
    ((A ⊗ₖ (1 : Matrix Z Z R)) * M * (B ⊗ₖ (1 : Matrix Z Z R))) (w, z) (v, z') =
      ∑ x, ∑ y, A w x * M (x, z) (y, z') * B y v := by
  simp only [mul_apply, kroneckerMap_apply, one_apply, Fintype.sum_prod_type,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_mul]
  exact Finset.sum_comm

end Matrix
