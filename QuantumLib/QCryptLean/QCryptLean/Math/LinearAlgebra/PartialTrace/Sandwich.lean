import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic

/-!
# Multiplication on the retained register

Rectangular sandwiches on the retained register commute with partial trace. Only
the intermediate indices need finiteness, and only the discarded identity needs
decidable equality. The coefficients need not be commutative.
-/

namespace Matrix

open scoped Kronecker

variable {V W X Y Z R : Type*} [Semiring R] [Fintype Z] [DecidableEq Z]

/-- Left multiplication on the retained register commutes with right partial trace. -/
theorem partialTraceRight_kronecker_one_mul [Fintype X]
    (A : Matrix W X R) (M : Matrix (X × Z) (Y × Z) R) :
    partialTraceRight ((A ⊗ₖ (1 : Matrix Z Z R)) * M) = A * partialTraceRight M := by
  ext w y
  simp only [partialTraceRight_apply, mul_apply, kroneckerMap_apply, one_apply,
    Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum]
  exact Finset.sum_comm

/-- Right multiplication on the retained register commutes with right partial trace. -/
theorem partialTraceRight_mul_kronecker_one [Fintype Y]
    (M : Matrix (X × Z) (Y × Z) R) (B : Matrix Y V R) :
    partialTraceRight (M * (B ⊗ₖ (1 : Matrix Z Z R))) = partialTraceRight M * B := by
  ext x v
  simp only [partialTraceRight_apply, mul_apply, kroneckerMap_apply, one_apply,
    Fintype.sum_prod_type, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_mul]
  exact Finset.sum_comm

/-- Rectangular sandwiches commute with right partial trace. -/
theorem partialTraceRight_kronecker_one_sandwich [Fintype X] [Fintype Y]
    (A : Matrix W X R) (M : Matrix (X × Z) (Y × Z) R) (B : Matrix Y V R) :
    partialTraceRight ((A ⊗ₖ (1 : Matrix Z Z R)) * M * (B ⊗ₖ (1 : Matrix Z Z R))) =
      A * partialTraceRight M * B := by
  rw [partialTraceRight_mul_kronecker_one, partialTraceRight_kronecker_one_mul]

/-- Left multiplication on the retained register commutes with left partial trace. -/
theorem partialTraceLeft_one_kronecker_mul [Fintype X]
    (A : Matrix W X R) (M : Matrix (Z × X) (Z × Y) R) :
    partialTraceLeft (((1 : Matrix Z Z R) ⊗ₖ A) * M) = A * partialTraceLeft M := by
  ext w y
  simp only [partialTraceLeft_apply, mul_apply, kroneckerMap_apply, one_apply,
    Fintype.sum_prod_type, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, Finset.mul_sum]
  exact Finset.sum_comm

/-- Right multiplication on the retained register commutes with left partial trace. -/
theorem partialTraceLeft_mul_one_kronecker [Fintype Y]
    (M : Matrix (Z × X) (Z × Y) R) (B : Matrix Y V R) :
    partialTraceLeft (M * ((1 : Matrix Z Z R) ⊗ₖ B)) = partialTraceLeft M * B := by
  ext x v
  simp only [partialTraceLeft_apply, mul_apply, kroneckerMap_apply, one_apply,
    Fintype.sum_prod_type, ite_mul, one_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Finset.sum_mul]
  exact Finset.sum_comm

/-- Rectangular sandwiches commute with left partial trace. -/
theorem partialTraceLeft_one_kronecker_sandwich [Fintype X] [Fintype Y]
    (A : Matrix W X R) (M : Matrix (Z × X) (Z × Y) R) (B : Matrix Y V R) :
    partialTraceLeft (((1 : Matrix Z Z R) ⊗ₖ A) * M * ((1 : Matrix Z Z R) ⊗ₖ B)) =
      A * partialTraceLeft M * B := by
  rw [partialTraceLeft_mul_one_kronecker, partialTraceLeft_one_kronecker_mul]

end Matrix
