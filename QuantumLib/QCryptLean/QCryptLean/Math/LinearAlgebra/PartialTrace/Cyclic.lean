import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Sandwich

/-!
# Partial trace and actions on the discarded register

The entries of the marginal are traces of blocks. Cyclicity of the scalar trace
therefore gives invariance under inverse actions on the discarded register.
-/

namespace Matrix

open scoped Kronecker

variable {X Y Z R : Type*} [CommSemiring R] [Fintype X] [Fintype Y] [Fintype Z]
  [DecidableEq X] [DecidableEq Y]

/-- Sandwiching the discarded register sandwiches each retained matrix-entry block. -/
theorem partialTraceRight_one_kronecker_sandwich_apply
    (A B : Matrix Z Z R) (M : Matrix (X × Z) (Y × Z) R) (x : X) (y : Y) :
    partialTraceRight (((1 : Matrix X X R) ⊗ₖ A) * M * ((1 : Matrix Y Y R) ⊗ₖ B)) x y =
      (A * (of fun i j => M (x, i) (y, j)) * B).trace := by
  simp [partialTraceRight, trace, diag, mul_apply, kroneckerMap_apply,
    Fintype.sum_prod_type, one_apply, apply_ite]

/-- A right-register sandwich with inverse factors leaves the retained marginal unchanged. -/
theorem partialTraceRight_one_kronecker_sandwich_of_mul_eq_one [DecidableEq Z]
    (A B : Matrix Z Z R) (M : Matrix (X × Z) (Y × Z) R) (h : B * A = 1) :
    partialTraceRight (((1 : Matrix X X R) ⊗ₖ A) * M * ((1 : Matrix Y Y R) ⊗ₖ B)) =
      partialTraceRight M := by
  ext x y
  rw [partialTraceRight_one_kronecker_sandwich_apply, trace_mul_cycle, h, Matrix.one_mul]
  rfl

omit [DecidableEq X] [DecidableEq Y] in
/-- A retained-register sandwich survives inverse actions on the discarded register. -/
theorem partialTraceRight_kronecker_sandwich_of_mul_eq_one {V W : Type*} [DecidableEq Z]
    (A : Matrix W X R) (B : Matrix Y V R) (U V' : Matrix Z Z R)
    (M : Matrix (X × Z) (Y × Z) R) (h : V' * U = 1) :
    partialTraceRight ((A ⊗ₖ U) * M * (B ⊗ₖ V')) = A * partialTraceRight M * B := by
  classical
  have he : (A ⊗ₖ (1 : Matrix Z Z R)) *
      (((1 : Matrix X X R) ⊗ₖ U) * M * ((1 : Matrix Y Y R) ⊗ₖ V')) *
        (B ⊗ₖ (1 : Matrix Z Z R)) = (A ⊗ₖ U) * M * (B ⊗ₖ V') := by
    calc
      _ = ((A ⊗ₖ (1 : Matrix Z Z R)) * ((1 : Matrix X X R) ⊗ₖ U)) * M *
          (((1 : Matrix Y Y R) ⊗ₖ V') * (B ⊗ₖ (1 : Matrix Z Z R))) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
          Matrix.one_mul, Matrix.mul_one]
  rw [← he, partialTraceRight_kronecker_one_sandwich,
    partialTraceRight_one_kronecker_sandwich_of_mul_eq_one U V' M h]

end Matrix
