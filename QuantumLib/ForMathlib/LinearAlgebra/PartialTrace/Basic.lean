import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Basic -/


namespace Matrix

open scoped BigOperators Kronecker

variable {X Y Z W R S : Type*}

section AddCommMonoid

variable [AddCommMonoid R] [Fintype Z]

/-- Sum the diagonal blocks indexed by the right register. -/
def partialTraceRight (M : Matrix (X × Z) (Y × Z) R) : Matrix X Y R :=
  of fun x y => ∑ z, M (x, z) (y, z)

/-- Sum the diagonal blocks indexed by the left register. -/
def partialTraceLeft (M : Matrix (Z × X) (Z × Y) R) : Matrix X Y R :=
  of fun x y => ∑ z, M (z, x) (z, y)

/-- Entry formula for tracing out the right register. -/
@[simp] theorem partialTraceRight_apply (M : Matrix (X × Z) (Y × Z) R) (x : X) (y : Y) :
    partialTraceRight M x y = ∑ z, M (x, z) (y, z) := rfl

/-- Entry formula for tracing out the left register. -/
@[simp] theorem partialTraceLeft_apply (M : Matrix (Z × X) (Z × Y) R) (x : X) (y : Y) :
    partialTraceLeft M x y = ∑ z, M (z, x) (z, y) := rfl

/-- The right partial trace is a sum of restrictions to fixed right indices. -/
theorem partialTraceRight_eq_sum (M : Matrix (X × Z) (Y × Z) R) :
    partialTraceRight M = ∑ z, M.submatrix (fun x => (x, z)) (fun y => (y, z)) := by
  ext x y
  simp [Matrix.sum_apply]

/-- The left partial trace is a sum of restrictions to fixed left indices. -/
theorem partialTraceLeft_eq_sum (M : Matrix (Z × X) (Z × Y) R) :
    partialTraceLeft M = ∑ z, M.submatrix (fun x => (z, x)) (fun y => (z, y)) := by
  ext x y
  simp [Matrix.sum_apply]

/-- The right partial trace preserves addition. -/
@[simp] theorem partialTraceRight_add (M N : Matrix (X × Z) (Y × Z) R) :
    partialTraceRight (M + N) = partialTraceRight M + partialTraceRight N := by
  ext x y
  simp [Finset.sum_add_distrib]

/-- The left partial trace preserves addition. -/
@[simp] theorem partialTraceLeft_add (M N : Matrix (Z × X) (Z × Y) R) :
    partialTraceLeft (M + N) = partialTraceLeft M + partialTraceLeft N := by
  ext x y
  simp [Finset.sum_add_distrib]

/-- The right partial trace of zero is zero. -/
@[simp] theorem partialTraceRight_zero :
    partialTraceRight (0 : Matrix (X × Z) (Y × Z) R) = 0 := by
  ext x y
  simp

/-- The left partial trace of zero is zero. -/
@[simp] theorem partialTraceLeft_zero :
    partialTraceLeft (0 : Matrix (Z × X) (Z × Y) R) = 0 := by
  ext x y
  simp

/-- Right partial trace commutes with a finite sum. -/
@[simp] theorem partialTraceRight_sum {ι : Type*} (s : Finset ι)
    (M : ι → Matrix (X × Z) (Y × Z) R) :
    partialTraceRight (∑ i ∈ s, M i) = ∑ i ∈ s, partialTraceRight (M i) := by
  ext x y
  simp only [partialTraceRight_apply, Matrix.sum_apply]
  exact Finset.sum_comm

/-- Left partial trace commutes with a finite sum. -/
@[simp] theorem partialTraceLeft_sum {ι : Type*} (s : Finset ι)
    (M : ι → Matrix (Z × X) (Z × Y) R) :
    partialTraceLeft (∑ i ∈ s, M i) = ∑ i ∈ s, partialTraceLeft (M i) := by
  ext x y
  simp only [partialTraceLeft_apply, Matrix.sum_apply]
  exact Finset.sum_comm

/-- Tracing out an empty right register gives zero. -/
@[simp] theorem partialTraceRight_of_isEmpty [IsEmpty Z]
    (M : Matrix (X × Z) (Y × Z) R) : partialTraceRight M = 0 := by
  ext x y
  simp

/-- Tracing out an empty left register gives zero. -/
@[simp] theorem partialTraceLeft_of_isEmpty [IsEmpty Z]
    (M : Matrix (Z × X) (Z × Y) R) : partialTraceLeft M = 0 := by
  ext x y
  simp

/-- Tracing out a singleton right register restricts to its only block. -/
theorem partialTraceRight_of_unique [Unique Z] (M : Matrix (X × Z) (Y × Z) R) :
    partialTraceRight M = M.submatrix (fun x => (x, default)) (fun y => (y, default)) := by
  ext x y
  simp

/-- Tracing out a singleton left register restricts to its only block. -/
theorem partialTraceLeft_of_unique [Unique Z] (M : Matrix (Z × X) (Z × Y) R) :
    partialTraceLeft M = M.submatrix (fun x => (default, x)) (fun y => (default, y)) := by
  ext x y
  simp

/-- The right partial trace preserves the full trace. -/
@[simp] theorem trace_partialTraceRight [Fintype X] (M : Matrix (X × Z) (X × Z) R) :
    (partialTraceRight M).trace = M.trace := by
  simp [trace, Fintype.sum_prod_type]

/-- The left partial trace preserves the full trace. -/
@[simp] theorem trace_partialTraceLeft [Fintype X] (M : Matrix (Z × X) (Z × X) R) :
    (partialTraceLeft M).trace = M.trace := by
  simp only [trace, diag, partialTraceLeft_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- Iterated right partial traces agree after genuine product reassociation. -/
theorem partialTraceRight_partialTraceRight [Fintype W]
    (M : Matrix ((X × Z) × W) ((Y × Z) × W) R) :
    partialTraceRight (partialTraceRight M) =
      partialTraceRight (reindex (Equiv.prodAssoc X Z W) (Equiv.prodAssoc Y Z W) M) := by
  ext x y
  simp [Fintype.sum_prod_type]

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup R] [Fintype Z]

/-- Right partial trace preserves subtraction. -/
@[simp] theorem partialTraceRight_sub (M N : Matrix (X × Z) (Y × Z) R) :
    partialTraceRight (M - N) = partialTraceRight M - partialTraceRight N := by
  ext x y
  simp [Finset.sum_sub_distrib]

/-- Left partial trace preserves subtraction. -/
@[simp] theorem partialTraceLeft_sub (M N : Matrix (Z × X) (Z × Y) R) :
    partialTraceLeft (M - N) = partialTraceLeft M - partialTraceLeft N := by
  ext x y
  simp [Finset.sum_sub_distrib]

end AddCommGroup

section Module

variable [Semiring S] [AddCommMonoid R] [Module S R] [Fintype Z]

/-- The right partial trace commutes with scalar multiplication. -/
@[simp] theorem partialTraceRight_smul (s : S) (M : Matrix (X × Z) (Y × Z) R) :
    partialTraceRight (s • M) = s • partialTraceRight M := by
  ext x y
  simp [Finset.smul_sum]

/-- The left partial trace commutes with scalar multiplication. -/
@[simp] theorem partialTraceLeft_smul (s : S) (M : Matrix (Z × X) (Z × Y) R) :
    partialTraceLeft (s • M) = s • partialTraceLeft M := by
  ext x y
  simp [Finset.smul_sum]

/-- Right partial trace as a linear map over any scalar ring acting on the entries. -/
def partialTraceRightLinearMap : Matrix (X × Z) (Y × Z) R →ₗ[S] Matrix X Y R where
  toFun := partialTraceRight
  map_add' := partialTraceRight_add
  map_smul' := partialTraceRight_smul

/-- Left partial trace as a linear map over any scalar ring acting on the entries. -/
def partialTraceLeftLinearMap : Matrix (Z × X) (Z × Y) R →ₗ[S] Matrix X Y R where
  toFun := partialTraceLeft
  map_add' := partialTraceLeft_add
  map_smul' := partialTraceLeft_smul

/-- Evaluation of the right partial-trace linear map. -/
@[simp] theorem partialTraceRightLinearMap_apply (M : Matrix (X × Z) (Y × Z) R) :
    partialTraceRightLinearMap (S := S) M = partialTraceRight M := rfl

/-- Evaluation of the left partial-trace linear map. -/
@[simp] theorem partialTraceLeftLinearMap_apply (M : Matrix (Z × X) (Z × Y) R) :
    partialTraceLeftLinearMap (S := S) M = partialTraceLeft M := rfl

end Module

section CommSemiring

variable [CommSemiring R] [Fintype Z]

/-- Tracing the right factor of a Kronecker product multiplies by its trace. -/
@[simp] theorem partialTraceRight_kronecker (A : Matrix X Y R) (B : Matrix Z Z R) :
    partialTraceRight (A ⊗ₖ B) = B.trace • A := by
  ext x y
  simp [trace, ← Finset.mul_sum, mul_comm]

/-- Tracing the left factor of a Kronecker product multiplies by its trace. -/
@[simp] theorem partialTraceLeft_kronecker (A : Matrix Z Z R) (B : Matrix X Y R) :
    partialTraceLeft (A ⊗ₖ B) = A.trace • B := by
  ext x y
  simp [trace, ← Finset.sum_mul]

/-- Tracing the right register of the identity counts its dimension. -/
@[simp] theorem partialTraceRight_one [DecidableEq X] [DecidableEq Z] :
    partialTraceRight (1 : Matrix (X × Z) (X × Z) R) =
      (Fintype.card Z : R) • (1 : Matrix X X R) := by
  rw [← one_kronecker_one, partialTraceRight_kronecker, trace_one]

/-- Tracing the left register of the identity counts its dimension. -/
@[simp] theorem partialTraceLeft_one [DecidableEq X] [DecidableEq Z] :
    partialTraceLeft (1 : Matrix (Z × X) (Z × X) R) =
      (Fintype.card Z : R) • (1 : Matrix X X R) := by
  rw [← one_kronecker_one, partialTraceLeft_kronecker, trace_one]

end CommSemiring

end Matrix
