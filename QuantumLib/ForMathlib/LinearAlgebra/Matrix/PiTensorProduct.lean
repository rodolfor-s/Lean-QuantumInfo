import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! # Pi Tensor Product -/


namespace Matrix

variable {I R : Type*} {X Y Z : I → Type*} [Fintype I]

/-- The tensor product of a dependent family of rectangular matrices. -/
def piTensorProduct [CommMonoid R] (A : ∀ i, Matrix (X i) (Y i) R) :
    Matrix ((i : I) → X i) ((i : I) → Y i) R := of fun x y => ∏ i, A i (x i) (y i)

/-- Entries of a tensor family are products over its sites. -/
@[simp] theorem piTensorProduct_apply [CommMonoid R]
    (A : ∀ i, Matrix (X i) (Y i) R) (x : ∀ i, X i) (y : ∀ i, Y i) :
    piTensorProduct A x y = ∏ i, A i (x i) (y i) := rfl

/-- Transposition commutes with a tensor family. -/
theorem transpose_piTensorProduct [CommMonoid R] (A : ∀ i, Matrix (X i) (Y i) R) :
    (piTensorProduct A)ᵀ = piTensorProduct (fun i => (A i)ᵀ) := rfl

/-- Conjugate transposition commutes with a tensor family. -/
@[simp] theorem conjTranspose_piTensorProduct [CommMonoid R] [StarMul R]
    (A : ∀ i, Matrix (X i) (Y i) R) :
    (piTensorProduct A)ᴴ = piTensorProduct (fun i => (A i)ᴴ) := by
  ext x y
  simp [conjTranspose_apply, star_prod]

/-- Sitewise transport induces pointwise transport of function registers. -/
theorem piTensorProduct_reindex [CommMonoid R] {X' Y' : I → Type*}
    (e : ∀ i, X i ≃ X' i) (f : ∀ i, Y i ≃ Y' i)
    (A : ∀ i, Matrix (X i) (Y i) R) :
    piTensorProduct (fun i => reindex (e i) (f i) (A i)) =
      reindex (Equiv.piCongrRight e) (Equiv.piCongrRight f) (piTensorProduct A) := rfl

open scoped Kronecker in
/-- Regrouping a tensor family of Kronecker products separates its two component families. -/
theorem reindex_piTensorProduct_kronecker [CommMonoid R] {X' Y' : I → Type*}
    (A : ∀ i, Matrix (X i) (Y i) R) (B : ∀ i, Matrix (X' i) (Y' i) R) :
    reindex (Equiv.arrowProdEquivProdArrow I X X') (Equiv.arrowProdEquivProdArrow I Y Y')
      (piTensorProduct (fun i => A i ⊗ₖ B i)) = piTensorProduct A ⊗ₖ piTensorProduct B := by
  ext x y
  exact Finset.prod_mul_distrib

/-- A tensor family of coordinate matrix units is the coordinate unit of the function register. -/
@[simp] theorem piTensorProduct_single_one [CommMonoidWithZero R]
    [∀ i, DecidableEq (X i)] [∀ i, DecidableEq (Y i)]
    (x : ∀ i, X i) (y : ∀ i, Y i) :
    piTensorProduct (fun i => single (x i) (y i) (1 : R)) = single x y 1 := by
  classical
  ext a b
  simp only [piTensorProduct_apply, single_apply, Fintype.prod_boole]
  simp only [forall_and, ← funext_iff]

section Semiring

variable [CommSemiring R] [DecidableEq I]

omit [DecidableEq I] in
/-- Tensor products preserve identity matrices, including the empty family. -/
@[simp] theorem piTensorProduct_one [∀ i, DecidableEq (X i)] :
    piTensorProduct (fun i => (1 : Matrix (X i) (X i) R)) = 1 := by
  ext x y
  simp only [piTensorProduct_apply, one_apply, Fintype.prod_boole, ← funext_iff]

/-- Multiplication contracts each intermediate register independently. -/
theorem piTensorProduct_mul [∀ i, Fintype (Y i)]
    (A : ∀ i, Matrix (X i) (Y i) R) (B : ∀ i, Matrix (Y i) (Z i) R) :
    piTensorProduct A * piTensorProduct B = piTensorProduct (fun i => A i * B i) := by
  ext x z
  simp only [mul_apply, piTensorProduct_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i y => A i (x i) y * B i y (z i))).symm

/-- The trace of a tensor family is the product of the traces. -/
theorem trace_piTensorProduct [∀ i, Fintype (X i)]
    (A : ∀ i, Matrix (X i) (X i) R) :
    (piTensorProduct A).trace = ∏ i, (A i).trace := by
  exact (Fintype.prod_sum (fun i x => A i x x)).symm

omit [DecidableEq I] in
/-- Tensoring diagonal matrices gives the diagonal product of their entries. -/
theorem piTensorProduct_diagonal [∀ i, DecidableEq (X i)] (d : ∀ i, X i → R) :
    piTensorProduct (fun i => diagonal (d i)) = diagonal (fun x => ∏ i, d i (x i)) := by
  ext x y
  by_cases h : x = y
  · subst y
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    simp only [piTensorProduct_apply, diagonal_apply, h, ite_false]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

omit [DecidableEq I] in
/-- Tensoring rank-one matrices multiplies their vectors pointwise over the sites. -/
theorem piTensorProduct_vecMulVec (v : ∀ i, X i → R) (w : ∀ i, Y i → R) :
    piTensorProduct (fun i => vecMulVec (v i) (w i)) =
      vecMulVec (fun x => ∏ i, v i (x i)) (fun y => ∏ i, w i (y i)) := by
  ext x y
  exact Finset.prod_mul_distrib

/-- The square tensor family as a monoid homomorphism. -/
def piTensorProductMonoidHom [∀ i, Fintype (X i)] [∀ i, DecidableEq (X i)] :
    (∀ i, Matrix (X i) (X i) R) →* Matrix ((i : I) → X i) ((i : I) → X i) R where
  toFun := piTensorProduct
  map_one' := piTensorProduct_one
  map_mul' A B := (piTensorProduct_mul A B).symm

end Semiring

section Positivity

open scoped ComplexOrder MatrixOrder


/-- Hermitian factors give a Hermitian tensor family. -/
theorem IsHermitian.piTensorProduct [CommMonoid R] [StarMul R]
    {A : ∀ i, Matrix (X i) (X i) R}
    (h : ∀ i, (A i).IsHermitian) : (piTensorProduct A).IsHermitian := by
  rw [IsHermitian, conjTranspose_piTensorProduct]
  exact congrArg Matrix.piTensorProduct (funext fun i => (h i).eq)

/-- Positive factors give a positive tensor family by factoring each factor as a Gram matrix. -/
theorem PosSemidef.piTensorProduct [∀ i, Finite (X i)] {A : ∀ i, Matrix (X i) (X i) ℂ}
    (h : ∀ i, (A i).PosSemidef) : (piTensorProduct A).PosSemidef := by
  classical
  let (i : I) : Fintype (X i) := Fintype.ofFinite (X i)
  let B := fun i => CFC.sqrt (A i)
  have hB : ∀ i, (B i)ᴴ * B i = A i := by
    intro i
    rw [show (B i)ᴴ = B i from
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (A i))).isHermitian]
    exact CFC.sqrt_mul_sqrt_self (A i) (h i).nonneg
  have hAB : A = fun i => (B i)ᴴ * B i := funext fun i => (hB i).symm
  rw [hAB, ← piTensorProduct_mul, ← conjTranspose_piTensorProduct]
  exact posSemidef_conjTranspose_mul_self _

/-- Strictly positive factors give a strictly positive tensor family. -/
theorem PosDef.piTensorProduct [∀ i, Finite (X i)] {A : ∀ i, Matrix (X i) (X i) ℂ}
    (h : ∀ i, (A i).PosDef) : (piTensorProduct A).PosDef := by
  classical
  let (i : I) : Fintype (X i) := Fintype.ofFinite (X i)
  apply (PosSemidef.piTensorProduct fun i => (h i).posSemidef).posDef_iff_isUnit.mpr
  exact (Pi.isUnit_iff.mpr fun i => (h i).isUnit).map piTensorProductMonoidHom

end Positivity

end Matrix
