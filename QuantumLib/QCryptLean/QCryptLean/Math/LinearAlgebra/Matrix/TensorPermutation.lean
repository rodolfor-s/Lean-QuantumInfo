import Mathlib.LinearAlgebra.Matrix.Permutation
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct

/-!
# Permuting the sites of a function register

The action is defined on functions, without an enumeration of either the sites or
local basis. Its convention sends a basis function `x` to `x ∘ σ.symm`.
-/

namespace Matrix

variable {I X R : Type*} [Fintype I] [DecidableEq X]

/-- The matrix that permutes tensor sites by `σ`. -/
def tensorPermutation [Zero R] [One R] (σ : Equiv.Perm I) : Matrix (I → X) (I → X) R :=
  of fun x y => if x = y ∘ σ.symm then 1 else 0

omit [Fintype I] [DecidableEq X] in
/-- Move a permutation from one side of a function equality to the other. -/
theorem eq_comp_symm_iff (x y : I → X) (σ : Equiv.Perm I) :
    x = y ∘ σ.symm ↔ x ∘ σ = y := by
  constructor <;> intro h <;> funext i
  · simpa using congrFun h (σ i)
  · simpa using congrFun h (σ.symm i)

/-- Relabelling the local basis commutes with every permutation of tensor sites. -/
theorem reindex_tensorPermutation {Y : Type*} [DecidableEq Y] [Zero R] [One R]
    (e : X ≃ Y) (σ : Equiv.Perm I) :
    reindex (Equiv.piCongrRight fun _ : I => e) (Equiv.piCongrRight fun _ : I => e)
      (tensorPermutation (X := X) (R := R) σ) = tensorPermutation (X := Y) σ := by
  ext x y
  change (if e.symm ∘ x = (e.symm ∘ y) ∘ σ.symm then (1 : R) else 0) =
    if x = y ∘ σ.symm then 1 else 0
  have he : e.symm ∘ x = (e.symm ∘ y) ∘ σ.symm ↔ x = y ∘ σ.symm :=
    e.symm.injective.comp_left.eq_iff
  simp only [he]

variable [Fintype (I → X)]

/-- Composition of site permutations is represented by matrix multiplication. -/
theorem tensorPermutation_mul [Semiring R] (σ τ : Equiv.Perm I) :
    tensorPermutation (X := X) (R := R) σ * tensorPermutation (X := X) (R := R) τ =
      tensorPermutation (X := X) (R := R) (σ * τ) := by
  ext x y
  simp only [tensorPermutation, mul_apply, of_apply]
  rw [Finset.sum_eq_single (y ∘ τ.symm)]
  · simp only [↓reduceIte, mul_one]
    congr 1
  · intro z _ hz
    simp [hz]
  · simp

omit [Fintype (I → X)] in
/-- The identity site permutation is the identity matrix. -/
theorem tensorPermutation_one [Zero R] [One R] :
    tensorPermutation (X := X) (R := R) (1 : Equiv.Perm I) = 1 := by
  ext x y
  rfl

omit [Fintype (I → X)] in
/-- Transposition inverts the site permutation. -/
theorem tensorPermutation_transpose [Zero R] [One R] (σ : Equiv.Perm I) :
    (tensorPermutation (X := X) (R := R) σ)ᵀ = tensorPermutation (X := X) (R := R) σ⁻¹ := by
  ext x y
  simp only [transpose_apply, tensorPermutation, of_apply]
  have h : y = x ∘ σ.symm ↔ x = y ∘ σ := by
    simpa only [eq_comm] using eq_comp_symm_iff y x σ
  simp only [h, Equiv.Perm.inv_def, Equiv.symm_symm]

omit [Fintype (I → X)] in
/-- Adjoint inverts the site permutation. -/
theorem tensorPermutation_conjTranspose [Semiring R] [StarRing R] (σ : Equiv.Perm I) :
    (tensorPermutation (X := X) (R := R) σ)ᴴ = tensorPermutation (X := X) (R := R) σ⁻¹ := by
  rw [← tensorPermutation_transpose]
  ext x y
  simp only [conjTranspose_apply, transpose_apply, tensorPermutation, of_apply]
  split_ifs <;> simp

/-- Site permutations are unitary, including on empty registers. -/
theorem tensorPermutation_unitary [Semiring R] [StarRing R] (σ : Equiv.Perm I) :
    (tensorPermutation (X := X) (R := R) σ)ᴴ * tensorPermutation (X := X) (R := R) σ = 1 ∧
      tensorPermutation (X := X) (R := R) σ * (tensorPermutation (X := X) (R := R) σ)ᴴ = 1 := by
  simp [tensorPermutation_conjTranspose, tensorPermutation_mul, tensorPermutation_one]

/-- Acting on a vector precomposes its basis function with the site permutation. -/
theorem tensorPermutation_mulVec [Semiring R] (σ : Equiv.Perm I) (v : (I → X) → R)
    (x : I → X) : (tensorPermutation σ *ᵥ v) x = v (x ∘ σ) := by
  simp only [mulVec, dotProduct, tensorPermutation, of_apply, eq_comp_symm_iff]
  simp

/-- Conjugation acts by precomposition on both function indices. -/
theorem tensorPermutation_conj_apply [Semiring R] [StarRing R]
    (σ : Equiv.Perm I) (A : Matrix (I → X) (I → X) R) (x y : I → X) :
    (tensorPermutation (X := X) (R := R) σ * A * (tensorPermutation (X := X) (R := R) σ)ᴴ) x y =
      A (x ∘ σ) (y ∘ σ) := by
  have hleft (z : I → X) :
      (tensorPermutation (X := X) (R := R) σ * A) x z = A (x ∘ σ) z := by
    simp only [mul_apply, tensorPermutation, of_apply, eq_comp_symm_iff]
    simp
  rw [tensorPermutation_conjTranspose]
  change (∑ z, (tensorPermutation (X := X) (R := R) σ * A) x z *
    tensorPermutation (X := X) (R := R) σ⁻¹ z y) = _
  simp_rw [hleft]
  simp [tensorPermutation, Equiv.Perm.inv_def]

/-- Conjugation permutes the factors of a tensor family. -/
theorem tensorPermutation_conj_piTensorProduct [CommSemiring R] [StarRing R]
    (σ : Equiv.Perm I) (A : I → Matrix X X R) :
    tensorPermutation (X := X) (R := R) σ * piTensorProduct A *
        (tensorPermutation (X := X) (R := R) σ)ᴴ =
      piTensorProduct (fun i => A (σ.symm i)) := by
  ext x y
  rw [tensorPermutation_conj_apply]
  exact Fintype.prod_equiv σ _ _ (fun i => by simp)

/-- A repeated rectangular factor intertwines the permutations of its two function registers. -/
theorem tensorPermutation_mul_piTensorProduct_const {Y : Type*} [DecidableEq Y]
    [Fintype (I → Y)] [CommSemiring R] (σ : Equiv.Perm I) (A : Matrix X Y R) :
    tensorPermutation σ * piTensorProduct (fun _ : I => A) =
      piTensorProduct (fun _ : I => A) * tensorPermutation σ := by
  ext x y
  have hl : (tensorPermutation (X := X) (R := R) σ * piTensorProduct (fun _ : I => A)) x y =
      piTensorProduct (fun _ : I => A) (x ∘ σ) y := by
    simp [Matrix.mul_apply, tensorPermutation, eq_comp_symm_iff]
  have hr : (piTensorProduct (fun _ : I => A) * tensorPermutation (X := Y) (R := R) σ) x y =
      piTensorProduct (fun _ : I => A) x (y ∘ σ.symm) := by
    simp [Matrix.mul_apply, tensorPermutation]
  rw [hl, hr]
  exact Fintype.prod_equiv σ _ _ (fun i => by simp)

end Matrix
