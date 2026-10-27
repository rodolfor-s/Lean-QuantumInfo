import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.Math.LinearAlgebra.Matrix.KroneckerSandwich
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Operators.Basic

/-! # Kraus Algebra -/


namespace Quantum.Channels

open Matrix Quantum.Operators

variable {X Y I : Type*} [Fintype X] [Fintype I]

/-- A Kraus map is the sum of the common matrix conjugation maps. -/
theorem krausMap_eq_sum_conjLinearMap (K : I → Matrix Y X ℂ) :
    krausMap K = ∑ i, Matrix.conjLinearMap (K i) := by
  ext A x y
  simp [krausMap, Matrix.conjLinearMap, LinearMap.sum_apply, Matrix.sum_apply]

/-- Reindexing the finite Kraus family leaves its operation unchanged. -/
theorem krausMap_comp_equiv {J : Type*} [Fintype J] (K : I → Matrix Y X ℂ)
    (e : J ≃ I) : krausMap (fun j => K (e j)) = krausMap K := by
  rw [krausMap_eq_sum_conjLinearMap, krausMap_eq_sum_conjLinearMap]
  exact Equiv.sum_comp e (fun i => Matrix.conjLinearMap (K i))

/-- A termwise partition of Kraus sandwiches partitions the whole operation. -/
theorem krausMap_eq_add_of_sandwich_eq_add (K L M : I → Matrix Y X ℂ)
    (h : ∀ i A, K i * A * (K i)ᴴ = L i * A * (L i)ᴴ + M i * A * (M i)ᴴ) :
    krausMap K = krausMap L + krausMap M := by
  apply LinearMap.ext
  intro A
  change (∑ i, K i * A * (K i)ᴴ) =
    (∑ i, L i * A * (L i)ᴴ) + ∑ i, M i * A * (M i)ᴴ
  simp only [h, Finset.sum_add_distrib]

omit [Fintype I] in
/-- A family with one Kraus operator is matrix conjugation. -/
@[simp] theorem krausMap_const_unit (K : Matrix Y X ℂ) :
    krausMap (fun _ : Unit => K) = Matrix.conjLinearMap K := by
  rw [krausMap_eq_sum_conjLinearMap]
  simp

omit [Fintype I] in
/-- Conjugation by a rectangular matrix is completely positive. -/
theorem isCompletelyPositive_conjLinearMap [Finite Y] (K : Matrix Y X ℂ) :
    IsCompletelyPositive (Matrix.conjLinearMap K) := by
  rw [← krausMap_const_unit]
  exact isCompletelyPositive_krausMap _

omit [Fintype I] in
open scoped Classical in
/-- A conjugation map is a channel precisely when its matrix is an isometry. -/
theorem isChannel_conjLinearMap_iff [Fintype Y] (K : Matrix Y X ℂ) :
    IsChannel (Matrix.conjLinearMap K) ↔ Kᴴ * K = 1 := by
  rw [IsChannel, and_iff_right (isCompletelyPositive_conjLinearMap K),
    ← krausMap_const_unit, isTracePreserving_krausMap_iff]
  simp

omit [Fintype I] in
open scoped Kronecker in
/-- Amplifying a conjugation tensors its rectangular matrix with the reference identity. -/
theorem mapTensorId_conjLinearMap {Z : Type*} [Fintype Z] [DecidableEq Z]
    (K : Matrix Y X ℂ) :
    mapTensorId (Matrix.conjLinearMap K) Z = Matrix.conjLinearMap (K ⊗ₖ (1 : Op Z)) := by
  ext A ⟨x, r⟩ ⟨y, s⟩
  change (K * (Matrix.of fun a b => A (a, r) (b, s)) * Kᴴ) x y =
    ((K ⊗ₖ (1 : Op Z)) * A * (K ⊗ₖ (1 : Op Z))ᴴ) (x, r) (y, s)
  rw [conjTranspose_kronecker, conjTranspose_one, kronecker_one_sandwich_apply]
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
  exact Finset.sum_comm

section Reindex

variable {X Y X' Y' I : Type*} [Fintype X] [Fintype X'] [Fintype I]

/-- Relabelling a Kraus operation relabels each rectangular Kraus matrix. -/
theorem krausMap_reindex (e : X ≃ X') (f : Y ≃ Y') (K : I → Matrix Y X ℂ) :
    krausMap (fun i => Matrix.reindex f e (K i)) =
      (Matrix.reindexLinearEquiv ℂ ℂ f f).toLinearMap.comp
        ((krausMap K).comp (Matrix.reindexLinearEquiv ℂ ℂ e.symm e.symm).toLinearMap) := by
  apply LinearMap.ext
  intro A
  change (∑ i, Matrix.reindex f e (K i) * A * (Matrix.reindex f e (K i))ᴴ) =
    Matrix.reindex f f (∑ i, K i * A.submatrix e e * (K i)ᴴ)
  have hA : A = (A.submatrix e e).submatrix e.symm e.symm := by
    ext a b
    simp
  conv_lhs => rw [hA]
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv]
  ext a b
  simp only [Matrix.sum_apply, Matrix.submatrix_apply]

end Reindex

section Intertwining

variable {X X' Y Y' I : Type*} [Fintype X] [Fintype X'] [Fintype Y'] [Fintype I]

/-- Intertwining Kraus matrices up to unit phases intertwines their conjugation sums. -/
theorem krausMap_conj_of_phased_intertwining
    (K : I → Matrix Y X ℂ) (L : I → Matrix Y' X' ℂ)
    (U : Matrix X X' ℂ) (V : Matrix Y Y' ℂ) (c : I → ℂ)
    (hc : ∀ i, c i * star (c i) = 1)
    (h : ∀ i, K i * U = c i • (V * L i)) (A : Op X') :
    krausMap K (U * A * Uᴴ) = V * krausMap L A * Vᴴ := by
  change (∑ i, K i * (U * A * Uᴴ) * (K i)ᴴ) =
    V * (∑ i, L i * A * (L i)ᴴ) * Vᴴ
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  calc _ = (K i * U) * A * (K i * U)ᴴ := by
             simp only [conjTranspose_mul, Matrix.mul_assoc]
       _ = V * (L i * A * (L i)ᴴ) * Vᴴ := by
             simp only [h, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
               smul_smul]
             rw [mul_comm (star (c i)), hc, one_smul]
             simp only [conjTranspose_mul, Matrix.mul_assoc]

end Intertwining

end Quantum.Channels
