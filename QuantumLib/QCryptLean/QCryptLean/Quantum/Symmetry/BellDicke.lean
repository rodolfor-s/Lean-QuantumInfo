import Batteries.Tactic.OpenPrivate
import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Symmetry.BellDickeCore
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.BellDoubling
import QCryptLean.Quantum.Symmetry.BellMixture

/-! # Bell Dicke -/


noncomputable section
namespace Quantum.Symmetry
open Matrix Quantum.Operators
open scoped Kronecker ComplexOrder
open private bellPerm_count_zero
  from QCryptLean.Quantum.Symmetry.BellDickeCore

/-- The symmetric projector entry is the inverse occupation multiplicity on an orbit. -/
theorem symmetricProjector_apply_eq_typeIndicator (k : ℕ) (i j : Fin k → Fin 4) :
    symmetricProjector (Fin 4) k i j =
      if bellTypeOfIndex i = bellTypeOfIndex j then
        (bellTypeMult k (bellTypeOfIndex i) : ℂ)⁻¹ else 0 := by
  classical
  have he : symmetricProjector (Fin 4) k i j = (k.factorial : ℂ)⁻¹ *
      ((Finset.univ.filter (fun σ : Equiv.Perm (Fin k) => i ∘ σ = j)).card : ℂ) := by
    simp only [symmetricProjector, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
      permutationRepresentation, tensorPermutation, Matrix.of_apply, eq_comp_symm_iff,
      Finset.sum_boole, one_div]
  rw [he]
  by_cases h : bellTypeOfIndex i = bellTypeOfIndex j
  · rw [ite_eq_left h]
    have hm : Finset.univ.val.map j = Finset.univ.val.map i := (congrArg Subtype.val h).symm
    have hp := Quantum.Symmetry.bellPerm_count_mul_orbit hm
    have ho : (Finset.univ.filter (fun f : Fin k → Fin 4 =>
        Finset.univ.val.map f = Finset.univ.val.map i)).card =
          bellTypeMult k (bellTypeOfIndex i) := by
      unfold bellTypeMult
      congr 1
      apply Finset.filter_congr
      intro f _
      constructor
      · exact fun h => Subtype.ext h
      · exact fun h => congrArg Subtype.val h
    rw [ho] at hp
    have hp' : ((Finset.univ.filter (fun σ : Equiv.Perm (Fin k) => i ∘ σ = j)).card : ℂ) *
        (bellTypeMult k (bellTypeOfIndex i) : ℂ) = (k.factorial : ℂ) := by exact_mod_cast hp
    have hn : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hn' := right_ne_zero_of_mul (hp' ▸ hn)
    apply (mul_right_cancel₀ hn')
    rw [mul_assoc, hp', inv_mul_cancel₀ hn, inv_mul_cancel₀ hn']
  · rw [ite_eq_right h]
    have hm : Finset.univ.val.map j ≠ Finset.univ.val.map i := by
      intro he
      exact h (Subtype.ext he.symm)
    rw [bellPerm_count_zero hm]
    simp

/-- Rotating between Bell labels and Boolean pairs preserves the symmetric projector. -/
theorem bellRotation_conjTranspose_symmetricProjector (k : ℕ) :
    (bellRotation k)ᴴ * symmetricProjector (Fin 4) k * bellRotation k =
      symmetricProjector (Bool × Bool) k := by
  have hc (σ : Equiv.Perm (Fin k)) :
      permutationRepresentation (X := Fin 4) σ * bellRotation k =
        bellRotation k * permutationRepresentation (X := Bool × Bool) σ :=
    tensorPermutation_mul_piTensorProduct_const σ bellSinglePairRotation
  have he : symmetricProjector (Fin 4) k * bellRotation k =
      bellRotation k * symmetricProjector (Bool × Bool) k := by
    simp only [symmetricProjector, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.sum_mul, Matrix.mul_sum, hc]
  rw [Matrix.mul_assoc, he, ← Matrix.mul_assoc, bellRotation_unitary, Matrix.one_mul]

/-- The unnormalized Dicke vectors resolve the symmetric projector. -/
theorem symmetricProjector_eq_bellDicke_resolution (k : ℕ) :
    symmetricProjector (Bool × Bool) k =
      ∑ T : Sym (Fin 4) k, (bellTypeMult k T : ℂ)⁻¹ • (bellDickeKet k T).projector := by
  classical
  let v (T : Sym (Fin 4) k) : (Fin k → Fin 4) → ℂ :=
    fun i => if bellTypeOfIndex i = T then 1 else 0
  have hc : (∑ T : Sym (Fin 4) k, (bellTypeMult k T : ℂ)⁻¹ •
      vecMulVec (v T) (star (v T))) = symmetricProjector (Fin 4) k := by
    ext i j
    rw [symmetricProjector_apply_eq_typeIndicator]
    simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, v,
      apply_ite (star : ℂ → ℂ), star_one, star_zero, smul_eq_mul]
    by_cases h : bellTypeOfIndex i = bellTypeOfIndex j
    · simp [h]
    · simp [mul_ite, h]
  rw [← bellRotation_conjTranspose_symmetricProjector k, ← hc, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro T _
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  change (bellRotation k)ᴴ * vecMulVec (v T) (star (v T)) * bellRotation k =
    vecMulVec ((bellRotation k)ᴴ *ᵥ v T) (star ((bellRotation k)ᴴ *ᵥ v T))
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.star_mulVec,
    conjTranspose_conjTranspose]

end Quantum.Symmetry
