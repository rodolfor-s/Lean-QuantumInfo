import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.QKD.BB84.Model.TwoBasisMeasurement
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Gates
import QCryptLean.Quantum.Symmetry.Basic

/-! # Sift Operation -/


open Quantum.Operators Quantum.Symmetry Matrix
open QKD.BB84.Measurement
open scoped Matrix ComplexConjugate

noncomputable section

namespace QKD.BB84.Model

/-- The local BB84 sift/permutation operator `F U_π` on `n` qubit rounds. -/
def siftPermHalf (n : ℕ) (peSel xSel : Fin n → Bool) (π : Equiv.Perm (Fin n)) : Op (Bits n) :=
  piTensorProduct (fun a => if peSel a && xSel a then
    reindex finTwoEquiv.symm finTwoEquiv.symm Quantum.Gates.hadamard
    else (1 : Op Bit)) *
    permutationRepresentation π

/-- One party's factor of the quantum prefix is unitary — a product of a tensor family of
Hadamards and identities with a permutation representation, both unitary. -/
theorem siftPermHalf_unitary (n : ℕ) (peSel xSel : Fin n → Bool) (π : Equiv.Perm (Fin n)) :
    (siftPermHalf n peSel xSel π)ᴴ * siftPermHalf n peSel xSel π = 1 := by
  have hfam : ∀ a : Fin n,
      (if peSel a && xSel a then
        reindex finTwoEquiv.symm finTwoEquiv.symm Quantum.Gates.hadamard
      else (1 : Op Bit))ᴴ *
      (if peSel a && xSel a then
        reindex finTwoEquiv.symm finTwoEquiv.symm Quantum.Gates.hadamard
      else (1 : Op Bit)) = 1 := by
    intro a
    split_ifs
    · simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
        Matrix.submatrix_mul_equiv, Quantum.Gates.hadamard_unitary,
        Matrix.submatrix_one_equiv]
    · simp
  have hA : (piTensorProduct (fun a => if peSel a && xSel a then
      reindex finTwoEquiv.symm finTwoEquiv.symm Quantum.Gates.hadamard
      else (1 : Op Bit)))ᴴ *
      piTensorProduct (fun a => if peSel a && xSel a then
        reindex finTwoEquiv.symm finTwoEquiv.symm Quantum.Gates.hadamard
        else (1 : Op Bit)) = 1 := by
    rw [conjTranspose_piTensorProduct, piTensorProduct_mul]
    simp only [hfam, piTensorProduct_one]
  unfold siftPermHalf
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc _ _ (permutationRepresentation π), hA, Matrix.one_mul]
  exact (tensorPermutation_unitary π).1

end QKD.BB84.Model
