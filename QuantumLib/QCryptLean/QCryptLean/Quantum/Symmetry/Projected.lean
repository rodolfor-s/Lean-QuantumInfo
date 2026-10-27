import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Projector
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Symmetry.Basic

/-! # Projected -/


noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators
open scoped ComplexOrder

variable {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ}

/-- A tensor power commutes with every site permutation. -/
theorem tensorPow_commute_permutationRepresentation (A : Op X) (σ : Equiv.Perm (Fin k)) :
    Commute (Op.tensorPow A k) (permutationRepresentation σ) := by
  have h := tensorPermutation_conj_piTensorProduct σ (fun _ => A)
  have hu := (tensorPermutation_unitary (X := X) (R := ℂ) σ).1
  have hh := congrArg (fun B => B * tensorPermutation (X := X) (R := ℂ) σ) h
  simp only [Matrix.mul_assoc, hu, mul_one] at hh
  exact hh.symm

/-- Every tensor power commutes with the symmetric projector. -/
theorem tensorPow_commute_symmetricProjector (A : Op X) :
    Commute (Op.tensorPow A k) (symmetricProjector X k) := by
  exact (Commute.sum_right Finset.univ _ _
    (fun σ _ => tensorPow_commute_permutationRepresentation A σ)).smul_right _

/-- Compress the symmetric projector to the tensor power of a projected register. -/
def projectedSymmetricProjector (P : Op X) (k : ℕ) : Op (Fin k → X) :=
  Op.tensorPow P k * symmetricProjector X k * (Op.tensorPow P k)ᴴ

/-- The compression is positive for every compression matrix. -/
theorem projectedSymmetricProjector_posSemidef (P : Op X) (k : ℕ) :
    (projectedSymmetricProjector P k).PosSemidef :=
  symmetricProjector_posSemidef.mul_mul_conjTranspose_same _

/-- For an orthogonal projection the compression simplifies to a commuting product. -/
theorem projectedSymmetricProjector_eq (P : Op X) (hP : IsOrthogonalProjector P) :
    projectedSymmetricProjector P k = Op.tensorPow P k * symmetricProjector X k := by
  have hPP : Op.tensorPow P k * Op.tensorPow P k = Op.tensorPow P k := by
    change piTensorProduct (fun _ => P) * piTensorProduct (fun _ => P) = _
    rw [piTensorProduct_mul]
    simp only [hP.2]
    rfl
  have hPH : (Op.tensorPow P k)ᴴ = Op.tensorPow P k := by
    change (piTensorProduct (fun _ => P))ᴴ = _
    rw [conjTranspose_piTensorProduct]
    simp only [hP.1.eq]
    rfl
  rw [projectedSymmetricProjector, hPH, Matrix.mul_assoc,
    ← (tensorPow_commute_symmetricProjector P).eq, ← Matrix.mul_assoc, hPP]

end Quantum.Symmetry
