import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Symmetry.BellDoubling
import QCryptLean.Quantum.Symmetry.BellMixture

/-! # Coherent Bell copying and vectorized type projectors -/
noncomputable section
namespace Quantum.Symmetry
open Matrix Quantum.Operators
open scoped Kronecker

private theorem bellDoublingIsometry_mul_rotation_adjoint :
    bellDoublingIsometry * bellSinglePairRotationᴴ =
      Matrix.of (fun p i => bellSinglePairRotationᴴ p.1 i * bellSinglePairRotationᴴ p.2 i) := by
  rw [bellDoublingIsometry, Matrix.mul_assoc, Matrix.mul_assoc,
    bellSinglePairRotation_mul_conjTranspose, Matrix.mul_one]
  ext ⟨p, q⟩ i
  simp [Matrix.mul_apply, bellDoublingCopy, kroneckerMap_apply]

private theorem bellDoublingIsometryPow_mul_rotation_adjoint (k : ℕ)
    (p : Fin k → (Bool × Bool) × (Bool × Bool)) (i : Fin k → Fin 4) :
    (bellDoublingIsometryPow k * (bellRotation k)ᴴ) p i =
      (bellRotation k)ᴴ (fun a => (p a).1) i *
        (bellRotation k)ᴴ (fun a => (p a).2) i := by
  rw [bellDoublingIsometryPow, bellRotation, conjTranspose_piTensorProduct, piTensorProduct_mul]
  simp only [bellDoublingIsometry_mul_rotation_adjoint, piTensorProduct_apply, of_apply]
  exact Finset.prod_mul_distrib

/-- Doubling a Dicke vector gives the vectorization of its Bell-type sector projector. -/
theorem bellDoubling_dicke_vectorize (k : ℕ) (T : Sym (Fin 4) k)
    (p q : Fin k → Bool × Bool) :
    (bellDoublingIsometryPow k *ᵥ (bellDickeKet k T).vec) (fun a => (p a, q a)) =
      bellTypeProjector k T p q := by
  change (bellDoublingIsometryPow k *ᵥ ((bellRotation k)ᴴ *ᵥ
    (fun i => if bellTypeOfIndex i = T then 1 else 0))) _ = _
  rw [Matrix.mulVec_mulVec]
  simp only [mulVec, dotProduct, bellDoublingIsometryPow_mul_rotation_adjoint]
  rw [bellTypeProjector, bellTypeDiagProjector, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  simp only [conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [bellRotation_star]
  split_ifs <;> simp [mul_comm]

end Quantum.Symmetry
