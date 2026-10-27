import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Operators.Topology
import QCryptLean.Quantum.Symmetry.BellMixture

/-!
# Coherent Bell doubling on Boolean-pair registers

The copying map copies classical Bell labels. Conjugating it by the rectangular
Bell rotation gives a quantum isometry. No enumeration enters these definitions.
-/

noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators
open scoped Kronecker ComplexOrder

/-- Coherent copying of a classical Bell label. -/
def bellDoublingCopy : Matrix (Fin 4 × Fin 4) (Fin 4) ℂ :=
  fun i j => if i = (j, j) then 1 else 0

/-- Copying orthogonal labels is an isometry. -/
theorem bellDoublingCopy_conjTranspose_mul : bellDoublingCopyᴴ * bellDoublingCopy = 1 := by
  ext i j
  simp [Matrix.mul_apply, bellDoublingCopy, conjTranspose_apply, one_apply,
    eq_comm]

/-- The isometry that doubles an orthogonal Bell vector. -/
def bellDoublingIsometry : Matrix ((Bool × Bool) × (Bool × Bool)) (Bool × Bool) ℂ :=
  (bellSinglePairRotationᴴ ⊗ₖ bellSinglePairRotationᴴ) *
    bellDoublingCopy * bellSinglePairRotation

/-- Bell doubling preserves inner products. -/
theorem bellDoublingIsometry_isometry : bellDoublingIsometryᴴ * bellDoublingIsometry = 1 := by
  unfold bellDoublingIsometry
  simp only [conjTranspose_mul, conjTranspose_kronecker, conjTranspose_conjTranspose,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (bellSinglePairRotation ⊗ₖ bellSinglePairRotation),
    ← mul_kronecker_mul, bellSinglePairRotation_mul_conjTranspose, one_kronecker_one,
    Matrix.one_mul, ← Matrix.mul_assoc bellDoublingCopyᴴ, bellDoublingCopy_conjTranspose_mul,
    Matrix.one_mul, bellSinglePairRotation_conjTranspose_mul]

/-- Bell doubling as a state embedding, with the two output registers explicit. -/
def bellWembed (φ : DensityOp (Bool × Bool)) : DensityOp ((Bool × Bool) × (Bool × Bool)) where
  toOp := bellDoublingIsometry * φ.toOp * bellDoublingIsometryᴴ
  posSemidef := φ.posSemidef.mul_mul_conjTranspose_same _
  trace_one := by
    rw [trace_mul_cycle, bellDoublingIsometry_isometry, one_mul]
    exact φ.trace_one

/-- Bell doubling is continuous in the entries of the input state. -/
theorem continuous_bellWembed : Continuous bellWembed := by
  apply continuous_induced_rng.mpr
  exact (continuous_const.matrix_mul DensityOp.continuous_toOp).matrix_mul continuous_const

/-- Bell doubling preserves purity because its matrix is an isometry. -/
theorem bellWembed_isPure {φ : DensityOp (Bool × Bool)} (hφ : φ.IsPure) :
    (bellWembed φ).IsPure := by
  change (bellDoublingIsometry * φ.toOp * bellDoublingIsometryᴴ) *
    (bellDoublingIsometry * φ.toOp * bellDoublingIsometryᴴ) = _
  calc _ = bellDoublingIsometry * φ.toOp *
        (bellDoublingIsometryᴴ * bellDoublingIsometry) * φ.toOp * bellDoublingIsometryᴴ := by
          simp only [Matrix.mul_assoc]
       _ = bellDoublingIsometry * (φ.toOp * φ.toOp) * bellDoublingIsometryᴴ := by
          rw [bellDoublingIsometry_isometry]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
       _ = _ := by rw [hφ]; rfl

/-- Independent Bell doubling at each site. -/
def bellDoublingIsometryPow (k : ℕ) :
    Matrix (Fin k → (Bool × Bool) × (Bool × Bool)) (Fin k → Bool × Bool) ℂ :=
  piTensorProduct (fun _ => bellDoublingIsometry)

/-- Tensor powers preserve the Bell-doubling sandwich. -/
theorem bellWembed_tensorPow_toOp_eq_conj (k : ℕ) (φ : DensityOp (Bool × Bool)) :
    ((bellWembed φ).tensorPow k).toOp =
      bellDoublingIsometryPow k * (φ.tensorPow k).toOp * (bellDoublingIsometryPow k)ᴴ := by
  simp only [DensityOp.tensorPow, DensityOp.tensorFamily, bellDoublingIsometryPow,
    conjTranspose_piTensorProduct, piTensorProduct_mul]
  rfl

/-- The size of an occupation-type fiber, counted directly on words. -/
def bellTypeMult (k : ℕ) (T : Sym (Fin 4) k) : ℕ :=
  (Finset.univ.filter (fun i : Fin k → Fin 4 => bellTypeOfIndex i = T)).card

/-- The unnormalized Bell Dicke ket obtained by rotating an occupation indicator. -/
def bellDickeKet (k : ℕ) (T : Sym (Fin 4) k) : Ket (Fin k → Bool × Bool) :=
  ⟨(bellRotation k)ᴴ *ᵥ (fun i => if bellTypeOfIndex i = T then 1 else 0)⟩

end Quantum.Symmetry
