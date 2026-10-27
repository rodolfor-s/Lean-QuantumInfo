import QCryptLean.Math.LinearAlgebra.Matrix.EntryIntegral
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.Probability.MatrixHaarAverage
import QCryptLean.Math.Probability.UnitaryHaar
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.EmbeddedPurification
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Symmetry.EmbeddedEntanglement
import QCryptLean.Quantum.Symmetry.EmbeddedEntanglementAlgebra
import QCryptLean.Quantum.Symmetry.HaarFlatten
import QCryptLean.Quantum.Symmetry.Paired
import QCryptLean.Quantum.Symmetry.TensorUnitaryCommutant

/-! # Tensor moments of embedded purifications -/
noncomputable section
namespace Quantum.Operators
open Matrix Quantum.Symmetry MeasureTheory
open scoped Kronecker MatrixOrder ComplexOrder
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- Grouping purification tensor powers gives the filtered entangled vector. -/
theorem DensityOp.reindex_tensorPow_embeddedPurification (ρ : DensityOp X) (e : X ↪ Y)
    (U : unitaryGroup Y ℂ) (k : ℕ) :
    Matrix.reindex (pairFunctions X Y k) (pairFunctions X Y k)
      ((ρ.embeddedPurification e U).tensorPow k).toOp =
      (Op.tensorPow (CFC.sqrt ρ.toOp) k ⊗ₖ Op.tensorPow U.val k) *
        (embeddedMaxEntangled (e.arrowCongrRight : (Fin k → X) ↪ (Fin k → Y))).projector *
        (Op.tensorPow (CFC.sqrt ρ.toOp) k ⊗ₖ Op.tensorPow U.val k)ᴴ := by
  let f := reindexAlgEquiv ℂ ℂ (pairFunctions X Y k)
  change f (piTensorProduct (fun _ : Fin k => (ρ.embeddedPurification e U).toOp)) = _
  simp only [ρ.embeddedPurification_toOp, ← piTensorProduct_mul,
    ← conjTranspose_piTensorProduct]
  rw [map_mul, map_mul]
  have hK : f (piTensorProduct (fun _ : Fin k => CFC.sqrt ρ.toOp ⊗ₖ U.val)) =
      Op.tensorPow (CFC.sqrt ρ.toOp) k ⊗ₖ Op.tensorPow U.val k :=
    reindex_piTensorProduct_kronecker _ _
  have hΘ : f (piTensorProduct (fun _ : Fin k => (embeddedMaxEntangled e).projector)) =
      (embeddedMaxEntangled (e.arrowCongrRight : (Fin k → X) ↪ (Fin k → Y))).projector := by
    rw [← Ket.projector_tensorFamily]
    change ((Ket.tensorFamily (fun _ : Fin k => embeddedMaxEntangled e)).reindex
      (pairFunctions X Y k)).projector = _
    rw [tensorFamily_embeddedMaxEntangled_reindex]
  rw [hK, hΘ]
  change _ * _ * Matrix.reindex _ _ _ᴴ = _
  rw [← conjTranspose_reindex]
  exact congrArg (fun M => _ * Mᴴ) hK

/-- The Haar tensor moment is a fixed square-root sandwich of the entangled Haar average. -/
theorem DensityOp.integral_tensorPow_embeddedPurification (ρ : DensityOp X) (e : X ↪ Y)
    (k : ℕ) :
    (of fun i j => ∫ U, Matrix.reindex (pairFunctions X Y k) (pairFunctions X Y k)
      ((ρ.embeddedPurification e U).tensorPow k).toOp i j ∂UnitaryGroup.haarProbUnitary Y) =
      (Op.tensorPow (CFC.sqrt ρ.toOp) k ⊗ₖ (1 : Op (Fin k → Y))) *
        unitaryHaarAverage (tensorUnitaryRepresentation (Fin k → X) Y k)
          (embeddedMaxEntangled (e.arrowCongrRight : (Fin k → X) ↪ (Fin k → Y))).projector *
        (Op.tensorPow (CFC.sqrt ρ.toOp) k ⊗ₖ (1 : Op (Fin k → Y)))ᴴ := by
  let V := tensorUnitaryRepresentation (Fin k → X) Y k
  let S := Op.tensorPow (CFC.sqrt ρ.toOp) k ⊗ₖ (1 : Op (Fin k → Y))
  let Θ := (embeddedMaxEntangled (e.arrowCongrRight : (Fin k → X) ↪ (Fin k → Y))).projector
  change _ = S * unitaryHaarAverage V Θ * Sᴴ
  rw [unitaryHaarAverage, sandwich_entryIntegral S
    (integrable_unitary_conjugate V (continuous_tensorUnitaryRepresentation _ _ _) Θ)]
  ext i j
  apply integral_congr_ae
  filter_upwards [] with U
  rw [ρ.reindex_tensorPow_embeddedPurification]
  have hK : S * (V U).val = Op.tensorPow (CFC.sqrt ρ.toOp) k ⊗ₖ Op.tensorPow U.val k := by
    change (_ ⊗ₖ (1 : Op (Fin k → Y))) * ((1 : Op (Fin k → X)) ⊗ₖ _) = _
    rw [← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have he : S * ((V U).val * Θ * (V U).valᴴ) * Sᴴ =
      (S * (V U).val) * Θ * (S * (V U).val)ᴴ := by
    rw [conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [he, hK]

end Quantum.Operators
