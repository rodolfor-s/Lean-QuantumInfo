import QCryptLean.Math.LinearAlgebra.Matrix.SqrtScale
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.Scaling
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.Extension
import QCryptLean.Quantum.Operators.StateOperations

/-! # Extension Metrics -/


noncomputable section

namespace Quantum.Operators

open scoped ComplexOrder MatrixOrder

open Matrix Quantum.Metrics

variable {X : Type*} [Fintype X] {n : ℕ}

/-- Generalized fidelity is ordinary fidelity after adding the abort outcome.
The direct-sum square-root identity computes both contributions. -/
theorem SubDensityOp.toDensityOpExtend_fidelity [Nonempty X] (ρ σ : SubDensityOp X) :
    fidelity ρ.toDensityOpExtend.toPosSemidefOp σ.toDensityOpExtend.toPosSemidefOp =
      fidelityGen ρ σ := by
  obtain ⟨_x⟩ := (inferInstance : Nonempty X)
  let A : PosSemidefOp Unit := ⟨ρ.defect • 1,
    Matrix.PosSemidef.one.smul (Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr ρ.trace_le_one, rfl⟩)⟩
  let B : PosSemidefOp Unit := ⟨σ.defect • 1,
    Matrix.PosSemidef.one.smul (Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr σ.trace_le_one, rfl⟩)⟩
  let U : PosSemidefOp Unit := ⟨1, Matrix.PosSemidef.one⟩
  have he : fidelity ρ.toDensityOpExtend.toPosSemidefOp σ.toDensityOpExtend.toPosSemidefOp =
      fidelity ρ.toPosSemidefOp σ.toPosSemidefOp + fidelity A B :=
    fidelity_fromBlocks_zero ρ.toPosSemidefOp σ.toPosSemidefOp A B
  rw [he,
    fidelity_smul_smul (sub_nonneg.mpr ρ.trace_le_one) (sub_nonneg.mpr σ.trace_le_one)
      U U A B rfl rfl]
  have hU : fidelity U U = 1 := by
    unfold fidelity sqrtPosSemidefOp
    simp [U]
  rw [hU, mul_one]
  rfl

/-- Generalized trace distance is ordinary trace distance of the extensions.
The direct-sum norm formula retains both factors one half. -/
theorem SubDensityOp.toDensityOpExtend_traceDistance (ρ σ : SubDensityOp X) :
    traceDistance ρ.extendOp σ.extendOp = traceDistanceGen ρ.toOp σ.toOp := by
  classical
  have he : ρ.extendOp - σ.extendOp = Matrix.fromBlocks (ρ.toOp - σ.toOp) 0 0
      ((ρ.defect - σ.defect) • (1 : Op Unit)) := by
    ext (i | i) (j | j) <;> simp [SubDensityOp.extendOp, sub_smul]
  have h1 : traceNorm (1 : Op Unit) = 1 := by
    rw [traceNorm_eq_trace_sqrt]
    simp
  have hd : ‖ρ.defect - σ.defect‖ = |(ρ.toOp.trace - σ.toOp.trace).re| := by
    rw [SubDensityOp.defect, SubDensityOp.defect, ← Complex.ofReal_sub, Complex.norm_real]
    change |1 - ρ.trace - (1 - σ.trace)| = |ρ.trace - σ.trace|
    rw [show 1 - ρ.trace - (1 - σ.trace) = -(ρ.trace - σ.trace) by ring, abs_neg]
  unfold traceDistance traceDistanceGen
  rw [he, traceNorm_fromBlocks_zero, traceNorm_smul, h1, mul_one, hd]
  unfold traceDistance
  ring

end Quantum.Operators
