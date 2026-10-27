import QCryptLean.Math.LinearAlgebra.Matrix.UnitaryGram
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceDuality
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification

/-! # Uhlmann -/


noncomputable section

namespace Quantum.Metrics

open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Uhlmann achievability with a fixed canonical source purification.
The target vector is on `X × X`; no enumeration occurs in the conclusion. -/
theorem exists_purification_overlap_re_eq_fidelity (A B : PosSemidefOp X) :
    ∃ v : Ket (X × X), Matrix.partialTraceRight v.projector = B.val ∧
      (A.purificationKet.dag * v : ℂ).re = fidelity A B := by
  classical
  let M := sqrtPosSemidefOp A * sqrtPosSemidefOp B
  obtain ⟨U, hU⟩ := Matrix.exists_unitary_mul_eq_sqrt_gram Mᴴ
  have hsA := isHermitian_sqrtPosSemidefOp A
  have hsB := isHermitian_sqrtPosSemidefOp B
  have hMM : M * Mᴴ = sqrtPosSemidefOp A * B.val * sqrtPosSemidefOp A := by
    dsimp [M]
    rw [conjTranspose_mul, hsA.eq, hsB.eq]
    rw [Matrix.mul_assoc (sqrtPosSemidefOp A), ← Matrix.mul_assoc (sqrtPosSemidefOp B),
      sqrtPosSemidefOp_mul_self, ← Matrix.mul_assoc]
  have he := congrArg Matrix.conjTranspose hU
  rw [conjTranspose_mul, conjTranspose_conjTranspose,
    (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (M * Mᴴ))).isHermitian.eq,
    hMM] at he
  refine ⟨Ket.vectorize (sqrtPosSemidefOp B * U.valᴴ), ?_, ?_⟩
  · rw [Ket.partialTraceRight_vectorize, conjTranspose_mul, conjTranspose_conjTranspose,
      hsB.eq]
    calc
      _ = sqrtPosSemidefOp B * (U.valᴴ * U.val) * sqrtPosSemidefOp B := by
        simp only [Matrix.mul_assoc]
      _ = B.val := by rw [show U.valᴴ * U.val = 1 from U.property.1,
        Matrix.mul_one, sqrtPosSemidefOp_mul_self]
  · change ((Ket.vectorize (sqrtPosSemidefOp A)).dag *
      Ket.vectorize (sqrtPosSemidefOp B * U.valᴴ) : ℂ).re = _
    rw [Ket.vectorize_inner, hsA.eq, ← Matrix.mul_assoc]
    exact congrArg (fun C => Matrix.trace C |>.re) he

/-- Every pair of square-ancilla purifications has overlap at most fidelity. -/
theorem norm_overlap_le_fidelity_of_partialTraceRight_eq (ρ σ : DensityOp X)
    (v w : Ket (X × X))
    (hv : Matrix.partialTraceRight v.projector = ρ.toOp)
    (hw : Matrix.partialTraceRight w.projector = σ.toOp) :
    ‖(v.dag * w : ℂ)‖ ≤ fidelity ρ.toPosSemidefOp σ.toPosSemidefOp := by
  let : Nonempty X := ρ.nonempty
  exact norm_overlap_le_fidelity ρ.toPosSemidefOp σ.toPosSemidefOp v w hv hw

/-- The real-overlap bound follows from the complex norm bound. -/
theorem re_overlap_le_fidelity_of_partialTraceRight_eq (ρ σ : DensityOp X)
    (v w : Ket (X × X))
    (hv : Matrix.partialTraceRight v.projector = ρ.toOp)
    (hw : Matrix.partialTraceRight w.projector = σ.toOp) :
    (v.dag * w : ℂ).re ≤ fidelity ρ.toPosSemidefOp σ.toPosSemidefOp :=
  (Complex.re_le_norm _).trans (norm_overlap_le_fidelity_of_partialTraceRight_eq ρ σ v w hv hw)

end Quantum.Metrics
