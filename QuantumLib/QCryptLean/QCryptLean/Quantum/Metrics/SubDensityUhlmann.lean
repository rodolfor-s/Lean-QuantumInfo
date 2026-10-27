import QCryptLean.Math.LinearAlgebra.Matrix.UnitaryGram
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceDuality
import QCryptLean.Quantum.Metrics.Uhlmann
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification

/-! # Sub Density Uhlmann -/


noncomputable section

namespace Quantum.Operators

open Matrix Quantum.Metrics

variable {X R : Type*} [Fintype X] [Fintype R]

/-- The overlap of live purification branches is bounded by ordinary fidelity.
This uses the native rectangular-polar estimate. -/
theorem SubDensityOp.livePurificationOverlap_norm_le_fidelity [Nonempty X]
    (ρ σ : SubDensityOp X) (v w : Ket (X × R))
    (hv : Matrix.partialTraceRight v.projector = ρ.toOp)
    (hw : Matrix.partialTraceRight w.projector = σ.toOp) :
    ‖(v.dag * w : ℂ)‖ ≤ fidelity ρ.toPosSemidefOp σ.toPosSemidefOp := by
  exact norm_overlap_le_fidelity ρ.toPosSemidefOp σ.toPosSemidefOp v w hv hw

/-- The real live-branch overlap bound follows from its complex norm bound. -/
theorem SubDensityOp.livePurificationOverlap_re_le_fidelity [Nonempty X]
    (ρ σ : SubDensityOp X) (v w : Ket (X × R))
    (hv : Matrix.partialTraceRight v.projector = ρ.toOp)
    (hw : Matrix.partialTraceRight w.projector = σ.toOp) :
    (v.dag * w : ℂ).re ≤ fidelity ρ.toPosSemidefOp σ.toPosSemidefOp :=
  (Complex.re_le_norm _).trans (ρ.livePurificationOverlap_norm_le_fidelity σ v w hv hw)

/-- Fixed-source Uhlmann achievability on a sufficiently large finite reference.
The proof uses native prerequisites. -/
theorem SubDensityOp.exists_livePurification_overlap_eq_fidelity_fixed_source
    (ρ σ : SubDensityOp X) (v : Ket (X × R))
    (hv : Matrix.partialTraceRight v.projector = ρ.toOp)
    (hdim : Fintype.card X ≤ Fintype.card R) :
    ∃ w : Ket (X × R), Matrix.partialTraceRight w.projector = σ.toOp ∧
      (v.dag * w : ℂ).re = fidelity ρ.toPosSemidefOp σ.toPosSemidefOp := by
  classical
  let V : Matrix X R ℂ := fun i r => v.vec (i, r)
  let S := sqrtPosSemidefOp ρ.toPosSemidefOp
  have hS : Sᴴ = S := (isHermitian_sqrtPosSemidefOp ρ.toPosSemidefOp).eq
  have hgram : S * Sᴴ = V * Vᴴ := by
    rw [hS, sqrtPosSemidefOp_mul_self]
    exact hv.symm
  obtain ⟨U, hU, hV⟩ := Matrix.exists_coisometry_of_rowGram_eq S V hgram hdim
  obtain ⟨w, hw, ho⟩ := exists_purification_overlap_re_eq_fidelity
    ρ.toPosSemidefOp σ.toPosSemidefOp
  let W : Matrix X X ℂ := fun i j => w.vec (i, j)
  refine ⟨Ket.vectorize (W * U), ?_, ?_⟩
  · rw [Ket.partialTraceRight_vectorize, conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc U Uᴴ, hU, Matrix.one_mul]
    exact hw
  · have he : (v.dag * Ket.vectorize (W * U) : ℂ) =
        (ρ.toPosSemidefOp.purificationKet.dag * w : ℂ) := by
      change ((Ket.vectorize V).dag * Ket.vectorize (W * U) : ℂ) = _
      rw [Ket.vectorize_inner, hV, conjTranspose_mul]
      calc
        _ = (Sᴴ * W * (U * Uᴴ)).trace := by
          rw [Matrix.mul_assoc, Matrix.trace_mul_comm Uᴴ]
          simp only [Matrix.mul_assoc]
        _ = (Sᴴ * W).trace := by rw [hU, Matrix.mul_one]
        _ = _ := (Ket.vectorize_inner S W).symm
    rw [he]
    exact ho

end Quantum.Operators
