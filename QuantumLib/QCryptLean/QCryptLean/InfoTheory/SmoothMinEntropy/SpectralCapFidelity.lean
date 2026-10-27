import QCryptLean.InfoTheory.SmoothMinEntropy.Measurement
import QCryptLean.InfoTheory.SmoothMinEntropy.SpectralCapBasis
import QCryptLean.InfoTheory.SmoothMinEntropy.SpectralCapBlock
import QCryptLean.InfoTheory.SmoothMinEntropy.SpectralCapCoefficients
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.Flagged
import QCryptLean.Quantum.Metrics.ProjectionMixture
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Projector

/-! # Fidelity retained by spectral capping -/
noncomputable section
namespace InfoTheory.SmoothMinEntropy.SpectralCap
open Matrix Quantum.Operators Quantum.Metrics
open _root_.InfoTheory.SmoothMinEntropy.RankOneProjectiveBasis
open scoped ComplexOrder MatrixOrder
variable {Q : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]

/-- Spectral capping retains at least the capped trace as fidelity. -/
theorem trace_block_le_fidelity (A σ : PosSemidefOp Q) {ell : ℝ} (hell : 0 ≤ ell) :
    (block A σ ell).trace.re ≤ fidelity A ⟨block A σ ell, block_posSemidef A σ hell⟩ := by
  let T : Q × Fin (Fintype.card Q) → PosSemidefOp Q := fun iz =>
    ⟨(coefficient σ (A.property.isHermitian.eigenvalues iz.1) ell iz.2 : ℂ) •
      proj A.property.isHermitian.eigenvectorBasis iz.1,
      (Ket.posSemidef_projector (vec A.property.isHermitian.eigenvectorBasis iz.1)).smul
        (Complex.zero_le_real.mpr
          (coefficient_nonneg σ (A.property.eigenvalues_nonneg iz.1) hell iz.2))⟩
  let P : Q × Fin (Fintype.card Q) → Op Q := fun iz => cumulativeProjector σ iz.2
  have hP (iz : Q × Fin (Fintype.card Q)) : IsOrthogonalProjector (P iz) :=
    cumulativeProjector_isOrthogonalProjector σ iz.2
  have ha : (∑ i, (A.property.isHermitian.eigenvalues i : ℂ) •
      proj A.property.isHermitian.eigenvectorBasis i) = A.val := by
    rw [← Equiv.sum_comp (labels A)]
    exact sum_eigenvalue_smul_eigenprojector A
  have hle : (∑ iz, (T iz).val) ≤ A.val := by
    rw [Fintype.sum_prod_type, ← ha]
    apply Finset.sum_le_sum
    intro i _
    change (∑ z, (coefficient σ (A.property.isHermitian.eigenvalues i) ell z : ℂ) •
      proj A.property.isHermitian.eigenvectorBasis i) ≤ _
    rw [← Finset.sum_smul, ← Complex.ofReal_sum]
    apply Matrix.le_iff.mpr
    rw [← sub_smul, ← Complex.ofReal_sub]
    exact (Ket.posSemidef_projector (vec A.property.isHermitian.eigenvectorBasis i)).smul
      (Complex.zero_le_real.mpr (sub_nonneg.mpr
        (sum_coefficient_le σ (A.property.eigenvalues_nonneg i) ell)))
  have he : (∑ iz, P iz * (T iz).val * P iz) = block A σ ell := by
    simp only [P, T, Fintype.sum_prod_type, Matrix.mul_smul, Matrix.smul_mul, block]
  have h := sum_trace_projectorSandwich_le_fidelity T P hP A hle
  have hs : sumPosSemidefOp Finset.univ (fun iz =>
      (⟨P iz * (T iz).val * P iz, by
        simpa only [(hP iz).isHermitian.eq] using
          (T iz).property.conjTranspose_mul_mul_same (P iz)⟩ : PosSemidefOp Q)) =
        ⟨block A σ ell, block_posSemidef A σ hell⟩ := by
    apply Subtype.ext
    simpa [sumPosSemidefOp] using he
  rw [hs, ← Complex.re_sum, ← trace_sum, he] at h
  exact h

end InfoTheory.SmoothMinEntropy.SpectralCap
