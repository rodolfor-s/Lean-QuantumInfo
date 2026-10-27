import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDCumulative
import QCryptLean.InfoTheory.SmoothMinEntropy.Measurement
import QCryptLean.InfoTheory.SmoothMinEntropy.SpectralCapBasis
import QCryptLean.InfoTheory.SmoothMinEntropy.SpectralCapCoefficients
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Projector

/-! # Positive capped blocks and their feasible reference bound -/
noncomputable section
namespace InfoTheory.SmoothMinEntropy.SpectralCap
open Matrix Quantum.Operators
open _root_.InfoTheory.SmoothMinEntropy.RankOneProjectiveBasis
open InfoTheory.SmoothMinEntropy.AEP.IID.Cumulative
open scoped ComplexOrder MatrixOrder
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Renner's capped block, formed from projected eigenvectors on the original register. -/
def block (A σ : PosSemidefOp Q) (ell : ℝ) : Op Q :=
  ∑ i : Q, ∑ z, (coefficient σ (A.property.isHermitian.eigenvalues i) ell z : ℂ) •
    (cumulativeProjector σ z * proj A.property.isHermitian.eigenvectorBasis i *
      cumulativeProjector σ z)

/-- Capping preserves positivity. -/
theorem block_posSemidef (A σ : PosSemidefOp Q) {ell : ℝ} (hell : 0 ≤ ell) :
    (block A σ ell).PosSemidef := by
  apply posSemidef_sum
  intro i _
  apply posSemidef_sum
  intro z _
  apply PosSemidef.smul
  · simpa only [proj, (cumulativeProjector_isOrthogonalProjector σ z).isHermitian.eq] using
      PosSemidef.conjTranspose_mul_mul_same
        (Ket.posSemidef_projector (vec A.property.isHermitian.eigenvectorBasis i))
        (cumulativeProjector σ z)
  · exact Complex.zero_le_real.mpr (coefficient_nonneg σ (A.property.eigenvalues_nonneg i) hell z)

/-- The capped block is dominated by the requested multiple of its reference. -/
theorem block_le_reference (A σ : PosSemidefOp Q) {ell : ℝ} (hell : 0 ≤ ell) :
    block A σ ell ≤ (ell : ℂ) • σ.val := by
  have he : (ell : ℂ) • σ.val = ∑ i : Q, ∑ z,
      (ell * betaIncr (eigenvalue σ) z : ℝ) •
        (cumulativeProjector σ z * proj A.property.isHermitian.eigenvectorBasis i *
          cumulativeProjector σ z) := by
    conv_lhs => rw [reference_eq_sum_cumulative σ]
    rw [Finset.smul_sum, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    have hr : cumulativeProjector σ z = ∑ i : Q,
        cumulativeProjector σ z * proj A.property.isHermitian.eigenvectorBasis i *
          cumulativeProjector σ z := by
      rw [← Finset.sum_mul, ← Matrix.mul_sum, sum_proj, mul_one]
      exact (cumulativeProjector_isOrthogonalProjector σ z).idempotent.symm
    rw [smul_smul, ← Complex.ofReal_mul]
    conv_lhs => rw [hr]
    rw [Finset.smul_sum]
    ext a b
    simp [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul]
  apply Matrix.le_iff.mpr
  rw [he, block, ← Finset.sum_sub_distrib]
  apply posSemidef_sum
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply posSemidef_sum
  intro z _
  have hP := PosSemidef.conjTranspose_mul_mul_same
    (Ket.posSemidef_projector (vec A.property.isHermitian.eigenvectorBasis i))
    (cumulativeProjector σ z)
  rw [(cumulativeProjector_isOrthogonalProjector σ z).isHermitian.eq] at hP
  have hsmul (a : ℝ) (M : Op Q) : a • M = (a : ℂ) • M := by
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul]
  rw [hsmul, ← sub_smul, ← Complex.ofReal_sub]
  exact hP.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr (coefficient_le σ hell z)))

/-- Capping cannot increase the trace of a positive block. -/
theorem trace_block_le (A σ : PosSemidefOp Q) {ell : ℝ} (hell : 0 ≤ ell) :
    (block A σ ell).trace.re ≤ A.val.trace.re := by
  rw [A.property.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
  unfold block
  rw [trace_sum, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [trace_sum, Complex.re_sum]
  have hp : (proj A.property.isHermitian.eigenvectorBasis i).trace.re = 1 := by
    rw [proj, Ket.trace_projector, inner_vec, ite_eq_left rfl, Complex.one_re]
  have hb (z : Fin (Fintype.card Q)) :=
    (cumulativeProjector_isOrthogonalProjector σ z).re_trace_sandwich_le
      (Ket.posSemidef_projector (vec A.property.isHermitian.eigenvectorBasis i))
  change ∀ z, (cumulativeProjector σ z * proj A.property.isHermitian.eigenvectorBasis i *
      cumulativeProjector σ z).trace.re ≤
    (proj A.property.isHermitian.eigenvectorBasis i).trace.re at hb
  simp only [hp] at hb
  calc
    _ ≤ ∑ z, coefficient σ (A.property.isHermitian.eigenvalues i) ell z := by
      apply Finset.sum_le_sum
      intro z _
      rw [trace_smul]
      simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      exact mul_le_of_le_one_right
        (coefficient_nonneg σ (A.property.eigenvalues_nonneg i) hell z) (hb z)
    _ ≤ _ := sum_coefficient_le σ (A.property.eigenvalues_nonneg i) ell

end InfoTheory.SmoothMinEntropy.SpectralCap
