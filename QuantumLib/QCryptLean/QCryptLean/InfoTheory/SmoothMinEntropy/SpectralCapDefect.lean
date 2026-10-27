import QCryptLean.InfoTheory.SmoothMinEntropy.Measurement
import QCryptLean.InfoTheory.SmoothMinEntropy.SpectralCapBasis
import QCryptLean.InfoTheory.SmoothMinEntropy.SpectralCapBlock
import QCryptLean.InfoTheory.SmoothMinEntropy.SpectralCapCoefficients
import QCryptLean.Math.LinearAlgebra.Matrix.PositiveTrace
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Projector

/-! # Exact trace accounting and discarded spectral mass for a capped block -/
namespace InfoTheory.SmoothMinEntropy.SpectralCap
open Matrix Quantum.Operators
open _root_.InfoTheory.SmoothMinEntropy.RankOneProjectiveBasis
open scoped ComplexOrder MatrixOrder
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Eigenprojector overlaps are nonnegative trace pairings. -/
theorem overlap_nonneg (A σ : PosSemidefOp Q) (i : Q) (z : Fin (Fintype.card Q)) :
    0 ≤ (proj A.property.isHermitian.eigenvectorBasis i * eigenprojector σ z).trace.re :=
  (Complex.nonneg_iff.mp ((Ket.posSemidef_projector
    (vec A.property.isHermitian.eigenvectorBasis i)).trace_mul_nonneg
      (Ket.posSemidef_projector (vec σ.property.isHermitian.eigenvectorBasis (labels σ z))))).1

/-- Each input eigenvector has total reference overlap one. -/
theorem sum_overlap (A σ : PosSemidefOp Q) (i : Q) :
    (∑ z, (proj A.property.isHermitian.eigenvectorBasis i * eigenprojector σ z).trace.re) = 1 := by
  rw [← Complex.re_sum, ← trace_sum, ← Matrix.mul_sum, sum_eigenprojector, mul_one]
  rw [proj, Ket.trace_projector, inner_vec, ite_eq_left rfl, Complex.one_re]

/-- Cumulative projection traces telescope to capped eigenvalue-weighted overlaps. -/
theorem trace_block_eq (A σ : PosSemidefOp Q) (ell : ℝ) :
    (block A σ ell).trace.re = ∑ i, ∑ z,
      min (A.property.isHermitian.eigenvalues i) (ell * eigenvalue σ z) *
        (proj A.property.isHermitian.eigenvectorBasis i * eigenprojector σ z).trace.re := by
  unfold block
  rw [trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [trace_sum, Complex.re_sum]
  have he (z : Fin (Fintype.card Q)) :
      (cumulativeProjector σ z * proj A.property.isHermitian.eigenvectorBasis i *
        cumulativeProjector σ z).trace.re =
        ∑ j ∈ Finset.univ.filter (fun j => z ≤ j),
          (proj A.property.isHermitian.eigenvectorBasis i * eigenprojector σ j).trace.re := by
    rw [trace_mul_cycle, (cumulativeProjector_isOrthogonalProjector σ z).idempotent,
      trace_mul_comm, cumulativeProjector, Matrix.mul_sum, trace_sum, Complex.re_sum]
  simp only [trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, he, Finset.mul_sum]
  have hswap : (∑ z, ∑ j ∈ Finset.univ.filter (fun j => z ≤ j),
      coefficient σ (A.property.isHermitian.eigenvalues i) ell z *
        (proj A.property.isHermitian.eigenvectorBasis i * eigenprojector σ j).trace.re) =
      ∑ j, ∑ z ∈ Finset.univ.filter (fun z => z ≤ j),
        coefficient σ (A.property.isHermitian.eigenvalues i) ell z *
          (proj A.property.isHermitian.eigenvectorBasis i * eigenprojector σ j).trace.re := by
    apply Finset.sum_comm'
    intro z j
    simp [Finset.mem_filter]
  rw [hswap]
  simp only [← Finset.sum_mul, partialSum_coefficient]

/-- The cap's trace deficit is bounded by its over-threshold spectral mass. -/
theorem trace_sub_block_le (A σ : PosSemidefOp Q) {ell : ℝ} (hell : 0 ≤ ell) :
    A.val.trace.re - (block A σ ell).trace.re ≤
      ∑ i, ∑ z, if ell * eigenvalue σ z < A.property.isHermitian.eigenvalues i then
        A.property.isHermitian.eigenvalues i *
          (proj A.property.isHermitian.eigenvectorBasis i * eigenprojector σ z).trace.re
      else 0 := by
  rw [A.property.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum,
    trace_block_eq, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hi : A.property.isHermitian.eigenvalues i = ∑ z,
      A.property.isHermitian.eigenvalues i *
        (proj A.property.isHermitian.eigenvectorBasis i * eigenprojector σ z).trace.re := by
    rw [← Finset.mul_sum, sum_overlap, mul_one]
  change A.property.isHermitian.eigenvalues i - _ ≤ _
  conv_lhs => lhs; rw [hi]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro z _
  by_cases hz : ell * eigenvalue σ z < A.property.isHermitian.eigenvalues i
  · rw [ite_eq_left hz, min_eq_right hz.le]
    exact sub_le_self _ (mul_nonneg (mul_nonneg hell (eigenvalue_nonneg σ z))
      (overlap_nonneg A σ i z))
  · rw [ite_eq_right hz, min_eq_left (le_of_not_gt hz), sub_self]

end InfoTheory.SmoothMinEntropy.SpectralCap
