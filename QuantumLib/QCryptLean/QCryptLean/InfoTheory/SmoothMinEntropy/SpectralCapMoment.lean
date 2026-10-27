import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDChernoffTail
import QCryptLean.InfoTheory.SmoothMinEntropy.Measurement
import QCryptLean.InfoTheory.SmoothMinEntropy.SpectralCapBasis
import QCryptLean.InfoTheory.SmoothMinEntropy.SpectralCapBlock
import QCryptLean.InfoTheory.SmoothMinEntropy.SpectralCapDefect
import QCryptLean.InfoTheory.SmoothMinEntropy.SpectralCapSupport
import QCryptLean.Math.SpectralTheory.MatrixCFC
import QCryptLean.Quantum.Operators.Algebra

/-! # Native spectral-cap moment bound

The scalar Chernoff inequality is reused unchanged. CFC powers and their spectral
expansions act on the original finite register; star order is scoped locally.
-/
namespace InfoTheory.SmoothMinEntropy.SpectralCap
open Matrix Quantum.Operators
open _root_.InfoTheory.SmoothMinEntropy.RankOneProjectiveBasis
open scoped ComplexOrder MatrixOrder
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- A positive cap scale bounds discarded trace by any nonnegative tilted moment. -/
theorem trace_sub_block_le_moment (A σ : PosSemidefOp Q) {t ell s : ℝ}
    (h : A.val ≤ (t : ℂ) • σ.val) (hell : 0 < ell) (hs : 0 ≤ s) :
    A.val.trace.re - (block A σ ell).trace.re ≤
      ell ^ (-s) * (A.val ^ (1 + s) * σ.val ^ (-s)).trace.re := by
  have he : (A.val ^ (1 + s) * σ.val ^ (-s)).trace.re = ∑ i, ∑ z,
      A.property.isHermitian.eigenvalues i ^ (1 + s) * eigenvalue σ z ^ (-s) *
        (proj A.property.isHermitian.eigenvectorBasis i * eigenprojector σ z).trace.re := by
    rw [Math.SpectralTheory.trace_cfcRpow_mul_cfcRpow_eq_eigen_double_sum
      A.property σ.property, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.re_sum, ← Equiv.sum_comp (labels σ)]
    apply Finset.sum_congr rfl
    intro z _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      zero_mul, sub_zero, Complex.mul_im, add_zero]
    rfl
  rw [he, Finset.mul_sum]
  apply (trace_sub_block_le A σ hell.le).trans
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  have hsup (hp : 0 < A.property.isHermitian.eigenvalues i) (hz : eigenvalue σ z = 0) :
      (proj A.property.isHermitian.eigenvectorBasis i * eigenprojector σ z).trace.re = 0 :=
    (mul_eq_zero.mp (weighted_overlap_eq_zero A σ h i z hz)).resolve_left hp.ne'
  simpa only [neg_neg] using InfoTheory.SmoothMinEntropy.chernoff_termwise_bound
    (A.property.isHermitian.eigenvalues i)
    (proj A.property.isHermitian.eigenvectorBasis i * eigenprojector σ z).trace.re
    ell (eigenvalue σ z) (-s) (A.property.eigenvalues_nonneg i)
    (overlap_nonneg A σ i z) hell (eigenvalue_nonneg σ z) (neg_nonpos.mpr hs) hsup

end InfoTheory.SmoothMinEntropy.SpectralCap
