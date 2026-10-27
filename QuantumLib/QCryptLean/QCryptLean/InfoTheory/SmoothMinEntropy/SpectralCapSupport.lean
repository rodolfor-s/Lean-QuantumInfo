import QCryptLean.InfoTheory.SmoothMinEntropy.Measurement
import QCryptLean.InfoTheory.SmoothMinEntropy.SpectralCapBasis
import QCryptLean.InfoTheory.SmoothMinEntropy.SpectralCapDefect
import QCryptLean.Math.LinearAlgebra.Matrix.PositiveTrace
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.BraKet

/-! # Singular-reference support in spectral cap weights -/
namespace InfoTheory.SmoothMinEntropy.SpectralCap
open Matrix Quantum.Operators
open _root_.InfoTheory.SmoothMinEntropy.RankOneProjectiveBasis
open scoped ComplexOrder MatrixOrder
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Domination eliminates every spectral weight outside the reference support. -/
theorem weighted_overlap_eq_zero (A σ : PosSemidefOp Q) {t : ℝ}
    (h : A.val ≤ (t : ℂ) • σ.val) (i : Q) (z : Fin (Fintype.card Q))
    (hz : eigenvalue σ z = 0) :
    A.property.isHermitian.eigenvalues i *
      (proj A.property.isHermitian.eigenvectorBasis i * eigenprojector σ z).trace.re = 0 := by
  have hP : (eigenprojector σ z).PosSemidef :=
    Ket.posSemidef_projector (vec σ.property.isHermitian.eigenvectorBasis (labels σ z))
  have hact : σ.val * eigenprojector σ z = (eigenvalue σ z : ℂ) • eigenprojector σ z := by
    change σ.val * vecMulVec
      ((σ.property.isHermitian.eigenvectorBasis (labels σ z)).ofLp)
      (star (σ.property.isHermitian.eigenvectorBasis (labels σ z)).ofLp) =
        (σ.property.isHermitian.eigenvalues (labels σ z) : ℂ) •
          vecMulVec ((σ.property.isHermitian.eigenvectorBasis (labels σ z)).ofLp)
            (star (σ.property.isHermitian.eigenvectorBasis (labels σ z)).ofLp)
    rw [Matrix.mul_vecMulVec, σ.property.isHermitian.mulVec_eigenvectorBasis]
    ext a b
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
      Complex.real_smul, mul_assoc]
  have ht := (Complex.nonneg_iff.mp
    ((Matrix.le_iff.mp h).trace_mul_nonneg hP)).1
  rw [sub_mul, trace_sub, Complex.sub_re, Matrix.smul_mul, hact, hz] at ht
  simp only [Complex.ofReal_zero, zero_smul, smul_zero, trace_zero, Complex.zero_re,
    zero_sub, neg_nonneg] at ht
  have ht0 : (A.val * eigenprojector σ z).trace.re = 0 :=
    le_antisymm ht (Complex.nonneg_iff.mp (A.property.trace_mul_nonneg hP)).1
  have ha : A.val = ∑ j, (A.property.isHermitian.eigenvalues j : ℂ) •
      proj A.property.isHermitian.eigenvectorBasis j := by
    rw [← Equiv.sum_comp (labels A)]
    exact (sum_eigenvalue_smul_eigenprojector A).symm
  rw [ha, Finset.sum_mul, trace_sum, Complex.re_sum] at ht0
  simp only [Matrix.smul_mul, trace_smul, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at ht0
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
    mul_nonneg (A.property.eigenvalues_nonneg j) (overlap_nonneg A σ j z))).mp ht0 i
      (Finset.mem_univ i)

end InfoTheory.SmoothMinEntropy.SpectralCap
