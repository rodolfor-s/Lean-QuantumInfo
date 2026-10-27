import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Normed
import QCryptLean.Math.SpectralTheory.Matrix

/-!
# Trace pairing bounds on finite matrix registers

The matrix norm in this file is explicitly Mathlib's L2 operator norm. Its
instance is locally scoped and does not replace the Frobenius norm in consumers.
-/

noncomputable section

namespace Matrix

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Each entry is bounded by the L2 operator norm, also for rectangular matrices. -/
theorem norm_entry_le_l2_opNorm [DecidableEq Y] (A : Matrix X Y ℂ) (i : X) (j : Y) :
    ‖A i j‖ ≤ ‖A‖ := by
  classical
  let v : EuclideanSpace ℂ Y := EuclideanSpace.single j 1
  have h := (PiLp.norm_apply_le (WithLp.toLp 2 (A *ᵥ v.ofLp)) i).trans
    (Matrix.l2_opNorm_mulVec A v)
  simpa [v, PiLp.norm_single] using h

/-- Pairing an arbitrary matrix with a positive matrix is bounded by operator norm times trace. -/
theorem PosSemidef.norm_trace_mul_le [DecidableEq X] [Nonempty X]
    {P : Matrix X X ℂ} (hP : P.PosSemidef) (Q : Matrix X X ℂ) :
    ‖(Q * P).trace‖ ≤ ‖Q‖ * P.trace.re := by
  let U := hP.isHermitian.eigenvectorUnitary
  let D := diagonal (fun i => (hP.isHermitian.eigenvalues i : ℂ))
  have he : P = U.val * D * U.valᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, RCLike.ofReal_eq_complex_ofReal,
      Matrix.star_eq_conjTranspose, Function.comp_def] using hP.isHermitian.spectral_theorem
  have hU : ‖U.val‖ = 1 := CStarRing.norm_of_mem_unitary U.property
  have hUs : ‖U.valᴴ‖ = 1 := by rw [l2_opNorm_conjTranspose, hU]
  have hn : ‖U.valᴴ * Q * U.val‖ ≤ ‖Q‖ := by
    calc
      _ ≤ ‖U.valᴴ * Q‖ * ‖U.val‖ := l2_opNorm_mul _ _
      _ ≤ (‖U.valᴴ‖ * ‖Q‖) * ‖U.val‖ :=
        mul_le_mul_of_nonneg_right (l2_opNorm_mul _ _) (norm_nonneg _)
      _ = ‖Q‖ := by rw [hU, hUs, one_mul, mul_one]
  have ht : (Q * P).trace = ∑ i, (U.valᴴ * Q * U.val) i i *
      (hP.isHermitian.eigenvalues i : ℂ) := by
    conv_lhs => rw [he]
    rw [← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    simp [D, trace, Matrix.mul_diagonal]
  rw [ht, hP.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
  simp only [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hP.eigenvalues_nonneg i)]
  exact mul_le_mul_of_nonneg_right ((norm_entry_le_l2_opNorm _ i i).trans hn)
    (hP.eigenvalues_nonneg i)

end Matrix
