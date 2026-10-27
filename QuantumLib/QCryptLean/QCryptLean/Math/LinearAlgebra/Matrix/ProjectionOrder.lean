import Mathlib.Analysis.CStarAlgebra.Matrix
import QCryptLean.Math.LinearAlgebra.Matrix.PositiveTrace

/-!
# Trace caps and supported positive matrices

The proofs use the local matrix star order and L2 operator norm for continuous
functional calculus. Neither instance is exported.
-/
namespace Matrix
noncomputable section
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A positive matrix is bounded above by its real trace times the identity. -/
theorem PosSemidef.le_re_trace_smul_one {A : Matrix X X ℂ} (hA : A.PosSemidef) :
    A ≤ (A.trace.re : ℂ) • 1 := by
  let U := hA.isHermitian.eigenvectorUnitary
  have he : ∀ i, hA.isHermitian.eigenvalues i ≤ A.trace.re := by
    intro i
    rw [hA.isHermitian.trace_eq_sum_eigenvalues]
    simp only [Complex.re_sum]
    exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hd : (diagonal (fun i => (A.trace.re : ℂ) - hA.isHermitian.eigenvalues i)).PosSemidef :=
    PosSemidef.diagonal (fun i => by
      rw [← Complex.ofReal_sub]
      exact Complex.zero_le_real.mpr (sub_nonneg.mpr (he i)))
  have hU : U.val * U.valᴴ = 1 := Unitary.coe_mul_star_self U
  have ha : A = U.val * diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ)) * U.valᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, RCLike.ofReal_eq_complex_ofReal,
      Function.comp_def, Matrix.star_eq_conjTranspose] using hA.isHermitian.spectral_theorem
  apply Matrix.le_iff.mpr
  have hh := hd.mul_mul_conjTranspose_same U.val
  have hc : diagonal (fun _ : X => (A.trace.re : ℂ)) = (A.trace.re : ℂ) • 1 := by
    ext i j
    simp [Matrix.diagonal, Matrix.one_apply]
  rw [← diagonal_sub, hc, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hU, ← ha] at hh
  exact hh

omit [DecidableEq X] in
/-- A supported positive matrix is bounded by its trace times the support projector. -/
theorem PosSemidef.le_re_trace_smul_projection {A P : Matrix X X ℂ}
    (hA : A.PosSemidef) (hP : P.IsHermitian) (hPP : P * P = P) (hPA : P * A = A) :
    A ≤ (A.trace.re : ℂ) • P := by
  classical
  have hAP : A * P = A := by
    simpa only [conjTranspose_mul, hP.eq, hA.isHermitian.eq] using
      congrArg Matrix.conjTranspose hPA
  have hh := (Matrix.le_iff.mp hA.le_re_trace_smul_one).mul_mul_conjTranspose_same P
  rw [hP.eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hPP, hPA, hAP] at hh
  exact Matrix.le_iff.mpr hh

omit [DecidableEq X] in
/-- A supported positive matrix with trace at most one is bounded by its support projector. -/
theorem PosSemidef.le_projection_of_trace_le_one {A P : Matrix X X ℂ}
    (hA : A.PosSemidef) (ht : A.trace.re ≤ 1) (hP : P.IsHermitian)
    (hPP : P * P = P) (hPA : P * A = A) : A ≤ P := by
  classical
  have hp : IsStarProjection P := ⟨hPP, hP⟩
  exact hA.le_re_trace_smul_projection hP hPP hPA |>.trans (by
    simpa only [one_smul] using smul_le_smul_of_nonneg_right
      (show (A.trace.re : ℂ) ≤ 1 from by exact_mod_cast ht) hp.nonneg)


end
end Matrix
