import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import QCryptLean.InfoTheory.VonNeumannEntropy.Basic
import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.Math.ClassicalEntropy.KLDivergence
import QCryptLean.Math.LinearAlgebra.Matrix.DiagonalConjugation
import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Spectrum

/-! # Diagonal measurement entropy and the matrix Gibbs variational inequality -/
noncomputable section
namespace InfoTheory.VonNeumannEntropy
open Quantum.Operators Matrix Math.ClassicalEntropy
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Measuring a state in an orthonormal basis increases its Shannon entropy. -/
theorem vonNeumannEntropy_le_arbitrary_diagonal_entropy
    (W : Op Q) (hW : W * Wᴴ = 1) (ρ : DensityOp Q) :
    vonNeumannEntropy ρ ≤ shannonEntropy (fun i => ((W * ρ.toOp * Wᴴ) i i).re) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Q) (Classical.decEq Q)
  classical
  let U := ρ.isHermitian.eigenvectorUnitary.val
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self _
  have hU' : U * Uᴴ = 1 := Unitary.coe_mul_star_self _
  have hW' : Wᴴ * W = 1 := mul_eq_one_comm.mpr hW
  let T := W * U
  have hT : Tᴴ * T = 1 := by
    simp only [T, conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Wᴴ W, hW', one_mul, hU]
  have hT' : T * Tᴴ = 1 := mul_eq_one_comm.mp hT
  let D : Matrix Q Q ℝ := fun i j => Complex.normSq (T i j)
  have hrow (i : Q) : ∑ j, D i j = 1 := by
    simpa only [D, hT', one_apply_eq, Complex.one_re] using
      sum_normSq_row_eq_diag_mul_conjTranspose T i
  have hcol (j : Q) : ∑ i, D i j = 1 := by
    simpa only [D, hT, one_apply_eq, Complex.one_re] using
      sum_normSq_col_eq_diag_conjTranspose_mul T j
  have he : (fun i => ((W * ρ.toOp * Wᴴ) i i).re) =
      fun i => ∑ j, D i j * ρ.eigenvalues j := by
    funext i
    conv_lhs => rw [ρ.isHermitian.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply]
    have he : W * (U * diagonal (fun i => (ρ.eigenvalues i : ℂ)) * Uᴴ) * Wᴴ =
        T * diagonal (fun i => (ρ.eigenvalues i : ℂ)) * Tᴴ := by
      simp only [T, conjTranspose_mul, Matrix.mul_assoc]
    change ((W * (U * diagonal (fun i => (ρ.eigenvalues i : ℂ)) * Uᴴ) * Wᴴ) i i).re = _
    rw [he]
    exact conj_diagonal_diag_eq_sum_normSq T ρ.eigenvalues i
  rw [he]
  exact shannonEntropy_doubly_stochastic_ge ρ.eigenvalues D ρ.eigenvalues_nonneg
    (fun i j => Complex.normSq_nonneg _) hrow hcol

/-- The matrix Gibbs variational inequality for a Hermitian logarithmic perturbation. -/
theorem vonNeumannEntropy_add_re_trace_mul_le_log_re_trace_exp
    (ρ : DensityOp Q) (H : Op Q) (hH : H.IsHermitian) :
    vonNeumannEntropy ρ + (ρ.toOp * H).trace.re ≤ Real.log (NormedSpace.exp H).trace.re := by
  let : Nonempty Q := ρ.nonempty
  let U := hH.eigenvectorUnitary.val
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self _
  have hU' : U * Uᴴ = 1 := Unitary.coe_mul_star_self _
  let r : Q → ℝ := fun i => ((Uᴴ * ρ.toOp * U) i i).re
  have hn (i : Q) : 0 ≤ r i := by
    have h := (ρ.posSemidef.mul_mul_conjTranspose_same Uᴴ).diag_nonneg (i := i)
    simpa only [conjTranspose_conjTranspose] using (Complex.nonneg_iff.mp h).1
  have hs : ∑ i, r i = 1 := by
    change (∑ i, ((Uᴴ * ρ.toOp * U) i i).re) = 1
    rw [← Complex.re_sum]
    change (Uᴴ * ρ.toOp * U).trace.re = 1
    rw [trace_mul_cycle, hU', one_mul, ρ.trace_one, Complex.one_re]
  have hg := shannonEntropy_add_sum_mul_le_log_sum_exp r hH.eigenvalues hn hs
  have he := vonNeumannEntropy_le_arbitrary_diagonal_entropy Uᴴ
    (by simpa only [conjTranspose_conjTranspose] using hU) ρ
  have ht : (ρ.toOp * H).trace.re = ∑ i, r i * hH.eigenvalues i := by
    conv_lhs => rw [hH.spectral_theorem]
    exact trace_mul_conj_real_diagonal_re ρ.toOp U hH.eigenvalues
  have hex : (NormedSpace.exp H).trace.re = ∑ i, Real.exp (hH.eigenvalues i) := by
    rw [← CFC.real_exp_eq_normedSpace_exp hH.isSelfAdjoint, hH.trace_cfc, Complex.re_sum]
    rfl
  rw [ht, hex]
  exact (add_le_add (show vonNeumannEntropy ρ ≤ shannonEntropy r by
    simpa only [conjTranspose_conjTranspose] using he) (le_refl _)).trans hg
end InfoTheory.VonNeumannEntropy
