import QCryptLean.InfoTheory.RelativeEntropy.Basic
import QCryptLean.InfoTheory.RelativeEntropy.Variational
import QCryptLean.Math.ClassicalEntropy.KLDivergence
import QCryptLean.Math.LinearAlgebra.Matrix.DiagonalConjugation
import QCryptLean.Math.SpectralTheory.MatrixCFC
import QCryptLean.Quantum.Operators.Basic

/-! # Relative entropy under projective measurements -/

noncomputable section
namespace InfoTheory.RelativeEntropy
open Quantum.Operators Matrix Math.ClassicalEntropy Math.SpectralTheory
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Projective measurement in an orthonormal basis contracts relative entropy. -/
lemma classicalKLDiv_diagonal_conjugate_le (ρ σ : DensityOp Q)
    (U : Op Q) (hU : Uᴴ * U = 1)
    (hker : ∀ v, σ.toOp.mulVec v = 0 → ρ.toOp.mulVec v = 0) :
    classicalKLDiv (fun i => ((Uᴴ * ρ.toOp * U) i i).re)
      (fun i => ((Uᴴ * σ.toOp * U) i i).re) ≤ relativeEntropyReal ρ σ := by
  classical
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  let p (i : Q) := ((Uᴴ * ρ.toOp * U) i i).re
  let q (i : Q) := ((Uᴴ * σ.toOp * U) i i).re
  have hdiag (M : Op Q) (i : Q) :
      (Uᴴ * M * U) i i = star (fun j => U j i) ⬝ᵥ M *ᵥ (fun j => U j i) := by
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    rfl
  have hp (i : Q) : 0 ≤ p i := by
    exact (Complex.nonneg_iff.mp
      (by simpa only [p, hdiag] using ρ.posSemidef.dotProduct_mulVec_nonneg (fun j => U j i))).1
  have hs : ∑ i, p i = 1 := by
    rw [← Complex.re_sum]
    change (Uᴴ * ρ.toOp * U).trace.re = 1
    rw [trace_mul_cycle, hU', one_mul, ρ.trace_one, Complex.one_re]
  have hsupp (i : Q) (hi : 0 < p i) : 0 < q i := by
    have hn := σ.posSemidef.dotProduct_mulVec_nonneg (fun j => U j i)
    have hqn : 0 ≤ q i := by simpa only [q, hdiag] using (Complex.nonneg_iff.mp hn).1
    by_contra! hq
    have hz : star (fun j => U j i) ⬝ᵥ σ.toOp *ᵥ (fun j => U j i) = 0 := by
      apply Complex.ext
      · simpa only [q, hdiag, Complex.zero_re] using le_antisymm hq hqn
      · exact (Complex.nonneg_iff.mp hn).2.symm
    have hv := hker _ (σ.posSemidef.dotProduct_mulVec_zero_iff.mp hz)
    have hpz : p i = 0 := by
      simp only [p, hdiag, hv, dotProduct_zero, Complex.zero_re]
    exact hi.ne' hpz
  apply classicalKLDiv_le_of_gibbs p q hp hs hsupp
  intro a
  let D : Op Q := diagonal (fun i => (a i : ℂ))
  have hD : D.IsHermitian := isHermitian_diagonal_ofReal a
  let V : unitary (Op Q) := ⟨U, by
    exact ⟨hU, hU'⟩⟩
  have he : NormedSpace.exp (U * D * Uᴴ) =
      U * diagonal (fun i => (Real.exp (a i) : ℂ)) * Uᴴ := by
    rw [← CFC.real_exp_eq_normedSpace_exp
      (isHermitian_mul_mul_conjTranspose U hD).isSelfAdjoint]
    change cfc Real.exp (Unitary.conjStarAlgAut ℂ _ V D) = _
    rw [cfc_conjStarAlgAut D hD V Real.exp, cfc_diagonal_ofReal]
    rfl
  have hg := gibbs_variational_bound_of_ker_sub ρ σ (U * D * Uᴴ)
    (isHermitian_mul_mul_conjTranspose U hD) hker
  rw [he] at hg
  change (ρ.toOp * (U * diagonal (RCLike.ofReal ∘ a) * Uᴴ)).trace.re -
    Real.log (σ.toOp * (U * diagonal
      (RCLike.ofReal ∘ (fun i => Real.exp (a i))) * Uᴴ)).trace.re ≤ _ at hg
  rw [trace_mul_conj_real_diagonal_re, trace_mul_conj_real_diagonal_re] at hg
  exact hg
end InfoTheory.RelativeEntropy
