import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Basic

/-!
# Native trace-norm foundations on finite registers

Jordan decomposition and dilation use matrix star order locally. No matrix norm
instance is selected or exported; the trace norm remains an explicit function.
-/

noncomputable section

namespace Quantum.Metrics

open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- For Hermitian operators the singular-value sum is the absolute eigenvalue sum. -/
theorem traceNorm_eq_traceNormHermitian (A : Op X) (hA : A.IsHermitian) :
    traceNorm A = traceNormHermitian A hA := by
  classical
  have ha : IsSelfAdjoint A := hA
  rw [traceNorm_eq_trace_sqrt,
    CFC.sqrt_eq_real_sqrt _ (posSemidef_conjTranspose_mul_self A).nonneg,
    cfcₙ_eq_cfc (hf0 := Real.sqrt_zero), hA.eq, ← sq, ← cfc_pow_id (R := ℝ) A 2 ha,
    ← cfc_comp Real.sqrt (fun x : ℝ => x ^ 2) A ha, hA.trace_cfc, Complex.re_sum]
  simp [traceNormHermitian, Real.sqrt_sq_eq_abs]

/-- A positive operator's trace norm is its real trace. -/
theorem traceNorm_of_posSemidef (A : Op X) (hA : A.PosSemidef) :
    traceNorm A = A.trace.re := by
  classical
  rw [traceNorm_eq_traceNormHermitian A hA.isHermitian, hA.isHermitian.trace_eq_sum_eigenvalues]
  simp [traceNormHermitian, abs_of_nonneg, hA.eigenvalues_nonneg]

/-- A Hermitian operator splits into positive parts with total mass its trace norm. -/
theorem exists_posSemidef_sub_traceNorm_eq (A : Op X) (hA : A.IsHermitian) :
    ∃ P Q : Op X, P.PosSemidef ∧ Q.PosSemidef ∧ A = P - Q ∧
      traceNorm A = (P.trace + Q.trace).re := by
  classical
  let U := hA.eigenvectorUnitary
  let p : X → ℂ := fun i => (max (hA.eigenvalues i) 0 : ℝ)
  let q : X → ℂ := fun i => (max (-hA.eigenvalues i) 0 : ℝ)
  have hp : (diagonal p).PosSemidef := PosSemidef.diagonal
    (fun i => Complex.zero_le_real.mpr (le_max_right _ _))
  have hq : (diagonal q).PosSemidef := PosSemidef.diagonal
    (fun i => Complex.zero_le_real.mpr (le_max_right _ _))
  refine ⟨U.val * diagonal p * U.valᴴ, U.val * diagonal q * U.valᴴ,
    hp.mul_mul_conjTranspose_same _, hq.mul_mul_conjTranspose_same _, ?_, ?_⟩
  · have hd : (fun i => p i - q i) = Complex.ofReal ∘ hA.eigenvalues := by
      funext i
      simp only [p, q, Function.comp_apply, ← Complex.ofReal_sub]
      congr 1
      simp [max_def]; split <;> split <;> linarith
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub, hd]
    simpa only [Unitary.conjStarAlgAut_apply, RCLike.ofReal_eq_complex_ofReal,
      Matrix.star_eq_conjTranspose] using hA.spectral_theorem
  · have ht (D : Op X) : (U.val * D * U.valᴴ).trace = D.trace := by
      rw [trace_mul_cycle]
      change (star U.val * U.val * D).trace = _
      rw [U.property.1, one_mul]
    rw [ht, ht, trace_diagonal, trace_diagonal, traceNorm_eq_traceNormHermitian A hA]
    simp only [traceNormHermitian, Complex.add_re, Complex.re_sum, p, q, Complex.ofReal_re,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp [abs_eq_max_neg, max_def]; split <;> split <;> linarith

/-- The trace norm of a difference of positive operators is bounded by their total mass. -/
theorem traceNorm_sub_posSemidef_le (P Q : Op X) (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) : traceNorm (P - Q) ≤ (P.trace + Q.trace).re := by
  classical
  let hA := hP.isHermitian.sub hQ.isHermitian
  let U := hA.eigenvectorUnitary
  have ht (D : Op X) : (U.valᴴ * D * U.val).trace = D.trace := by
    rw [trace_mul_cycle]
    change (U.val * star U.val * D).trace = _
    rw [U.property.2, one_mul]
  have hd : U.valᴴ * (P - Q) * U.val =
      diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
    have he := hA.conjStarAlgAut_star_eigenvectorUnitary
    simp only [Unitary.conjStarAlgAut_star_apply] at he
    simpa only [RCLike.ofReal_eq_complex_ofReal, Matrix.star_eq_conjTranspose,
      Function.comp_def] using he
  rw [traceNorm_eq_traceNormHermitian _ hA, ← ht P, ← ht Q]
  simp only [traceNormHermitian, Complex.add_re, Matrix.trace, Complex.re_sum,
    ← Finset.sum_add_distrib, Matrix.diag_apply]
  apply Finset.sum_le_sum
  intro i _
  have hp := (hP.conjTranspose_mul_mul_same U.val).diag_nonneg (i := i)
  have hq := (hQ.conjTranspose_mul_mul_same U.val).diag_nonneg (i := i)
  have he := congrArg Complex.re (congrFun (congrFun hd i) i)
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply, diagonal_apply_eq,
    Complex.sub_re, Complex.ofReal_re] at he
  have hp' := (Complex.nonneg_iff.mp hp).1
  have hq' := (Complex.nonneg_iff.mp hq).1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The trace norm satisfies the triangle inequality on Hermitian operators. -/
theorem traceNorm_add_le_of_isHermitian (A B : Op X) (hA : A.IsHermitian)
    (hB : B.IsHermitian) : traceNorm (A + B) ≤ traceNorm A + traceNorm B := by
  obtain ⟨P, Q, hP, hQ, hPQ, hNA⟩ := exists_posSemidef_sub_traceNorm_eq A hA
  obtain ⟨R, S, hR, hS, hRS, hNB⟩ := exists_posSemidef_sub_traceNorm_eq B hB
  have h := traceNorm_sub_posSemidef_le (P + R) (Q + S) (hP.add hR) (hQ.add hS)
  rw [show P + R - (Q + S) = A + B by rw [hPQ, hRS]; abel] at h
  simpa only [hNA, hNB, trace_add, Complex.add_re, add_add_add_comm] using h

/-- Adjoint preserves the trace norm, by equality of the two Gram spectra. -/
theorem traceNorm_conjTranspose (A : Op X) : traceNorm Aᴴ = traceNorm A := by
  classical
  have he := (isHermitian_mul_conjTranspose_self A).eigenvalues_eq_eigenvalues_iff
    (isHermitian_conjTranspose_mul_self A)
  have hv := he.mpr (charpoly_mul_comm A Aᴴ)
  simp only [traceNorm, conjTranspose_conjTranspose]
  convert congrArg (fun f : X → ℝ => ∑ i, Real.sqrt (f i)) hv using 1

/-- Two off-diagonal square blocks contribute additively to the trace norm. -/
theorem traceNorm_fromBlocks_offDiagonal (A B : Op X) :
    traceNorm (fromBlocks 0 A B 0) = traceNorm A + traceNorm B := by
  classical
  rw [traceNorm_eq_trace_sqrt, fromBlocks_conjTranspose, fromBlocks_multiply]
  simp only [conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero]
  rw [(posSemidef_conjTranspose_mul_self B).sqrt_fromBlocks_zero
    (posSemidef_conjTranspose_mul_self A)]
  simp only [Matrix.trace, Fintype.sum_sum_type, Complex.add_re]
  change (CFC.sqrt (Bᴴ * B)).trace.re + (CFC.sqrt (Aᴴ * A)).trace.re = _
  rw [← traceNorm_eq_trace_sqrt, ← traceNorm_eq_trace_sqrt, add_comm]

/-- A self-adjoint dilation has twice the trace norm of its off-diagonal block. -/
theorem traceNorm_fromBlocks_dilation (A : Op X) :
    traceNorm (fromBlocks 0 A Aᴴ 0) = 2 * traceNorm A := by
  rw [traceNorm_fromBlocks_offDiagonal, traceNorm_conjTranspose]
  ring

/-- The trace norm satisfies the triangle inequality on all operators. -/
theorem traceNorm_add_le (A B : Op X) : traceNorm (A + B) ≤ traceNorm A + traceNorm B := by
  have hH (C : Op X) : (fromBlocks 0 C Cᴴ 0).IsHermitian := by
    simp [Matrix.IsHermitian, fromBlocks_conjTranspose]
  have h := traceNorm_add_le_of_isHermitian _ _ (hH A) (hH B)
  simp only [fromBlocks_add, add_zero, ← conjTranspose_add, traceNorm_fromBlocks_dilation,
    traceNorm_fromBlocks_dilation, traceNorm_fromBlocks_dilation] at h
  linarith

/-- Positive trace-nonincreasing linear maps contract the trace norm on Hermitian inputs. -/
theorem traceNorm_apply_le_of_isHermitian (Φ : Op X →ₗ[ℂ] Op Y)
    (hpos : ∀ A, A.PosSemidef → (Φ A).PosSemidef)
    (htrace : ∀ A, A.PosSemidef → (Φ A).trace.re ≤ A.trace.re) (A : Op X) (hA : A.IsHermitian) :
    traceNorm (Φ A) ≤ traceNorm A := by
  obtain ⟨P, Q, hP, hQ, he, ht⟩ := exists_posSemidef_sub_traceNorm_eq A hA
  rw [he, map_sub]
  apply (traceNorm_sub_posSemidef_le _ _ (hpos P hP) (hpos Q hQ)).trans
  rw [← he, ht, Complex.add_re, Complex.add_re]
  exact add_le_add (htrace P hP) (htrace Q hQ)

/-- Negation preserves the trace norm. -/
@[simp] theorem traceNorm_neg (A : Op X) : traceNorm (-A) = traceNorm A := by
  simpa only [neg_one_smul, norm_neg, norm_one, one_mul] using traceNorm_smul (-1) A

/-- The trace norm of a difference is bounded by the sum of the trace norms. -/
theorem traceNorm_sub_le (A B : Op X) : traceNorm (A - B) ≤ traceNorm A + traceNorm B := by
  simpa only [sub_eq_add_neg, traceNorm_neg] using traceNorm_add_le A (-B)

open scoped Classical in
/-- Rectangular isometric conjugation preserves the trace norm on arbitrary operators. -/
theorem traceNorm_isometry_conj (V : Matrix Y X ℂ) (hV : Vᴴ * V = 1) (A : Op X) :
    traceNorm (V * A * Vᴴ) = traceNorm A := by
  classical
  have he : (V * A * Vᴴ)ᴴ * (V * A * Vᴴ) = V * (Aᴴ * A) * Vᴴ := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul]
  rw [traceNorm_eq_trace_sqrt, he,
    (posSemidef_conjTranspose_mul_self A).sqrt_conj_of_isometry V hV,
    Matrix.trace_mul_cycle, hV, Matrix.one_mul, traceNorm_eq_trace_sqrt]

end Quantum.Metrics
