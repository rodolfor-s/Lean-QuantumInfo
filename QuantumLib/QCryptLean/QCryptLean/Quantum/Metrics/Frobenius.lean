import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Basic

/-!
# Trace norm bounds with explicitly local Frobenius instances

Only this file's norm notation selects `Matrix.frobeniusNormedAddCommGroup` and
`Matrix.frobeniusNormedSpace`. The trace norm itself is still a separate function.
These comparisons justify boundedness of the diamond supremum by continuity of
finite-dimensional linear maps, without changing any ambient norm instance.
-/

noncomputable section

namespace Quantum.Metrics

open Matrix Quantum.Operators
open scoped ComplexOrder

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

variable {X : Type*} [Fintype X]

/-- The Frobenius norm is the square root of the trace of the Gram matrix. -/
theorem frobenius_eq_sqrt_trace (A : Op X) : ‖A‖ = √((Aᴴ * A).trace.re) := by
  have ht : (Aᴴ * A).trace.re = ∑ i, ∑ j, ‖A j i‖ ^ 2 := by
    simp only [trace, diag, mul_apply, conjTranspose_apply, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show star (A j i) = (starRingEnd ℂ) (A j i) from rfl,
      ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [Matrix.frobenius_norm_def, ht, Finset.sum_comm]
  simp only [Real.rpow_two, Real.sqrt_eq_rpow]

/-- Cauchy--Schwarz bounds the singular-value sum by dimension times Frobenius norm. -/
theorem traceNorm_le_sqrt_card_mul_frobenius (A : Op X) :
    traceNorm A ≤ √(Fintype.card X : ℝ) * ‖A‖ := by
  classical
  let h := isHermitian_conjTranspose_mul_self A
  have hs : ∑ i, h.eigenvalues i = (Aᴴ * A).trace.re := by
    rw [h.trace_eq_sum_eigenvalues]
    simp
  have hc := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset X)
    (f := h.eigenvalues) (g := fun _ => (1 : ℝ))
    (posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg (fun _ => zero_le_one)
  simp only [Real.sqrt_one, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hc
  rw [hs] at hc
  rw [frobenius_eq_sqrt_trace, mul_comm]
  exact hc

/-- The Frobenius norm is bounded by the trace norm, for every operator. -/
theorem frobenius_le_traceNorm (A : Op X) : ‖A‖ ≤ traceNorm A := by
  classical
  let h := isHermitian_conjTranspose_mul_self A
  have hs : ∑ i, h.eigenvalues i = (Aᴴ * A).trace.re := by
    rw [h.trace_eq_sum_eigenvalues]
    simp
  have hc := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := (Finset.univ : Finset X)) (f := fun i => √(h.eigenvalues i))
    (fun _ _ => Real.sqrt_nonneg _)
  simp_rw [Real.sq_sqrt ((posSemidef_conjTranspose_mul_self A).eigenvalues_nonneg _)] at hc
  rw [hs] at hc
  rw [frobenius_eq_sqrt_trace]
  exact (Real.sqrt_le_left (traceNorm_nonneg A)).mpr hc

end Quantum.Metrics
