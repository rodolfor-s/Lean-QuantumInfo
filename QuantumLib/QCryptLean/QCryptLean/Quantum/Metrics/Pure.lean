import QCryptLean.Math.LinearAlgebra.Matrix.SqrtScale
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.Uhlmann
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification

/-! # Pure -/


noncomputable section

namespace Quantum.Metrics

open Matrix Quantum.Operators
open scoped MatrixOrder ComplexOrder

variable {X : Type*} [Fintype X]

/-- Pure-state fidelity is the absolute overlap by rank-one multiplication. -/
theorem fidelity_pure (v w : NormKet X) :
    fidelity v.toDensityOp.toPosSemidefOp w.toDensityOp.toPosSemidefOp =
      ‖(v.toKet.dag * w.toKet : ℂ)‖ := by
  classical
  have hs : CFC.sqrt v.toDensityOp.toOp = v.toDensityOp.toOp :=
    CFC.sqrt_unique v.isPure_toDensityOp v.toDensityOp.posSemidef.nonneg
  let z : ℂ := (v.toKet.dag * w.toKet : ℂ)
  have hconj : (w.toKet.dag * v.toKet : ℂ) = star z := by
    change (star w.vec ⬝ᵥ v.vec) = star (star v.vec ⬝ᵥ w.vec)
    simp only [dotProduct, star_sum, star_mul', Pi.star_apply, star_star]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  have hp : v.toDensityOp.toOp * w.toDensityOp.toOp * v.toDensityOp.toOp =
      (‖z‖ ^ 2 : ℝ) • v.toDensityOp.toOp := by
    change vecMulVec v.vec (star v.vec) * vecMulVec w.vec (star w.vec) *
      vecMulVec v.vec (star v.vec) = _
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul, Matrix.smul_mul,
      vecMulVec_mul_vecMulVec, vecMulVec_smul, smul_smul]
    change (z * (w.toKet.dag * v.toKet : ℂ)) • v.toDensityOp.toOp = _
    rw [hconj, show z * star z = (‖z‖ ^ 2 : ℝ) by
      change z * (starRingEnd ℂ) z = _
      rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]]
    rfl
  have hp' : v.toDensityOp.toOp * w.toDensityOp.toOp * v.toDensityOp.toOp =
      ((‖z‖ ^ 2 : ℝ) : ℂ) • v.toDensityOp.toOp := hp
  unfold fidelity sqrtPosSemidefOp
  change (CFC.sqrt (CFC.sqrt v.toDensityOp.toOp * w.toDensityOp.toOp *
    CFC.sqrt v.toDensityOp.toOp)).trace.re = _
  rw [hs, hp', v.toDensityOp.posSemidef.sqrt_ofReal_smul (sq_nonneg _), hs,
    Matrix.trace_smul, v.toDensityOp.trace_one, smul_eq_mul, mul_one,
    Complex.ofReal_re, Real.sqrt_sq (norm_nonneg _)]

/-- The exact pure-state trace distance has its usual square-root overlap formula.
The proof computes the square root using the cubic identity for the projector difference. -/
theorem traceDistance_pure (v w : NormKet X) :
    traceDistance v.toDensityOp.toOp w.toDensityOp.toOp =
      Real.sqrt (1 - ‖(v.toKet.dag * w.toKet : ℂ)‖ ^ 2) := by
  classical
  let : Nonempty X := v.toDensityOp.nonempty
  let P := v.toDensityOp.toOp
  let Q := w.toDensityOp.toOp
  let t := ‖(v.toKet.dag * w.toKet : ℂ)‖ ^ 2
  have hP : P * P = P := v.isPure_toDensityOp
  have hQ : Q * Q = Q := w.isPure_toDensityOp
  have htriple (u z : NormKet X) :
      u.toDensityOp.toOp * z.toDensityOp.toOp * u.toDensityOp.toOp =
        ((‖(u.toKet.dag * z.toKet : ℂ)‖ ^ 2 : ℝ) : ℂ) • u.toDensityOp.toOp := by
    have hc : (z.toKet.dag * u.toKet : ℂ) = star (u.toKet.dag * z.toKet : ℂ) := by
      change star z.vec ⬝ᵥ u.vec = star (star u.vec ⬝ᵥ z.vec)
      simp only [dotProduct, star_sum, star_mul', Pi.star_apply, star_star]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    change vecMulVec u.vec (star u.vec) * vecMulVec z.vec (star z.vec) *
      vecMulVec u.vec (star u.vec) = _
    rw [vecMulVec_mul_vecMulVec, vecMulVec_smul, Matrix.smul_mul,
      vecMulVec_mul_vecMulVec, vecMulVec_smul, smul_smul]
    change ((u.toKet.dag * z.toKet : ℂ) * (z.toKet.dag * u.toKet : ℂ)) • _ = _
    rw [hc, mul_comm]
    change (((starRingEnd ℂ) (u.toKet.dag * z.toKet : ℂ)) *
      (u.toKet.dag * z.toKet : ℂ)) • _ = _
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    rfl
  have hPQ : P * Q * P = (t : ℂ) • P := htriple v w
  have hQP : Q * P * Q = (t : ℂ) • Q := by
    rw [show t = ‖(w.toKet.dag * v.toKet : ℂ)‖ ^ 2 by
      dsimp only [t]
      have he : star (v.toKet.dag * w.toKet : ℂ) = (w.toKet.dag * v.toKet : ℂ) := by
        change star (star v.vec ⬝ᵥ w.vec) = star w.vec ⬝ᵥ v.vec
        simp only [dotProduct, star_sum, star_mul', Pi.star_apply, star_star]
        exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      rw [← he, norm_star]]
    exact htriple w v
  let D := P - Q
  have hD : D.IsHermitian := v.toDensityOp.isHermitian.sub w.toDensityOp.isHermitian
  have hD3 : D * D * D = ((1 - t : ℝ) : ℂ) • D := by
    dsimp only [D]
    simp only [mul_sub, sub_mul, hP, hQ, hPQ, hQP,
      show P * Q * Q = P * Q by rw [Matrix.mul_assoc, hQ],
      show Q * P * P = Q * P by rw [Matrix.mul_assoc, hP],
      Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul, smul_sub]
    abel
  have hD4 : (D * D) * (D * D) = ((1 - t : ℝ) : ℂ) • (D * D) := by
    rw [← Matrix.mul_assoc, hD3, Matrix.smul_mul]
  have hpos : (D * D).PosSemidef := by
    simpa only [hD.eq] using posSemidef_conjTranspose_mul_self D
  have ht : 0 ≤ 1 - t := by
    have hn (z : NormKet X) : ‖(WithLp.toLp 2 z.vec : EuclideanSpace ℂ X)‖ = 1 := by
      rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct,
        dotProduct_comm]
      change Real.sqrt (z.toKet.dag * z.toKet : ℂ).re = 1
      rw [z.normalized, Complex.one_re, Real.sqrt_one]
    have hf := norm_inner_le_norm (𝕜 := ℂ)
      (WithLp.toLp 2 v.vec : EuclideanSpace ℂ X)
      (WithLp.toLp 2 w.vec : EuclideanSpace ℂ X)
    rw [hn, hn, mul_one, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at hf
    change ‖(v.toKet.dag * w.toKet : ℂ)‖ ≤ 1 at hf
    dsimp only [t]
    nlinarith [norm_nonneg (v.toKet.dag * w.toKet : ℂ)]
  have hs := CFC.sqrt_mul_self (D * D) hpos.nonneg
  rw [hD4, hpos.sqrt_ofReal_smul ht] at hs
  have htrace : (D * D).trace.re = 2 * (1 - t) := by
    have hpq := congrArg Matrix.trace hPQ
    rw [Matrix.trace_mul_cycle, hP, Matrix.trace_smul,
      show P.trace = 1 from v.toDensityOp.trace_one, smul_eq_mul, mul_one] at hpq
    dsimp only [D]
    rw [mul_sub, sub_mul, sub_mul, hP, hQ, Matrix.trace_sub, Matrix.trace_sub,
      Matrix.trace_sub, Matrix.trace_mul_comm Q P, hpq,
      show P.trace = 1 from v.toDensityOp.trace_one,
      show Q.trace = 1 from w.toDensityOp.trace_one]
    change ((1 : ℂ) - (t : ℂ) - ((t : ℂ) - 1)).re = _
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    ring
  have hn : Real.sqrt (1 - t) * traceNorm D = 2 * (1 - t) := by
    have hh := congrArg (fun M : Op X => M.trace.re) hs
    rw [Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, htrace] at hh
    rw [traceNorm_eq_trace_sqrt, hD.eq]
    exact hh
  change (1 / 2 : ℝ) * traceNorm D = Real.sqrt (1 - t)
  by_cases hz : 1 - t = 0
  · have hDD : D * D = 0 := by simpa only [hz, Real.sqrt_zero, Complex.ofReal_zero,
      zero_smul, eq_comm] using hs
    rw [traceNorm_eq_trace_sqrt, hD.eq, hDD, CFC.sqrt_zero, Matrix.trace_zero,
      Complex.zero_re, mul_zero, hz, Real.sqrt_zero]
  · have hsq := Real.sq_sqrt ht
    have hp := Real.sqrt_pos.mpr (lt_of_le_of_ne ht (Ne.symm hz))
    nlinarith

end Quantum.Metrics
