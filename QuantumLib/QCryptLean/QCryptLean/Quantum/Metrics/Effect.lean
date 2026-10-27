import QCryptLean.Math.LinearAlgebra.Matrix.PositiveTrace
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.GramDifference
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra

/-! # Effect -/


noncomputable section

namespace Quantum.Metrics

open Matrix Quantum.Operators
open scoped ComplexOrder

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The sharp disturbance estimate for a positive contraction. -/
theorem traceNorm_sub_effectSandwich_le_sqrt_mul {P G : Op X}
    (hP : P.PosSemidef) (hG : G.PosSemidef) (hG1 : ((1 : Op X) - G).PosSemidef) :
    traceNorm (P - G * P * G) ≤
      Real.sqrt ((P.trace.re - (G * P * G).trace.re) *
        (P.trace.re + 3 * (G * P * G).trace.re)) := by
  have hGG : (G - G * G).PosSemidef := by
    let S := sqrtPosSemidefOp (⟨G, hG⟩ : PosSemidefOp X)
    have hSS : S * S = G := sqrtPosSemidefOp_mul_self ⟨G, hG⟩
    have hS : Sᴴ = S := (isHermitian_sqrtPosSemidefOp ⟨G, hG⟩).eq
    have hc : S * G = G * S := by rw [← hSS, Matrix.mul_assoc]
    have he : S * (1 - G) * Sᴴ = G - G * G := by
      rw [hS, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hSS, hc,
        Matrix.mul_assoc, hSS]
    rw [← he]
    exact hG1.mul_mul_conjTranspose_same S
  set Pp : PosSemidefOp X := ⟨P, hP⟩ with hPp
  set S : Op X := sqrtPosSemidefOp Pp with hX
  set Y : Op X := G * S with hY
  have hXX2 : S * S = P := sqrtPosSemidefOp_mul_self Pp
  have hXh : Sᴴ = S := (isHermitian_sqrtPosSemidefOp Pp).eq
  have hGh : Gᴴ = G := hG.isHermitian.eq
  have hXXd : S * Sᴴ = P := by rw [hXh, hXX2]
  have hYYd : Y * Yᴴ = G * P * G := by
    rw [hY, Matrix.conjTranspose_mul, hXh, hGh, mul_assoc G S (S * G), ← mul_assoc S S G,
      ← mul_assoc, hXX2]
  have hXYd : S * Yᴴ = P * G := by
    rw [hY, Matrix.conjTranspose_mul, hXh, hGh, ← mul_assoc, hXX2]
  have hYXd : Y * Sᴴ = G * P := by rw [hY, hXh, mul_assoc, hXX2]
  set p : ℝ := P.trace.re with hp
  set q : ℝ := (G * P * G).trace.re with hq
  set f : ℝ := (P * G).trace.re with hf
  -- the two Frobenius squares, exactly
  have hUexp : (S + Y) * (S + Y)ᴴ = P + P * G + G * P + G * P * G := by
    rw [Matrix.conjTranspose_add, add_mul, mul_add, mul_add, hXXd, hXYd, hYXd, hYYd,
      ← add_assoc]
  have hVexp : (S - Y) * (S - Y)ᴴ = P - P * G - G * P + G * P * G := by
    rw [Matrix.conjTranspose_sub, sub_mul, mul_sub, mul_sub, hXXd, hXYd, hYXd, hYYd]
    abel
  have hGP : (G * P).trace = (P * G).trace := Matrix.trace_mul_comm G P
  have hnU : ((S + Y) * (S + Y)ᴴ).trace.re = p + 2 * f + q := by
    rw [hUexp]
    simp only [Matrix.trace_add, Complex.add_re, hGP]
    rw [hp, hf, hq]; ring
  have hnV : ((S - Y) * (S - Y)ᴴ).trace.re = p - 2 * f + q := by
    rw [hVexp]
    simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re, hGP]
    rw [hp, hf, hq]; ring
  -- the effect inequalities `0 ≤ q ≤ f ≤ p`
  have hcyc : (G * P * G).trace = (P * (G * G)).trace := by
    rw [mul_assoc, Matrix.trace_mul_comm G (P * G), mul_assoc]
  have hfq : q ≤ f := by
    have h := (Complex.nonneg_iff.mp (hP.trace_mul_nonneg hGG)).1
    rw [mul_sub] at h
    simp only [Matrix.trace_sub, Complex.sub_re] at h
    rw [hq, hcyc, hf]
    linarith
  have hfp : f ≤ p := by
    have h := (Complex.nonneg_iff.mp (hP.trace_mul_nonneg hG1)).1
    rw [mul_sub, mul_one] at h
    simp only [Matrix.trace_sub, Complex.sub_re] at h
    rw [hp, hf]
    linarith
  have hq0 : 0 ≤ q := by
    have hgpg := Matrix.PosSemidef.mul_mul_conjTranspose_same hP G
    rw [hGh] at hgpg
    rw [hq]
    exact (Complex.nonneg_iff.mp hgpg.trace_nonneg).1
  have hmaster := traceNorm_sub_mulConjTranspose_le_frobenius S Y
  rw [hXXd, hYYd, hnU, hnV] at hmaster
  refine hmaster.trans (Real.sqrt_le_sqrt ?_)
  -- `(p - q)(p + 3q) - (p + 2f + q)(p - 2f + q) = 4 (f - q)(f + q) ≥ 0`, as `0 ≤ q ≤ f`.
  have hkey : 0 ≤ (f - q) * (f + q) := mul_nonneg (sub_nonneg.mpr hfq) (by linarith)
  rw [← sub_nonneg]
  calc 0 ≤ 4 * ((f - q) * (f + q)) := mul_nonneg zero_le_four hkey
    _ = _ := by ring

/-- Homogeneous gentle-measurement bound, retaining the sharp constant two. -/
theorem traceNorm_sub_effectSandwich_le_homogeneous {P G : Op X}
    (hP : P.PosSemidef) (hG : G.PosSemidef) (hG1 : ((1 : Op X) - G).PosSemidef) :
    traceNorm (P - G * P * G) ≤
      2 * Real.sqrt (P.trace.re * (P.trace.re - (G * P * G).trace.re)) := by
  have hs := traceNorm_sub_effectSandwich_le_sqrt_mul hP hG hG1
  have hp : 0 ≤ P.trace.re := (Complex.nonneg_iff.mp hP.trace_nonneg).1
  have hq : 0 ≤ (G * P * G).trace.re := by
    have h := hP.mul_mul_conjTranspose_same G
    rw [hG.isHermitian.eq] at h
    exact (Complex.nonneg_iff.mp h.trace_nonneg).1
  refine hs.trans ?_
  by_cases hgap : 0 ≤ P.trace.re - (G * P * G).trace.re
  · rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num), ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (P.trace.re - (G * P * G).trace.re)]
  · rw [Real.sqrt_eq_zero_of_nonpos
      (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hgap) (by linarith))]
    positivity

end Quantum.Metrics
