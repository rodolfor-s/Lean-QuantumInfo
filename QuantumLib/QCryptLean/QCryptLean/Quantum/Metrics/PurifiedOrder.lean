import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.Frobenius
import QCryptLean.Quantum.Metrics.PurifiedBasic
import QCryptLean.Quantum.Metrics.Purified
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.StateOperations

/-! # Purified Order -/


noncomputable section

namespace Quantum.Operators

open Matrix Quantum.Metrics
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {X : Type*} [Fintype X]

/-- Real quadratic-form domination of positive states implies trace domination. -/
theorem SubDensityOp.trace_le_of_opLe (ρ τ : SubDensityOp X) (h : OpLe τ.toOp ρ.toOp) :
    τ.trace ≤ ρ.trace := by
  have hp := (opLe_iff_posSemidef_sub τ.isHermitian ρ.isHermitian).mp h
  have ht := (Complex.nonneg_iff.mp hp.trace_nonneg).1
  simpa only [Matrix.trace_sub, Complex.sub_re, sub_nonneg, SubDensityOp.trace] using ht

/-- Squared fidelity is bounded by the product of the subnormalized traces. -/
theorem SubDensityOp.fidelity_sq_le_trace_mul_trace (ρ τ : SubDensityOp X) :
    fidelity ρ.toPosSemidefOp τ.toPosSemidefOp ^ 2 ≤ ρ.trace * τ.trace := by
  have h := fidelity_le_sqrt_trace_mul_trace ρ.toPosSemidefOp τ.toPosSemidefOp
  have hs := Real.sq_sqrt (mul_nonneg ρ.trace_nonneg τ.trace_nonneg)
  have hn := fidelity_nonneg ρ.toPosSemidefOp τ.toPosSemidefOp
  change _ ≤ Real.sqrt (ρ.trace * τ.trace) at h
  nlinarith

/-- Proximity to a normalized center forces a lower bound on surviving mass. -/
theorem SubDensityOp.one_sub_sq_le_trace_of_purifiedDistance_le (ρ τ : SubDensityOp X)
    (hρ : ρ.trace = 1) {ε : ℝ} (hP : purifiedDistance ρ τ ≤ ε) :
    1 - ε ^ 2 ≤ τ.trace := by
  have hsq := purifiedDistance_sq ρ τ
  have hf := ρ.fidelity_sq_le_trace_mul_trace τ
  rw [fidelityGen_eq_fidelity_of_trace_one ρ τ hρ] at hsq
  rw [hρ, one_mul] at hf
  nlinarith [purifiedDistance_nonneg ρ τ]

/-- A dominated state's trace is at most its fidelity with the larger state.
The proof uses matrix square-root monotonicity and positivity of the trace. -/
theorem SubDensityOp.trace_le_fidelity_of_opLe
    (ρ τ : SubDensityOp X) (h : OpLe τ.toOp ρ.toOp) :
    τ.trace ≤ fidelity ρ.toPosSemidefOp τ.toPosSemidefOp := by
  classical
  let S := sqrtPosSemidefOp τ.toPosSemidefOp
  have hS : Sᴴ = S := (isHermitian_sqrtPosSemidefOp τ.toPosSemidefOp).eq
  have hSS : S * S = τ.toOp := sqrtPosSemidefOp_mul_self τ.toPosSemidefOp
  have hd :=
    ((opLe_iff_posSemidef_sub τ.isHermitian ρ.isHermitian).mp h).mul_mul_conjTranspose_same S
  rw [hS, mul_sub, sub_mul] at hd
  have hs : (CFC.sqrt (S * ρ.toOp * S) - CFC.sqrt (S * τ.toOp * S)).PosSemidef := by
    exact nonneg_iff_posSemidef.mp
      (sub_nonneg.mpr (CFC.sqrt_le_sqrt _ _ (sub_nonneg.mp hd.nonneg)))
  have he : S * τ.toOp * S = τ.toOp * τ.toOp := by
    calc
      S * τ.toOp * S = S * (S * S) * S := by rw [hSS]
      _ = (S * S) * (S * S) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hSS]
  rw [he, CFC.sqrt_mul_self τ.toOp τ.posSemidef.nonneg] at hs
  have ht := (Complex.nonneg_iff.mp hs.trace_nonneg).1
  rw [fidelity_comm]
  change τ.toOp.trace.re ≤ (CFC.sqrt (S * ρ.toOp * S)).trace.re
  simpa only [Matrix.trace_sub, Complex.sub_re, sub_nonneg] using ht

/-- Order domination bounds purified distance by the square root of twice the trace gap.
The proof combines the order-fidelity estimate with the missing-trace term. -/
theorem SubDensityOp.purifiedDistance_le_sqrt_two_mul_trace_gap_of_opLe
    (ρ τ : SubDensityOp X) (h : OpLe τ.toOp ρ.toOp) :
    purifiedDistance ρ τ ≤ Real.sqrt (2 * (ρ.trace - τ.trace)) := by
  have ht := ρ.trace_le_of_opLe τ h
  have hf := ρ.trace_le_fidelity_of_opLe τ h
  have hc : 1 - ρ.trace ≤ Real.sqrt ((1 - ρ.trace) * (1 - τ.trace)) := by
    apply (Real.le_sqrt (sub_nonneg.mpr ρ.trace_le_one)
      (mul_nonneg (sub_nonneg.mpr ρ.trace_le_one) (sub_nonneg.mpr τ.trace_le_one))).mpr
    change (1 - ρ.trace) ^ 2 ≤ (1 - ρ.trace) * (1 - τ.trace)
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left ht 1) (sub_nonneg.mpr ρ.trace_le_one)
  have hfg : 1 - (ρ.trace - τ.trace) ≤ fidelityGen ρ τ := by
    unfold fidelityGen
    linarith
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (fidelityGen ρ τ - 1)]

/-- A numerical upper bound on the trace gap yields the corresponding distance bound. -/
theorem SubDensityOp.purifiedDistance_le_sqrt_two_mul_trace_gap_epsilon_of_opLe
    (ρ τ : SubDensityOp X) (h : OpLe τ.toOp ρ.toOp) {ε : ℝ}
    (hgap : ρ.trace - τ.trace ≤ ε) : purifiedDistance ρ τ ≤ Real.sqrt (2 * ε) :=
  (ρ.purifiedDistance_le_sqrt_two_mul_trace_gap_of_opLe τ h).trans
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hgap (by norm_num)))

end Quantum.Operators

namespace Quantum.Metrics

open Quantum.Operators

/-- Purified distance separates sub-density states via the trace-distance bound. -/
theorem purifiedDistance_eq_zero_iff {X : Type*} [Fintype X] [Nonempty X]
    (ρ σ : SubDensityOp X) : purifiedDistance ρ σ = 0 ↔ ρ = σ := by
  constructor
  · intro h
    have hd := traceDistanceGen_le_purifiedDistance ρ σ
    rw [h] at hd
    have hn : traceNorm (ρ.toOp - σ.toOp) ≤ 0 := by
      unfold traceDistanceGen traceDistance at hd
      linarith [abs_nonneg ((ρ.toOp.trace - σ.toOp.trace).re)]
    have hz : ρ.toOp - σ.toOp = 0 := by
      let := Matrix.frobeniusNormedAddCommGroup (n := X) (m := X) (α := ℂ)
      exact norm_eq_zero.mp (le_antisymm ((frobenius_le_traceNorm _).trans hn) (norm_nonneg _))
    exact SubDensityOp.ext (sub_eq_zero.mp hz)
  · rintro rfl
    exact purifiedDistance_self ρ

end Quantum.Metrics
