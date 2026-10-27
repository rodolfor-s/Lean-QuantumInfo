import QCryptLean.Quantum.Metrics.PurifiedDistanceWeightFloor
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.Purified
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.StateOperations

/-! # Weight Floor -/


namespace Quantum.Metrics

open Quantum.Operators

/-- Purified-distance closeness gives the scalar Bhattacharyya lower bound on
the traces of two sub-density operators. -/
theorem SubDensityOp.sqrt_one_sub_sq_le_bhattacharyya
    {X : Type*} [Fintype X] (ρ τ : SubDensityOp X) {ε : ℝ}
    (hε_nn : 0 ≤ ε)
    (hε_sq_lt_trace : ε ^ 2 < ρ.trace)
    (hP : purifiedDistance ρ τ ≤ ε) :
    Real.sqrt (1 - ε ^ 2) ≤
      Real.sqrt (ρ.trace * τ.trace) +
        Real.sqrt ((1 - ρ.trace) * (1 - τ.trace)) := by
  have hP_nn : 0 ≤ purifiedDistance ρ τ := purifiedDistance_nonneg
    ρ τ
  have hP_sq_le : purifiedDistance ρ τ ^ 2 ≤ ε ^ 2 := by
    exact sq_le_sq' (by linarith [hε_nn, hP_nn]) hP
  have hP_sq_eq : purifiedDistance ρ τ ^ 2 = 1 - fidelityGen ρ τ ^ 2 :=
    purifiedDistance_sq ρ τ
  have h_one_sub_eps_sq_le_fidelity_sq : 1 - ε ^ 2 ≤ fidelityGen ρ τ ^ 2 := by
    rw [hP_sq_eq] at hP_sq_le
    linarith
  have hε_sq_lt_one : ε ^ 2 < 1 := lt_of_lt_of_le hε_sq_lt_trace ρ.trace_le_one
  have h_one_sub_eps_sq_nonneg : 0 ≤ 1 - ε ^ 2 := by
    linarith
  have h_sqrt_le_fidelityGen :
      Real.sqrt (1 - ε ^ 2) ≤ fidelityGen ρ τ := by
    have hsq :
        Real.sqrt (1 - ε ^ 2) ^ 2 ≤ fidelityGen ρ τ ^ 2 := by
      rwa [Real.sq_sqrt h_one_sub_eps_sq_nonneg]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (fidelityGen_nonneg ρ τ)).mp hsq
  have h_fidelity_le_sqrt :
      fidelity ρ.toPosSemidefOp τ.toPosSemidefOp ≤
        Real.sqrt (ρ.trace * τ.trace) := by
    exact fidelity_le_sqrt_trace_mul_trace ρ.toPosSemidefOp τ.toPosSemidefOp
  have h_fidelityGen_le_bhattacharyya :
      fidelityGen ρ τ ≤
        Real.sqrt (ρ.trace * τ.trace) +
          Real.sqrt ((1 - ρ.trace) * (1 - τ.trace)) := by
    unfold fidelityGen
    exact add_le_add h_fidelity_le_sqrt (le_refl _)
  exact le_trans h_sqrt_le_fidelityGen h_fidelityGen_le_bhattacharyya

/-- Operator-level total-trace floor for an `ε` purified-distance ball. -/
theorem SubDensityOp.purifiedDistanceWeightFloor_le_trace
    {X : Type*} [Fintype X] (ρ τ : SubDensityOp X) {ε : ℝ}
    (hε_nn : 0 ≤ ε)
    (hε_sq_lt_trace : ε ^ 2 < ρ.trace)
    (hP : purifiedDistance ρ τ ≤ ε) :
    Quantum.Metrics.purifiedDistanceWeightFloor ε ρ.trace ≤ τ.trace := by
  exact Quantum.Metrics.purifiedDistanceWeightFloor_le_of_bhattacharyya_lower
    ⟨ρ.trace_nonneg, ρ.trace_le_one⟩
    ⟨τ.trace_nonneg, τ.trace_le_one⟩
    hε_nn
    hε_sq_lt_trace
    (SubDensityOp.sqrt_one_sub_sq_le_bhattacharyya
      ρ τ hε_nn hε_sq_lt_trace hP)

end Quantum.Metrics
