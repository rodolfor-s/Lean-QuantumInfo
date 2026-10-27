import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.StateOperations

/-!
# Elementary identities for fidelity and purified distance

The Löwner order is opened only for the square-root
identity; no matrix norm instance is changed.
-/

namespace Quantum.Metrics

open Matrix Quantum.Operators
open scoped MatrixOrder

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Self-fidelity is the trace, also for unnormalized positive operators. -/
theorem fidelity_self (A : PosSemidefOp X) : fidelity A A = A.val.trace.re := by
  classical
  have h := sqrtPosSemidefOp_mul_self A
  have hi : sqrtPosSemidefOp A * A.val * sqrtPosSemidefOp A = A.val * A.val := by
    calc
      _ = (sqrtPosSemidefOp A * sqrtPosSemidefOp A) *
          (sqrtPosSemidefOp A * sqrtPosSemidefOp A) := by
        conv_lhs => rw [← h]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [h]
  simp only [fidelity, hi, CFC.sqrt_mul_self A.val A.property.nonneg]

/-- Generalized fidelity of a state with itself is one, even for the zero state. -/
theorem fidelityGen_self (ρ : SubDensityOp X) : fidelityGen ρ ρ = 1 := by
  rw [fidelityGen, fidelity_self]
  change ρ.trace + Real.sqrt ((1 - ρ.trace) * (1 - ρ.trace)) = 1
  rw [Real.sqrt_mul_self (show 0 ≤ 1 - ρ.trace from sub_nonneg.mpr ρ.trace_le_one)]
  ring

/-- Purified distance vanishes on the diagonal. -/
theorem purifiedDistance_self (ρ : SubDensityOp X) : purifiedDistance ρ ρ = 0 := by
  simp [purifiedDistance, fidelityGen_self]

/-- A normalized argument removes the missing-mass correction from fidelity. -/
theorem fidelityGen_eq_fidelity_of_trace_one (ρ σ : SubDensityOp X) (h : ρ.trace = 1) :
    fidelityGen ρ σ = fidelity ρ.toPosSemidefOp σ.toPosSemidefOp := by
  simp [fidelityGen, h]

/-- Generalized fidelity decreases exactly when purified distance increases. -/
theorem purifiedDistance_le_of_le_fidelityGen (ρ σ : SubDensityOp X) (τ υ : SubDensityOp Y)
    (h : fidelityGen τ υ ≤ fidelityGen ρ σ) :
    purifiedDistance ρ σ ≤ purifiedDistance τ υ := by
  apply Real.sqrt_le_sqrt
  nlinarith [fidelityGen_nonneg ρ σ, fidelityGen_nonneg τ υ]

/-- Distance to the zero substate is the square root of the retained trace mass. -/
@[simp] theorem purifiedDistance_zero (ρ : SubDensityOp X) :
    purifiedDistance ρ SubDensityOp.zero = Real.sqrt ρ.trace := by
  classical
  have hf : fidelity ρ.toPosSemidefOp
      (SubDensityOp.zero : SubDensityOp X).toPosSemidefOp = 0 := by
    simp [fidelity, SubDensityOp.toPosSemidefOp, SubDensityOp.zero]
  have hz : (SubDensityOp.zero : SubDensityOp X).trace = 0 := by
    simp [SubDensityOp.trace, SubDensityOp.zero]
  rw [purifiedDistance, fidelityGen, hf, hz, zero_add, sub_zero, mul_one,
    Real.sq_sqrt (show 0 ≤ 1 - ρ.trace from sub_nonneg.mpr ρ.trace_le_one),
    sub_sub_cancel]

end Quantum.Metrics
