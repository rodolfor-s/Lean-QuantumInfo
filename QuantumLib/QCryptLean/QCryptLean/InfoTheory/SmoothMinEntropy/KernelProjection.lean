import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-! # Marginal identities through coarsening and spectator announcements -/

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators Matrix

variable {C D Q R V : Type*} [Fintype C] [Fintype D] [Fintype Q]
  [Fintype R] [Fintype V]

/-- Keeping classical outcomes never increases total mass and never renormalizes it. -/
theorem CQState.filterKeep_weight_le (ρ : CQState C Q) (keep : C → Bool) :
    ∑ c, ((ρ.filterKeep keep).stateMap c).trace ≤ ∑ c, (ρ.stateMap c).trace := by
  apply Finset.sum_le_sum
  intro c _
  cases h : keep c
  · simpa [CQState.filterKeep, h, SubDensityOp.zero, SubDensityOp.trace] using
      (ρ.stateMap c).trace_nonneg
  · simp [CQState.filterKeep, h]

/-- Coarsening classical labels commutes with tracing out a quantum factor. -/
theorem CQState.partialTraceRight_coarsen [DecidableEq D]
    (ρ : CQState C (Q × V)) (f : C → D) :
    (ρ.coarsen f).partialTraceRight = ρ.partialTraceRight.coarsen f := by
  ext d i j
  simp only [CQState.partialTraceRight, CQState.coarsen, CQState.ofBlocks,
    SubDensityOp.partialTraceRight_toOp, Matrix.partialTraceRight, Matrix.of_apply,
    Matrix.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp

/-- A fixed left announcement survives a trailing trace-out identity unchanged. -/
theorem CQState.partialTraceRight_tensorLeftKernel
    (ρQV : CQState C (Q × V)) (ρ : CQState C Q) (K : C → SubDensityOp R)
    (hblocks : ∀ c, Matrix.partialTraceRight (ρQV.stateMap c).toOp = (ρ.stateMap c).toOp) :
    ((ρQV.tensorLeftKernel K).reindex (Equiv.prodAssoc R Q V).symm).partialTraceRight =
      ρ.tensorLeftKernel K := by
  ext c ⟨r,q⟩ ⟨s,t⟩
  change (∑ v, (K c).toOp r s * (ρQV.stateMap c).toOp (q,v) (t,v)) =
    (K c).toOp r s * (ρ.stateMap c).toOp q t
  rw [← Finset.mul_sum, ← hblocks c]
  rfl

end InfoTheory.SmoothMinEntropy
