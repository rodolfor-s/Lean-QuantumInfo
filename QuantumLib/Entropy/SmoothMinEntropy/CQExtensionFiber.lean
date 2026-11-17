import QuantumLib.Entropy.SmoothMinEntropy.CQState
import QuantumLib.ForMathlib.LinearAlgebra.PartialTrace.Basic
import QuantumLib.ForPhyslib.QuantumInfo.Metrics.Basic
import QuantumLib.ForPhyslib.QuantumInfo.Metrics.ExtensionFiber
import QuantumLib.ForPhyslib.QuantumInfo.Metrics.Flagged
import QuantumLib.ForPhyslib.QuantumInfo.Metrics.FlaggedBounds
import QuantumLib.ForPhyslib.QuantumInfo.Operators.Basic
import QuantumLib.ForPhyslib.QuantumInfo.Operators.Algebra
import QuantumLib.ForPhyslib.QuantumInfo.Operators.StateOperations

/-! # CQExtension Fiber -/


noncomputable section
namespace InfoTheory.SmoothMinEntropy
open Matrix Quantum.Operators Quantum.Metrics
variable {C Q R : Type*} [Fintype C] [Fintype Q] [Fintype R]
  [DecidableEq C] [Nonempty C] [Nonempty Q] [Nonempty R]

omit [Nonempty C] in
/-- Every target CQ marginal has a blockwise extension attaining its marginal distance. -/
theorem CQState.exists_extension_of_partialTraceRight_purifiedDistance_eq
    (ρ : CQState C (Q × R)) (σ : CQState C Q) :
    ∃ τ : CQState C (Q × R), τ.partialTraceRight = σ ∧
      ρ.purifiedDistance τ = ρ.partialTraceRight.purifiedDistance σ := by
  have hb (c : C) := (ρ.stateMap c).exists_extension_of_partialTraceRight_fidelityGen_eq
    (σ.stateMap c)
  choose v hv hf using hb
  have ht (c : C) : (v c).trace = (σ.stateMap c).trace := by
    have h := congrArg SubDensityOp.trace (hv c)
    simpa only [SubDensityOp.trace, SubDensityOp.partialTraceRight,
      trace_partialTraceRight] using h
  let τ : CQState C (Q × R) := ⟨v, by simpa only [ht] using σ.weight_le_one⟩
  have hm : τ.partialTraceRight = σ := by
    apply CQState.ext
    exact funext hv
  have hρ (c : C) : (ρ.partialTraceRight.stateMap c).trace = (ρ.stateMap c).trace :=
    congrArg Complex.re (trace_partialTraceRight _)
  have hf' (c : C) : fidelity (ρ.stateMap c).toPosSemidefOp (v c).toPosSemidefOp =
      fidelity (ρ.partialTraceRight.stateMap c).toPosSemidefOp (σ.stateMap c).toPosSemidefOp := by
    have h := hf c
    change _ + Real.sqrt ((1 - (ρ.stateMap c).trace) * (1 - (v c).trace)) =
      _ + Real.sqrt ((1 - (ρ.partialTraceRight.stateMap c).trace) * (1 - (σ.stateMap c).trace)) at h
    rw [ht, hρ] at h
    exact add_right_cancel h
  have hj : fidelityGen ρ.toJointDensity τ.toJointDensity =
      fidelityGen ρ.partialTraceRight.toJointDensity σ.toJointDensity := by
    unfold fidelityGen
    change fidelity (cqBlockPosSemidefOp fun c => (ρ.stateMap c).toPosSemidefOp)
        (cqBlockPosSemidefOp fun c => (v c).toPosSemidefOp) + _ =
      fidelity (cqBlockPosSemidefOp fun c => (ρ.partialTraceRight.stateMap c).toPosSemidefOp)
        (cqBlockPosSemidefOp fun c => (σ.stateMap c).toPosSemidefOp) + _
    rw [fidelity_cqBlock_eq_sum, fidelity_cqBlock_eq_sum]
    simp only [hf', CQState.toJointDensity_trace]
    change _ + Real.sqrt ((1 - ∑ c, (ρ.stateMap c).trace) * (1 - ∑ c, (v c).trace)) = _
    simp only [ht, hρ]
  refine ⟨τ, hm, ?_⟩
  exact congrArg (fun f : ℝ => Real.sqrt (1 - f ^ 2)) hj

end InfoTheory.SmoothMinEntropy
