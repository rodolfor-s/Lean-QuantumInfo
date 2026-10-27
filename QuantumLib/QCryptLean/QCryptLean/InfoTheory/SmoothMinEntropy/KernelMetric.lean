import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.Kernel
import QCryptLean.InfoTheory.SmoothMinEntropy.KernelOperations
import QCryptLean.Math.Probability.Bhattacharyya
import QCryptLean.Quantum.Channels.Classical
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Channels.LeftAmplification
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.Flagged
import QCryptLean.Quantum.Metrics.FlaggedBounds
import QCryptLean.Quantum.Metrics.PurifiedBasic
import QCryptLean.Quantum.Metrics.Purified
import QCryptLean.Quantum.Metrics.SubDensityMonotonicity
import QCryptLean.Quantum.Metrics.Tensor
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor

/-! # Purified-distance contraction for classical processing and normalized kernels -/

noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators Quantum.Channels Quantum.Metrics

variable {C D Q R : Type*} [Fintype C] [Fintype D] [Fintype Q] [Fintype R]
  [DecidableEq C] [DecidableEq D]

/-- Classical coarsening is the classical channel applied to the CQ joint state. -/
theorem CQState.toJointDensity_coarsen (f : C → D) (ρ : CQState C Q) :
    (isChannel_classicalMap f).mapIdTensor.applySubDensity ρ.toJointDensity =
      (ρ.coarsen f).toJointDensity := by
  apply SubDensityOp.ext
  ext p q
  have h := congrArg (fun M : Op D => M p.2 q.2)
    (Quantum.Channels.classicalMap_apply f
      (fun c d => ρ.toJointOp (p.1,c) (q.1,d)))
  refine h.trans ?_
  by_cases hpq : p.2 = q.2
  · simp only [CQState.toJointOp, Matrix.blockDiagonal_apply, ↓reduceIte, hpq,
      Matrix.sum_apply, Matrix.single_apply, and_self, CQState.toJointDensity,
      CQState.coarsen, CQState.ofBlocks]
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> rfl
  · simp only [CQState.toJointOp, Matrix.blockDiagonal_apply, ↓reduceIte,
      Matrix.sum_apply, Matrix.single_apply, ite_and, CQState.toJointDensity,
      CQState.coarsen, CQState.ofBlocks, hpq]
    apply Finset.sum_eq_zero
    intro c _
    by_cases hc : f c = p.2
    · simp [hc, hpq]
    · simp [hc]

/-- A deterministic coarsening contracts the full CQ purified distance. -/
theorem CQState.purifiedDistance_coarsen_le [Nonempty C] [Nonempty D] [Nonempty Q]
    (f : C → D) (ρ τ : CQState C Q) :
    (ρ.coarsen f).purifiedDistance (τ.coarsen f) ≤ ρ.purifiedDistance τ := by
  have h := Quantum.Metrics.purifiedDistance_apply_le
    (mapIdTensor Q (classicalMap f)) (isChannel_classicalMap f).mapIdTensor
    ρ.toJointDensity τ.toJointDensity
  simpa only [CQState.toJointDensity_coarsen, CQState.purifiedDistance] using h

/-- Attaching the same normalized left kernel contracts purified distance. -/
theorem CQState.purifiedDistance_tensorLeftKernel_le (ρ τ : CQState C Q)
    (K : C → SubDensityOp R) (hK : ∀ c, (K c).trace = 1) :
    (ρ.tensorLeftKernel K).purifiedDistance (τ.tensorLeftKernel K) ≤ ρ.purifiedDistance τ := by
  apply le_of_eq
  apply congrArg (fun f : ℝ => Real.sqrt (1 - f ^ 2))
  unfold fidelityGen
  change fidelity (cqBlockPosSemidefOp fun c => ((K c).kronecker (ρ.stateMap c)).toPosSemidefOp)
      (cqBlockPosSemidefOp fun c => ((K c).kronecker (τ.stateMap c)).toPosSemidefOp) + _ =
    fidelity (cqBlockPosSemidefOp fun c => (ρ.stateMap c).toPosSemidefOp)
      (cqBlockPosSemidefOp fun c => (τ.stateMap c).toPosSemidefOp) + _
  rw [fidelity_cqBlock_eq_sum, fidelity_cqBlock_eq_sum]
  have hf c : fidelity ((K c).kronecker (ρ.stateMap c)).toPosSemidefOp
      ((K c).kronecker (τ.stateMap c)).toPosSemidefOp =
      fidelity (ρ.stateMap c).toPosSemidefOp (τ.stateMap c).toPosSemidefOp := by
    change fidelity ((K c).toPosSemidefOp.kronecker (ρ.stateMap c).toPosSemidefOp)
      ((K c).toPosSemidefOp.kronecker (τ.stateMap c).toPosSemidefOp) = _
    rw [fidelity_kronecker, fidelity_self]
    change (K c).trace * _ = _
    rw [hK, one_mul]
  simp only [hf, CQState.toJointDensity_trace, CQState.tensorLeftKernel_weight _ _ hK]

/-- Attaching the same normalized right kernel contracts purified distance. -/
theorem CQState.purifiedDistance_tensorRightKernel_le (ρ τ : CQState C Q)
    (K : C → SubDensityOp R) (hK : ∀ c, (K c).trace = 1) :
    (ρ.tensorRightKernel K).purifiedDistance (τ.tensorRightKernel K) ≤ ρ.purifiedDistance τ := by
  apply le_of_eq
  apply congrArg (fun f : ℝ => Real.sqrt (1 - f ^ 2))
  unfold fidelityGen
  change fidelity (cqBlockPosSemidefOp fun c => ((ρ.stateMap c).kronecker (K c)).toPosSemidefOp)
      (cqBlockPosSemidefOp fun c => ((τ.stateMap c).kronecker (K c)).toPosSemidefOp) + _ =
    fidelity (cqBlockPosSemidefOp fun c => (ρ.stateMap c).toPosSemidefOp)
      (cqBlockPosSemidefOp fun c => (τ.stateMap c).toPosSemidefOp) + _
  rw [fidelity_cqBlock_eq_sum, fidelity_cqBlock_eq_sum]
  have hf c : fidelity ((ρ.stateMap c).kronecker (K c)).toPosSemidefOp
      ((τ.stateMap c).kronecker (K c)).toPosSemidefOp =
      fidelity (ρ.stateMap c).toPosSemidefOp (τ.stateMap c).toPosSemidefOp := by
    change fidelity ((ρ.stateMap c).toPosSemidefOp.kronecker (K c).toPosSemidefOp)
      ((τ.stateMap c).toPosSemidefOp.kronecker (K c).toPosSemidefOp) = _
    rw [fidelity_kronecker, fidelity_self]
    change _ * (K c).trace = _
    rw [hK, mul_one]
  simp only [hf, CQState.toJointDensity_trace, CQState.tensorRightKernel_weight _ _ hK]
/-- Attaching a common subnormalized ancilla contracts the full CQ purified distance. -/
theorem CQState.purifiedDistance_tensorRight_const_le (ρ σ : CQState C Q) (τ : SubDensityOp R) :
    (ρ.tensorRightKernel (fun _ => τ)).purifiedDistance
      (σ.tensorRightKernel (fun _ => τ)) ≤ ρ.purifiedDistance σ := by
  unfold CQState.purifiedDistance
  apply purifiedDistance_le_of_le_fidelityGen
  have htr (υ : CQState C Q) : (υ.tensorRightKernel (fun _ => τ)).toJointDensity.trace =
      υ.toJointDensity.trace * τ.trace := by
    simp only [CQState.toJointDensity_trace, CQState.tensorRightKernel_stateMap,
      subDensityOp_kronecker_trace, Finset.sum_mul]
  have hf : fidelity (ρ.tensorRightKernel (fun _ => τ)).toJointDensity.toPosSemidefOp
      (σ.tensorRightKernel (fun _ => τ)).toJointDensity.toPosSemidefOp =
      τ.trace * fidelity ρ.toJointDensity.toPosSemidefOp σ.toJointDensity.toPosSemidefOp := by
    change fidelity (cqBlockPosSemidefOp fun c => ((ρ.stateMap c).kronecker τ).toPosSemidefOp)
      (cqBlockPosSemidefOp fun c => ((σ.stateMap c).kronecker τ).toPosSemidefOp) =
      τ.trace * fidelity (cqBlockPosSemidefOp fun c => (ρ.stateMap c).toPosSemidefOp)
        (cqBlockPosSemidefOp fun c => (σ.stateMap c).toPosSemidefOp)
    rw [fidelity_cqBlock_eq_sum, fidelity_cqBlock_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    change fidelity ((ρ.stateMap c).toPosSemidefOp.kronecker τ.toPosSemidefOp)
      ((σ.stateMap c).toPosSemidefOp.kronecker τ.toPosSemidefOp) = _
    rw [fidelity_kronecker, fidelity_self, mul_comm]
    rfl
  unfold fidelityGen
  rw [hf, htr, htr]
  exact Real.add_sqrt_le_scale_add_sqrt
    ⟨ρ.toJointDensity.trace_nonneg, ρ.toJointDensity.trace_le_one⟩
    ⟨σ.toJointDensity.trace_nonneg, σ.toJointDensity.trace_le_one⟩
    ⟨τ.trace_nonneg, τ.trace_le_one⟩ (fidelity_nonneg _ _)
    (fidelity_le_sqrt_trace_mul_trace _ _)

end InfoTheory.SmoothMinEntropy
