import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.SpectralCapBlock
import QCryptLean.InfoTheory.SmoothMinEntropy.SpectralCapFidelity
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.Flagged
import QCryptLean.Quantum.Metrics.FlaggedBounds
import QCryptLean.Quantum.Metrics.PurifiedBasic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.StateOperations

/-! # Spectral Cap State -/


noncomputable section
namespace InfoTheory.SmoothMinEntropy.SpectralCap
open Matrix Quantum.Operators Quantum.Metrics
open scoped ComplexOrder MatrixOrder
variable {C Q : Type*} [Fintype C] [Fintype Q] [DecidableEq Q]

/-- Cap each classical block at the same positive reference. -/
def cqState (ρ : CQState C Q) (σ : SubDensityOp Q) (ell : ℝ) (hell : 0 ≤ ell) : CQState C Q where
  stateMap c :=
    ⟨block (ρ.stateMap c).toPosSemidefOp σ.toPosSemidefOp ell,
      block_posSemidef _ _ hell,
      (trace_block_le _ _ hell).trans (ρ.stateMap c).trace_le_one⟩
  weight_le_one := (Finset.sum_le_sum fun _ _ => trace_block_le _ _ hell).trans ρ.weight_le_one

/-- The cap parameter is a feasible scale against the original reference. -/
theorem cqState_isFeasible (ρ : CQState C Q) (σ : SubDensityOp Q)
    {ell : ℝ} (hell : 0 ≤ ell) : IsFeasible (cqState ρ σ ell hell) σ ell := by
  refine ⟨hell, fun c => opLe_of_posSemidef_sub ?_⟩
  exact Matrix.le_iff.mp (block_le_reference (ρ.stateMap c).toPosSemidefOp
    σ.toPosSemidefOp hell)

/-- The capped joint trace cannot exceed the original joint trace. -/
theorem cqState_trace_le [DecidableEq C] (ρ : CQState C Q) (σ : SubDensityOp Q)
    {ell : ℝ} (hell : 0 ≤ ell) :
    (cqState ρ σ ell hell).toJointDensity.trace ≤ ρ.toJointDensity.trace := by
  rw [CQState.toJointDensity_trace, CQState.toJointDensity_trace]
  exact Finset.sum_le_sum fun c _ => trace_block_le _ _ hell

/-- The capped joint trace is a fidelity lower bound, including subnormalized input. -/
theorem cqState_trace_le_fidelity [DecidableEq C] [Nonempty Q]
    (ρ : CQState C Q) (σ : SubDensityOp Q) {ell : ℝ} (hell : 0 ≤ ell) :
    (cqState ρ σ ell hell).toJointDensity.trace ≤
      fidelity ρ.toJointDensity.toPosSemidefOp
        (cqState ρ σ ell hell).toJointDensity.toPosSemidefOp := by
  rw [CQState.toJointDensity_trace]
  change _ ≤ fidelity (cqBlockPosSemidefOp (fun c => (ρ.stateMap c).toPosSemidefOp))
    (cqBlockPosSemidefOp (fun c => ((cqState ρ σ ell hell).stateMap c).toPosSemidefOp))
  rw [fidelity_cqBlock_eq_sum]
  exact Finset.sum_le_sum fun c _ => trace_block_le_fidelity _ _ hell

/-- For a normalized input, the cap's trace deficit bounds its squared purified distance. -/
theorem cqState_purifiedDistance_le [DecidableEq C] [Nonempty Q]
    (ρ : CQState C Q) (hρ : ∑ c, (ρ.stateMap c).trace = 1) (σ : SubDensityOp Q)
    {ell : ℝ} (hell : 0 ≤ ell) :
    ρ.purifiedDistance (cqState ρ σ ell hell) ≤
      Real.sqrt (2 * (1 - (cqState ρ σ ell hell).toJointDensity.trace)) := by
  have ht : ρ.toJointDensity.trace = 1 := (CQState.toJointDensity_trace ρ).trans hρ
  have hf := cqState_trace_le_fidelity ρ σ hell
  unfold CQState.purifiedDistance Quantum.Metrics.purifiedDistance
  rw [fidelityGen_eq_fidelity_of_trace_one _ _ ht]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (fidelity ρ.toJointDensity.toPosSemidefOp
    (cqState ρ σ ell hell).toJointDensity.toPosSemidefOp - 1)]

end InfoTheory.SmoothMinEntropy.SpectralCap
