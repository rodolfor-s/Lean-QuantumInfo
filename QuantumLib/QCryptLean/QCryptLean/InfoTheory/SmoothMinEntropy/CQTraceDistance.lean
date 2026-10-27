import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceNormFinite
import QCryptLean.Quantum.Metrics.TraceNormSum
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-! # Generalized trace distance for classical–quantum blocks -/
noncomputable section
namespace InfoTheory.SmoothMinEntropy
open Matrix Quantum.Operators Quantum.Metrics
variable {C Q : Type*} [Fintype C] [Fintype Q]

/-- Generalized CQ trace distance separates into block trace norms and the total weight deficit. -/
theorem CQState.traceDistanceGen_eq [DecidableEq C] (ρ τ : CQState C Q) :
    traceDistanceGen ρ.toJointDensity.toOp τ.toJointDensity.toOp =
      (1 / 2) * (∑ c, traceNorm ((ρ.stateMap c).toOp - (τ.stateMap c).toOp)) +
      (1 / 2) * |ρ.quantumMarginal.trace - τ.quantumMarginal.trace| := by
  have ht (σ : CQState C Q) : σ.toJointDensity.toOp.trace.re = σ.quantumMarginal.trace := by
    rw [← SubDensityOp.trace, CQState.toJointDensity_trace, CQState.quantumMarginal_trace]
  simp only [traceDistanceGen, traceDistance, Complex.sub_re, ht]
  change (1 / 2 : ℝ) * traceNorm (blockDiagonal (fun c => (ρ.stateMap c).toOp) -
    blockDiagonal (fun c => (τ.stateMap c).toOp)) + _ = _
  rw [← blockDiagonal_sub, traceNorm_blockDiagonal]
  rfl

/-- Forgetting the classical register contracts generalized trace distance. -/
theorem CQState.traceDistanceGen_quantumMarginal_le [DecidableEq C] (ρ τ : CQState C Q) :
    traceDistanceGen ρ.quantumMarginal.toOp τ.quantumMarginal.toOp ≤
      traceDistanceGen ρ.toJointDensity.toOp τ.toJointDensity.toOp := by
  rw [CQState.traceDistanceGen_eq]
  simp only [traceDistanceGen, traceDistance, Complex.sub_re, SubDensityOp.trace]
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  change traceNorm ((∑ c, (ρ.stateMap c).toOp) - ∑ c, (τ.stateMap c).toOp) ≤ _
  rw [← Finset.sum_sub_distrib]
  exact traceNorm_sum_le _ _

/-- Attaching an independent uniform classical register preserves generalized trace distance. -/
theorem traceDistanceGen_uniformCQState [DecidableEq C] [Nonempty C] (σ τ : SubDensityOp Q) :
    traceDistanceGen (uniformCQState (C := C) σ).toJointDensity.toOp
      (uniformCQState (C := C) τ).toJointDensity.toOp = traceDistanceGen σ.toOp τ.toOp := by
  rw [CQState.traceDistanceGen_eq, uniformCQState_quantumMarginal,
    uniformCQState_quantumMarginal]
  have he (c : C) : ((uniformCQState (C := C) σ).stateMap c).toOp -
      ((uniformCQState (C := C) τ).stateMap c).toOp =
      (↑((Fintype.card C : ℝ)⁻¹) : ℂ) • (σ.toOp - τ.toOp) := (smul_sub _ _ _).symm
  simp only [he, traceNorm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ (Fintype.card C : ℝ)⁻¹ by positivity),
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc (Fintype.card C : ℝ), mul_inv_cancel₀
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]
  rfl

end InfoTheory.SmoothMinEntropy
