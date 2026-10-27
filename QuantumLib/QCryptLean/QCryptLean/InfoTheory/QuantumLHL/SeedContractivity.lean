import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.QuantumLHL.Extractor
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.CQTraceDistance
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceNormSum
import QCryptLean.Quantum.Operators.Basic

/-! # Public-seed hashing contracts generalized CQ trace distance -/
noncomputable section
namespace InfoTheory.QuantumLHL.SeedKey
open Matrix Quantum.Operators Quantum.Metrics
open InfoTheory.SmoothMinEntropy
variable {S C Z Q : Type*} [Fintype S] [Nonempty S] [Fintype C]
  [Fintype Z] [DecidableEq Z] [Fintype Q] [DecidableEq S] [DecidableEq C]

/-- Retaining a public uniform seed and hashing contracts generalized trace distance. -/
theorem traceDistanceGen_output_le (H : HashFamily S C Z) (ρ τ : CQState C Q) :
    traceDistanceGen (output H ρ).toJointDensity.toOp (output H τ).toJointDensity.toOp ≤
      traceDistanceGen ρ.toJointDensity.toOp τ.toJointDensity.toOp := by
  have hm (σ : CQState C Q) : (output H σ).quantumMarginal = σ.quantumMarginal := by
    apply SubDensityOp.ext
    exact sum_weightedOp H σ
  rw [CQState.traceDistanceGen_eq, CQState.traceDistanceGen_eq, hm, hm]
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have he (sz : S × Z) : ((output H ρ).stateMap sz).toOp -
      ((output H τ).stateMap sz).toOp =
      (↑((Fintype.card S : ℝ)⁻¹) : ℂ) • ∑ c,
        if H.hash sz.1 c = sz.2 then (ρ.stateMap c).toOp - (τ.stateMap c).toOp else 0 := by
    change weightedOp H ρ sz.1 sz.2 - weightedOp H τ sz.1 sz.2 = _
    rw [weightedOp, weightedOp, ← smul_sub, ← Finset.sum_sub_distrib]
    have hh (c : C) : (if H.hash sz.1 c = sz.2 then (ρ.stateMap c).toOp else 0) -
        (if H.hash sz.1 c = sz.2 then (τ.stateMap c).toOp else 0) =
        if H.hash sz.1 c = sz.2 then (ρ.stateMap c).toOp - (τ.stateMap c).toOp else 0 := by
      split_ifs <;> simp
    simp_rw [hh]
    ext i j
    simp [Matrix.smul_apply, one_div, Complex.real_smul]
  simp_rw [he, traceNorm_smul]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (show (0 : ℝ) ≤ (Fintype.card S : ℝ)⁻¹ by positivity)]
  calc
    _ ≤ ∑ sz : S × Z, (Fintype.card S : ℝ)⁻¹ * ∑ c,
        if H.hash sz.1 c = sz.2 then traceNorm ((ρ.stateMap c).toOp - (τ.stateMap c).toOp)
        else 0 := by
      apply Finset.sum_le_sum
      intro sz _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [apply_ite traceNorm, traceNorm_zero] using
        traceNorm_sum_le Finset.univ (fun c =>
          if H.hash sz.1 c = sz.2 then (ρ.stateMap c).toOp - (τ.stateMap c).toOp else 0)
    _ = _ := by
      rw [← Finset.mul_sum, Fintype.sum_prod_type]
      have hh (s : S) : (∑ z : Z, ∑ c : C,
          if H.hash s c = z then traceNorm ((ρ.stateMap c).toOp - (τ.stateMap c).toOp)
          else 0) = ∑ c, traceNorm ((ρ.stateMap c).toOp - (τ.stateMap c).toOp) := by
        rw [Finset.sum_comm]
        simp
      simp_rw [hh]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]

end InfoTheory.QuantumLHL.SeedKey
