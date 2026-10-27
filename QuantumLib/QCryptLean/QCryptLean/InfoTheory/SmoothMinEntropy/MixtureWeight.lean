import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.Math.Analysis.CompactSpaceIntegrable
import QCryptLean.Math.LinearAlgebra.Matrix.EntryIntegral
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-! # Mixture Weight -/


noncomputable section
namespace InfoTheory.SmoothMinEntropy
open Matrix Quantum.Operators Quantum.DeFinetti MeasureTheory
variable {A C Q : Type*} [Fintype A] [Fintype C] [Fintype Q]

/-- An almost-everywhere component acceptance bound also bounds the restricted mixture weight. -/
theorem CQState.sum_trace_entryIntegral_le (μ : DensityMeasure A)
    (f : DensityOp A → CQState C Q)
    (hf : ∀ c, Continuous (fun τ : DensityOp A => ((f τ).stateMap c).toOp))
    (S : Set (DensityOp A)) {ε : ℝ} (hε : 0 ≤ ε)
    (hb : ∀ᵐ τ ∂μ.measure.restrict S, ∑ c, ((f τ).stateMap c).trace ≤ ε) :
    ∑ c, (Matrix.of fun i j => ∫ τ in S, ((f τ).stateMap c).toOp i j ∂μ.measure).trace.re ≤ ε := by
  let := μ.isProbability
  have hi (c : C) (i j : Q) : Integrable
      (fun τ : DensityOp A => ((f τ).stateMap c).toOp i j) (μ.measure.restrict S) :=
    ((((continuous_apply j).comp (continuous_apply i)).comp
      (hf c)).integrable_of_compactSpace).restrict
  have ht (c : C) : Integrable
      (fun τ : DensityOp A => ((f τ).stateMap c).toOp.trace) (μ.measure.restrict S) :=
    integrable_finsetSum _ fun i _ => hi c i i
  have he (c : C) :
      (Matrix.of fun i j => ∫ τ in S, ((f τ).stateMap c).toOp i j ∂μ.measure).trace.re =
        ∫ τ in S, ((f τ).stateMap c).trace ∂μ.measure := by
    rw [Matrix.trace_entryIntegral (fun i => hi c i i)]
    exact (integral_re (ht c)).symm
  simp_rw [he]
  have htr (c : C) : Integrable (fun τ => ((f τ).stateMap c).trace)
      (μ.measure.restrict S) := (ht c).re
  rw [← integral_finsetSum _ (fun c _ => htr c)]
  have h := integral_mono_ae (integrable_finsetSum _ fun c _ => htr c)
    (integrable_const ε) hb
  apply h.trans
  rw [integral_const]
  have hm : (μ.measure.restrict S).real Set.univ ≤ 1 := by
    rw [Measure.real, Measure.restrict_apply_univ]
    exact (ENNReal.toReal_mono (by norm_num) (by
      calc μ.measure S ≤ μ.measure Set.univ := measure_mono (Set.subset_univ _)
           _ = 1 := measure_univ)).trans_eq ENNReal.toReal_one
  simpa only [smul_eq_mul, one_mul] using mul_le_mul_of_nonneg_right hm hε

end InfoTheory.SmoothMinEntropy
