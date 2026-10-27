import QCryptLean.InfoTheory.RelativeEntropy.Basic
import QCryptLean.InfoTheory.Renyi.ConditionalVariance.CQReference
import QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
import QCryptLean.InfoTheory.Renyi.PetzConditional
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPBits
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Normalized
import QCryptLean.InfoTheory.VonNeumannEntropy.TraceFormula
import QCryptLean.Math.LinearAlgebra.Matrix.BlockCFC
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.StateOperations

/-! # AEPWeights -/


noncomputable section
namespace InfoTheory.SmoothMinEntropy.AEP.Spectral
open Matrix Quantum.Operators
open InfoTheory.VonNeumannEntropy
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open private nsW nsL nsW_nonneg nsW_sum nsWL_sum nsW_exp_sum nsW_exp_neg_le
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights
open private mulVec_eq_zero_of_le
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.CQReference
variable {C Q : Type*} [Fintype C] [Fintype Q] [DecidableEq Q]

/-- The spectral sample weight of a classical block and two basis labels. -/
def weight (ρ : CQState C Q) (σ : DensityOp Q) (p : C × Q × Q) : ℝ :=
  nsW (ρ.stateMap p.1).isHermitian σ.isHermitian p.2

/-- The spectral log-likelihood ratio in nats, with the inherited zero-log convention. -/
def logRatio (ρ : CQState C Q) (σ : DensityOp Q) (p : C × Q × Q) : ℝ :=
  nsL (ρ.stateMap p.1).isHermitian σ.isHermitian p.2

/-- Every CQ spectral weight is nonnegative. -/
theorem weight_nonneg (ρ : CQState C Q) (σ : DensityOp Q) (p : C × Q × Q) :
    0 ≤ weight ρ σ p := nsW_nonneg _ _ (ρ.stateMap p.1).posSemidef.nonneg p.2

/-- The complete spectral distribution has the original CQ weight. -/
theorem sum_weight (ρ : CQState C Q) (σ : DensityOp Q) :
    ∑ p, weight ρ σ p = ∑ c, (ρ.stateMap c).trace := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun c _ => nsW_sum (ρ.stateMap c).isHermitian σ.isHermitian

/-- Positive spectral moments equal the CFC collision moments under the support condition. -/
theorem sum_weight_mul_exp (ρ : CQState C Q) (σ : DensityOp Q)
    (hscale : HasScale ρ σ.toSubDensityOp) {s : ℝ} (hs : 0 ≤ s) :
    ∑ p, weight ρ σ p * Real.exp (s * logRatio ρ σ p) =
      ∑ c, ((ρ.stateMap c).toOp ^ (1 + s) * σ.toOp ^ (-s)).trace.re := by
  obtain ⟨t, ht⟩ := hscale
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  have hle : (ρ.stateMap c).toOp ≤ (t : ℂ) • σ.toOp := Matrix.le_iff.mpr
    ((opLe_iff_posSemidef_sub (ρ.stateMap c).isHermitian
      (σ.posSemidef.smul (Complex.zero_le_real.mpr ht.1)).isHermitian).mp (ht.2 c))
  have hsup (v : Q → ℂ) (hv : σ.toOp *ᵥ v = 0) : (ρ.stateMap c).toOp *ᵥ v = 0 :=
    mulVec_eq_zero_of_le (ρ.stateMap c).posSemidef.nonneg hle
      (by simp [Matrix.smul_mulVec, hv])
  have he := nsW_exp_sum (ρ.stateMap c).isHermitian σ.isHermitian
    (ρ.stateMap c).posSemidef.nonneg σ.posSemidef.nonneg hsup
    (show 0 < 1 + s by linarith)
  simpa only [weight, logRatio, add_sub_cancel_left,
    show 1 - (1 + s) = -s by ring, InfoTheory.Renyi.petzTrace] using he

/-- The mean spectral log-ratio is the negative reference conditional entropy in nats. -/
theorem sum_weight_mul_logRatio [DecidableEq C] (ρ : CQState C Q)
    (hρ : ∑ c, (ρ.stateMap c).trace = 1) (σ : DensityOp Q) :
    ∑ p, weight ρ σ p * logRatio ρ σ p =
      -Real.log 2 * referenceCondVonNeumannBits ρ hρ σ := by
  have he : (∑ p, weight ρ σ p * logRatio ρ σ p) =
      ∑ c, ((ρ.stateMap c).toOp * (CFC.log (ρ.stateMap c).toOp - CFC.log σ.toOp)).trace.re := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun c _ => nsWL_sum (ρ.stateMap c).isHermitian σ.isHermitian
  rw [he]
  simp only [mul_sub, trace_sub, Complex.sub_re, Finset.sum_sub_distrib]
  have hb : ((ρ.toJointDensityOp hρ).toOp *
      CFC.log (ρ.toJointDensityOp hρ).toOp).trace.re =
      ∑ c, ((ρ.stateMap c).toOp * CFC.log (ρ.stateMap c).toOp).trace.re := by
    change (blockDiagonal (fun c => (ρ.stateMap c).toOp) *
      cfc Real.log (blockDiagonal (fun c => (ρ.stateMap c).toOp))).trace.re = _
    rw [cfc_blockDiagonal _ (fun c => (ρ.stateMap c).isHermitian) _,
      ← blockDiagonal_mul, trace_blockDiagonal, Complex.re_sum]
    rfl
  have hm : ((ρ.quantumMarginalDensityOp hρ).toOp * CFC.log σ.toOp).trace.re =
      ∑ c, ((ρ.stateMap c).toOp * CFC.log σ.toOp).trace.re := by
    change ((∑ c, (ρ.stateMap c).toOp) * CFC.log σ.toOp).trace.re = _
    rw [Finset.sum_mul, trace_sum, Complex.re_sum]
  rw [← hb, ← hm]
  unfold referenceCondVonNeumannBits InfoTheory.RelativeEntropy.relativeEntropyReal
    InfoTheory.RelativeEntropy.traceProductLogSigma
  rw [vonNeumannEntropy_eq_neg_trace_mul_log (ρ.toJointDensityOp hρ)]
  have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  simp only [CFC.log]
  field_simp
  ring

end InfoTheory.SmoothMinEntropy.AEP.Spectral
