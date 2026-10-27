import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDSingleCopyEnvelope
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.RtFunction
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPBits
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPRates
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPWeightBudget
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPWeights
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.MinEntropy
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-! # AEPEnvelope -/


namespace InfoTheory.SmoothMinEntropy.AEP.Spectral
open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder
open private four_le_div_add_div_add_two_of_pos
  from QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDSingleCopyEnvelope
variable {C Q : Type*} [Fintype C] [Fintype Q] [DecidableEq C] [DecidableEq Q]

/-- The exact single-copy `r_t` envelope, retaining the reference conditional entropy in bits. -/
theorem moment_le_rennerRt_sub_add_one (ρ : CQState C Q)
    (hρ : ∑ c, (ρ.stateMap c).trace = 1) (σ : DensityOp Q)
    (hscale : HasScale ρ σ.toSubDensityOp) {s : ℝ} (hs : 0 ≤ s)
    (hrange : s * Real.log (IID.rtBoundBase ρ σ) ≤ Real.log 2) :
    (∑ c, ((ρ.stateMap c).toOp ^ (1 + s) * σ.toOp ^ (-s)).trace.re) ≤
      InfoTheory.SmoothMinEntropy.rennerRt s (IID.rtBoundBase ρ σ) -
        s * Real.log 2 * referenceCondVonNeumannBits ρ hρ σ + 1 := by
  classical
  let Z := fun p : C × Q × Q => Real.exp (logRatio ρ σ p) + Real.exp (-logRatio ρ σ p) + 2
  have hZ (p : C × Q × Q) : 4 ≤ Z p := by
    have h := four_le_div_add_div_add_two_of_pos (Real.exp_pos (logRatio ρ σ p)) zero_lt_one
    simpa only [div_one, one_div, ← Real.exp_neg,
      add_comm (Real.exp (-logRatio ρ σ p)) (Real.exp (logRatio ρ σ p))] using h
  have hw := sum_weight ρ σ |>.trans hρ
  have hmean := sum_weight_mul_exp_add_exp_neg_add_two_le ρ hρ σ hscale
  have hmean4 : 4 ≤ ∑ p, weight ρ σ p * Z p := by
    calc
      4 = ∑ p, weight ρ σ p * 4 := by rw [← Finset.sum_mul, hw, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun p _ =>
        mul_le_mul_of_nonneg_left (hZ p) (weight_nonneg ρ σ p)
  have hμ4 : 4 ≤ IID.rtBoundBase ρ σ := hmean4.trans hmean
  have hhalf : s ≤ 1 / 2 := by
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 4) hμ4
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at hlog
    norm_num only [Nat.cast_ofNat] at hlog
    nlinarith [mul_le_mul_of_nonneg_left hlog hs, Real.log_pos one_lt_two]
  have hconc := InfoTheory.SmoothMinEntropy.concaveOn_rennerRt_Ici_four
    (t := s) ⟨by linarith, hhalf⟩
  have hJ := hconc.le_map_sum (t := Finset.univ) (w := weight ρ σ) (p := Z)
    (fun p _ => weight_nonneg ρ σ p) hw (fun p _ => hZ p)
  simp only [smul_eq_mul] at hJ
  have hmono := InfoTheory.SmoothMinEntropy.monotoneOn_rennerRt_Ici_one s
    (show (∑ p, weight ρ σ p * Z p) ∈ Set.Ici (1 : ℝ) by exact le_trans (by norm_num) hmean4)
    (show IID.rtBoundBase ρ σ ∈ Set.Ici (1 : ℝ) by exact le_trans (by norm_num) hμ4) hmean
  have hterm (p : C × Q × Q) : Real.exp (s * logRatio ρ σ p) ≤
      InfoTheory.SmoothMinEntropy.rennerRt s (Z p) + s * logRatio ρ σ p + 1 := by
    have h := InfoTheory.SmoothMinEntropy.div_rpow_le_rennerRt_sub_add_one
      (Real.exp_pos (logRatio ρ σ p)) zero_lt_one hs
    simpa only [div_one, one_div, ← Real.exp_neg, Real.log_exp, ← Real.exp_mul,
      mul_comm (logRatio ρ σ p) s,
      add_comm (Real.exp (-logRatio ρ σ p)) (Real.exp (logRatio ρ σ p)),
      mul_neg, sub_neg_eq_add] using h
  rw [← sum_weight_mul_exp ρ σ hscale hs]
  have hsum := Finset.sum_le_sum fun p (_ : p ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hterm p) (weight_nonneg ρ σ p)
  have he : (∑ p, weight ρ σ p *
      (InfoTheory.SmoothMinEntropy.rennerRt s (Z p) + s * logRatio ρ σ p + 1)) =
      (∑ p, weight ρ σ p * InfoTheory.SmoothMinEntropy.rennerRt s (Z p)) +
        s * (∑ p, weight ρ σ p * logRatio ρ σ p) + 1 := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib, hw]
    congr 2
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [he, sum_weight_mul_logRatio ρ hρ σ] at hsum
  nlinarith [hJ.trans hmono]

end InfoTheory.SmoothMinEntropy.AEP.Spectral
