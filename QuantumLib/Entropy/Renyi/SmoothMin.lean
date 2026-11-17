import QuantumLib.Entropy.Renyi.PetzConditional
import QuantumLib.Entropy.Renyi.Basic
import QuantumLib.Entropy.Renyi.Reindex
import QuantumLib.Entropy.Renyi.PetzSmooth
import QuantumLib.Entropy.Renyi.PetzTensor
import QuantumLib.Entropy.SmoothMinEntropy.AEPRates
import QuantumLib.Entropy.SmoothMinEntropy.CQState
import QuantumLib.Entropy.SmoothMinEntropy.Normalized
import QuantumLib.Entropy.SmoothMinEntropy.Smooth
import QuantumLib.ForPhyslib.QuantumInfo.Operators.Basic
import QuantumLib.ForPhyslib.QuantumInfo.Operators.StateOperations

/-! # Smooth Min -/


noncomputable section

namespace InfoTheory.Renyi

open Quantum.Operators InfoTheory.SmoothMinEntropy

variable {C Q : Type*} [Fintype C] [Fintype Q] [DecidableEq C] [DecidableEq Q]

/-- Petz DOWN entropy is additive on function-indexed IID blocks. -/
theorem condPetzRenyiDown_tensorPower (α : ℝ) (ρ : CQState C Q) (k : ℕ) :
    condPetzRenyiDown α (ρ.tensorPower k) = k * condPetzRenyiDown α ρ := by
  rw [condPetzRenyiDown, petzRenyiDivergence, petzTrace_tensorPower]
  simp only [condPetzRenyiDown, petzRenyiDivergence, Real.logb, Real.log_pow]
  ring

/-- The fixed-marginal Petz floor bounds the entire extended smoothing domain. -/
theorem TensorPower.ofReal_mul_condPetzRenyiDown_sub_le_smoothMinEntropy
    (α : ℝ) (hα : 1 < α) (ε : ℝ) (hε : 0 < ε)
    (ρ : CQState C Q) (hρ : ∑ c, (ρ.stateMap c).trace = 1) (k : ℕ) :
    ENNReal.ofReal (renyiBlockEntropyFloor α ε ρ k) ≤
      smoothMinEntropy ε (ρ.tensorPower k)
        (AEP.IID.tensorReference (ρ.quantumMarginalDensityOp hρ) k) := by
  have h := ofReal_condPetzRenyiDown_sub_le_smoothMinEntropy α hα ε hε
    (ρ.tensorPower k) (ρ.tensorPower_sum_trace hρ k)
  rw [condPetzRenyiDown_tensorPower] at h
  have hm : (ρ.tensorPower k).quantumMarginal =
      AEP.IID.tensorReference (ρ.quantumMarginalDensityOp hρ) k := by
    apply SubDensityOp.ext
    exact ρ.tensorPower_quantumMarginal k
  rw [hm] at h
  exact h

/-- Native reformulation using the block Petz entropy rather than its per-copy value. -/
theorem ofReal_condPetzRenyiDown_tensorPower_sub_le_smoothMinEntropy
    (α : ℝ) (hα : 1 < α) (ε : ℝ) (hε : 0 < ε)
    (ρ : CQState C Q) (hρ : ∑ c, (ρ.stateMap c).trace = 1) (k : ℕ) :
    ENNReal.ofReal (condPetzRenyiDown α (ρ.tensorPower k) -
      Real.logb 2 (2 / ε ^ 2) / (α - 1)) ≤
      smoothMinEntropy ε (ρ.tensorPower k)
        (AEP.IID.tensorReference (ρ.quantumMarginalDensityOp hρ) k) := by
  rw [condPetzRenyiDown_tensorPower]
  exact TensorPower.ofReal_mul_condPetzRenyiDown_sub_le_smoothMinEntropy α hα ε hε ρ hρ k

end InfoTheory.Renyi
