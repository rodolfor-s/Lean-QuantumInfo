import QCryptLean.InfoTheory.Renyi.ConditionalVariance.Defs
import QCryptLean.InfoTheory.Renyi.PetzConditional
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.Quantum.Operators.Basic

/-! # Basic -/


noncomputable section

namespace InfoTheory.Renyi

open Quantum.Operators InfoTheory.SmoothMinEntropy

variable {C Q : Type*} [Fintype C] [DecidableEq C] [Fintype Q] [DecidableEq Q]

/-- Petz DOWN conditional entropy, with the fixed marginal reference, in bits. -/
def condPetzRenyiDown (α : ℝ) (ρ : CQState C Q) : ℝ :=
  - InfoTheory.Renyi.petzRenyiDivergence α ρ.toJointOp
    (Matrix.blockDiagonal (fun _ : C => ρ.quantumMarginal.toOp))

/-- Conditional von Neumann entropy in bits with the existing trace normalization. -/
def _root_.InfoTheory.SmoothMinEntropy.CQState.condVonNeumannBits
    (ρ : CQState C Q) : ℝ :=
  - InfoTheory.Renyi.relativeEntropyBits ρ.toJointOp
    (Matrix.blockDiagonal (fun _ : C => ρ.quantumMarginal.toOp))

/-- Conditional information variance in bits squared, with the same DOWN reference. -/
def condVariance (ρ : CQState C Q) : ℝ :=
  InfoTheory.Renyi.petzDivergenceVariance ρ.toJointOp
    (Matrix.blockDiagonal (fun _ : C => ρ.quantumMarginal.toOp))

/-- The completed Petz Rényi floor for an IID block. -/
def renyiBlockEntropyFloor (α ε : ℝ) (ρ : CQState C Q) (k : ℕ) : ℝ :=
  (k : ℝ) * condPetzRenyiDown α ρ - Real.logb 2 (2 / ε ^ 2) / (α - 1)

end InfoTheory.Renyi
