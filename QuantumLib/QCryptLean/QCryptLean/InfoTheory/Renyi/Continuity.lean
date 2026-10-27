import QCryptLean.InfoTheory.Renyi.ConditionalVariance.Continuity
import QCryptLean.InfoTheory.Renyi.Basic
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState

/-! # Continuity -/


noncomputable section

namespace InfoTheory.Renyi

open InfoTheory.SmoothMinEntropy

variable {C Q : Type*} [Fintype C] [Fintype Q] [DecidableEq C] [DecidableEq Q]

/-- The conditional Petz DOWN gap in bits. -/
def condPetzEntropyGap (α : ℝ) (ρ : CQState C Q) : ℝ :=
  ρ.condVonNeumannBits - condPetzRenyiDown α ρ

/-- The pointwise second-order remainder at tilt `2 - α`. -/
def secondOrderK (α : ℝ) (ρ : CQState C Q) : ℝ :=
  InfoTheory.Renyi.continuityRemainderScale (2 - α) *
    (2 : ℝ) ^ ((α - 1) * condPetzEntropyGap α ρ) *
    (Real.log ((2 : ℝ) ^ condPetzEntropyGap 2 ρ + Real.exp 2)) ^ 3

end InfoTheory.Renyi
