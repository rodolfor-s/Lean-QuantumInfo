import QCryptLean.InfoTheory.RelativeEntropy.Basic
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IIDBennett
import QCryptLean.InfoTheory.SmoothMinEntropy.AEPRates
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.Normalized
import QCryptLean.InfoTheory.VonNeumannEntropy.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-! # AEPBits -/


noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators InfoTheory.VonNeumannEntropy

variable {C Q : Type*} [Fintype C] [Fintype Q] [DecidableEq C] [DecidableEq Q]

/-- Conditional entropy relative to a fixed reference, converted from nats to bits. -/
def referenceCondVonNeumannBits (ρ : CQState C Q) (hρ : ∑ c, (ρ.stateMap c).trace = 1)
    (σ : DensityOp Q) : ℝ :=
  (vonNeumannEntropy (ρ.toJointDensityOp hρ) - vonNeumannEntropy (ρ.quantumMarginalDensityOp hρ)
    - InfoTheory.RelativeEntropy.relativeEntropyReal
      (ρ.quantumMarginalDensityOp hρ) σ) / Real.log 2

namespace AEP.IID

/-- The Renner floor after converting the entropy contribution to bits. -/
def bitEntropyFloor (ρ : CQState C Q) (hρ : ∑ c, (ρ.stateMap c).trace = 1)
    (σ : DensityOp Q) (k : ℕ) (ε : ℝ) : ℝ :=
  referenceCondVonNeumannBits ρ hρ σ - penalty ρ σ k ε

/-- The bit-normalized Renner floor for the complete block. -/
def bitBlockEntropyFloor (ρ : CQState C Q) (hρ : ∑ c, (ρ.stateMap c).trace = 1)
    (σ : DensityOp Q) (k : ℕ) (ε : ℝ) : ℝ := k * bitEntropyFloor ρ hρ σ k ε

omit [DecidableEq C] in
/-- The exact Bennett correction uses the scalar tilt width. -/
def bennettPenalty (ρ : CQState C Q) (σ : DensityOp Q) (k : ℕ) (ε : ℝ) : ℝ :=
  Real.logb 2 (rtBoundBase ρ σ) * InfoTheory.SmoothMinEntropy.bennettTiltWidth k ε

omit [DecidableEq C] in
/-- The exact negative Chernoff tilt at the Bennett width. -/
def bennettTilt (ρ : CQState C Q) (σ : DensityOp Q) (k : ℕ) (ε : ℝ) : ℝ :=
  -(Real.log (1 + InfoTheory.SmoothMinEntropy.bennettTiltWidth k ε) /
    Real.log (rtBoundBase ρ σ))

/-- The bit-normalized single-copy entropy floor at the Bennett correction. -/
def bitBennettEntropyFloor (ρ : CQState C Q) (hρ : ∑ c, (ρ.stateMap c).trace = 1)
    (σ : DensityOp Q) (k : ℕ) (ε : ℝ) : ℝ :=
  referenceCondVonNeumannBits ρ hρ σ - bennettPenalty ρ σ k ε

/-- The bit-normalized Bennett floor for the complete block. -/
def bitBennettBlockEntropyFloor (ρ : CQState C Q) (hρ : ∑ c, (ρ.stateMap c).trace = 1)
    (σ : DensityOp Q) (k : ℕ) (ε : ℝ) : ℝ := k * bitBennettEntropyFloor ρ hρ σ k ε

end AEP.IID
end InfoTheory.SmoothMinEntropy
