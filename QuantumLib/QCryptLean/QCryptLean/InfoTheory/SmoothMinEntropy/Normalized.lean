import Mathlib.Analysis.SpecialFunctions.Log.Base
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-! # Normalized CQ states and their classical support -/

noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators

variable {C Q : Type*} [Fintype C] [Fintype Q]

/-- The number of classical outcomes with strictly positive weight. -/
def CQState.classicalRank (ρ : CQState C Q) : ℕ := by
  classical
  exact (Finset.univ.filter (fun c => 0 < (ρ.stateMap c).trace)).card

/-- Classical Hartley entropy in bits, on nonempty support. -/
def CQState.classicalHmax (ρ : CQState C Q) (_hρ : 1 ≤ ρ.classicalRank) : ℝ :=
  Real.logb 2 (ρ.classicalRank : ℝ)

/-- Upgrade the marginal of a normalized CQ state to a density operator. -/
def CQState.quantumMarginalDensityOp (ρ : CQState C Q)
    (hρ : ∑ c, (ρ.stateMap c).trace = 1) : DensityOp Q where
  toOp := ρ.quantumMarginal.toOp
  posSemidef := ρ.quantumMarginal.posSemidef
  trace_one := Complex.ext (ρ.quantumMarginal_trace.trans hρ) ρ.quantumMarginal.trace_im

/-- Upgrade the joint state of a normalized CQ state to a density operator. -/
def CQState.toJointDensityOp [DecidableEq C] (ρ : CQState C Q)
    (hρ : ∑ c, (ρ.stateMap c).trace = 1) : DensityOp (Q × C) where
  toOp := ρ.toJointOp
  posSemidef := ρ.toJointDensity.posSemidef
  trace_one := Complex.ext (ρ.toJointDensity_trace.trans hρ) ρ.toJointDensity.trace_im

/-- A CQ state with unit total classical weight. -/
structure NormalizedCQState (C Q : Type*) [Fintype C] [Fintype Q] extends CQState C Q where
  /-- The quantum blocks have total trace one. -/
  weight_eq_one : ∑ c, (stateMap c).trace = 1

instance : Coe (NormalizedCQState C Q) (CQState C Q) := ⟨NormalizedCQState.toCQState⟩

end InfoTheory.SmoothMinEntropy
