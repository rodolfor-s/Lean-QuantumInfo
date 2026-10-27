import QCryptLean.InfoTheory.RelativeEntropy.Basic
import QCryptLean.InfoTheory.SmoothMinEntropy.AEP.IID.TensorPower
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Normalized
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.InfoTheory.VonNeumannEntropy.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor

/-! # AEPRates -/


noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators InfoTheory.VonNeumannEntropy
open scoped MatrixOrder ComplexOrder

variable {C Q : Type*} [Fintype C] [Fintype Q] [DecidableEq Q]

/-- The collision trace against the support pseudoinverse of a reference. -/
def CQState.tracedSquareTimesInvFactor (ρ : CQState C Q) (σ : DensityOp Q) : ℝ :=
  (∑ c, ((ρ.stateMap c).toOp * (ρ.stateMap c).toOp * σ.toOp ^ (-1 : ℝ)).trace).re

namespace AEP.IID

/-- The scalar base of the Renner correction. -/
def rtBoundBase (ρ : CQState C Q) (σ : DensityOp Q) : ℝ :=
  (ρ.classicalRank : ℝ) + ρ.tracedSquareTimesInvFactor σ + 2

/-- The Renner correction from the support inverse and the sampling noise factor. -/
def penalty (ρ : CQState C Q) (σ : DensityOp Q) (k : ℕ) (ε : ℝ) : ℝ :=
  2 * Real.logb 2 (rtBoundBase ρ σ) * InfoTheory.SmoothMinEntropy.noiseFactor k ε

omit [DecidableEq Q] in
/-- The classical correction has the library's constant four. -/
def classicalPenalty (ρ : CQState C Q) (k : ℕ) (ε : ℝ) : ℝ :=
  (2 * Real.logb 2 (ρ.classicalRank : ℝ) + 4) * InfoTheory.SmoothMinEntropy.noiseFactor k ε

/-- The IID reference on the function register. -/
def tensorReference (σ : DensityOp Q) (k : ℕ) : SubDensityOp (Fin k → Q) :=
  σ.toSubDensityOp.tensorPow k

variable [DecidableEq C]

/-- The signed single-copy entropy floor after the finite-sample and reference penalties. -/
def entropyFloor (ρ : CQState C Q) (hρ : ∑ c, (ρ.stateMap c).trace = 1)
    (σ : DensityOp Q) (k : ℕ) (ε : ℝ) : ℝ :=
  vonNeumannEntropy (ρ.toJointDensityOp hρ) - vonNeumannEntropy (ρ.quantumMarginalDensityOp hρ)
    - penalty ρ σ k ε
    - InfoTheory.RelativeEntropy.relativeEntropyReal (ρ.quantumMarginalDensityOp hρ) σ

/-- The block floor before division by the sample size. -/
def blockEntropyFloor (ρ : CQState C Q) (hρ : ∑ c, (ρ.stateMap c).trace = 1)
    (σ : DensityOp Q) (k : ℕ) (ε : ℝ) : ℝ := (k : ℝ) * entropyFloor ρ hρ σ k ε

/-- The signed smooth entropy per copy, defined using a real supremum. -/
def smoothRateReal (ρ : CQState C Q) (σ : DensityOp Q) (k : ℕ) (ε : ℝ) : ℝ :=
  (1 / (k : ℝ)) * smoothMinEntropyReal ε (ρ.tensorPower k) (tensorReference σ k)

/-- The extended smooth entropy per copy. -/
def smoothRate (ρ : CQState C Q) (σ : DensityOp Q) (k : ℕ) (ε : ℝ) : ENNReal :=
  smoothMinEntropy ε (ρ.tensorPower k) (tensorReference σ k) / k

omit [DecidableEq Q] in
/-- A block floor is equivalent to its extended per-copy rate for a positive sample size. -/
theorem ofReal_le_smoothRate_iff (ρ : CQState C Q) (σ : DensityOp Q)
    (k : ℕ) [NeZero k] (ε F : ℝ) :
    ENNReal.ofReal F ≤ smoothRate ρ σ k ε ↔
      ENNReal.ofReal ((k : ℝ) * F) ≤
        smoothMinEntropy ε (ρ.tensorPower k) (tensorReference σ k) := by
  have hk : (k : ENNReal) ≠ 0 := by exact_mod_cast NeZero.ne k
  rw [smoothRate, ENNReal.le_div_iff_mul_le (Or.inl hk) (Or.inl (by simp)),
    ENNReal.ofReal_mul (Nat.cast_nonneg k), ENNReal.ofReal_natCast, mul_comm]

omit [DecidableEq Q] in
/-- Any nearby witness meeting the completed block floor yields the extended rate bound. -/
theorem ofReal_le_smoothRate_of_blockFloor_le (ρ : CQState C Q) (σ : DensityOp Q)
    (k : ℕ) [NeZero k] (ε F : ℝ) (τ : CQState (Fin k → C) (Fin k → Q))
    (hτ : (ρ.tensorPower k).purifiedDistance τ ≤ ε)
    (hF : ENNReal.ofReal ((k : ℝ) * F) ≤ minEntropy τ (tensorReference σ k)) :
    ENNReal.ofReal F ≤ smoothRate ρ σ k ε :=
  (ofReal_le_smoothRate_iff ρ σ k ε F).mpr
    (hF.trans (minEntropy_le_smoothMinEntropy_of_purifiedDistance_le _ _ _ hτ))

/-- A nearby spectral witness in a bounded real smoothing set yields the signed AEP rate.
Only the smoothed state of the spectral witness is needed for this final assembly. -/
theorem entropyFloor_le_smoothRateReal (ρ : CQState C Q)
    (hρ : ∑ c, (ρ.stateMap c).trace = 1) (σ : DensityOp Q) (k : ℕ) [NeZero k]
    (ε : ℝ) (τ : CQState (Fin k → C) (Fin k → Q))
    (hbdd : BddAbove (Set.ofPred (IsInSmoothedSetReal ε (ρ.tensorPower k) (tensorReference σ k))))
    (hτ : (ρ.tensorPower k).purifiedDistance τ ≤ ε)
    (hF : blockEntropyFloor ρ hρ σ k ε ≤ minEntropyReal τ (tensorReference σ k)) :
    entropyFloor ρ hρ σ k ε ≤ smoothRateReal ρ σ k ε := by
  have hmem : minEntropyReal τ (tensorReference σ k) ≤
      smoothMinEntropyReal ε (ρ.tensorPower k) (tensorReference σ k) :=
    le_csSup hbdd ⟨τ, rfl, hτ⟩
  have hk : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  have hh := mul_le_mul_of_nonneg_left (hF.trans hmem) (le_of_lt (one_div_pos.mpr hk))
  simpa only [smoothRateReal, blockEntropyFloor, ← mul_assoc,
    one_div_mul_cancel (ne_of_gt hk), one_mul]
    using hh

end AEP.IID
end InfoTheory.SmoothMinEntropy
