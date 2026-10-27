import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Basic.ENNReal.Real
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra

/-! # Min Entropy -/


noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators
open scoped ComplexOrder

variable {C Q : Type*} [Fintype C] [Fintype Q]

/-- Nonnegative scalar domination of every quantum block by a fixed reference. -/
def IsFeasible (ρ : CQState C Q) (σ : SubDensityOp Q) (t : ℝ) : Prop :=
  0 ≤ t ∧ ∀ c, OpLe (ρ.stateMap c).toOp ((t : ℂ) • σ.toOp)

/-- The infimum of the feasible scales, with the real empty-set convention. -/
def minScale (ρ : CQState C Q) (σ : SubDensityOp Q) : ℝ :=
  sInf (Set.ofPred (IsFeasible ρ σ))

/-- The reference admits at least one finite feasible domination scale. -/
def HasScale (ρ : CQState C Q) (σ : SubDensityOp Q) : Prop := ∃ t, IsFeasible ρ σ t

/-- Signed, real-valued fixed-reference min-entropy in bits. -/
def minEntropyReal (ρ : CQState C Q) (σ : SubDensityOp Q) : ℝ :=
  -Real.log (minScale ρ σ) / Real.log 2

/-- Real optimized entropy ranges over every sub-density reference. -/
def minEntropyOptReal (ρ : CQState C Q) : ℝ :=
  sSup {h | ∃ σ : SubDensityOp Q, h = minEntropyReal ρ σ}

/-- Extended positive-part entropy: infeasible references give zero, while a
feasible zero optimum gives infinity. -/
def minEntropy (ρ : CQState C Q) (σ : SubDensityOp Q) : ENNReal := by
  classical
  exact if 0 < minScale ρ σ then ENNReal.ofReal (minEntropyReal ρ σ)
    else if HasScale ρ σ then ⊤ else 0

/-- Extended optimized entropy, with the feasible-reference domain retained. -/
def minEntropyOpt (ρ : CQState C Q) : ENNReal :=
  sSup {h | ∃ σ : SubDensityOp Q, HasScale ρ σ ∧ h = minEntropy ρ σ}

/-- An empty feasible set has real infimum zero. -/
theorem minScale_eq_zero_of_not_hasScale (ρ : CQState C Q) (σ : SubDensityOp Q)
    (h : ¬ HasScale ρ σ) : minScale ρ σ = 0 := by
  have he : Set.ofPred (IsFeasible ρ σ) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    exact h
  rw [minScale, he, Real.sInf_empty]

/-- Feasible scales are bounded below by zero. -/
theorem bddBelow_setOf_isFeasible (ρ : CQState C Q) (σ : SubDensityOp Q) :
    BddBelow (Set.ofPred (IsFeasible ρ σ)) := ⟨0, fun _ ht => ht.1⟩

/-- Each feasible scale bounds the infimum from above. -/
theorem minScale_le_of_isFeasible (ρ : CQState C Q) (σ : SubDensityOp Q)
    {t : ℝ} (ht : IsFeasible ρ σ t) : minScale ρ σ ≤ t :=
  csInf_le (bddBelow_setOf_isFeasible ρ σ) ht

/-- The infimum is nonnegative, also for an empty feasible set. -/
theorem minScale_nonneg (ρ : CQState C Q) (σ : SubDensityOp Q) : 0 ≤ minScale ρ σ := by
  by_cases h : HasScale ρ σ
  · exact le_csInf h (fun _ ht => ht.1)
  · rw [minScale_eq_zero_of_not_hasScale ρ σ h]

/-- Increasing a feasible scalar preserves feasibility. -/
theorem IsFeasible.mono {ρ : CQState C Q} {σ : SubDensityOp Q}
    {t s : ℝ} (ht : IsFeasible ρ σ t) (hts : t ≤ s) : IsFeasible ρ σ s := by
  refine ⟨ht.1.trans hts, fun c v => (ht.2 c v).trans ?_⟩
  have hn := (Complex.nonneg_iff.mp (σ.posSemidef.dotProduct_mulVec_nonneg v)).1
  simpa [quadraticForm, Matrix.smul_mulVec, dotProduct_smul, Complex.mul_re] using
    mul_le_mul_of_nonneg_right hts hn

/-- Infeasible references contribute zero to the extended positive part. -/
theorem minEntropy_eq_zero_of_not_hasScale (ρ : CQState C Q) (σ : SubDensityOp Q)
    (h : ¬ HasScale ρ σ) : minEntropy ρ σ = 0 := by
  simp [minEntropy, minScale_eq_zero_of_not_hasScale ρ σ h, h]

/-- A feasible zero optimum has infinite extended entropy. -/
theorem minEntropy_eq_top_of_minScale_eq_zero (ρ : CQState C Q) (σ : SubDensityOp Q)
    (h : HasScale ρ σ) (h0 : minScale ρ σ = 0) : minEntropy ρ σ = ⊤ := by
  simp [minEntropy, h0, h]

/-- The zero CQ state has infinite extended entropy against every reference. -/
@[simp] theorem minEntropy_zeroCQ (σ : SubDensityOp Q) :
    minEntropy (CQState.zero : CQState C Q) σ = ⊤ := by
  have ht : IsFeasible (CQState.zero : CQState C Q) σ 0 := by
    refine ⟨le_rfl, fun _ => ?_⟩
    simpa only [CQState.zero, SubDensityOp.zero, Complex.ofReal_zero, zero_smul] using
      OpLe.refl (0 : Op Q)
  exact minEntropy_eq_top_of_minScale_eq_zero _ _ ⟨0, ht⟩
    (le_antisymm (minScale_le_of_isFeasible _ _ ht) (minScale_nonneg _ _))

/-- Positive real optima use the finite positive-part convention. -/
theorem minEntropy_eq_of_pos (ρ : CQState C Q) (σ : SubDensityOp Q)
    (h : 0 < minScale ρ σ) : minEntropy ρ σ = ENNReal.ofReal (minEntropyReal ρ σ) := by
  simp [minEntropy, h]

end InfoTheory.SmoothMinEntropy
