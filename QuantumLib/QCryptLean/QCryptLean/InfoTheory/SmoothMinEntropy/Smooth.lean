import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.MinEntropy
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.PurifiedBasic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations

/-! # Smooth -/


noncomputable section

namespace InfoTheory.SmoothMinEntropy

open Quantum.Operators

variable {C Q : Type*} [Fintype C] [Fintype Q]

/-- The closed purified-distance ball of subnormalized states. -/
def epsilonBall (ρ : SubDensityOp Q) (ε : ℝ) : Set (SubDensityOp Q) :=
  {τ | Quantum.Metrics.purifiedDistance ρ τ ≤ ε}

/-- Every nonnegative-radius ball contains its center. -/
theorem epsilonBall_self_mem (ρ : SubDensityOp Q) {ε : ℝ} (hε : 0 ≤ ε) :
    ρ ∈ epsilonBall ρ ε := by
  simpa [epsilonBall, Quantum.Metrics.purifiedDistance_self] using hε

/-- Balls grow with their radius. -/
theorem epsilonBall_mono (ρ : SubDensityOp Q) {ε δ : ℝ} (h : ε ≤ δ) :
    epsilonBall ρ ε ⊆ epsilonBall ρ δ := fun _ ht => ht.trans h

variable [DecidableEq C]

/-- The full signed-real smoothing set against a fixed reference. -/
def IsInSmoothedSetReal (ε : ℝ) (ρ : CQState C Q) (σ : SubDensityOp Q) (h : ℝ) : Prop :=
  ∃ τ : CQState C Q, h = minEntropyReal τ σ ∧ ρ.purifiedDistance τ ≤ ε

/-- Real smoothing uses the real supremum, retaining its totalization convention. -/
def smoothMinEntropyReal (ε : ℝ) (ρ : CQState C Q) (σ : SubDensityOp Q) : ℝ :=
  sSup (Set.ofPred (IsInSmoothedSetReal ε ρ σ))

/-- Extended fixed-reference smoothing, with negative radii yielding zero. -/
def smoothMinEntropy (ε : ℝ) (ρ : CQState C Q) (σ : SubDensityOp Q) : ENNReal :=
  ⨆ τ : CQState C Q, ⨆ (_ : ρ.purifiedDistance τ ≤ ε), minEntropy τ σ

/-- Extended smoothing optimized over all sub-density reference operators. -/
def smoothMinEntropyOpt (ε : ℝ) (ρ : CQState C Q) : ENNReal :=
  ⨆ σ : SubDensityOp Q, smoothMinEntropy ε ρ σ

/-- A nonnegative smoothing radius gives a nonempty real optimization domain. -/
theorem smoothedSetReal_nonempty (ρ : CQState C Q) (σ : SubDensityOp Q)
    {ε : ℝ} (hε : 0 ≤ ε) : (Set.ofPred (IsInSmoothedSetReal ε ρ σ)).Nonempty :=
  ⟨minEntropyReal ρ σ, ρ, rfl, by simpa using hε⟩

/-- Each member of the joint CQ ball contributes to extended smooth entropy. -/
theorem minEntropy_le_smoothMinEntropy_of_purifiedDistance_le
    (ρ τ : CQState C Q) (σ : SubDensityOp Q) {ε : ℝ}
    (h : ρ.purifiedDistance τ ≤ ε) : minEntropy τ σ ≤ smoothMinEntropy ε ρ σ :=
  le_iSup_of_le τ (le_iSup_of_le h le_rfl)

/-- Extended smooth entropy is monotone in its radius. -/
theorem smoothMinEntropy_mono_eps {ε δ : ℝ} (h : ε ≤ δ)
    (ρ : CQState C Q) (σ : SubDensityOp Q) :
    smoothMinEntropy ε ρ σ ≤ smoothMinEntropy δ ρ σ := by
  refine iSup_le fun τ => iSup_le fun ht => ?_
  exact minEntropy_le_smoothMinEntropy_of_purifiedDistance_le ρ τ σ (ht.trans h)

/-- A nonnegative smoothing radius includes the unsmoothed fixed-reference value. -/
theorem minEntropy_le_smoothMinEntropy {ε : ℝ} (hε : 0 ≤ ε)
    (ρ : CQState C Q) (σ : SubDensityOp Q) : minEntropy ρ σ ≤ smoothMinEntropy ε ρ σ :=
  minEntropy_le_smoothMinEntropy_of_purifiedDistance_le ρ ρ σ (by simpa using hε)

/-- Every fixed reference contributes to reference-optimized smoothing. -/
theorem smoothMinEntropy_le_smoothMinEntropyOpt (ε : ℝ) (ρ : CQState C Q)
    (σ : SubDensityOp Q) : smoothMinEntropy ε ρ σ ≤ smoothMinEntropyOpt ε ρ :=
  le_iSup (fun τ => smoothMinEntropy ε ρ τ) σ

/-- A smoothing ball reaching zero has infinite extended entropy, including its boundary. -/
theorem smoothMinEntropy_eq_top_of_weight_le_eps_sq {ε : ℝ} (hε : 0 ≤ ε)
    (ρ : CQState C Q) (σ : SubDensityOp Q) (hweight : ∑ c, (ρ.stateMap c).trace ≤ ε ^ 2) :
    smoothMinEntropy ε ρ σ = ⊤ := by
  have hz : (CQState.zero : CQState C Q).toJointDensity = SubDensityOp.zero := by
    ext i j
    simp [CQState.toJointDensity, CQState.toJointOp, CQState.zero, SubDensityOp.zero,
      Matrix.blockDiagonal]
  have hd : ρ.purifiedDistance CQState.zero ≤ ε := by
    rw [CQState.purifiedDistance, hz, Quantum.Metrics.purifiedDistance_zero,
      CQState.toJointDensity_trace]
    exact (Real.sqrt_le_iff).mpr ⟨hε, hweight⟩
  apply top_unique
  simpa only [minEntropy_zeroCQ] using
    minEntropy_le_smoothMinEntropy_of_purifiedDistance_le ρ CQState.zero σ hd

end InfoTheory.SmoothMinEntropy
