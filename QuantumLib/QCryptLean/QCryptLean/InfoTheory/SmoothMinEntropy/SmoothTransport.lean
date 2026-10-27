import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.InfoTheory.SmoothMinEntropy.FeasibleFloor
import QCryptLean.InfoTheory.SmoothMinEntropy.FeasibleRegularization
import QCryptLean.InfoTheory.SmoothMinEntropy.MinEntropy
import QCryptLean.InfoTheory.SmoothMinEntropy.Smooth
import QCryptLean.Quantum.Operators.Basic

/-! # Extended smooth-entropy transport with an explicit exponential scale cost -/
namespace InfoTheory.SmoothMinEntropy
open Quantum.Operators
variable {C D Q R : Type*} [Fintype C] [Fintype D] [Fintype Q] [Fintype R]
  [DecidableEq C] [DecidableEq D]

/-- Transport of every smoothing witness with a scale cost gives the same additive entropy cost. -/
theorem smoothMinEntropy_le_add_of_feasible_transport
    (ρ : CQState C Q) (σ : SubDensityOp Q) (ρ' : CQState D R) (σ' : SubDensityOp R)
    (ε ε' c : ℝ) (hc : 0 ≤ c)
    (h : ∀ τ : CQState C Q, ρ.purifiedDistance τ ≤ ε →
      ∃ τ' : CQState D R, ρ'.purifiedDistance τ' ≤ ε' ∧
        ∀ t, IsFeasible τ σ t → IsFeasible τ' σ' (2 ^ c * t)) :
    smoothMinEntropy ε ρ σ ≤ smoothMinEntropy ε' ρ' σ' + ENNReal.ofReal c := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  obtain ⟨τ, hτ⟩ := lt_iSup_iff.mp hr
  obtain ⟨hd, ht⟩ := lt_iSup_iff.mp hτ
  have ht' : ENNReal.ofReal (r : ℝ) < minEntropy τ σ := by
    simpa only [ENNReal.ofReal_coe_nnreal] using ht
  obtain ⟨a, ha, har⟩ := exists_isFeasible_lt_rpow_of_lt_minEntropy τ σ ht'
  obtain ⟨τ', hd', hf⟩ := h τ hd
  have hscale : (2 : ℝ) ^ (-(r - c : ℝ)) = (2 : ℝ) ^ c * (2 : ℝ) ^ (-(r : ℝ)) := by
    rw [show -(r - c : ℝ) = c + -(r : ℝ) from by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hfloor : ENNReal.ofReal ((r : ℝ) - c) ≤ smoothMinEntropy ε' ρ' σ' := by
    apply (ofReal_le_minEntropy_of_isFeasible τ' σ' ((r : ℝ) - c) ?_).trans
      (minEntropy_le_smoothMinEntropy_of_purifiedDistance_le ρ' τ' σ' hd')
    rw [hscale]
    exact hf _ (ha.mono har.le)
  rw [ENNReal.ofReal_sub _ hc, ENNReal.ofReal_coe_nnreal] at hfloor
  exact tsub_le_iff_right.mp hfloor

end InfoTheory.SmoothMinEntropy
