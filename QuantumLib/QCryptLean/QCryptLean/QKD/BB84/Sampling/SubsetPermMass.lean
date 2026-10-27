import QCryptLean.Math.FiniteEmbedding.SubsetPerm
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Basic
import QCryptLean.QKD.BB84.Sampling.FiberMass
import QCryptLean.QKD.BB84.Sampling.Selection

/-!
# Selected subset/permutation mass

This module maps the fixed-quota selector through the explicit finite-embedding equivalence and
records the unnormalized mass of each retained-subset and inner-permutation pair.

Renner, arXiv:quant-ph/0512258v2, lines 673--736, and Pfister et al.,
arXiv:1506.07502v3, Sections IV--V and Eq. (35), motivate the fixed-batch sampling schedule.
-/

open scoped ENNReal BigOperators

noncomputable section

namespace QKD.BB84.Sampling

open QKD.BB84.Measurement
open Math.FiniteEmbedding

/-- The actual quota selector, expressed as an image subset and inverse-rank inner permutation. -/
def selectSubsetPerm {N : ℕ} (nK mZ mX : ℕ) (omega : RawControl N) :
    Option
      (Set.powersetCard (Fin N) (nK + mZ + mX) ×
        Equiv.Perm (Fin (nK + mZ + mX))) :=
  (select nK mZ mX omega).map
    (embeddingSubsetPermEquiv (nK + mZ + mX) N)

/-- Unnormalized mass of raw controls producing one fixed subset/permutation pair. -/
def selectedSubsetPermMass
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (π : Equiv.Perm (Fin (nK + mZ + mX))) : ℝ≥0∞ :=
  ∑ omega : RawControl N,
    if selectSubsetPerm nK mZ mX omega = some (S, π)
    then rawControlLaw N pA pB omega
    else 0

/-- A subset/permutation pair has exactly the mass of its joined selected-injection fiber.

This is the change-of-coordinates identity induced by `embeddingSubsetPermEquiv`; no support or
positivity premise is required. -/
theorem selectedSubsetPermMass_eq_fiberMass
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (π : Equiv.Perm (Fin (nK + mZ + mX))) :
    selectedSubsetPermMass N nK mZ mX pA pB S π =
      selectedInjectionFiberMass N nK mZ mX pA pB (joinSubsetPerm S π) := by
  rw [selectedSubsetPermMass, selectedInjectionFiberMass]
  apply Finset.sum_congr rfl
  intro omega _
  cases hselect : select nK mZ mX omega with
  | none => simp [selectSubsetPerm, hselect]
  | some f =>
      simp only [selectSubsetPerm, hselect, Option.map_some, Option.some.injEq]
      change (if embeddingSubsetPermForward f = (S, π) then _ else _) = _
      have hiff :
          embeddingSubsetPermForward f = (S, π) ↔ f = joinSubsetPerm S π := by
        constructor
        · intro h
          apply (embeddingSubsetPermEquiv (nK + mZ + mX) N).injective
          change embeddingSubsetPermForward f =
            embeddingSubsetPermForward (joinSubsetPerm S π)
          rw [h, embeddingSubsetPermForward_join]
        · intro h
          rw [h, embeddingSubsetPermForward_join]
      by_cases hf : f = joinSubsetPerm S π
      · simp [hf, embeddingSubsetPermForward_join]
      · have hp : embeddingSubsetPermForward f ≠ (S, π) := fun h => hf (hiff.mp h)
        simp [hf, hp]

/-- Exact unnormalized mass of each retained-subset and inner-permutation pair.

The supplied subset entails the needed cardinality relation, so no separate `n ≤ N` or positivity
premise is required. -/
theorem selectedSubsetPerm_mass
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (π : Equiv.Perm (Fin (nK + mZ + mX))) :
    selectedSubsetPermMass N nK mZ mX pA pB S π =
      selectionSuccessMass N nK mZ mX pA pB /
        ((N.choose (nK + mZ + mX) : ℝ≥0∞) *
          ((nK + mZ + mX).factorial : ℝ≥0∞)) := by
  rw [selectedSubsetPermMass_eq_fiberMass, selectedInjection_fiberMass]
  congr 1
  exact_mod_cast
    (Nat.descFactorial_eq_factorial_mul_choose N (nK + mZ + mX)).trans (Nat.mul_comm _ _)

/-! ## Selector formulas -/

/-- A successful actual selector maps to its explicit subset/permutation coordinates. -/
theorem selectSubsetPerm_of_select_some
    {N : ℕ} (nK mZ mX : ℕ) (omega : RawControl N)
    (f : Fin (nK + mZ + mX) ↪ Fin N)
    (h : select nK mZ mX omega = some f) :
    selectSubsetPerm nK mZ mX omega =
      some (embeddingSubsetPermForward f) := by
  simp only [selectSubsetPerm, h, Option.map_some]
  rfl

/-- A failed actual selector remains failed after changing coordinates. -/
theorem selectSubsetPerm_of_select_none
    {N : ℕ} (nK mZ mX : ℕ) (omega : RawControl N)
    (h : select nK mZ mX omega = none) :
    selectSubsetPerm nK mZ mX omega = none := by
  simp [selectSubsetPerm, h]

end QKD.BB84.Sampling
