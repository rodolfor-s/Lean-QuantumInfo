import QCryptLean.Math.FiniteEmbedding
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Basic
import QCryptLean.QKD.BB84.Sampling.Relabel
import QCryptLean.QKD.BB84.Sampling.Selection

/-!
# Unnormalized selected-injection fiber mass

This module defines the total quota-success mass and the mass of a fixed selected-injection fiber.
Explicit physical-index relabeling shows that all fibers have equal mass, while finite partitioning
relates their sum to the success mass.

Renner, arXiv:quant-ph/0512258v2, lines 673--736, and Pfister et al.,
arXiv:1506.07502v3, Sections IV--V and Eq. (35), motivate the fixed-batch sampling schedule.
-/

open scoped ENNReal BigOperators

noncomputable section

namespace QKD.BB84.Sampling

open QKD.BB84.Measurement

/-- Total unnormalized probability mass of raw controls meeting both fixed basis quotas. -/
def selectionSuccessMass (N nK mZ mX : ℕ) (pA pB : PMF Basis) : ℝ≥0∞ :=
  ∑ omega : RawControl N,
    if HasQuotas nK mZ mX omega then rawControlLaw N pA pB omega else 0

/-- Unnormalized probability mass of raw controls selecting one fixed role-packed injection. -/
def selectedInjectionFiberMass (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (f : Fin (nK + mZ + mX) ↪ Fin N) : ℝ≥0∞ :=
  ∑ omega : RawControl N,
    if select nK mZ mX omega = some f then rawControlLaw N pA pB omega else 0

/-- Every selected-injection fiber has the same unnormalized mass.

Relabeling carries the selector output from one embedding to the other and preserves the
raw-control point mass. No support or positivity premise is required. -/
theorem selectedInjectionFiberMass_eq_of_embeddings
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (f g : Fin (nK + mZ + mX) ↪ Fin N) :
    selectedInjectionFiberMass N nK mZ mX pA pB f =
      selectedInjectionFiberMass N nK mZ mX pA pB g := by
  let τ := Math.FiniteEmbedding.embeddingTransportPerm f g
  have hτ : relabelEmbedding τ f = g := by
    ext k
    simpa [τ, relabelEmbedding] using congrArg Fin.val
      (Math.FiniteEmbedding.embeddingTransportPerm_apply f g k)
  rw [selectedInjectionFiberMass, selectedInjectionFiberMass]
  refine Fintype.sum_equiv (rawControlRelabel τ) _ _ ?_
  intro omega
  rw [rawControlLaw_apply_relabel]
  rw [select_relabel]
  cases hselect : select nK mZ mX omega with
  | none => simp
  | some f' =>
      simp only [Option.map_some, Option.some.injEq]
      have hiff : relabelEmbedding τ f' = g ↔ f' = f := by
        rw [← hτ]
        constructor
        · intro h
          ext k
          have hk := DFunLike.congr_fun h k
          change τ (f' k) = τ (f k) at hk
          exact congrArg Fin.val (τ.injective hk)
        · exact congrArg (relabelEmbedding τ)
      by_cases hf : f' = f
      · simp [hf, hτ]
      · have hr : ¬relabelEmbedding τ f' = g := fun h => hf (hiff.mp h)
        simp [hf, hr]

/-- Success mass is the sum of the disjoint selected-injection fiber masses.

A raw control contributes precisely when `select` returns its unique injection. -/
theorem selectionSuccessMass_eq_sum_fibers
    (N nK mZ mX : ℕ) (pA pB : PMF Basis) :
    selectionSuccessMass N nK mZ mX pA pB =
      ∑ f : Fin (nK + mZ + mX) ↪ Fin N,
        selectedInjectionFiberMass N nK mZ mX pA pB f := by
  rw [selectionSuccessMass]
  simp_rw [selectedInjectionFiberMass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro omega _
  by_cases hq : HasQuotas nK mZ mX omega
  · have hs : (select nK mZ mX omega).isSome = true :=
      (select_isSome_iff nK mZ mX omega).2 hq
    obtain ⟨f, hf⟩ : ∃ f, select nK mZ mX omega = some f := by
      cases hselect : select nK mZ mX omega with
      | none => simp [hselect] at hs
      | some f => exact ⟨f, rfl⟩
    simp only [hq, ite_true]
    rw [hf]
    simp
  · have hs : select nK mZ mX omega = none := by
      cases hselect : select nK mZ mX omega with
      | none => rfl
      | some f =>
          exfalso
          apply hq
          apply (select_isSome_iff nK mZ mX omega).mp
          simp [hselect]
    simp [hq, hs]

/-- Exact unnormalized mass of every selected-injection fiber.

The denominator is the number `N.descFactorial (nK + mZ + mX)` of embeddings. The supplied
embedding itself entails the needed cardinality relation, so the equality also covers zero quotas,
`N = 0`, and zero success mass without an additional premise. -/
theorem selectedInjection_fiberMass
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (f : Fin (nK + mZ + mX) ↪ Fin N) :
    selectedInjectionFiberMass N nK mZ mX pA pB f =
      selectionSuccessMass N nK mZ mX pA pB /
        (N.descFactorial (nK + mZ + mX) : ℝ≥0∞) := by
  have hle : nK + mZ + mX ≤ N := by
    simpa using Fintype.card_le_of_injective f f.injective
  have hpos : 0 < N.descFactorial (nK + mZ + mX) :=
    Nat.descFactorial_pos.mpr hle
  apply (ENNReal.eq_div_iff (by exact_mod_cast hpos.ne') ENNReal.coe_ne_top).2
  rw [selectionSuccessMass_eq_sum_fibers]
  simp_rw [selectedInjectionFiberMass_eq_of_embeddings N nK mZ mX pA pB _ f]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_embedding_eq]
  simp

/-- Zero quotas accept every raw control, so their total success mass is one. -/
theorem selectionSuccessMass_zero_quotas (N : ℕ) (pA pB : PMF Basis) :
    selectionSuccessMass N 0 0 0 pA pB = 1 := by
  rw [selectionSuccessMass]
  simp only [HasQuotas, zero_add, zero_le, and_self, ite_true]
  rw [← tsum_fintype (L := SummationFilter.unconditional _)]
  exact (rawControlLaw N pA pB).tsum_coe

end QKD.BB84.Sampling
