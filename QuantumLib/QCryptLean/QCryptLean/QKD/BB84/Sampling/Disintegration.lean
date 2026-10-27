import QCryptLean.Math.FiniteEmbedding.SubsetPerm
import QCryptLean.Math.Probability.PMFFilterOrPure
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Basic
import QCryptLean.QKD.BB84.Sampling.FiberMass
import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.QKD.BB84.Sampling.SubsetPermMass

/-!
# Status-tagged exact disintegration of BB84 sampling controls

This module reconstructs the complete raw public control from an explicit success/failure status.
On success it samples a retained subset and inverse-oriented inner permutation before sampling the
corresponding raw-control fiber. On failure it samples the complete failure fiber. Zero-mass
branches use the explicit `defaultRawControl` fallback.

Renner, arXiv:quant-ph/0512258v2, lines 673--736, and Pfister et al.,
arXiv:1506.07502v3, Sections IV--V and Eq. (35), motivate the fixed-batch schedule and
unnormalized mass. The status-tagged equality is proved by the explicit finite construction below.
-/

open scoped ENNReal BigOperators

noncomputable section

namespace QKD.BB84.Sampling

open QKD.BB84.Measurement
open Math.FiniteEmbedding

/-- Total unnormalized probability mass of raw controls failing at least one fixed quota. -/
def selectionFailureMass (N nK mZ mX : ℕ) (pA pB : PMF Basis) : ℝ≥0∞ :=
  ∑ omega : RawControl N,
    if ¬HasQuotas nK mZ mX omega then rawControlLaw N pA pB omega else 0

/-- Success and failure partition the complete raw-control probability mass.

This status normalization holds without a success-positivity premise. -/
theorem selectionSuccessMass_add_failureMass
    (N nK mZ mX : ℕ) (pA pB : PMF Basis) :
    selectionSuccessMass N nK mZ mX pA pB +
      selectionFailureMass N nK mZ mX pA pB = 1 := by
  rw [selectionSuccessMass, selectionFailureMass, ← Finset.sum_add_distrib]
  calc
    (∑ omega : RawControl N,
        ((if HasQuotas nK mZ mX omega then rawControlLaw N pA pB omega else 0) +
          if ¬HasQuotas nK mZ mX omega then rawControlLaw N pA pB omega else 0)) =
        ∑ omega : RawControl N, rawControlLaw N pA pB omega := by
      apply Finset.sum_congr rfl
      intro omega _
      by_cases h : HasQuotas nK mZ mX omega <;> simp [h]
    _ = 1 := by
      rw [← tsum_fintype (L := SummationFilter.unconditional _)]
      exact (rawControlLaw N pA pB).tsum_coe

/-- The quota-success mass is finite: it is at most one. -/
theorem selectionSuccessMass_ne_top (N nK mZ mX : ℕ) (pA pB : PMF Basis) :
    selectionSuccessMass N nK mZ mX pA pB ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (selectionSuccessMass_add_failureMass N nK mZ mX pA pB ▸ le_self_add)

/-- The quota-success mass as a real sum over the public controls.

Every summand is finite (a point mass of the raw-control PMF), so no side condition is needed.
The quantitative bounds on the complementary failure mass are in the Sampling.QuotaFailure
module. -/
theorem selectionSuccessMass_toReal (N nK mZ mX : ℕ) (pA pB : PMF Basis) :
    (selectionSuccessMass N nK mZ mX pA pB).toReal =
      ∑ ω, if HasQuotas nK mZ mX ω then (rawControlLaw N pA pB ω).toReal else 0 := by
  rw [selectionSuccessMass, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun ω _ => ?_
    split_ifs <;> simp
  · intro ω _
    split_ifs
    · exact PMF.apply_ne_top _ _
    · exact ENNReal.zero_ne_top

/-- The real quota-success and quota-failure masses add up to one. -/
theorem selectionMass_toReal_add (N nK mZ mX : ℕ) (pA pB : PMF Basis) :
    (selectionSuccessMass N nK mZ mX pA pB).toReal +
      (selectionFailureMass N nK mZ mX pA pB).toReal = 1 := by
  have h := selectionSuccessMass_add_failureMass N nK mZ mX pA pB
  have hS : selectionSuccessMass N nK mZ mX pA pB ≠ ⊤ :=
    selectionSuccessMass_ne_top N nK mZ mX pA pB
  have hF : selectionFailureMass N nK mZ mX pA pB ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (h ▸ le_add_self)
  rw [← ENNReal.toReal_add hS hF, h, ENNReal.toReal_one]

/-- Raw controls selecting one fixed role-packed injection. -/
def selectedFiberSet
    {N : ℕ} (nK mZ mX : ℕ) (f : Fin (nK + mZ + mX) ↪ Fin N) :
    Set (RawControl N) :=
  {omega | select nK mZ mX omega = some f}

/-- Raw controls failing at least one fixed quota. -/
def failureSet {N : ℕ} (nK mZ mX : ℕ) : Set (RawControl N) :=
  {omega | ¬HasQuotas nK mZ mX omega}

/-- The indicator `tsum` of one selected fiber is its existing finite fiber mass. -/
theorem tsum_selectedFiberSet_indicator
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (f : Fin (nK + mZ + mX) ↪ Fin N) :
    (∑' omega : RawControl N,
      (selectedFiberSet nK mZ mX f).indicator (rawControlLaw N pA pB) omega) =
        selectedInjectionFiberMass N nK mZ mX pA pB f := by
  rw [selectedInjectionFiberMass, tsum_fintype]
  apply Finset.sum_congr rfl
  intro omega _
  by_cases h : select nK mZ mX omega = some f <;>
    simp [selectedFiberSet, h]

/-- The failure-set indicator `tsum` is the existing finite failure mass. -/
theorem tsum_failureSet_indicator
    (N nK mZ mX : ℕ) (pA pB : PMF Basis) :
    (∑' omega : RawControl N,
      (failureSet nK mZ mX).indicator (rawControlLaw N pA pB) omega) =
        selectionFailureMass N nK mZ mX pA pB := by
  rw [selectionFailureMass, tsum_fintype]
  apply Finset.sum_congr rfl
  intro omega _
  by_cases h : ¬HasQuotas nK mZ mX omega <;>
    simp [failureSet, h]

/-- Conditional raw-control law on one selected injection, totalized by the canonical raw
control. -/
def selectedControlKernel
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (f : Fin (nK + mZ + mX) ↪ Fin N) : PMF (RawControl N) :=
  PMF.filterOrPure (rawControlLaw N pA pB)
    (selectedFiberSet nK mZ mX f) (defaultRawControl N)

/-- Exact point mass of the totalized selected-control kernel, including its explicit zero-mass
fallback branch. -/
theorem selectedControlKernel_apply
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (f : Fin (nK + mZ + mX) ↪ Fin N) (omega : RawControl N) :
    selectedControlKernel N nK mZ mX pA pB f omega =
      if selectedInjectionFiberMass N nK mZ mX pA pB f = 0 then
        PMF.pure (defaultRawControl N) omega
      else
        (if select nK mZ mX omega = some f then rawControlLaw N pA pB omega else 0) /
          selectedInjectionFiberMass N nK mZ mX pA pB f := by
  classical
  unfold selectedControlKernel
  by_cases hmass : selectedInjectionFiberMass N nK mZ mX pA pB f = 0
  · rw [ite_eq_left hmass]
    apply PMF.filterOrPure_apply_of_not_exists
    rintro ⟨x, hx, hsupp⟩
    have hsum :
        (∑' y : RawControl N,
          (selectedFiberSet nK mZ mX f).indicator (rawControlLaw N pA pB) y) = 0 :=
      (tsum_selectedFiberSet_indicator N nK mZ mX pA pB f).trans hmass
    have hxzero := (ENNReal.tsum_eq_zero.mp hsum) x
    rw [Set.indicator_of_mem hx] at hxzero
    exact (PMF.mem_support_iff _ _).mp hsupp hxzero
  · rw [ite_eq_right hmass]
    have hexists : ∃ x ∈ selectedFiberSet nK mZ mX f,
        x ∈ (rawControlLaw N pA pB).support := by
      by_contra hnone
      apply hmass
      rw [← tsum_selectedFiberSet_indicator N nK mZ mX pA pB f]
      apply ENNReal.tsum_eq_zero.mpr
      intro x
      by_cases hx : x ∈ selectedFiberSet nK mZ mX f
      · have hxmass : rawControlLaw N pA pB x = 0 := by
          by_contra hxmass
          exact hnone ⟨x, hx, (PMF.mem_support_iff _ _).mpr hxmass⟩
        simp [Set.indicator_of_mem hx, hxmass]
      · simp [Set.indicator_of_notMem hx]
    rw [PMF.filterOrPure_apply_of_exists _ _ _ _ hexists]
    rw [tsum_selectedFiberSet_indicator]
    by_cases hselect : select nK mZ mX omega = some f <;>
      simp [selectedFiberSet, hselect, div_eq_mul_inv]

/-- Conditional raw-control law on quota failure, totalized by the canonical raw control. -/
def failureControlKernel
    (N nK mZ mX : ℕ) (pA pB : PMF Basis) : PMF (RawControl N) :=
  PMF.filterOrPure (rawControlLaw N pA pB)
    (failureSet nK mZ mX) (defaultRawControl N)

/-- Exact point mass of the totalized failure-control kernel, including its explicit zero-mass
fallback branch. -/
theorem failureControlKernel_apply
    (N nK mZ mX : ℕ) (pA pB : PMF Basis) (omega : RawControl N) :
    failureControlKernel N nK mZ mX pA pB omega =
      if selectionFailureMass N nK mZ mX pA pB = 0 then
        PMF.pure (defaultRawControl N) omega
      else
        (if ¬HasQuotas nK mZ mX omega then rawControlLaw N pA pB omega else 0) /
          selectionFailureMass N nK mZ mX pA pB := by
  classical
  unfold failureControlKernel
  by_cases hmass : selectionFailureMass N nK mZ mX pA pB = 0
  · rw [ite_eq_left hmass]
    apply PMF.filterOrPure_apply_of_not_exists
    rintro ⟨x, hx, hsupp⟩
    have hsum :
        (∑' y : RawControl N,
          (failureSet nK mZ mX).indicator (rawControlLaw N pA pB) y) = 0 :=
      (tsum_failureSet_indicator N nK mZ mX pA pB).trans hmass
    have hxzero := (ENNReal.tsum_eq_zero.mp hsum) x
    rw [Set.indicator_of_mem hx] at hxzero
    exact (PMF.mem_support_iff _ _).mp hsupp hxzero
  · rw [ite_eq_right hmass]
    have hexists : ∃ x ∈ failureSet nK mZ mX,
        x ∈ (rawControlLaw N pA pB).support := by
      by_contra hnone
      apply hmass
      rw [← tsum_failureSet_indicator N nK mZ mX pA pB]
      apply ENNReal.tsum_eq_zero.mpr
      intro x
      by_cases hx : x ∈ failureSet nK mZ mX
      · have hxmass : rawControlLaw N pA pB x = 0 := by
          by_contra hxmass
          exact hnone ⟨x, hx, (PMF.mem_support_iff _ _).mpr hxmass⟩
        simp [Set.indicator_of_mem hx, hxmass]
      · simp [Set.indicator_of_notMem hx]
    rw [PMF.filterOrPure_apply_of_exists _ _ _ _ hexists]
    rw [tsum_failureSet_indicator]
    by_cases hquota : ¬HasQuotas nK mZ mX omega <;>
      simp [failureSet, hquota, div_eq_mul_inv]

/-- Initial `n`-element subset obtained from the explicit initial-segment embedding. -/
def initialRetainedSubset
    {N nK mZ mX : ℕ} (hN : nK + mZ + mX ≤ N) :
    Set.powersetCard (Fin N) (nK + mZ + mX) :=
  Set.powersetCard.ofFinEmb (nK + mZ + mX) (Fin N) (Fin.castLEEmb hN)

/-- Uniform retained-subset law with an explicit inhabitant supplied by `hN`. -/
def uniformRetainedSubset
    {N nK mZ mX : ℕ} (hN : nK + mZ + mX ≤ N) :
    PMF (Set.powersetCard (Fin N) (nK + mZ + mX)) :=
  letI : Nonempty (Set.powersetCard (Fin N) (nK + mZ + mX)) :=
    ⟨initialRetainedSubset hN⟩
  PMF.uniformOfFintype _

/-- Uniform law on inner permutations, inhabited explicitly by the identity permutation. -/
def uniformInnerPerm (n : ℕ) : PMF (Equiv.Perm (Fin n)) :=
  letI : Nonempty (Equiv.Perm (Fin n)) := ⟨Equiv.refl _⟩
  PMF.uniformOfFintype _

/-- Success/failure weight used to construct the explicit status PMF. -/
def selectionStatusWeight
    (N nK mZ mX : ℕ) (pA pB : PMF Basis) (status : Bool) : ℝ≥0∞ :=
  if status then selectionSuccessMass N nK mZ mX pA pB
  else selectionFailureMass N nK mZ mX pA pB

/-- The two explicit status weights sum to one. -/
theorem selectionStatusWeight_sum
    (N nK mZ mX : ℕ) (pA pB : PMF Basis) :
    ∑ status : Bool, selectionStatusWeight N nK mZ mX pA pB status = 1 := by
  rw [Fintype.sum_bool]
  simpa [selectionStatusWeight] using
    selectionSuccessMass_add_failureMass N nK mZ mX pA pB

/-- Explicit PMF on the success/failure status bit. -/
def selectionStatusLaw
    (N nK mZ mX : ℕ) (pA pB : PMF Basis) : PMF Bool :=
  PMF.ofFintype (selectionStatusWeight N nK mZ mX pA pB)
    (selectionStatusWeight_sum N nK mZ mX pA pB)

/-- The original raw-control law tagged by its actual quota-success status. -/
def taggedRawControlLaw
    (N nK mZ mX : ℕ) (pA pB : PMF Basis) : PMF (Bool × RawControl N) :=
  (rawControlLaw N pA pB).map fun omega =>
    (decide (HasQuotas nK mZ mX omega), omega)

/-- Reconstruct the full status-tagged raw control by explicit success and failure branches. -/
def reconstructedStatusRawLaw
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) : PMF (Bool × RawControl N) :=
  (selectionStatusLaw N nK mZ mX pA pB).bind fun status =>
    if status then
      (uniformRetainedSubset hN).bind fun S =>
        (uniformInnerPerm (nK + mZ + mX)).bind fun π =>
          (selectedControlKernel N nK mZ mX pA pB (joinSubsetPerm S π)).bind fun omega =>
            PMF.pure (true, omega)
    else
      (failureControlKernel N nK mZ mX pA pB).bind fun omega =>
        PMF.pure (false, omega)

/-- Exact status-tagged disintegration of the complete raw public control.

The construction retains shortage abort and every raw-control field, uses uniform subset and
inverse-oriented inner-permutation draws on success, and includes both zero-mass fallbacks. -/
theorem reconstructedStatusRawLaw_eq
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) :
    reconstructedStatusRawLaw N nK mZ mX pA pB hN =
      taggedRawControlLaw N nK mZ mX pA pB := by
  classical
  apply PMF.ext
  rintro ⟨status, omega⟩
  rw [reconstructedStatusRawLaw, taggedRawControlLaw, PMF.bind_apply, PMF.map_apply]
  simp only [tsum_fintype, Fintype.sum_bool, selectionStatusLaw,
    PMF.ofFintype_apply, selectionStatusWeight, Bool.false_eq_true, ite_false, ite_true]
  rw [Fintype.sum_eq_single omega]
  · simp only [Prod.mk.injEq, and_true]
    cases status
    · simp only [PMF.bind_apply, PMF.pure_apply, Prod.mk.injEq,
        Bool.false_eq_true, false_and, ite_false, mul_zero, tsum_fintype,
        Finset.sum_const_zero, true_and, mul_ite, mul_one, Finset.sum_ite_eq,
        Finset.mem_univ, zero_add, false_eq_decide_iff, ite_not]
      by_cases hq : HasQuotas nK mZ mX omega
      · rw [failureControlKernel_apply]
        by_cases hmass : selectionFailureMass N nK mZ mX pA pB = 0 <;>
          simp [hq, hmass]
      · by_cases hmass : selectionFailureMass N nK mZ mX pA pB = 0
        · have hsum :
              (∑' x : RawControl N,
                (failureSet nK mZ mX).indicator (rawControlLaw N pA pB) x) = 0 :=
            (tsum_failureSet_indicator N nK mZ mX pA pB).trans hmass
          have homegaZero := (ENNReal.tsum_eq_zero.mp hsum) omega
          have homegaMem : omega ∈ failureSet nK mZ mX := hq
          rw [Set.indicator_of_mem homegaMem] at homegaZero
          rw [failureControlKernel_apply]
          simp [hq, hmass, homegaZero]
        · have hmassTop : selectionFailureMass N nK mZ mX pA pB ≠ ∞ := by
            intro htop
            have hsum := selectionSuccessMass_add_failureMass N nK mZ mX pA pB
            rw [htop, add_top] at hsum
            exact ENNReal.top_ne_one hsum
          rw [failureControlKernel_apply, ite_eq_right hmass]
          simp only [hq, not_false_eq_true, ite_true, ite_false]
          -- `m · (r / m) = r · (m · m⁻¹) = r`
          rw [div_eq_mul_inv, mul_left_comm, ENNReal.mul_inv_cancel hmass hmassTop, mul_one]
    · simp only [PMF.bind_apply, PMF.pure_apply, Prod.mk.injEq, true_and,
        mul_ite, mul_one, mul_zero, tsum_fintype, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true, Bool.true_eq_false, false_and,
        true_eq_decide_iff]
      by_cases hsuccess : selectionSuccessMass N nK mZ mX pA pB = 0
      · rw [hsuccess, zero_mul]
        by_cases hq : HasQuotas nK mZ mX omega
        · rw [ite_eq_left hq]
          have hsumzero :
              (∑ x : RawControl N,
                if HasQuotas nK mZ mX x then rawControlLaw N pA pB x else 0) = 0 :=
            hsuccess
          have hterm :=
            (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => zero_le)).mp hsumzero
              omega (Finset.mem_univ omega)
          simpa [hq] using hterm.symm
        · simp [hq]
      · have hfiberNonzero
            (S : Set.powersetCard (Fin N) (nK + mZ + mX))
            (π : Equiv.Perm (Fin (nK + mZ + mX))) :
            selectedInjectionFiberMass N nK mZ mX pA pB (joinSubsetPerm S π) ≠ 0 := by
          intro hfiber
          apply hsuccess
          rw [selectionSuccessMass_eq_sum_fibers]
          apply Finset.sum_eq_zero
          intro g _
          rw [selectedInjectionFiberMass_eq_of_embeddings
            N nK mZ mX pA pB g (joinSubsetPerm S π)]
          exact hfiber
        by_cases hq : HasQuotas nK mZ mX omega
        · rw [ite_eq_left hq]
          have hisSome : (select nK mZ mX omega).isSome = true :=
            (select_isSome_iff nK mZ mX omega).mpr hq
          obtain ⟨f, hselect⟩ :
              ∃ f : Fin (nK + mZ + mX) ↪ Fin N,
                select nK mZ mX omega = some f := by
            cases hs : select nK mZ mX omega with
            | none => simp [hs] at hisSome
            | some f => exact ⟨f, rfl⟩
          have hfiberEq
              (S : Set.powersetCard (Fin N) (nK + mZ + mX))
              (π : Equiv.Perm (Fin (nK + mZ + mX))) :
              selectedInjectionFiberMass N nK mZ mX pA pB (joinSubsetPerm S π) =
                selectedInjectionFiberMass N nK mZ mX pA pB f :=
            selectedInjectionFiberMass_eq_of_embeddings
              N nK mZ mX pA pB (joinSubsetPerm S π) f
          have hpair
              (S : Set.powersetCard (Fin N) (nK + mZ + mX))
              (π : Equiv.Perm (Fin (nK + mZ + mX))) :
              f = joinSubsetPerm S π ↔
                S = imageSubset f ∧ π = embeddingPermutation f := by
            constructor
            · intro h
              have hp := congrArg embeddingSubsetPermForward h.symm
              rw [embeddingSubsetPermForward_join] at hp
              simpa [embeddingSubsetPermForward] using hp
            · rintro ⟨rfl, rfl⟩
              exact (join_imageSubset_embeddingPermutation f).symm
          simp_rw [selectedControlKernel_apply,
            ite_eq_right (hfiberNonzero _ _), hselect, Option.some.injEq, hfiberEq, hpair]
          simp only [ite_false, Finset.sum_const_zero, mul_zero, add_zero]
          rw [Fintype.sum_eq_single (imageSubset f)]
          · rw [Fintype.sum_eq_single (embeddingPermutation f)]
            · simp only [true_and, ite_true]
              have hcardSubset :
                  (Fintype.card
                    (Set.powersetCard (Fin N) (nK + mZ + mX)) : ℝ≥0∞) =
                    (N.choose (nK + mZ + mX) : ℝ≥0∞) := by
                have hcardNat :
                    Fintype.card (Set.powersetCard (Fin N) (nK + mZ + mX)) =
                      N.choose (nK + mZ + mX) := by
                  rw [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_fin]
                exact_mod_cast hcardNat
              have hcardPerm :
                  (Fintype.card (Equiv.Perm (Fin (nK + mZ + mX))) : ℝ≥0∞) =
                    ((nK + mZ + mX).factorial : ℝ≥0∞) := by
                rw [Fintype.card_perm, Fintype.card_fin]
              have hmassFormula :
                  selectedInjectionFiberMass N nK mZ mX pA pB f =
                    selectionSuccessMass N nK mZ mX pA pB /
                      ((N.choose (nK + mZ + mX) : ℝ≥0∞) *
                        ((nK + mZ + mX).factorial : ℝ≥0∞)) := by
                calc
                  selectedInjectionFiberMass N nK mZ mX pA pB f =
                      selectedSubsetPermMass N nK mZ mX pA pB
                        (imageSubset f) (embeddingPermutation f) := by
                    rw [selectedSubsetPermMass_eq_fiberMass,
                      join_imageSubset_embeddingPermutation]
                  _ = selectionSuccessMass N nK mZ mX pA pB /
                        ((N.choose (nK + mZ + mX) : ℝ≥0∞) *
                          ((nK + mZ + mX).factorial : ℝ≥0∞)) :=
                    selectedSubsetPerm_mass N nK mZ mX pA pB
                      (imageSubset f) (embeddingPermutation f)
              have hsuccessTop : selectionSuccessMass N nK mZ mX pA pB ≠ ∞ := by
                intro htop
                have hsum := selectionSuccessMass_add_failureMass N nK mZ mX pA pB
                rw [htop, top_add] at hsum
                exact ENNReal.top_ne_one hsum
              have hchoose : (N.choose (nK + mZ + mX) : ℝ≥0∞) ≠ 0 := by
                exact_mod_cast (Nat.choose_pos hN).ne'
              have hfactorial : ((nK + mZ + mX).factorial : ℝ≥0∞) ≠ 0 := by
                exact_mod_cast Nat.factorial_ne_zero (nK + mZ + mX)
              have hdenom :
                  (N.choose (nK + mZ + mX) : ℝ≥0∞) *
                      ((nK + mZ + mX).factorial : ℝ≥0∞) ≠ 0 :=
                mul_ne_zero hchoose hfactorial
              have hfiberZero :
                  selectedInjectionFiberMass N nK mZ mX pA pB f ≠ 0 := by
                have h := hfiberNonzero (imageSubset f) (embeddingPermutation f)
                simpa [join_imageSubset_embeddingPermutation] using h
              have hfiberTop :
                  selectedInjectionFiberMass N nK mZ mX pA pB f ≠ ∞ := by
                rw [hmassFormula]
                exact ENNReal.div_ne_top hsuccessTop hdenom
              let : Nonempty
                  (Set.powersetCard (Fin N) (nK + mZ + mX)) :=
                ⟨initialRetainedSubset hN⟩
              let : Nonempty (Equiv.Perm (Fin (nK + mZ + mX))) :=
                ⟨Equiv.refl _⟩
              rw [uniformRetainedSubset, PMF.uniformOfFintype_apply,
                uniformInnerPerm, PMF.uniformOfFintype_apply, hcardSubset, hcardPerm]
              calc
                selectionSuccessMass N nK mZ mX pA pB *
                    ((N.choose (nK + mZ + mX) : ℝ≥0∞)⁻¹ *
                      (((nK + mZ + mX).factorial : ℝ≥0∞)⁻¹ *
                        (rawControlLaw N pA pB omega /
                          selectedInjectionFiberMass N nK mZ mX pA pB f))) =
                    (selectionSuccessMass N nK mZ mX pA pB /
                      ((N.choose (nK + mZ + mX) : ℝ≥0∞) *
                        ((nK + mZ + mX).factorial : ℝ≥0∞))) *
                      (rawControlLaw N pA pB omega /
                        selectedInjectionFiberMass N nK mZ mX pA pB f) := by
                  simp only [div_eq_mul_inv]
                  rw [ENNReal.mul_inv (Or.inl hchoose) (Or.inr hfactorial)]
                  simp only [mul_assoc]
                _ = selectedInjectionFiberMass N nK mZ mX pA pB f *
                      (rawControlLaw N pA pB omega /
                        selectedInjectionFiberMass N nK mZ mX pA pB f) := by
                  rw [← hmassFormula]
                _ = rawControlLaw N pA pB omega := by
                  rw [div_eq_mul_inv, mul_left_comm, ENNReal.mul_inv_cancel hfiberZero hfiberTop,
                    mul_one]
            · -- the indicator vanishes off `π = embeddingPermutation f`
              intro π hπ
              simp only [hπ, and_false, ite_false, ENNReal.zero_div, mul_zero]
          · -- the indicator vanishes off `S = imageSubset f`
            intro S hS
            simp only [hS, false_and, ite_false, ENNReal.zero_div, mul_zero,
              Finset.sum_const_zero]
        · have hselect : select nK mZ mX omega = none := by
            cases hs : select nK mZ mX omega with
            | none => rfl
            | some f =>
                exfalso
                apply hq
                exact (select_isSome_iff nK mZ mX omega).mp (by simp [hs])
          simp_rw [selectedControlKernel_apply,
            ite_eq_right (hfiberNonzero _ _), hselect]
          simp [hq]
  · -- only the tag `(status, omega)` itself can match
    intro x hx
    exact ite_eq_right fun h => hx (congrArg Prod.snd h).symm

/-! ## Kernel and status formulas -/

/-- Status-law point masses are the success and failure masses by construction. -/
theorem selectionStatusLaw_apply
    (N nK mZ mX : ℕ) (pA pB : PMF Basis) (status : Bool) :
    selectionStatusLaw N nK mZ mX pA pB status =
      selectionStatusWeight N nK mZ mX pA pB status := by
  rfl

/-- Zero quotas have no failure mass. -/
theorem selectionFailureMass_zero_quotas (N : ℕ) (pA pB : PMF Basis) :
    selectionFailureMass N 0 0 0 pA pB = 0 := by
  simp [selectionFailureMass, HasQuotas]

end QKD.BB84.Sampling
