import QCryptLean.Math.Combinatorics.CoordinateCounts
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Basic
import QCryptLean.QKD.BB84.Sampling.BasisPartition
import QCryptLean.QKD.BB84.Sampling.Disintegration
import QCryptLean.QKD.BB84.Sampling.FiberMass
import QCryptLean.QKD.BB84.Sampling.Interleave
import QCryptLean.QKD.BB84.Sampling.Selection

/-!
# Matched-basis counts of the independent BB84 basis draws

The raw control law `rawControlLaw N pA pB` draws Alice's and Bob's basis strings independently,
round by round from `pA` and `pB`, and then a uniformly random ordering of the rounds on which the
two strings agree.  This module derives the law of the two **raw-round** counts

* `(MatchedZ a b).card`, the number of the `N` measured rounds on which both parties chose Z, and
* `(MatchedX a b).card`, the number on which both chose X,

and the exact quota-failure mass `selectionFailureMass` that this law determines.  These are
counts of matched raw rounds, not of retained rounds: on quota success the selector retains
exactly `nK + mZ` of the matched-Z rounds and `mX` of the matched-X rounds and ignores the rest.

## Main statements

* `hasQuotas_iff`: the shuffled basis orders `zOrder` and `xOrder` list the matched rounds exactly
  once (`length_zOrder`, `length_xOrder`), so the quota event is a condition on the two counts
  alone and does not depend on the sampled ordering.
* `rawControlLaw_map_basisStrings`: forgetting the ordering leaves the independent product of the
  two string laws, because the conditionally uniform ordering integrates to one.
* `rawControlLaw_map_matchedCounts_apply`: the two counts have the trinomial law
  `matchedCountMass`, with per-round probabilities `matchedProb pA pB .z`,
  `matchedProb pA pB .x` and `mismatchProb pA pB`.  The two counts share the `N` rounds and are
  in general dependent.
* `rawControlLaw_map_card_matchedZ_apply`, `rawControlLaw_map_card_matchedX_apply`: each count
  alone is binomial.
* `selectionSuccessMass_eq_sum`, `selectionFailureMass_eq_sum`: the exact success and failure
  masses as finite sums of the joint law over the quota region and its complement.
* `selectionFailureMass_eq_one_of_lt`: quotas exceeding the batch, `N < nK + mZ + mX`, fail surely.
* `selectionFailureMass_le_add`: the union bound by the binomial shortfall masses
  `matchedShortfallMass`, `P[K_Z < nK + mZ] + P[K_X < mX]`, which needs no independence of the
  counts; `matchedShortfallMass_z_le_selectionFailureMass` and its X counterpart show that it is
  within a factor two of the exact mass.

The Sampling.QuotaFailure module turns the union bound into real concentration bounds.

Every statement holds for all `N` (including `N = 0`), all quotas, and arbitrary — possibly
unequal or degenerate — per-round basis laws.  The quota comparison is non-strict:
`nK + mZ` matched-Z rounds suffice, so the failure event is the strict shortage `K_Z < nK + mZ`
or `K_X < mX`.

The basis choice and sifting schedule, including biased basis choices, follow Renner,
arXiv:quant-ph/0512258v2, lines 673--736.  The pushforward identities are proved here from the
explicit finite construction.
-/

open scoped ENNReal BigOperators
open Finset

noncomputable section

namespace QKD.BB84.Sampling

open QKD.BB84.Measurement

/-! ## The quota event depends only on the matched counts -/

/-- The shuffled Z order lists each matched-Z round exactly once. -/
theorem length_zOrder {N : ℕ} (omega : RawControl N) :
    (zOrder omega).length = (MatchedZ omega.a omega.b).card := by
  obtain ⟨a, b, o⟩ := omega
  rw [← (shuffleInterleave_basisLists a b o).1, List.length_ofFn]

/-- The shuffled X order lists each matched-X round exactly once. -/
theorem length_xOrder {N : ℕ} (omega : RawControl N) :
    (xOrder omega).length = (MatchedX omega.a omega.b).card := by
  obtain ⟨a, b, o⟩ := omega
  rw [← (shuffleInterleave_basisLists a b o).2, List.length_ofFn]

/-- **Quota availability depends only on the matched counts.**  Both quotas are available exactly
when at least `nK + mZ` raw rounds are matched in Z and at least `mX` in X; the sampled ordering
of the matched rounds does not enter. -/
theorem hasQuotas_iff {N : ℕ} (nK mZ mX : ℕ) (omega : RawControl N) :
    HasQuotas nK mZ mX omega ↔
      nK + mZ ≤ (MatchedZ omega.a omega.b).card ∧ mX ≤ (MatchedX omega.a omega.b).card := by
  rw [HasQuotas, length_zOrder, length_xOrder]

/-- Matched-Z rounds are the rounds on which both parties chose Z. -/
theorem matchedZ_eq_filter {N : ℕ} (a b : Fin N → Basis) :
    MatchedZ a b = ({i | a i = .z ∧ b i = .z} : Finset (Fin N)) := by
  ext i
  simp only [mem_matchedZ_iff, Matched, mem_filter, mem_univ, true_and]
  exact ⟨fun h => ⟨h.2, h.1.symm.trans h.2⟩, fun h => ⟨h.1.trans h.2.symm, h.1⟩⟩

/-- Matched-X rounds are the rounds on which both parties chose X. -/
theorem matchedX_eq_filter {N : ℕ} (a b : Fin N → Basis) :
    MatchedX a b = ({i | a i = .x ∧ b i = .x} : Finset (Fin N)) := by
  ext i
  simp only [mem_matchedX_iff, Matched, mem_filter, mem_univ, true_and]
  exact ⟨fun h => ⟨h.2, h.1.symm.trans h.2⟩, fun h => ⟨h.1.trans h.2.symm, h.1⟩⟩

/-! ## Marginalizing the uniform ordering -/

/-- **Forgetting the matched-round ordering.**  The basis-string marginal of the raw control law
is the independent product of Alice's and Bob's string laws: for each fixed pair of strings the
conditionally uniform ordering is a probability law and integrates to one (`PMF.bind_const`). -/
theorem rawControlLaw_map_basisStrings (N : ℕ) (pA pB : PMF Basis) :
    (rawControlLaw N pA pB).map (fun omega => (omega.a, omega.b)) =
      (basisStringLaw N pA).bind fun a =>
        (basisStringLaw N pB).bind fun b => PMF.pure (a, b) := by
  simp only [rawControlLaw, PMF.map_bind, PMF.pure_map, PMF.bind_const]

/-- Point mass of the basis-string marginal: the product of the two string weights. -/
theorem rawControlLaw_map_basisStrings_apply (N : ℕ) (pA pB : PMF Basis)
    (a b : Fin N → Basis) :
    (rawControlLaw N pA pB).map (fun omega => (omega.a, omega.b)) (a, b) =
      (∏ i, pA (a i)) * ∏ i, pB (b i) := by
  rw [rawControlLaw_map_basisStrings]
  simp [PMF.bind_apply, PMF.pure_apply, tsum_fintype, basisStringLaw_apply, ite_and]

/-- Summing an indicator of a function of the sample against a PMF on a finite type is summing
the indicator against the pushforward, over any finite set containing the range. -/
private theorem sum_ite_comp_eq_sum_map {α β : Type*} [Fintype α]
    (μ : PMF α) (f : α → β) {s : Finset β} (hs : ∀ x, f x ∈ s) (P : β → Prop)
    [DecidablePred P] :
    ∑ x, (if P (f x) then μ x else 0) = ∑ y ∈ s, if P y then μ.map f y else 0 := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := s) (g := f) fun x _ => hs x]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [PMF.map_apply, tsum_fintype]
  split_ifs with hP
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : f x = y
    · simp [hx, hP]
    · simp [hx, Ne.symm hx]
  · refine Finset.sum_eq_zero fun x hx => ?_
    rw [(Finset.mem_filter.mp hx).2]
    simp [hP]

/-- The mass of a lower-tail event of a natural-number statistic is the sum of the pushforward
point masses below the threshold. -/
private theorem sum_ite_lt_eq_sum_range_map {α : Type*} [Fintype α] (μ : PMF α) (c : α → ℕ)
    (q : ℕ) :
    ∑ x, (if c x < q then μ x else 0) = ∑ k ∈ range q, μ.map c k := by
  simp only [PMF.map_apply, tsum_fintype]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : c x < q
  · rw [ite_eq_left hx, Finset.sum_eq_single_of_mem (c x) (mem_range.mpr hx)]
    · simp
    · intro k _ hk
      simp [hk]
  · rw [ite_eq_right hx]
    refine (Finset.sum_eq_zero fun k hk => ?_).symm
    have hne : k ≠ c x := fun h => hx (h ▸ mem_range.mp hk)
    simp [hne]

/-- **Events of the basis strings.**  An event that depends only on the two basis strings has
the probability assigned by the independent product of the string laws. -/
theorem sum_rawControlLaw_basisStrings (N : ℕ) (pA pB : PMF Basis)
    (P : (Fin N → Basis) → (Fin N → Basis) → Prop) [∀ a b, Decidable (P a b)] :
    ∑ omega : RawControl N, (if P omega.a omega.b then rawControlLaw N pA pB omega else 0) =
      ∑ a, ∑ b, if P a b then (∏ i, pA (a i)) * ∏ i, pB (b i) else 0 := by
  rw [sum_ite_comp_eq_sum_map (rawControlLaw N pA pB) (fun omega => (omega.a, omega.b))
      (fun _ => mem_univ _) (fun ab => P ab.1 ab.2),
    Fintype.sum_prod_type]
  simp only [rawControlLaw_map_basisStrings_apply]

/-! ## Per-round sifting probabilities -/

/-- Probability that one raw round is matched in basis `θ`: both parties choose `θ`. -/
def matchedProb (pA pB : PMF Basis) (θ : Basis) : ℝ≥0∞ :=
  pA θ * pB θ

/-- Probability that one raw round is mismatched: the parties choose different bases. -/
def mismatchProb (pA pB : PMF Basis) : ℝ≥0∞ :=
  pA .z * pB .x + pA .x * pB .z

private theorem sum_basis {M : Type*} [AddCommMonoid M] (f : Basis → M) :
    ∑ θ, f θ = f .z + f .x :=
  Fintype.sum_eq_add Basis.z Basis.x (by decide) fun θ h => by cases θ <;> simp at h

private theorem pmf_basis_add (p : PMF Basis) : p .z + p .x = 1 := by
  rw [← sum_basis, ← tsum_fintype (L := SummationFilter.unconditional _)]
  exact p.tsum_coe

/-- Each raw round is matched in Z, mismatched, or matched in X. -/
theorem matchedProb_add_mismatchProb_add_matchedProb (pA pB : PMF Basis) :
    matchedProb pA pB .z + mismatchProb pA pB + matchedProb pA pB .x = 1 := by
  calc
    matchedProb pA pB .z + mismatchProb pA pB + matchedProb pA pB .x =
        (pA .z + pA .x) * (pB .z + pB .x) := by
      simp only [matchedProb, mismatchProb]
      ring
    _ = 1 := by rw [pmf_basis_add, pmf_basis_add, one_mul]

/-- A matched probability is at most one. -/
theorem matchedProb_le_one (pA pB : PMF Basis) (θ : Basis) : matchedProb pA pB θ ≤ 1 := by
  have h := matchedProb_add_mismatchProb_add_matchedProb pA pB
  cases θ
  · rw [← h, add_assoc]
    exact le_self_add
  · rw [← h]
    exact le_add_self

/-- A matched probability is finite. -/
theorem matchedProb_ne_top (pA pB : PMF Basis) (θ : Basis) : matchedProb pA pB θ ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (matchedProb_le_one pA pB θ)

/-- The joint per-round weight of a basis pair. -/
private def pairWeight (pA pB : PMF Basis) (c : Basis × Basis) : ℝ≥0∞ :=
  pA c.1 * pB c.2

private theorem sum_pairWeight_diag (pA pB : PMF Basis) (θ : Basis) :
    ∑ c with c.1 = θ ∧ c.2 = θ, pairWeight pA pB c = matchedProb pA pB θ := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  cases θ <;> simp [sum_basis, pairWeight, matchedProb]

private theorem sum_pairWeight_not_diag (pA pB : PMF Basis) (θ : Basis) :
    ∑ c with ¬(c.1 = θ ∧ c.2 = θ), pairWeight pA pB c = 1 - matchedProb pA pB θ := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (Basis × Basis))
    (fun c => c.1 = θ ∧ c.2 = θ) (pairWeight pA pB)
  have htotal : ∑ c, pairWeight pA pB c = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [pairWeight, ← Finset.mul_sum, ← Finset.sum_mul, sum_basis, pmf_basis_add, one_mul]
  rw [htotal, sum_pairWeight_diag] at hsplit
  exact ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top (by rw [add_comm]; exact hsplit)

private theorem sum_pairWeight_rest (pA pB : PMF Basis) :
    ∑ c with ¬(c.1 = Basis.z ∧ c.2 = Basis.z) ∧ ¬(c.1 = Basis.x ∧ c.2 = Basis.x),
      pairWeight pA pB c = mismatchProb pA pB := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp [sum_basis, pairWeight, mismatchProb]

/-- Reindex a pair of basis strings as one string of basis pairs. -/
private theorem sum_basisStrings_eq_sum_pairs (N : ℕ)
    (G : (Fin N → Basis) → (Fin N → Basis) → ℝ≥0∞) :
    ∑ a, ∑ b, G a b = ∑ ω : Fin N → Basis × Basis, G (fun i => (ω i).1) (fun i => (ω i).2) := by
  rw [← Fintype.sum_prod_type', ← (Equiv.arrowProdEquivProdArrow _ _ _).sum_comp]
  rfl

private theorem prod_pairWeight {N : ℕ} (pA pB : PMF Basis) (ω : Fin N → Basis × Basis) :
    (∏ i, pA (ω i).1) * ∏ i, pB (ω i).2 = ∏ i, pairWeight pA pB (ω i) := by
  rw [← Finset.prod_mul_distrib]
  rfl

/-! ## The law of the matched counts -/

/-- The numbers of raw rounds matched in the Z basis and in the X basis. -/
def matchedCounts {N : ℕ} (omega : RawControl N) : ℕ × ℕ :=
  ((MatchedZ omega.a omega.b).card, (MatchedX omega.a omega.b).card)

/-- The trinomial probability that exactly `z` of `N` raw rounds are matched in Z and exactly `x`
are matched in X.  It vanishes unless `z + x ≤ N`. -/
def matchedCountMass (N : ℕ) (pA pB : PMF Basis) (z x : ℕ) : ℝ≥0∞ :=
  N.choose z * (N - z).choose x * matchedProb pA pB .z ^ z * matchedProb pA pB .x ^ x *
    mismatchProb pA pB ^ (N - z - x)

/-- **The joint law of the matched counts is trinomial.**  The numbers of matched-Z and matched-X
raw rounds have the point masses `matchedCountMass N pA pB z x`, for every `N`, every `z` and
`x`, and arbitrary per-round basis laws. -/
theorem rawControlLaw_map_matchedCounts_apply (N : ℕ) (pA pB : PMF Basis) (z x : ℕ) :
    (rawControlLaw N pA pB).map matchedCounts (z, x) = matchedCountMass N pA pB z x := by
  have hevent := sum_rawControlLaw_basisStrings N pA pB
    (fun a b => (MatchedZ a b).card = z ∧ (MatchedX a b).card = x)
  rw [PMF.map_apply, tsum_fintype]
  simp only [matchedCounts, Prod.mk.injEq, eq_comm (a := z), eq_comm (a := x)]
  rw [hevent, sum_basisStrings_eq_sum_pairs, ← Finset.sum_filter]
  simp only [matchedZ_eq_filter, matchedX_eq_filter, prod_pairWeight]
  rw [Fintype.sum_prod_filter_card_eq_and_card_eq (fun c : Basis × Basis => c.1 = .z ∧ c.2 = .z)
      (fun c => c.1 = .x ∧ c.2 = .x) (fun c hz hx => by simp_all) (pairWeight pA pB) z x,
    sum_pairWeight_diag, sum_pairWeight_diag, sum_pairWeight_rest, Fintype.card_fin]
  rfl

/-- Summing a predicate of one diagonal count gives its binomial law. -/
private theorem sum_rawControlLaw_card_diag (N : ℕ) (pA pB : PMF Basis) (θ : Basis) (k : ℕ) :
    ∑ omega : RawControl N,
        (if (#{i | omega.a i = θ ∧ omega.b i = θ} : ℕ) = k then rawControlLaw N pA pB omega
          else 0) =
      N.choose k * matchedProb pA pB θ ^ k * (1 - matchedProb pA pB θ) ^ (N - k) := by
  rw [sum_rawControlLaw_basisStrings N pA pB (fun a b => #{i | a i = θ ∧ b i = θ} = k),
    sum_basisStrings_eq_sum_pairs, ← Finset.sum_filter]
  simp only [prod_pairWeight]
  rw [Fintype.sum_prod_filter_card_eq (fun c : Basis × Basis => c.1 = θ ∧ c.2 = θ)
      (pairWeight pA pB) k,
    sum_pairWeight_diag, sum_pairWeight_not_diag, Fintype.card_fin]

/-- **The matched-Z count is binomial** with success probability `matchedProb pA pB .z`. -/
theorem rawControlLaw_map_card_matchedZ_apply (N : ℕ) (pA pB : PMF Basis) (k : ℕ) :
    (rawControlLaw N pA pB).map (fun omega => (MatchedZ omega.a omega.b).card) k =
      N.choose k * matchedProb pA pB .z ^ k * (1 - matchedProb pA pB .z) ^ (N - k) := by
  rw [PMF.map_apply, tsum_fintype, ← sum_rawControlLaw_card_diag N pA pB .z k]
  refine Finset.sum_congr rfl fun omega _ => ?_
  rw [matchedZ_eq_filter]
  by_cases h : k = #{i | omega.a i = Basis.z ∧ omega.b i = Basis.z}
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

/-- **The matched-X count is binomial** with success probability `matchedProb pA pB .x`. -/
theorem rawControlLaw_map_card_matchedX_apply (N : ℕ) (pA pB : PMF Basis) (k : ℕ) :
    (rawControlLaw N pA pB).map (fun omega => (MatchedX omega.a omega.b).card) k =
      N.choose k * matchedProb pA pB .x ^ k * (1 - matchedProb pA pB .x) ^ (N - k) := by
  rw [PMF.map_apply, tsum_fintype, ← sum_rawControlLaw_card_diag N pA pB .x k]
  refine Finset.sum_congr rfl fun omega _ => ?_
  rw [matchedX_eq_filter]
  by_cases h : k = #{i | omega.a i = Basis.x ∧ omega.b i = Basis.x}
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

/-! ## Exact success and failure masses -/

/-- An event of the two matched counts has the mass of the trinomial law on the event. -/
theorem sum_rawControlLaw_matchedCounts (N : ℕ) (pA pB : PMF Basis) (F : ℕ → ℕ → Prop)
    [∀ z x, Decidable (F z x)] :
    ∑ omega : RawControl N,
        (if F (MatchedZ omega.a omega.b).card (MatchedX omega.a omega.b).card then
          rawControlLaw N pA pB omega else 0) =
      ∑ z ∈ range (N + 1), ∑ x ∈ range (N + 1),
        if F z x then matchedCountMass N pA pB z x else 0 := by
  have hcard : ∀ s : Finset (Fin N), s.card < N + 1 := fun s => by
    simpa using Nat.lt_succ_of_le (card_le_univ s)
  have hrange : ∀ omega : RawControl N,
      matchedCounts omega ∈ range (N + 1) ×ˢ range (N + 1) := fun omega =>
    mem_product.mpr ⟨mem_range.mpr (hcard (MatchedZ omega.a omega.b)),
      mem_range.mpr (hcard (MatchedX omega.a omega.b))⟩
  rw [show (∑ omega : RawControl N,
        if F (MatchedZ omega.a omega.b).card (MatchedX omega.a omega.b).card then
          rawControlLaw N pA pB omega else 0) =
      ∑ omega : RawControl N,
        if F (matchedCounts omega).1 (matchedCounts omega).2 then
          rawControlLaw N pA pB omega else 0 from rfl,
    sum_ite_comp_eq_sum_map (rawControlLaw N pA pB) matchedCounts hrange
      (fun c => F c.1 c.2),
    Finset.sum_product]
  simp only [rawControlLaw_map_matchedCounts_apply]

/-- **Exact quota-success mass.**  The raw controls meeting both quotas have the trinomial mass of
the counts with at least `nK + mZ` matched-Z and at least `mX` matched-X raw rounds. -/
theorem selectionSuccessMass_eq_sum (N nK mZ mX : ℕ) (pA pB : PMF Basis) :
    selectionSuccessMass N nK mZ mX pA pB =
      ∑ z ∈ range (N + 1), ∑ x ∈ range (N + 1),
        if nK + mZ ≤ z ∧ mX ≤ x then matchedCountMass N pA pB z x else 0 := by
  rw [selectionSuccessMass, ← sum_rawControlLaw_matchedCounts]
  simp only [hasQuotas_iff]

/-- **Exact quota-failure mass.**  The raw controls failing a quota have the trinomial mass of the
counts with fewer than `nK + mZ` matched-Z or fewer than `mX` matched-X raw rounds.  The
shortage inequalities are strict: exactly `nK + mZ` matched-Z rounds meet the Z quota. -/
theorem selectionFailureMass_eq_sum (N nK mZ mX : ℕ) (pA pB : PMF Basis) :
    selectionFailureMass N nK mZ mX pA pB =
      ∑ z ∈ range (N + 1), ∑ x ∈ range (N + 1),
        if z < nK + mZ ∨ x < mX then matchedCountMass N pA pB z x else 0 := by
  rw [selectionFailureMass, ← sum_rawControlLaw_matchedCounts]
  simp only [hasQuotas_iff, not_and_or, not_le]

/-- **Infeasible quotas fail surely.**  At most `N` raw rounds are matched in total, so quotas
with `N < nK + mZ + mX` are never met; in particular every positive quota fails when `N = 0`. -/
theorem selectionFailureMass_eq_one_of_lt {N nK mZ mX : ℕ} (pA pB : PMF Basis)
    (h : N < nK + mZ + mX) : selectionFailureMass N nK mZ mX pA pB = 1 := by
  have hsuccess : selectionSuccessMass N nK mZ mX pA pB = 0 := by
    rw [selectionSuccessMass]
    refine Finset.sum_eq_zero fun omega _ => ite_eq_right fun hq => ?_
    rw [hasQuotas_iff] at hq
    have hpart := matchedBasis_partition_card omega.a omega.b
    have hle : (Matched omega.a omega.b).card ≤ N := by
      simpa using card_le_univ (Matched omega.a omega.b)
    omega
  simpa [hsuccess] using selectionSuccessMass_add_failureMass N nK mZ mX pA pB

/-! ## Shortfalls and the union bound -/

/-- The probability `P[K_θ < q]` that fewer than `q` of the `N` raw rounds are matched in basis
`θ`: the lower tail of the binomial law with success probability `matchedProb pA pB θ`. -/
def matchedShortfallMass (N q : ℕ) (pA pB : PMF Basis) (θ : Basis) : ℝ≥0∞ :=
  ∑ k ∈ range q, N.choose k * matchedProb pA pB θ ^ k * (1 - matchedProb pA pB θ) ^ (N - k)

/-- The raw controls with fewer than `q` matched-Z rounds have mass
`matchedShortfallMass N q pA pB .z`. -/
theorem sum_rawControlLaw_card_matchedZ_lt (N q : ℕ) (pA pB : PMF Basis) :
    ∑ omega : RawControl N,
        (if (MatchedZ omega.a omega.b).card < q then rawControlLaw N pA pB omega else 0) =
      matchedShortfallMass N q pA pB .z := by
  have h := sum_ite_lt_eq_sum_range_map (rawControlLaw N pA pB)
    (fun omega => (MatchedZ omega.a omega.b).card) q
  simp only [rawControlLaw_map_card_matchedZ_apply] at h
  exact h

/-- The raw controls with fewer than `q` matched-X rounds have mass
`matchedShortfallMass N q pA pB .x`. -/
theorem sum_rawControlLaw_card_matchedX_lt (N q : ℕ) (pA pB : PMF Basis) :
    ∑ omega : RawControl N,
        (if (MatchedX omega.a omega.b).card < q then rawControlLaw N pA pB omega else 0) =
      matchedShortfallMass N q pA pB .x := by
  have h := sum_ite_lt_eq_sum_range_map (rawControlLaw N pA pB)
    (fun omega => (MatchedX omega.a omega.b).card) q
  simp only [rawControlLaw_map_card_matchedX_apply] at h
  exact h

/-- **Union bound on the quota-failure mass.**  Failing a quota means a shortage of matched-Z or
of matched-X raw rounds, so the failure mass is at most `P[K_Z < nK + mZ] + P[K_X < mX]`.  The
two counts are in general dependent; the bound uses no independence between them. -/
theorem selectionFailureMass_le_add (N nK mZ mX : ℕ) (pA pB : PMF Basis) :
    selectionFailureMass N nK mZ mX pA pB ≤
      matchedShortfallMass N (nK + mZ) pA pB .z + matchedShortfallMass N mX pA pB .x := by
  rw [← sum_rawControlLaw_card_matchedZ_lt, ← sum_rawControlLaw_card_matchedX_lt,
    ← Finset.sum_add_distrib, selectionFailureMass]
  refine Finset.sum_le_sum fun omega _ => ?_
  simp only [hasQuotas_iff, not_and_or, not_le]
  by_cases hz : (MatchedZ omega.a omega.b).card < nK + mZ
  · simp [hz]
  · by_cases hx : (MatchedX omega.a omega.b).card < mX
    · simp [hz, hx]
    · simp [hz, hx]

/-- A shortage of matched-Z raw rounds alone fails the quotas.  With its X counterpart this shows
that the union bound `selectionFailureMass_le_add` is within a factor two of the exact mass. -/
theorem matchedShortfallMass_z_le_selectionFailureMass (N nK mZ mX : ℕ) (pA pB : PMF Basis) :
    matchedShortfallMass N (nK + mZ) pA pB .z ≤ selectionFailureMass N nK mZ mX pA pB := by
  rw [← sum_rawControlLaw_card_matchedZ_lt, selectionFailureMass]
  refine Finset.sum_le_sum fun omega _ => ?_
  by_cases hz : (MatchedZ omega.a omega.b).card < nK + mZ
  · have hq : ¬HasQuotas nK mZ mX omega := fun hq => absurd ((hasQuotas_iff _ _ _ _).mp hq).1
      (not_le.mpr hz)
    simp [hz, hq]
  · simp [hz]

/-- A shortage of matched-X raw rounds alone fails the quotas. -/
theorem matchedShortfallMass_x_le_selectionFailureMass (N nK mZ mX : ℕ) (pA pB : PMF Basis) :
    matchedShortfallMass N mX pA pB .x ≤ selectionFailureMass N nK mZ mX pA pB := by
  rw [← sum_rawControlLaw_card_matchedX_lt, selectionFailureMass]
  refine Finset.sum_le_sum fun omega _ => ?_
  by_cases hx : (MatchedX omega.a omega.b).card < mX
  · have hq : ¬HasQuotas nK mZ mX omega := fun hq => absurd ((hasQuotas_iff _ _ _ _).mp hq).2
      (not_le.mpr hx)
    simp [hx, hq]
  · simp [hx]

end QKD.BB84.Sampling
