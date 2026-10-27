import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Hash Families

2-universal hash family — a seed-indexed family of functions `Domain → Codomain`
with a collision-probability bound. Used by both classical privacy amplification
(`Math/Concentration/PrivacyAmplification.lean`) and the quantum Leftover Hash
Lemma (`InfoTheory/QuantumLHL/*`).
-/

noncomputable section

namespace Math

/-- A hash family from Domain to Codomain, parameterized by a seed type `Seed`.

    For each seed s, we get a hash function `hash s : Domain → Codomain`.

    The 2-universality property is NOT bundled here; it is a separate predicate
    `HashFamily.IsUniversal`. This structure only packages the hash function
    and the required Fintype/Nonempty instances on Seed and Codomain. -/
structure HashFamily (Domain Codomain Seed : Type*) where
  /-- The hash function parameterized by seed -/
  hash : Seed → Domain → Codomain
  /-- Seeds form a fintype for probability calculations -/
  [seedFintype : Fintype Seed]
  /-- Seeds are nonempty -/
  [seedNonempty : Nonempty Seed]
  /-- Codomain is a fintype -/
  [codomainFintype : Fintype Codomain]
  /-- Codomain is nonempty -/
  [codomainNonempty : Nonempty Codomain]

/-- The 2-universal collision bound property.

    For any two distinct inputs x ≠ x', the number of seeds where they
    collide under the hash function is bounded by |Seed| / |Codomain|
    (floor division). Equivalently, the collision probability is at
    most 1/|Codomain|.

    Code form (ℕ floor division, convenient for combinatorial proofs):
      |{s : h(s,x) = h(s,x')}| ≤ |Seed| / |Codomain|

    Equivalent real form (via `HashFamily.collisionProb`):
      H.collisionProb x x' ≤ 1 / (|Codomain| : ℝ) -/
def HashFamily.IsUniversal {Domain Codomain Seed : Type*}
    [DecidableEq Codomain]
    (H : HashFamily Domain Codomain Seed) : Prop :=
  ∀ x x' : Domain, x ≠ x' →
    ((@Finset.univ Seed H.seedFintype).filter (fun s => H.hash s x = H.hash s x')).card ≤
    @Fintype.card Seed H.seedFintype / @Fintype.card Codomain H.codomainFintype

/-- The collision probability for inputs x and x': the fraction of seeds
    where h(s, x) = h(s, x'), as a real number in [0, 1]. -/
def HashFamily.collisionProb {Domain Codomain Seed : Type*}
    [DecidableEq Codomain]
    (H : HashFamily Domain Codomain Seed) (x x' : Domain) : ℝ :=
  ((@Finset.univ Seed H.seedFintype).filter (fun s => H.hash s x = H.hash s x')).card /
  (@Fintype.card Seed H.seedFintype : ℝ)

/-- `IsUniversal` in real-valued form: the collision probability is bounded by
    `1/|Codomain|`. Equivalent to `HashFamily.IsUniversal` (via `Nat.cast_le` and
    `Nat.cast_div_le`), but more convenient for real-arithmetic downstream proofs
    (e.g., in the quantum Leftover Hash Lemma). -/
theorem HashFamily.isUniversal_iff_collisionProb_le
    {Domain Codomain Seed : Type*} [DecidableEq Codomain]
    (H : HashFamily Domain Codomain Seed) :
    H.IsUniversal ↔
      ∀ x x' : Domain, x ≠ x' →
        H.collisionProb x x' ≤ 1 / (@Fintype.card Codomain H.codomainFintype : ℝ) := by
  have hS : (0 : ℝ) < @Fintype.card Seed H.seedFintype :=
    Nat.cast_pos.mpr (@Fintype.card_pos Seed H.seedFintype H.seedNonempty)
  have hC : (0 : ℝ) < @Fintype.card Codomain H.codomainFintype :=
    Nat.cast_pos.mpr (@Fintype.card_pos Codomain H.codomainFintype H.codomainNonempty)
  have hCN : 0 < @Fintype.card Codomain H.codomainFintype :=
    @Fintype.card_pos Codomain H.codomainFintype H.codomainNonempty
  simp only [HashFamily.IsUniversal, HashFamily.collisionProb]
  constructor
  · intro h x x' hne
    have hmul := (Nat.le_div_iff_mul_le hCN).mp (h x x' hne)
    rw [div_le_div_iff₀ hS hC, one_mul]
    exact_mod_cast hmul
  · intro h x x' hne
    rw [Nat.le_div_iff_mul_le hCN]
    have hle := h x x' hne
    rw [div_le_div_iff₀ hS hC, one_mul] at hle
    exact_mod_cast hle

end Math

end -- noncomputable section
