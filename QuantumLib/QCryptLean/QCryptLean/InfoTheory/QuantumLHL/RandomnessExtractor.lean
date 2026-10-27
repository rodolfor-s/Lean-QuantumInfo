import QCryptLean.Math.Concentration.PrivacyAmplification

/-! # Randomness Extractor -/


noncomputable section

open scoped BigOperators

namespace InfoTheory.QuantumLHL


/-- A classical seeded hash family: seed-indexed classical hash functions from X to Z.

    This is the classical hash family structure adapted for use in the quantum
    leftover hash lemma. The quantum side is handled at the level of the extractor
    output state, not inside this structure.

    Tomamichel 2016, §7.3.1: the seed F is drawn from distribution τ(f);
    here we use the uniform distribution over a finite seed type S. -/
structure HashFamily (S X Z : Type*) where
  /-- The hash function: seed s and input x give output z -/
  hash : S → X → Z
  /-- Seed type has finitely many elements -/
  [seedFintype : Fintype S]
  /-- Seed type is nonempty -/
  [seedNonempty : Nonempty S]
  /-- Output type has finitely many elements -/
  [outputFintype : Fintype Z]
  /-- Output type is nonempty -/
  [outputNonempty : Nonempty Z]

/-- 2-universality property for a classical seeded hash family.

    Tomamichel 2016, §7.3.2, eq. 7.31:
    For any two distinct inputs x ≠ x' in domain X,
      Pr_{s ∼ Uniform(S)}[hash(s, x) = hash(s, x')] ≤ 1/|Z|

    The collision probability is |{s : hash(s,x) = hash(s,x')}| / |S| ≤ 1/|Z|,
    which after clearing |S| gives the ℝ-valued inequality below. -/
def HashFamily.IsTwoUniversal {S X Z : Type*} [Fintype S] [Fintype Z] [DecidableEq Z]
    (H : HashFamily S X Z) : Prop :=
  ∀ x x' : X, x ≠ x' →
    ((Finset.univ.filter (fun s => H.hash s x = H.hash s x')).card : ℝ) ≤
    (Fintype.card S : ℝ) / (Fintype.card Z : ℝ)

end InfoTheory.QuantumLHL

end -- noncomputable section
