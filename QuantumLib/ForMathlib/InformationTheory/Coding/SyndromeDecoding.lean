import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic.Positivity

/-!
# Collision counts and syndrome representatives

`collisionCount` counts the competitors of an error pattern under an additive binary syndrome.
The representative lemmas bound decoding failure by missing the candidate set or colliding with
another candidate. A syndrome with no short nonzero kernel word corrects its entire Hamming ball.
Representatives are explicit data; the lemmas require membership and syndrome preservation.
-/

open scoped BigOperators

namespace Math.CodingTheory

variable {I : Type*} [Fintype I] {m : ℕ}

/-- The number of competing candidates with the same syndrome as an error pattern. -/
def collisionCount (syn : (I → Fin 2) →+ (Fin m → Fin 2))
    (T : Finset (I → Fin 2)) (e : I → Fin 2) : ℝ :=
  ∑ y ∈ T, if y ≠ e ∧ syn y = syn e then 1 else 0

/-- Collision counts are nonnegative. -/
lemma collisionCount_nonneg (syn : (I → Fin 2) →+ (Fin m → Fin 2))
    (T : Finset (I → Fin 2)) (e : I → Fin 2) :
    0 ≤ collisionCount syn T e := by
  unfold collisionCount
  positivity

/-- Each actual competing candidate contributes one to the collision count. -/
lemma one_le_collisionCount (syn : (I → Fin 2) →+ (Fin m → Fin 2)) (T : Finset (I → Fin 2))
    (e y : I → Fin 2) (hy : y ∈ T) (hne : y ≠ e)
    (hsyn : syn y = syn e) : 1 ≤ collisionCount syn T e := by
  have h := Finset.single_le_sum (f := fun y =>
    if y ≠ e ∧ syn y = syn e then (1 : ℝ) else 0)
    (fun _ _ => by positivity) hy
  simpa [collisionCount, hne, hsyn] using h

omit [Fintype I] in
/-- A candidate alone in its syndrome class is the representative of that class. -/
lemma syndromeRepresentative_eq_of_unique
    (syn : (I → Fin 2) →+ (Fin m → Fin 2)) (T : Finset (I → Fin 2))
    (rep : (Fin m → Fin 2) → (I → Fin 2))
    (hmem : ∀ e ∈ T, rep (syn e) ∈ T)
    (hsyn : ∀ e ∈ T, syn (rep (syn e)) = syn e)
    (e : I → Fin 2) (he : e ∈ T)
    (hunique : ∀ f ∈ T, syn f = syn e → f = e) : rep (syn e) = e :=
  hunique _ (hmem e he) (hsyn e he)

variable [DecidableEq I]

/-- A syndrome separating differences of weight at most twice the radius corrects the whole ball. -/
lemma syndromeRepresentative_eq_of_hamming_separation
    (syn : (I → Fin 2) →+ (Fin m → Fin 2)) (t : ℕ)
    (rep : (Fin m → Fin 2) → (I → Fin 2))
    (hmem : ∀ e ∈ Finset.univ.filter (fun e => hammingDist e 0 ≤ t),
      rep (syn e) ∈ Finset.univ.filter (fun e => hammingDist e 0 ≤ t))
    (hsyn : ∀ e ∈ Finset.univ.filter (fun e => hammingDist e 0 ≤ t),
      syn (rep (syn e)) = syn e)
    (hsep : ∀ e, hammingDist e 0 ≤ 2 * t → syn e = 0 → e = 0)
    (e : I → Fin 2) (he : hammingDist e 0 ≤ t) :
    rep (syn e) = e := by
  apply syndromeRepresentative_eq_of_unique syn _ rep hmem hsyn e
    (Finset.mem_filter.mpr ⟨Finset.mem_univ e, he⟩)
  intro f hf hs
  apply sub_eq_zero.mp
  apply hsep
  · rw [hammingDist_zero_right, sub_eq_neg_add, ← hammingDist_eq_hammingNorm,
      hammingDist_comm e f]
    have htri := hammingDist_triangle f 0 e
    rw [hammingDist_comm 0 e] at htri
    have hf' := (Finset.mem_filter.mp hf).2
    omega
  · simp only [map_sub, hs, sub_self]

/-- A wrong representative is charged either to a missing candidate or to a syndrome collision. -/
lemma syndromeRepresentative_failure_le (syn : (I → Fin 2) →+ (Fin m → Fin 2))
    (T : Finset (I → Fin 2)) (rep : (Fin m → Fin 2) → (I → Fin 2))
    (hmem : ∀ e ∈ T, rep (syn e) ∈ T)
    (hsyn : ∀ e ∈ T, syn (rep (syn e)) = syn e)
    (w : (I → Fin 2) → ℝ) (hw : ∀ e, 0 ≤ w e) :
    (∑ e, if rep (syn e) = e then 0 else w e) ≤
      (∑ e, if e ∈ T then 0 else w e) + ∑ e, w e * collisionCount syn T e := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  have hnn := mul_nonneg (hw e) (collisionCount_nonneg syn T e)
  by_cases hrep : rep (syn e) = e
  · rw [ite_eq_left hrep]
    apply add_nonneg _ hnn
    split_ifs
    · exact le_refl 0
    · exact hw e
  · rw [ite_eq_right hrep]
    by_cases he : e ∈ T
    · rw [ite_eq_left he, zero_add]
      have hc := one_le_collisionCount syn T e _ (hmem e he) hrep (hsyn e he)
      simpa using mul_le_mul_of_nonneg_left hc (hw e)
    · rw [ite_eq_right he]
      exact le_add_of_nonneg_right hnn

end Math.CodingTheory
