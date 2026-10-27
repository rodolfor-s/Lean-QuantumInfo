import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.QuantumLHL.ScalarTwoUniversalL2

/-! # Two Universal Exact -/


open Matrix

noncomputable section

namespace InfoTheory.QuantumLHL

/-- **Exact (`2*`-universal) collision predicate.** For any two distinct inputs
`x ≠ x'`, the number of seeds on which they collide, times `|Z|`, equals `|S|`
(equality, not merely `≤`). This holds for affine/linear universal families and
is what forces the centred off-diagonal coefficient to vanish exactly. -/
def HashFamily.IsExactTwoUniversal {S X Z : Type*} [Fintype S] [Fintype Z]
    [DecidableEq Z] (H : HashFamily S X Z) : Prop :=
  ∀ x x' : X, x ≠ x' →
    (Finset.univ.filter (fun s => H.hash s x = H.hash s x')).card * Fintype.card Z
      = Fintype.card S

/-- **Exact ⇒ 2-universal.** Dividing the Nat equality by `|Z| > 0` gives the
`≤`-form collision bound `HashFamily.IsTwoUniversal` (Tomamichel eq. 7.31). -/
lemma HashFamily.IsExactTwoUniversal.isTwoUniversal {S X Z : Type*} [Fintype S]
    [Fintype Z] [DecidableEq Z] {H : HashFamily S X Z}
    (h : H.IsExactTwoUniversal) : H.IsTwoUniversal := by
  have : Nonempty Z := H.outputNonempty
  intro x x' hxx'
  have hZ_pos : 0 < (Fintype.card Z : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Z)
  have hcard := h x x' hxx'
  have hR : ((Finset.univ.filter (fun s => H.hash s x = H.hash s x')).card : ℝ)
      * (Fintype.card Z : ℝ) = (Fintype.card S : ℝ) := by
    exact_mod_cast hcard
  rw [le_div_iff₀ hZ_pos]
  exact le_of_eq hR

end InfoTheory.QuantumLHL

end -- noncomputable section
