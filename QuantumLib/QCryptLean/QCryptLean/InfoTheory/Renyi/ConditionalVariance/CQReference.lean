import Batteries.Tactic.OpenPrivate
import QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights

/-! # CQReference -/


open Matrix 
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators

noncomputable section

namespace InfoTheory.Renyi

private local instance (m : Type*) [Fintype m] [DecidableEq m] :
    CStarAlgebra (Matrix m m ℂ) := {}


open private log_eq_cfc'
  from QCryptLean.InfoTheory.Renyi.ConditionalVariance.SpectralWeights


/-- The Loewner order carries kernel inclusion backwards: `0 ≤ A ≤ B` forces
`ker B ⊆ ker A`. -/
private lemma mulVec_eq_zero_of_le {m : Type*} [Fintype m]
    {A B : Matrix m m ℂ} (hA : 0 ≤ A) (hAB : A ≤ B) {v : m → ℂ}
    (hv : B.mulVec v = 0) : A.mulVec v = 0 := by
  have hApsd : A.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hA
  have hBA : (B - A).PosSemidef := Matrix.le_iff.mp hAB
  have h1 : (0 : ℂ) ≤ star v ⬝ᵥ ((B - A).mulVec v) := hBA.dotProduct_mulVec_nonneg v
  have h2 : (0 : ℂ) ≤ star v ⬝ᵥ (A.mulVec v) := hApsd.dotProduct_mulVec_nonneg v
  have h3 : star v ⬝ᵥ ((B - A).mulVec v) = - (star v ⬝ᵥ (A.mulVec v)) := by
    rw [Matrix.sub_mulVec, hv, dotProduct_sub, dotProduct_zero, zero_sub]
  rw [h3] at h1
  exact hApsd.dotProduct_mulVec_zero_iff.mp
    (le_antisymm (neg_nonneg.mp h1) h2)

section CQAux

variable {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}

end CQAux


end InfoTheory.Renyi

end
