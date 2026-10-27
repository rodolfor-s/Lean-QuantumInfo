import Mathlib.GroupTheory.SemidirectProduct
import QCryptLean.Math.Probability.HaarMeasure
import QCryptLean.Quantum.Symmetry.FiniteGroupCommutant
import QCryptLean.Quantum.Symmetry.UnitaryCentralizerTensorPowers

/-! # Finite Group Tensor Commutant -/



noncomputable section

open scoped BigOperators

namespace Quantum.Symmetry

/-- Permutations act on group-valued words by permuting their positions. -/
def wordPermutationAction (G : Type*) [Group G] (n : ℕ) :
    Equiv.Perm (Fin n) →* MulAut (Fin n → G) where
  toFun σ :=
    { toFun := fun v => v ∘ σ.symm
      invFun := fun v => v ∘ σ
      left_inv v := by funext k; simp
      right_inv v := by funext k; simp
      map_mul' v w := rfl }
  map_one' := by ext v k; rfl
  map_mul' σ τ := by ext v k; rfl

end Quantum.Symmetry
