import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD

/-!
# Positive definite block diagonal matrices

Positive definite block diagonal matrices.
-/

open Matrix
open scoped ComplexOrder

noncomputable section

/-- **A block-diagonal matrix with positive-definite blocks is positive definite.**  Strict sibling
of
`Matrix.posSemidef_blockDiagonal`: any nonzero vector has a nonzero component on some block `k`,
whose
quadratic form is strictly positive while the others are nonnegative. -/
lemma _root_.Matrix.posDef_blockDiagonal {n : ℕ} {o : Type*} [Finite o] [DecidableEq o]
    {M : o → Matrix (Fin n) (Fin n) ℂ} (h : ∀ i, (M i).PosDef) :
    (Matrix.blockDiagonal M).PosDef := by
  classical
  let := Fintype.ofFinite o
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.posSemidef_blockDiagonal (fun i => (h i).posSemidef)).isHermitian ?_
  intro x hx
  have hsum : star x ⬝ᵥ (Matrix.blockDiagonal M *ᵥ x)
      = ∑ k : o, star (fun b => x (b, k)) ⬝ᵥ (M k *ᵥ (fun b => x (b, k))) := by
    simp only [dotProduct, Pi.star_apply, Fintype.sum_prod_type, blockDiagonal_mulVec_apply]
    rw [Finset.sum_comm]
  rw [hsum]
  obtain ⟨⟨a, k⟩, hp⟩ := Function.ne_iff.mp hx
  refine Finset.sum_pos'
    (fun k' _ => (h k').posSemidef.dotProduct_mulVec_nonneg (fun b => x (b, k')))
    ⟨k, Finset.mem_univ k, ?_⟩
  refine (h k).dotProduct_mulVec_pos (fun hzero => hp ?_)
  exact congrFun hzero a

end
