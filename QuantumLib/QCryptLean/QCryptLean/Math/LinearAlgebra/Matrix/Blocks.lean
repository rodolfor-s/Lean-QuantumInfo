import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD
import QCryptLean.Math.LinearAlgebra.Matrix.Transport

/-! # Blocks -/


namespace Matrix

variable {X Y I J R : Type*}

/-- A matrix with zero off-diagonal blocks is reconstructed from its diagonal blocks. -/
theorem eq_blockDiagonal_of_offDiag_zero [Zero R] [DecidableEq I]
    (M : Matrix (X × I) (Y × I) R)
    (h : ∀ x y i j, i ≠ j → M (x, i) (y, j) = 0) :
    M = blockDiagonal (fun i => of fun x y => M (x, i) (y, i)) := by
  ext ⟨x, i⟩ ⟨y, j⟩
  by_cases hij : i = j
  · subst j
    simp
  · simp [blockDiagonal, hij, h x y i j hij]

/-- Relabel the two summands of a rectangular block matrix independently. -/
theorem reindex_fromBlocks {X' Y' I' J' : Type*}
    (e : X ≃ X') (f : Y ≃ Y') (g : I ≃ I') (h : J ≃ J')
    (A : Matrix X Y R) (B : Matrix X J R) (C : Matrix I Y R) (D : Matrix I J R) :
    reindex (e.sumCongr g) (f.sumCongr h) (fromBlocks A B C D) =
      fromBlocks (reindex e f A) (reindex e h B) (reindex g f C) (reindex g h D) := by
  ext (x | i) (y | j) <;> rfl

/-- Multiplication by a block-diagonal matrix acts separately on each block. -/
theorem blockDiagonal_mulVec [NonUnitalNonAssocSemiring R] [Fintype Y] [Fintype I]
    [DecidableEq I] (A : I → Matrix X Y R) (v : Y × I → R) (x : X) (i : I) :
    (blockDiagonal A *ᵥ v) (x, i) = (A i *ᵥ fun y => v (y, i)) x := by
  simp [mulVec, dotProduct, blockDiagonal, Fintype.sum_prod_type, ite_mul]

open scoped ComplexOrder

/-- Strictly positive blocks give a strictly positive operator on any finite product register. -/
theorem PosDef.blockDiagonal [Finite X] [Finite I] [DecidableEq I]
    {A : I → Matrix X X ℂ} (h : ∀ i, (A i).PosDef) : (Matrix.blockDiagonal A).PosDef := by
  classical
  let := Fintype.ofFinite X
  let := Fintype.ofFinite I
  refine PosDef.of_dotProduct_mulVec_pos
    (Matrix.posSemidef_blockDiagonal (fun i => (h i).posSemidef)).isHermitian ?_
  intro v hv
  have hs : star v ⬝ᵥ (Matrix.blockDiagonal A *ᵥ v) =
      ∑ i, star (fun x => v (x, i)) ⬝ᵥ (A i *ᵥ fun x => v (x, i)) := by
    simp only [dotProduct, Pi.star_apply, Fintype.sum_prod_type, blockDiagonal_mulVec]
    exact Finset.sum_comm
  rw [hs]
  obtain ⟨⟨x, i⟩, hx⟩ := Function.ne_iff.mp hv
  refine Finset.sum_pos' (fun j _ => (h j).posSemidef.dotProduct_mulVec_nonneg _) ?_
  refine ⟨i, Finset.mem_univ i, (h i).dotProduct_mulVec_pos ?_⟩
  exact fun hz => hx (congrFun hz x)

end Matrix
