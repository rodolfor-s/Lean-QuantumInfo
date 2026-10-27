import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic

/-!
# Matrix transport without numbered registers

Mathlib's reindex equivalences supply the additive, linear, ring and algebra laws.
This module supplies trace, positivity, diagonal/block and partial-trace transport.
Product permutations use actual equivalences of the index types.
-/

namespace Matrix

open scoped Kronecker

variable {X Y Z X' Y' Z' R : Type*}

/-- Simultaneous row and column transport preserves trace over any additive coefficients. -/
theorem reindex_trace [AddCommMonoid R] [Fintype X] [Fintype Y]
    (e : X ≃ Y) (M : Matrix X X R) : (reindex e e M).trace = M.trace :=
  Equiv.sum_comp e.symm (fun x => M x x)

/-- A diagonal matrix transports by transporting its diagonal entries. -/
theorem reindex_diagonal [Zero R] [DecidableEq X] [DecidableEq Y]
    (e : X ≃ Y) (d : X → R) :
    reindex e e (diagonal d) = diagonal (d ∘ e.symm) := by
  ext i j
  simp [diagonal, e.symm.injective.eq_iff]

/-- Transport the block labels and both within-block indices independently. -/
theorem reindex_blockDiagonal [Zero R] [DecidableEq Z] [DecidableEq Z']
    (e : X ≃ X') (f : Y ≃ Y') (g : Z ≃ Z') (M : Z → Matrix X Y R) :
    reindex (e.prodCongr g) (f.prodCongr g) (blockDiagonal M) =
      blockDiagonal (fun z => reindex e f (M (g.symm z))) := by
  ext ⟨x, z⟩ ⟨y, w⟩
  simp [blockDiagonal, g.symm.injective.eq_iff]

/-- Positivity is independent of the names of basis indices. -/
theorem posSemidef_reindex_iff [Ring R] [PartialOrder R] [StarRing R]
    (e : X ≃ Y) (M : Matrix X X R) : (reindex e e M).PosSemidef ↔ M.PosSemidef :=
  posSemidef_submatrix_equiv e.symm

/-- Positive definiteness is independent of the names of basis indices. -/
theorem posDef_reindex_iff [Ring R] [PartialOrder R] [StarRing R]
    (e : X ≃ Y) (M : Matrix X X R) : (reindex e e M).PosDef ↔ M.PosDef := by
  constructor
  · intro h
    simpa using h.submatrix e.injective
  · exact fun h => h.submatrix e.symm.injective

/-- Commuting tensor factors transports both product indices by `Prod.swap`. -/
theorem reindex_prodComm_kronecker [CommMagma R]
    (A : Matrix X Y R) (B : Matrix X' Y' R) :
    reindex (Equiv.prodComm X X') (Equiv.prodComm Y Y') (A ⊗ₖ B) = B ⊗ₖ A := by
  ext i j
  exact mul_comm _ _

/-- Product association is an equivalence, requiring no dimension arithmetic. -/
theorem reindex_prodAssoc_kronecker [Semigroup R]
    (A : Matrix X Y R) (B : Matrix X' Y' R) (C : Matrix Z Z' R) :
    reindex (Equiv.prodAssoc X X' Z) (Equiv.prodAssoc Y Y' Z') ((A ⊗ₖ B) ⊗ₖ C) =
      A ⊗ₖ (B ⊗ₖ C) := kronecker_assoc A B C

/-- Right partial trace is natural in the retained and discarded register equivalences. -/
theorem partialTraceRight_reindex [AddCommMonoid R] [Fintype Z] [Fintype Z']
    (e : X ≃ X') (f : Y ≃ Y') (g : Z ≃ Z') (M : Matrix (X × Z) (Y × Z) R) :
    partialTraceRight (reindex (e.prodCongr g) (f.prodCongr g) M) =
      reindex e f (partialTraceRight M) := by
  ext x y
  exact Equiv.sum_comp g.symm (fun z => M (e.symm x, z) (f.symm y, z))

/-- Left partial trace is natural in the retained and discarded register equivalences. -/
theorem partialTraceLeft_reindex [AddCommMonoid R] [Fintype Z] [Fintype Z']
    (e : X ≃ X') (f : Y ≃ Y') (g : Z ≃ Z') (M : Matrix (Z × X) (Z × Y) R) :
    partialTraceLeft (reindex (g.prodCongr e) (g.prodCongr f) M) =
      reindex e f (partialTraceLeft M) := by
  ext x y
  exact Equiv.sum_comp g.symm (fun z => M (z, e.symm x) (z, f.symm y))

/-- Hermiticity is preserved by a Kronecker product over commutative star coefficients. -/
theorem IsHermitian.kronecker [CommMagma R] [StarMul R]
    {A : Matrix X X R} {B : Matrix Y Y R} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A ⊗ₖ B).IsHermitian := by
  rw [IsHermitian, conjTranspose_kronecker, hA.eq, hB.eq]

end Matrix
