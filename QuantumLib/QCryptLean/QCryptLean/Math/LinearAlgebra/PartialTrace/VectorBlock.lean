import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Weighted

/-! # Vector contractions of one matrix register -/
namespace Matrix
open scoped Kronecker
variable {X Y Z R : Type*} [CommSemiring R] [StarRing R] [Fintype X]

/-- Contract the first register against a bra and a ket, retaining rectangular second registers. -/
def vectorBlock (M : Matrix (X × Y) (X × Z) R) (v w : X → R) : Matrix Y Z R :=
  of fun y z => ∑ i, ∑ j, star (v i) * M (i, y) (j, z) * w j

/-- Vector contraction is a weighted partial trace. -/
theorem vectorBlock_eq_partialTraceLeft [Fintype Z] [DecidableEq Z]
    (M : Matrix (X × Y) (X × Z) R) (v w : X → R) :
    vectorBlock M v w = partialTraceLeft (M * (vecMulVec w (star v) ⊗ₖ (1 : Matrix Z Z R))) := by
  ext y z
  simp only [vectorBlock, of_apply, partialTraceLeft_apply, mul_apply,
    kroneckerMap_apply, vecMulVec_apply, Pi.star_apply, Fintype.sum_prod_type, one_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Rank-one sandwiches factor into an outer product and a vector-contracted block. -/
theorem vecMulVec_kronecker_sandwich [Fintype Y] [DecidableEq Y]
    (a b c d : X → R) (M : Matrix (X × Y) (X × Y) R) :
    (vecMulVec a (star b) ⊗ₖ (1 : Matrix Y Y R)) * M *
      (vecMulVec c (star d) ⊗ₖ (1 : Matrix Y Y R)) =
    vecMulVec a (star d) ⊗ₖ vectorBlock M b c := by
  ext p q
  simp only [mul_apply, kroneckerMap_apply, vecMulVec_apply, Pi.star_apply,
    Fintype.sum_prod_type, one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, vectorBlock, of_apply,
    ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end Matrix

namespace Matrix
open scoped Kronecker ComplexOrder MatrixOrder
variable {X Y : Type*} [Fintype X] [Finite Y]

/-- Contracting a positive joint operator with the same vector on both sides is positive. -/
theorem PosSemidef.vectorBlock {M : Matrix (X × Y) (X × Y) ℂ}
    (hM : M.PosSemidef) (v : X → ℂ) : (Matrix.vectorBlock M v v).PosSemidef := by
  classical
  let := Fintype.ofFinite Y
  rw [vectorBlock_eq_partialTraceLeft]
  exact hM.partialTraceLeft_mul_kronecker (posSemidef_vecMulVec_self_star v)

end Matrix
