import Mathlib.LinearAlgebra.Matrix.PosDef
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic

/-! # Positivity -/


namespace Matrix

variable {X Z R : Type*} [Fintype Z]

section StarAddMonoid

variable [AddCommMonoid R] [StarAddMonoid R]

/-- The right partial trace preserves Hermiticity. -/
theorem IsHermitian.partialTraceRight {M : Matrix (X × Z) (X × Z) R}
    (hM : M.IsHermitian) : (partialTraceRight M).IsHermitian := by
  rw [partialTraceRight_eq_sum]
  exact isSelfAdjoint_sum _ fun z _ => hM.submatrix (fun x => (x, z))

/-- The left partial trace preserves Hermiticity. -/
theorem IsHermitian.partialTraceLeft {M : Matrix (Z × X) (Z × X) R}
    (hM : M.IsHermitian) : (partialTraceLeft M).IsHermitian := by
  rw [partialTraceLeft_eq_sum]
  exact isSelfAdjoint_sum _ fun z _ => hM.submatrix (fun x => (z, x))

end StarAddMonoid

variable [Ring R] [PartialOrder R] [StarRing R] [AddLeftMono R]

/-- The right partial trace preserves positive semidefiniteness. -/
theorem PosSemidef.partialTraceRight {M : Matrix (X × Z) (X × Z) R}
    (hM : M.PosSemidef) : (partialTraceRight M).PosSemidef := by
  rw [partialTraceRight_eq_sum]
  exact posSemidef_sum _ fun z _ => hM.submatrix (fun x => (x, z))

/-- The left partial trace preserves positive semidefiniteness. -/
theorem PosSemidef.partialTraceLeft {M : Matrix (Z × X) (Z × X) R}
    (hM : M.PosSemidef) : (partialTraceLeft M).PosSemidef := by
  rw [partialTraceLeft_eq_sum]
  exact posSemidef_sum _ fun z _ => hM.submatrix (fun x => (z, x))

/-- Positive definiteness is preserved when the discarded right register is nonempty. -/
theorem PosDef.partialTraceRight [Nonempty Z] {M : Matrix (X × Z) (X × Z) R}
    (hM : M.PosDef) : (partialTraceRight M).PosDef := by
  rw [partialTraceRight_eq_sum]
  exact posDef_sum Finset.univ_nonempty fun z _ =>
    hM.submatrix (fun _ _ h => congrArg Prod.fst h)

/-- Positive definiteness is preserved when the discarded left register is nonempty. -/
theorem PosDef.partialTraceLeft [Nonempty Z] {M : Matrix (Z × X) (Z × X) R}
    (hM : M.PosDef) : (partialTraceLeft M).PosDef := by
  rw [partialTraceLeft_eq_sum]
  exact posDef_sum Finset.univ_nonempty fun z _ =>
    hM.submatrix (fun _ _ h => congrArg Prod.snd h)

end Matrix
