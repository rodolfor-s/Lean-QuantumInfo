import QCryptLean.Math.LinearAlgebra.Matrix.CStarAmplification
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Operators.Basic

/-!
# The Mathlib completely positive linear-map bridge

This file selects `MatrixOrder` and `Matrix.Norms.L2Operator` locally, providing
the C-star algebra and star order needed by `CompletelyPositiveMap`. Neither
scope exports instances to callers. The bridge is on complex linear maps; it
makes no claim for the older Choi predicate on arbitrary functions. Nested
C-star amplifications are related explicitly to product-indexed matrices.
-/

noncomputable section

namespace Quantum.Channels

open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- A CP linear map, bundled as a Mathlib completely positive map. -/
def IsCompletelyPositive.toMathlib {Φ : Operation X Y} (h : IsCompletelyPositive Φ) :
    CompletelyPositiveMap (Op X) (Op Y) where
  toLinearMap := Φ
  map_cstarMatrix_nonneg' k M hM := by
    have hp := (cstarFlatten_posSemidef_iff M).mpr hM
    have hq := (h.mapTensorId (Z := Fin k)).posSemidef
      (hp.submatrix (Prod.swap : X × Fin k → Fin k × X))
    apply (cstarFlatten_posSemidef_iff (M.map Φ)).mp
    exact hq.submatrix (Prod.swap : Fin k × Y → Y × Fin k)

/-- Forgetting the Mathlib CP proof gives precisely the original linear operation. -/
@[simp] theorem IsCompletelyPositive.toMathlib_toLinearMap {Φ : Operation X Y}
    (h : IsCompletelyPositive Φ) : h.toMathlib.toLinearMap = Φ := rfl

/-- A Mathlib completely positive linear map has positive Choi matrix. -/
theorem isCompletelyPositive_toLinearMap (Φ : CompletelyPositiveMap (Op X) (Op Y)) :
    IsCompletelyPositive Φ.toLinearMap := by
  apply isCompletelyPositive_of_mapTensorId_posSemidef
  intro A hA
  let M : CStarMatrix X X (Op X) := CStarMatrix.ofMatrix fun s t i j => A (i, s) (j, t)
  have hM : 0 ≤ M := (cstarFlatten_posSemidef_iff M).mp (hA.submatrix Prod.swap)
  have hp := (cstarFlatten_posSemidef_iff (M.map Φ)).mpr (Φ.map_cstarMatrix_nonneg M hM)
  exact hp.submatrix Prod.swap

/-- Honest equivalence with the Mathlib bundle, restricted to linear maps. -/
theorem isCompletelyPositive_iff_exists_mathlib (Φ : Operation X Y) :
    IsCompletelyPositive Φ ↔
      ∃ Ψ : CompletelyPositiveMap (Op X) (Op Y), Ψ.toLinearMap = Φ := by
  refine ⟨fun h => ⟨h.toMathlib, rfl⟩, ?_⟩
  rintro ⟨Ψ, rfl⟩
  exact isCompletelyPositive_toLinearMap Ψ

end Quantum.Channels
