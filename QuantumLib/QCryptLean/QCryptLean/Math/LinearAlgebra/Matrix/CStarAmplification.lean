import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order

/-!
# Flattening nested C-star matrices

This module explicitly selects matrix star order (`MatrixOrder`) and the L2
operator norm (`Matrix.Norms.L2Operator`). Both scopes are local to this file;
no instance replaces the Frobenius norm in importing modules. The flattening
map is algebraic, and the positivity equivalence follows from its star algebra
structure, including for empty finite types.
-/

namespace Matrix

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {X Z : Type*} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq Z]

/-- Flatten a C-star matrix of complex matrices, in outer-then-inner index order. -/
def cstarFlatten : CStarMatrix Z Z (Matrix X X ℂ) ≃⋆ₐ[ℂ] Matrix (Z × X) (Z × X) ℂ :=
  { CStarMatrix.ofMatrixStarAlgEquiv.symm.toAlgEquiv.trans (compAlgEquiv Z X ℂ ℂ) with
    map_smul' _ _ := rfl
    map_star' _ := rfl }

/-- Flattening reads the corresponding nested entry. -/
theorem cstarFlatten_apply (A : CStarMatrix Z Z (Matrix X X ℂ)) (p q : Z × X) :
    cstarFlatten A p q = A p.1 q.1 p.2 q.2 := rfl

/-- The nested C-star order is exactly PSD after flattening. -/
theorem cstarFlatten_posSemidef_iff (A : CStarMatrix Z Z (Matrix X X ℂ)) :
    (cstarFlatten A).PosSemidef ↔ 0 ≤ A := by
  rw [← nonneg_iff_posSemidef]
  constructor
  · intro h
    simpa using map_nonneg cstarFlatten.symm h
  · exact map_nonneg cstarFlatten

end Matrix
