import Mathlib.Algebra.Star.Pi
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.Tactic

/-! # Equality of rank-one projectors -/
namespace Matrix

/-- Vectors defining the same outer-product projector differ by a scalar.
No finiteness or normalization of the vectors is required. -/
theorem exists_smul_eq_of_vecMulVec_star_eq {X R : Type*} [Field R] [StarRing R] {v w : X → R}
    (h : vecMulVec v (star v) = vecMulVec w (star w)) :
    ∃ a : R, v = a • w := by
  classical
  by_cases hv : v = 0
  · exact ⟨0, by simp [hv]⟩
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hv (funext hn)
  have hs : star (v j) ≠ 0 := star_ne_zero.mpr hj
  refine ⟨star (w j) / star (v j), ?_⟩
  funext i
  have he := congrFun (congrFun h i) j
  change v i * star (v j) = w i * star (w j) at he
  change v i = (star (w j) / star (v j)) * w i
  apply (mul_right_cancel₀ hs)
  rw [he]
  field_simp

end Matrix
