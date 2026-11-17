import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! # The projective angle triangle inequality in a complex inner product space -/

namespace InnerProductSpace
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The projective angle satisfies the triangle inequality on unit vectors. -/
theorem arccos_norm_inner_le (x y z : E) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hz : ‖z‖ = 1) :
    Real.arccos ‖inner ℂ x z‖ ≤ Real.arccos ‖inner ℂ x y‖ + Real.arccos ‖inner ℂ y z‖ := by
  let a := ‖inner ℂ x y‖
  let b := ‖inner ℂ y z‖
  let c := ‖inner ℂ x z‖
  have ha : a ≤ 1 := by simpa [a, hx, hy] using norm_inner_le_norm (𝕜 := ℂ) x y
  have hb : b ≤ 1 := by simpa [b, hy, hz] using norm_inner_le_norm (𝕜 := ℂ) y z
  have hyy : inner ℂ y y = 1 := inner_self_eq_one_of_norm_eq_one hy
  have hperp (u : E) (hu : ‖u‖ = 1) :
      ‖u - (inner ℂ y u) • y‖ = Real.sqrt (1 - ‖inner ℂ y u‖ ^ 2) := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ)]
    congr 1
    have he : inner ℂ (u - inner ℂ y u • y) (u - inner ℂ y u • y) =
        1 - (inner ℂ y u) * star (inner ℂ y u) := by
      simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        inner_self_eq_one_of_norm_eq_one hu, hyy]
      rw [show inner ℂ u y = star (inner ℂ y u) from (inner_conj_symm u y).symm]
      ring
    rw [he]
    change (1 - (inner ℂ y u) * star (inner ℂ y u)).re = _
    rw [Complex.sub_re, Complex.one_re, Complex.star_def, Complex.mul_conj,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have halg : a * b - Real.sqrt (1 - a ^ 2) * Real.sqrt (1 - b ^ 2) ≤ c := by
    let u := x - inner ℂ y x • y
    let v := z - inner ℂ y z • y
    have he : star (inner ℂ y x) * inner ℂ y z = inner ℂ x z - inner ℂ u v := by
      dsimp only [u, v]
      simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
        hyy]
      rw [show inner ℂ x y = star (inner ℂ y x) from (inner_conj_symm x y).symm]
      ring
    have hab : ‖star (inner ℂ y x) * inner ℂ y z‖ = a * b := by
      rw [norm_mul, norm_star, norm_inner_symm]
    have htri := norm_sub_le (inner ℂ x z) (inner ℂ u v)
    rw [← he, hab] at htri
    have hcs := norm_inner_le_norm (𝕜 := ℂ) u v
    have hu : ‖u‖ = Real.sqrt (1 - a ^ 2) := by
      rw [hperp x hx, norm_inner_symm]
    have hv : ‖v‖ = Real.sqrt (1 - b ^ 2) := hperp z hz
    rw [hu, hv] at hcs
    linarith
  change Real.arccos c ≤ Real.arccos a + Real.arccos b
  by_cases hs : Real.pi / 2 ≤ Real.arccos a + Real.arccos b
  · exact ((Real.arccos_le_pi_div_two).mpr (norm_nonneg _)).trans hs
  · have hn : 0 ≤ Real.arccos a + Real.arccos b :=
      add_nonneg (Real.arccos_nonneg _) (Real.arccos_nonneg _)
    have hp : Real.arccos a + Real.arccos b ≤ Real.pi := by
      linarith [Real.pi_nonneg]
    have he : Real.cos (Real.arccos a + Real.arccos b) =
        a * b - Real.sqrt (1 - a ^ 2) * Real.sqrt (1 - b ^ 2) := by
      rw [Real.cos_add, Real.cos_arccos (le_trans (by norm_num) (norm_nonneg _)) ha,
        Real.cos_arccos (le_trans (by norm_num) (norm_nonneg _)) hb,
        Real.sin_arccos, Real.sin_arccos]
    have h := Real.arccos_le_arccos (he.trans_le halg)
    rwa [Real.arccos_cos hn hp] at h

end InnerProductSpace
