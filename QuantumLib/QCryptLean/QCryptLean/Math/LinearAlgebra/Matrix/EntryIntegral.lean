import Mathlib.Analysis.Matrix.Order
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Entry Integral -/


namespace Matrix

open MeasureTheory
open scoped ComplexOrder

variable {Ω X : Type*} [MeasurableSpace Ω] [Fintype X] {μ : Measure Ω}
  {A : Ω → Matrix X X ℂ}

omit [Fintype X] in
/-- Entrywise integration preserves Hermiticity. -/
theorem isHermitian_entryIntegral (hA : ∀ ω, (A ω).IsHermitian) :
    (of fun i j => ∫ ω, A ω i j ∂μ).IsHermitian := by
  ext i j
  change starRingEnd ℂ (∫ ω, A ω j i ∂μ) = ∫ ω, A ω i j ∂μ
  rw [← integral_conj]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (hA ω).apply i j)

/-- Entrywise integration commutes with a fixed quadratic form. -/
theorem dotProduct_mulVec_entryIntegral
    (hint : ∀ i j, Integrable (fun ω => A ω i j) μ) (v : X → ℂ) :
    star v ⬝ᵥ (of fun i j => ∫ ω, A ω i j ∂μ) *ᵥ v =
      ∫ ω, star v ⬝ᵥ A ω *ᵥ v ∂μ := by
  have hmv (i : X) : Integrable (fun ω => (A ω *ᵥ v) i) μ :=
    integrable_finsetSum _ fun j _ => (hint i j).mul_const (v j)
  have he : (of fun i j => ∫ ω, A ω i j ∂μ) *ᵥ v =
      fun i => ∫ ω, (A ω *ᵥ v) i ∂μ := by
    ext i
    simp only [mulVec, dotProduct, of_apply]
    simp_rw [← integral_mul_const]
    exact (integral_finsetSum _ fun j _ => (hint i j).mul_const (v j)).symm
  rw [he]
  simp only [dotProduct]
  simp_rw [← integral_const_mul]
  exact (integral_finsetSum _ fun i _ => (hmv i).const_mul (star v i)).symm

omit [Fintype X] in
/-- Entrywise integration preserves positive semidefiniteness. -/
theorem posSemidef_entryIntegral [Finite X] (hA : ∀ ω, (A ω).PosSemidef)
    (hint : ∀ i j, Integrable (fun ω => A ω i j) μ) :
    (of fun i j => ∫ ω, A ω i j ∂μ).PosSemidef := by
  let := Fintype.ofFinite X
  have hh := isHermitian_entryIntegral (fun ω => (hA ω).isHermitian) (μ := μ)
  apply PosSemidef.of_dotProduct_mulVec_nonneg hh
  intro v
  apply Complex.nonneg_iff.mpr
  constructor
  · rw [dotProduct_mulVec_entryIntegral hint]
    have hi : Integrable (fun ω => star v ⬝ᵥ A ω *ᵥ v) μ :=
      integrable_finsetSum _ fun i _ =>
        (integrable_finsetSum _ fun j _ => (hint i j).mul_const (v j)).const_mul (star v i)
    change 0 ≤ RCLike.re (∫ ω, star v ⬝ᵥ A ω *ᵥ v ∂μ)
    rw [← integral_re hi]
    exact integral_nonneg fun ω => (Complex.nonneg_iff.mp ((hA ω).dotProduct_mulVec_nonneg v)).1
  · have hs := congrArg Complex.im (hh.star_dotProduct_mulVec_comm v v)
    change -(star v ⬝ᵥ _ *ᵥ v).im = (star v ⬝ᵥ _ *ᵥ v).im at hs
    linarith

/-- Trace commutes with entrywise integration when the diagonal entries are integrable. -/
theorem trace_entryIntegral (hint : ∀ i, Integrable (fun ω => A ω i i) μ) :
    (of fun i j => ∫ ω, A ω i j ∂μ).trace = ∫ ω, (A ω).trace ∂μ :=
  (integral_finsetSum _ fun i _ => hint i).symm

/-- A fixed rectangular left factor commutes with entrywise matrix integration. -/
theorem mul_entryIntegral {Y : Type*} (C : Matrix Y X ℂ)
    (hint : ∀ i j, Integrable (fun ω => A ω i j) μ) :
    C * (of fun i j => ∫ ω, A ω i j ∂μ) = of fun i j => ∫ ω, (C * A ω) i j ∂μ := by
  ext i j
  simp only [mul_apply, of_apply]
  simp_rw [← integral_const_mul]
  exact (integral_finsetSum _ fun x _ => (hint x j).const_mul (C i x)).symm

/-- A fixed rectangular right factor commutes with entrywise matrix integration. -/
theorem entryIntegral_mul {Y : Type*} (C : Matrix X Y ℂ)
    (hint : ∀ i j, Integrable (fun ω => A ω i j) μ) :
    (of fun i j => ∫ ω, A ω i j ∂μ) * C = of fun i j => ∫ ω, (A ω * C) i j ∂μ := by
  ext i j
  simp only [mul_apply, of_apply]
  simp_rw [← integral_mul_const]
  exact (integral_finsetSum _ fun x _ => (hint i x).mul_const (C x j)).symm

/-- Entrywise integration commutes with a fixed rectangular sandwich. -/
theorem sandwich_entryIntegral {Y : Type*} (C : Matrix Y X ℂ)
    (hint : ∀ i j, Integrable (fun ω => A ω i j) μ) :
    C * (of fun i j => ∫ ω, A ω i j ∂μ) * Cᴴ =
      of fun i j => ∫ ω, (C * A ω * Cᴴ) i j ∂μ := by
  rw [mul_entryIntegral C hint]
  ext i j
  simp only [mul_apply, of_apply]
  simp_rw [← integral_mul_const]
  exact (integral_finsetSum _ fun x _ =>
    (integrable_finsetSum _ fun y _ => (hint y x).const_mul (C i y)).mul_const (Cᴴ x j)).symm


omit [Fintype X] in
/-- A complex-linear map of finite rectangular matrices commutes with entrywise integration. -/
theorem linearMap_entryIntegral {I J K L : Type*} [Finite I] [Finite J]
    (T : Matrix I J ℂ →ₗ[ℂ] Matrix K L ℂ) (F : Ω → Matrix I J ℂ)
    (hF : ∀ i j, Integrable (fun ω => F ω i j) μ) :
    T (Matrix.of fun i j => ∫ ω, F ω i j ∂μ) =
      Matrix.of (fun k l => ∫ ω, T (F ω) k l ∂μ) := by
  classical
  let := Fintype.ofFinite I
  let := Fintype.ofFinite J
  have he (B : Matrix I J ℂ) :
      T B = ∑ i, ∑ j, B i j • T (Matrix.single i j 1) := by
    have hB : B = ∑ i, ∑ j, B i j • Matrix.single i j 1 := by
      simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using Matrix.matrix_eq_sum_single B
    conv_lhs => rw [hB]
    simp only [map_sum, map_smul]
  ext k l
  rw [he]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
  simp_rw [← integral_mul_const]
  calc
    _ = ∑ i, ∫ ω, ∑ j, F ω i j * T (Matrix.single i j 1) k l ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum _ (fun j _ => (hF i j).mul_const _)).symm
    _ = ∫ ω, ∑ i, ∑ j, F ω i j * T (Matrix.single i j 1) k l ∂μ :=
      (integral_finsetSum _ (fun i _ => integrable_finsetSum _
        fun j _ => (hF i j).mul_const _)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [he]
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

end Matrix
