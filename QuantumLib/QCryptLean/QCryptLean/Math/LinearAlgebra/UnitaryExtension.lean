import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Unitary Extension — Gram-matrix isometries, left- and right-unitary completion

This file records low-level finite-dimensional linear algebra statements used
to extend partial isometries to full unitary matrices.

## Main statements
- `exists_range_isometry_of_forall_norm_eq`: norm agreement induces an isometry
  between linear-map ranges
- `exists_unitary_left_mul_of_conjTranspose_mul_self_eq`: equal square column Gram
  matrices differ by left multiplication by a unitary matrix
- `exists_unitary_left_mul_of_rect_conjTranspose_mul_self_eq`: equal rectangular column
  Gram matrices differ by left multiplication by a unitary on the row space
- `exists_unitary_right_mul_of_row_gram_eq_full_col_rank`: two rectangular
  matrices with equal row Grams `A · Aᴴ = B · Bᴴ` and `A` of full column
  rank are related by right multiplication by a unitary matrix
- `exists_left_factor_contraction_of_sq_eq_selfAdjoint`: a Douglas-style
  contraction factorization from `P * P = M * Mᴴ`
- `Math.LinearAlgebra.UnitaryExtension.exists_rectangular_polar_contraction`: rectangular polar
decomposition in
  contraction form, `M = √(M Mᴴ) · W` with `‖W‖ ≤ 1`
- `l2_opNorm_mul_conjTranspose_le_one`: the product of two rectangular
  contractions, with the second adjointed, is a contraction
-/

open Matrix
open scoped Matrix ComplexConjugate ComplexOrder MatrixOrder
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace Math.LinearAlgebra.UnitaryExtension

/-- The inner product of two images of a matrix is the Gram-matrix pairing
`⟪A x, A y⟫ = ⟪x, (Aᴴ A) y⟫`. -/
lemma inner_toEuclideanLin_toEuclideanLin {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (x y : EuclideanSpace ℂ n) :
    inner ℂ (Matrix.toEuclideanLin A x) (Matrix.toEuclideanLin A y) =
      inner ℂ x (Matrix.toEuclideanLin (A.conjTranspose * A) y) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  -- `(A y) ⬝ conj (A x) = (Aᴴ A y) ⬝ conj x`.
  rw [star_mulVec, dotProduct_comm, ← dotProduct_mulVec, mulVec_mulVec]
  exact dotProduct_comm _ _

/-- Rectangular Gram equality gives equality of pulled-back inner products, even
when the two maps have different codomains. -/
lemma inner_toEuclideanLin_eq_of_adjoint_mul_eq
    {m p n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin p) (Fin n) ℂ)
    (hgram : A.conjTranspose * A = B.conjTranspose * B)
    (x y : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (Matrix.toEuclideanLin A x) (Matrix.toEuclideanLin A y) =
      inner ℂ (Matrix.toEuclideanLin B x) (Matrix.toEuclideanLin B y) := by
  rw [inner_toEuclideanLin_toEuclideanLin, hgram, ← inner_toEuclideanLin_toEuclideanLin]

/-- Square Gram equality gives equality of pulled-back inner products. -/
lemma matrix_toEuclideanLin_inner_eq_of_conjTranspose_mul_self_eq
    {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ)
    (hgram : A.conjTranspose * A = B.conjTranspose * B)
    (x y : EuclideanSpace ℂ (Fin d)) :
    inner ℂ (Matrix.toEuclideanLin A x) (Matrix.toEuclideanLin A y) =
      inner ℂ (Matrix.toEuclideanLin B x) (Matrix.toEuclideanLin B y) := by
  exact inner_toEuclideanLin_eq_of_adjoint_mul_eq
    A B hgram x y

/-- Rectangular Gram equality gives equality of pulled-back inner products. -/
lemma inner_toEuclideanLin_eq_of_adjoint_mul_eq_same_codomain
    {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ)
    (hgram : A.conjTranspose * A = B.conjTranspose * B)
    (x y : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (Matrix.toEuclideanLin A x) (Matrix.toEuclideanLin A y) =
      inner ℂ (Matrix.toEuclideanLin B x) (Matrix.toEuclideanLin B y) := by
  exact inner_toEuclideanLin_eq_of_adjoint_mul_eq
    A B hgram x y

/-- Rectangular Gram equality gives equality of Euclidean norms of matrix images,
even when the two maps have different codomains. -/
lemma norm_toEuclideanLin_eq_of_adjoint_mul_eq
    {m p n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (B : Matrix (Fin p) (Fin n) ℂ)
    (hgram : A.conjTranspose * A = B.conjTranspose * B)
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanLin B x‖ = ‖Matrix.toEuclideanLin A x‖ := by
  have hinner :=
    inner_toEuclideanLin_eq_of_adjoint_mul_eq
      A B hgram x x
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), hinner]

/-- Norm agreement induces an isometry from the range of `TA` to the codomain of
`TB`, allowing `TA` and `TB` to have different codomains. -/
lemma exists_range_isometry_of_forall_norm_eq_of_domain_codomain
    {D E F : Type*} [AddCommGroup D] [Module ℂ D]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (TA : D →ₗ[ℂ] E) (TB : D →ₗ[ℂ] F)
    (hnorm : ∀ x : D, ‖TB x‖ = ‖TA x‖) :
    ∃ L : LinearMap.range TA →ₗᵢ[ℂ] F,
      ∀ x : D, L ⟨TA x, LinearMap.mem_range_self TA x⟩ = TB x := by
  have hker : LinearMap.ker TA = LinearMap.ker TB := by
    ext x
    simp only [LinearMap.mem_ker]
    constructor
    · intro hx
      have hx0 : ‖TB x‖ = 0 := by
        simpa [hx] using hnorm x
      exact norm_eq_zero.mp hx0
    · intro hx
      have hx0 : ‖TA x‖ = 0 := by
        simpa [hx] using (hnorm x).symm
      exact norm_eq_zero.mp hx0
  let eRange : LinearMap.range TA ≃ₗ[ℂ] LinearMap.range TB :=
    (TA.quotKerEquivRange.symm).trans
      ((Submodule.quotEquivOfEq (LinearMap.ker TA) (LinearMap.ker TB) hker).trans
        TB.quotKerEquivRange)
  let Llin : LinearMap.range TA →ₗ[ℂ] F :=
    (LinearMap.range TB).subtype.comp eRange.toLinearMap
  have hL_apply : ∀ x : D, Llin ⟨TA x, LinearMap.mem_range_self TA x⟩ = TB x := by
    intro x
    change ((eRange ⟨TA x, LinearMap.mem_range_self TA x⟩ : LinearMap.range TB) : F) =
      TB x
    simp [eRange]
  have hL_norm : ∀ s : LinearMap.range TA, ‖Llin s‖ = ‖s‖ := by
    intro s
    obtain ⟨x, hx⟩ := s.property
    have hs : s = ⟨TA x, LinearMap.mem_range_self TA x⟩ := Subtype.ext hx.symm
    rw [hs, hL_apply x]
    simpa using hnorm x
  refine ⟨⟨Llin, hL_norm⟩, ?_⟩
  intro x
  exact hL_apply x

/-- Norm agreement induces an isometry from the range of `TA` to the common codomain. -/
lemma exists_range_isometry_of_forall_norm_eq_of_domain
    {D E : Type*} [AddCommGroup D] [Module ℂ D]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (TA TB : D →ₗ[ℂ] E)
    (hnorm : ∀ x : D, ‖TB x‖ = ‖TA x‖) :
    ∃ L : LinearMap.range TA →ₗᵢ[ℂ] E,
      ∀ x : D, L ⟨TA x, LinearMap.mem_range_self TA x⟩ = TB x := by
  exact exists_range_isometry_of_forall_norm_eq_of_domain_codomain TA TB hnorm

/-- Norm agreement for endomorphisms induces an isometry from the range of `TA`. -/
lemma exists_range_isometry_of_forall_norm_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (TA TB : E →ₗ[ℂ] E)
    (hnorm : ∀ x : E, ‖TB x‖ = ‖TA x‖) :
    ∃ L : LinearMap.range TA →ₗᵢ[ℂ] E,
      ∀ x : E, L ⟨TA x, LinearMap.mem_range_self TA x⟩ = TB x := by
  exact exists_range_isometry_of_forall_norm_eq_of_domain_codomain TA TB hnorm

/-- A matrix whose Euclidean linear map is a linear isometry equivalence is unitary. -/
lemma matrix_unitary_of_toEuclideanLin_eq_linearIsometryEquiv
    {d : ℕ} (U : Matrix (Fin d) (Fin d) ℂ)
    (e : EuclideanSpace ℂ (Fin d) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin d))
    (hU : Matrix.toEuclideanLin U = e.toLinearMap) :
    U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 := by
  constructor
  · apply
      (Matrix.toEuclideanLin :
        Matrix (Fin d) (Fin d) ℂ ≃ₗ[ℂ]
          EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)).injective
    rw [Matrix.toLpLin_mul_same]
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint U, hU]
    rw [LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]
    simp
  · apply
      (Matrix.toEuclideanLin :
        Matrix (Fin d) (Fin d) ℂ ≃ₗ[ℂ]
          EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)).injective
    rw [Matrix.toLpLin_mul_same]
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint U, hU]
    rw [LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]
    simp

/-- Equal rectangular column Gram matrices differ by left multiplication by a
square unitary on the common row space. -/
lemma exists_unitary_left_mul_of_rect_conjTranspose_mul_self_eq
    {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ)
    (hgram : A.conjTranspose * A = B.conjTranspose * B) :
    ∃ U : Matrix (Fin m) (Fin m) ℂ,
      U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 ∧ U * A = B := by
  let TA : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    Matrix.toEuclideanLin A
  let TB : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    Matrix.toEuclideanLin B
  have hnorm : ∀ x : EuclideanSpace ℂ (Fin n), ‖TB x‖ = ‖TA x‖ := by
    intro x
    change ‖Matrix.toEuclideanLin B x‖ = ‖Matrix.toEuclideanLin A x‖
    exact norm_toEuclideanLin_eq_of_adjoint_mul_eq
      A B hgram x
  obtain ⟨L, hL⟩ := exists_range_isometry_of_forall_norm_eq_of_domain TA TB hnorm
  let Lext : EuclideanSpace ℂ (Fin m) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m) :=
    LinearIsometry.extend L
  let e : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m) :=
    Lext.toLinearIsometryEquiv rfl
  let U : Matrix (Fin m) (Fin m) ℂ :=
    (Matrix.toEuclideanLin :
      Matrix (Fin m) (Fin m) ℂ ≃ₗ[ℂ]
        EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)).symm e.toLinearMap
  have hUlin : Matrix.toEuclideanLin U = e.toLinearMap := by
    simp [U]
  obtain ⟨hleft, hright⟩ :=
    matrix_unitary_of_toEuclideanLin_eq_linearIsometryEquiv U e hUlin
  have hExt_apply : ∀ x : EuclideanSpace ℂ (Fin n), e.toLinearMap (TA x) = TB x := by
    intro x
    change e (TA x) = TB x
    rw [LinearIsometry.toLinearIsometryEquiv_apply]
    change Lext (TA x) = TB x
    rw [show (TA x) = (⟨TA x, LinearMap.mem_range_self TA x⟩ : LinearMap.range TA) by
      rfl]
    rw [LinearIsometry.extend_apply]
    exact hL x
  have hmul : U * A = B := by
    apply
      (Matrix.toEuclideanLin :
        Matrix (Fin m) (Fin n) ℂ ≃ₗ[ℂ]
          EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m)).injective
    rw [Matrix.toLpLin_mul_same]
    rw [hUlin]
    exact LinearMap.ext hExt_apply
  exact ⟨U, hleft, hright, hmul⟩

/-- Equal column Gram matrices differ by a left unitary.

Mathematically, the columns of `A` and `B` define two finite families with the
same Gram matrix. The linear map sending each `A`-column to the corresponding
`B`-column is therefore a well-defined isometry on the span of the columns of
`A`; finite-dimensional orthonormal-basis extension then extends it to a full
unitary matrix. -/
lemma exists_unitary_left_mul_of_conjTranspose_mul_self_eq
    {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℂ)
    (hgram : A.conjTranspose * A = B.conjTranspose * B) :
    ∃ U : Matrix (Fin d) (Fin d) ℂ,
      U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 ∧ U * A = B := by
  exact exists_unitary_left_mul_of_rect_conjTranspose_mul_self_eq A B hgram

/-! ### Rectangular Gram-unitary extension

The following block collects pure linear-algebra helpers used to upgrade an
equality of row Gram matrices `A · Aᴴ = B · Bᴴ` (with `A` of full column rank)
to the existence of a unitary `W` such that `B = A · W`. This is the
rectangular analog of `exists_unitary_left_mul_of_conjTranspose_mul_self_eq`
and is used, for example, in the proof of minimal Stinespring uniqueness.
-/

/-- A matrix with full column rank has injective `mulVec`. -/
private lemma mulVec_injective_of_rank_eq
    {N r : ℕ} {M : Matrix (Fin N) (Fin r) ℂ} (hrank : Matrix.rank M = r) :
    Function.Injective M.mulVec := by
  have hpi : Module.finrank ℂ (Fin r → ℂ) = r := by
    rw [Module.finrank_pi, Fintype.card_fin]
  have hsum := M.mulVecLin.finrank_range_add_finrank_ker
  rw [hpi] at hsum
  have hrange : Module.finrank ℂ (LinearMap.range M.mulVecLin) = r := hrank
  have hker0 : Module.finrank ℂ (LinearMap.ker M.mulVecLin) = 0 := by omega
  have hker_bot : LinearMap.ker M.mulVecLin = ⊥ :=
    Submodule.finrank_eq_zero.mp hker0
  have hinj : Function.Injective M.mulVecLin := LinearMap.ker_eq_bot.mp hker_bot
  intro u v huv
  exact hinj (by simpa [Matrix.mulVecLin_apply] using huv)

/-- If `M` has full column rank, then `Mᴴ * M` is invertible. -/
private lemma isUnit_conjTranspose_mul_self_of_rank_eq
    {N r : ℕ} {M : Matrix (Fin N) (Fin r) ℂ}
    (hrank : Matrix.rank M = r) :
    IsUnit (Mᴴ * M) := by
  classical
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro u v huv
  apply mulVec_injective_of_rank_eq hrank
  have hsub : (Mᴴ * M) *ᵥ (u - v) = 0 := by
    rw [Matrix.mulVec_sub, huv, sub_self]
  have hMsub : M *ᵥ (u - v) = 0 :=
    (Matrix.conjTranspose_mul_self_mulVec_eq_zero M (u - v)).mp hsub
  have hdiff : M *ᵥ u - M *ᵥ v = 0 := by rw [← Matrix.mulVec_sub]; exact hMsub
  exact sub_eq_zero.mp hdiff

/-- The orthogonal projector `A * (Aᴴ * A)⁻¹ * Aᴴ` onto the column space of `A` fixes
`A`, provided `Aᴴ * A` is invertible. -/
private lemma mul_pseudoinv_mul_self
    {N r : ℕ} (A : Matrix (Fin N) (Fin r) ℂ)
    (hinv_cancel_l : (Aᴴ * A)⁻¹ * (Aᴴ * A) = 1) :
    A * ((Aᴴ * A)⁻¹ * Aᴴ) * A = A := by
  have heq : A * ((Aᴴ * A)⁻¹ * Aᴴ) * A = A * ((Aᴴ * A)⁻¹ * (Aᴴ * A)) := by
    rw [Matrix.mul_assoc A ((Aᴴ * A)⁻¹ * Aᴴ) A, Matrix.mul_assoc (Aᴴ * A)⁻¹ Aᴴ A]
  rw [heq, hinv_cancel_l, Matrix.mul_one]

/-- If two `N × r` matrices have the same row Gram `A · Aᴴ = B · Bᴴ` and `A` has full
column rank `r`, then so does `B`. -/
private lemma rank_eq_of_row_gram_eq_full_col_rank
    {N r : ℕ} {A B : Matrix (Fin N) (Fin r) ℂ}
    (hgram : A * Aᴴ = B * Bᴴ) (hrank : Matrix.rank A = r) :
    Matrix.rank B = r := by
  have h1 : (A * Aᴴ).rank = r := by
    rw [Matrix.rank_self_mul_conjTranspose, hrank]
  have h2 : (B * Bᴴ).rank = r := by rw [← hgram]; exact h1
  have h3 : (B * Bᴴ).rank = B.rank := Matrix.rank_self_mul_conjTranspose B
  have hub : B.rank ≤ r := by
    have := Matrix.rank_le_card_width B
    simpa [Fintype.card_fin] using this
  omega

/-- Equal row Gram matrices remain equal after sandwiching by `Aᴴ` and `A`. -/
lemma conjTranspose_mul_mul_conjTranspose_mul_of_row_gram_eq
    {N r : ℕ} {A B : Matrix (Fin N) (Fin r) ℂ}
    (hgram : A * Aᴴ = B * Bᴴ) :
    (Aᴴ * B) * (Bᴴ * A) = (Aᴴ * A) * (Aᴴ * A) := by
  calc (Aᴴ * B) * (Bᴴ * A)
      = Aᴴ * (B * Bᴴ) * A := by
        rw [Matrix.mul_assoc Aᴴ B (Bᴴ * A), ← Matrix.mul_assoc B Bᴴ A,
          ← Matrix.mul_assoc Aᴴ (B * Bᴴ) A]
    _ = Aᴴ * (A * Aᴴ) * A := by rw [← hgram]
    _ = (Aᴴ * A) * (Aᴴ * A) := by
        rw [← Matrix.mul_assoc Aᴴ A Aᴴ, Matrix.mul_assoc (Aᴴ * A) Aᴴ A]

/-- If `A Aᴴ = B Bᴴ` and `B` has full column rank, every square matrix fixing
`A` also fixes `B`. -/
lemma mul_eq_self_of_row_gram_eq_of_rank_eq
    {N r : ℕ} {P : Matrix (Fin N) (Fin N) ℂ} {A B : Matrix (Fin N) (Fin r) ℂ}
    (hgram : A * Aᴴ = B * Bᴴ) (hrankB : Matrix.rank B = r)
    (hPA : P * A = A) :
    P * B = B := by
  have hB_inj : Function.Injective B.mulVec := mulVec_injective_of_rank_eq hrankB
  have hP_AAH : P * (A * Aᴴ) = A * Aᴴ := by
    rw [← Matrix.mul_assoc, hPA]
  have hP_BBH : P * (B * Bᴴ) = B * Bᴴ := by
    rw [← hgram]; exact hP_AAH
  have hM_Bh : (P * B - B) * Bᴴ = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, hP_BBH, sub_self]
  have hB_Mh : B * (P * B - B)ᴴ = 0 := by
    have := congrArg Matrix.conjTranspose hM_Bh
    simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_zero] using this
  have hMh_zero : (P * B - B)ᴴ = 0 := by
    ext k j
    have hcol : B *ᵥ (fun k => (P * B - B)ᴴ k j) = 0 := by
      funext n
      have hentry := congrFun (congrFun hB_Mh n) j
      simp only [Matrix.mul_apply, Matrix.zero_apply] at hentry
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      exact hentry
    have hzero : (fun k => (P * B - B)ᴴ k j) = 0 := by
      apply hB_inj
      rw [hcol, Matrix.mulVec_zero]
    exact congrFun hzero k
  have hM_eq : P * B - B = 0 := by
    have := congrArg Matrix.conjTranspose hMh_zero
    simpa [Matrix.conjTranspose_zero, Matrix.conjTranspose_conjTranspose] using this
  exact sub_eq_zero.mp hM_eq

/-- Rectangular Gram-unitary extension.

Given `A B : Matrix (Fin N) (Fin r) ℂ` with `A · Aᴴ = B · Bᴴ` and `A` of full column
rank `r`, there exists a unitary `W : Matrix (Fin r) (Fin r) ℂ` with `B = A · W`. -/
lemma exists_unitary_right_mul_of_row_gram_eq_full_col_rank
    {N r : ℕ}
    (A B : Matrix (Fin N) (Fin r) ℂ)
    (hgram : A * Aᴴ = B * Bᴴ)
    (hrank : Matrix.rank A = r) :
    ∃ W : Matrix (Fin r) (Fin r) ℂ,
      Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ B = A * W := by
  classical
  have hrankB : Matrix.rank B = r := rank_eq_of_row_gram_eq_full_col_rank hgram hrank
  have hAA_unit : IsUnit (Aᴴ * A) := isUnit_conjTranspose_mul_self_of_rank_eq hrank
  have hAA_det : IsUnit (Aᴴ * A).det := (Matrix.isUnit_iff_isUnit_det _).mp hAA_unit
  have hinv_cancel_l : (Aᴴ * A)⁻¹ * (Aᴴ * A) = 1 :=
    Matrix.nonsing_inv_mul _ hAA_det
  have hinv_cancel_r : (Aᴴ * A) * (Aᴴ * A)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hAA_det
  set W : Matrix (Fin r) (Fin r) ℂ := (Aᴴ * A)⁻¹ * (Aᴴ * B) with hW_def
  have hAA_herm : (Aᴴ * A)ᴴ = Aᴴ * A := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hinv_herm : ((Aᴴ * A)⁻¹)ᴴ = (Aᴴ * A)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hAA_herm]
  have hPA : A * ((Aᴴ * A)⁻¹ * Aᴴ) * A = A := mul_pseudoinv_mul_self A hinv_cancel_l
  have hPB : A * ((Aᴴ * A)⁻¹ * Aᴴ) * B = B :=
    mul_eq_self_of_row_gram_eq_of_rank_eq hgram hrankB hPA
  have hB_eq : B = A * W := by
    rw [hW_def]
    calc B = A * ((Aᴴ * A)⁻¹ * Aᴴ) * B := hPB.symm
      _ = A * ((Aᴴ * A)⁻¹ * (Aᴴ * B)) := by
          rw [Matrix.mul_assoc A ((Aᴴ * A)⁻¹ * Aᴴ) B,
              Matrix.mul_assoc (Aᴴ * A)⁻¹ Aᴴ B]
  have hWh_eq : Wᴴ = Bᴴ * A * (Aᴴ * A)⁻¹ := by
    rw [hW_def, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hinv_herm,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hWWh : W * Wᴴ = 1 := by
    rw [hW_def, hWh_eq]
    calc (Aᴴ * A)⁻¹ * (Aᴴ * B) * (Bᴴ * A * (Aᴴ * A)⁻¹)
        = (Aᴴ * A)⁻¹ * ((Aᴴ * B) * (Bᴴ * A)) * (Aᴴ * A)⁻¹ := by
          rw [Matrix.mul_assoc (Aᴴ * A)⁻¹ (Aᴴ * B) (Bᴴ * A * (Aᴴ * A)⁻¹),
              ← Matrix.mul_assoc (Aᴴ * B) (Bᴴ * A) (Aᴴ * A)⁻¹,
              ← Matrix.mul_assoc (Aᴴ * A)⁻¹ ((Aᴴ * B) * (Bᴴ * A)) (Aᴴ * A)⁻¹]
      _ = (Aᴴ * A)⁻¹ * ((Aᴴ * A) * (Aᴴ * A)) * (Aᴴ * A)⁻¹ := by
          rw [conjTranspose_mul_mul_conjTranspose_mul_of_row_gram_eq hgram]
      _ = ((Aᴴ * A)⁻¹ * (Aᴴ * A)) * ((Aᴴ * A) * (Aᴴ * A)⁻¹) := by
          rw [Matrix.mul_assoc (Aᴴ * A)⁻¹ ((Aᴴ * A) * (Aᴴ * A)) (Aᴴ * A)⁻¹,
              Matrix.mul_assoc (Aᴴ * A) (Aᴴ * A) (Aᴴ * A)⁻¹,
              ← Matrix.mul_assoc (Aᴴ * A)⁻¹ (Aᴴ * A) ((Aᴴ * A) * (Aᴴ * A)⁻¹)]
      _ = 1 * 1 := by rw [hinv_cancel_l, hinv_cancel_r]
      _ = 1 := one_mul _
  have hWhW : Wᴴ * W = 1 := mul_eq_one_comm.mp hWWh
  exact ⟨W, hWhW, hWWh, hB_eq⟩

/-- Douglas-style contraction factor for finite matrices.

If a Hermitian square matrix `P` satisfies `P * P = M * Mᴴ`, then `M` factors
through `P` by a contraction. -/
lemma exists_left_factor_contraction_of_sq_eq_selfAdjoint
    {d a : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) (M : Matrix (Fin d) (Fin a) ℂ)
    (hP_herm : P.conjTranspose = P)
    (hP_sq : P * P = M * M.conjTranspose) :
    ∃ W : Matrix (Fin d) (Fin a) ℂ,
      M = P * W ∧ ‖W‖ ≤ 1 := by
  let TP : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d) :=
    Matrix.toEuclideanLin P
  let TMh : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin a) :=
    Matrix.toEuclideanLin M.conjTranspose
  -- `P` and `Mᴴ` have the same Gram matrix, so `P x ↦ Mᴴ x` is an isometry on the range of `P`.
  have hgram :
      P.conjTranspose * P =
        M.conjTranspose.conjTranspose * M.conjTranspose := by
    rw [hP_herm, hP_sq, Matrix.conjTranspose_conjTranspose]
  obtain ⟨L, hL⟩ := exists_range_isometry_of_forall_norm_eq_of_domain_codomain TP TMh
    (norm_toEuclideanLin_eq_of_adjoint_mul_eq
      P M.conjTranspose hgram)
  -- Extend it by zero on the orthogonal complement of the range; `U` is its matrix.
  let K : Submodule ℂ (EuclideanSpace ℂ (Fin d)) := LinearMap.range TP
  let C : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin a) :=
    L.toContinuousLinearMap.comp K.orthogonalProjectionOnto
  let U : Matrix (Fin a) (Fin d) ℂ := Matrix.toEuclideanLin.symm C.toLinearMap
  have hU : Matrix.toEuclideanLin U = C.toLinearMap := LinearEquiv.apply_symm_apply _ _
  refine ⟨U.conjTranspose, ?_, ?_⟩
  · -- `U P = Mᴴ`: on `P x` the projection is the identity and `L (P x) = Mᴴ x`.
    have hUP : U * P = M.conjTranspose := by
      refine Matrix.toEuclideanLin.injective (LinearMap.ext fun x => ?_)
      rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply, hU]
      exact (congrArg L (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := K)
        ⟨TP x, LinearMap.mem_range_self TP x⟩)).trans (hL x)
    rw [← Matrix.conjTranspose_conjTranspose M, ← hUP, Matrix.conjTranspose_mul, hP_herm]
  · -- `‖Uᴴ‖ = ‖U‖ = ‖C‖ ≤ 1`: `‖C x‖ = ‖proj x‖ ≤ ‖x‖`, since `L` is an isometry.
    have hC : ‖C‖ ≤ 1 := C.opNorm_le_bound zero_le_one fun x => by
      rw [one_mul]
      exact (L.norm_map _).trans_le (K.norm_orthogonalProjectionOnto_apply_le x)
    rw [Matrix.l2_opNorm_conjTranspose, Matrix.l2_opNorm_def, LinearEquiv.trans_apply, hU]
    exact hC

/-- **Rectangular polar decomposition (contraction form).**

For any rectangular `M : Matrix (Fin d) (Fin a) ℂ`, there exists a
*contraction* `W : Matrix (Fin d) (Fin a) ℂ` such that

  `M = √(M · Mᴴ) · W`.

The contraction bound is expressed using the `l2` operator norm. -/
lemma exists_rectangular_polar_contraction
    {d a : ℕ} (M : Matrix (Fin d) (Fin a) ℂ) :
    ∃ W : Matrix (Fin d) (Fin a) ℂ,
      M = CFC.sqrt (M * M.conjTranspose) * W ∧
      ‖W‖ ≤ 1 := by
  let P : Matrix (Fin d) (Fin d) ℂ := CFC.sqrt (M * M.conjTranspose)
  have hP_herm : P.conjTranspose = P :=
    ((CFC.sqrt_nonneg (M * M.conjTranspose)).posSemidef).isHermitian.eq
  have hMM_nonneg : (0 : Matrix (Fin d) (Fin d) ℂ) ≤ M * M.conjTranspose :=
    (Matrix.posSemidef_self_mul_conjTranspose M).nonneg
  have hP_sq : P * P = M * M.conjTranspose := by
    simpa [P] using
      CFC.sqrt_mul_sqrt_self (M * M.conjTranspose) (ha := hMM_nonneg)
  simpa [P] using
    exists_left_factor_contraction_of_sq_eq_selfAdjoint P M hP_herm hP_sq

/-- If `M * Mᴴ = A`, then the rectangular polar factorization can be written through
`sqrt A`. -/
lemma exists_rectangular_polar_contraction_of_gram_eq
    {d a : ℕ} {M : Matrix (Fin d) (Fin a) ℂ} {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : M * M.conjTranspose = A) :
    ∃ W : Matrix (Fin d) (Fin a) ℂ,
      M = CFC.sqrt A * W ∧
      ‖W‖ ≤ 1 := by
  obtain ⟨W, hM, hW⟩ := Math.LinearAlgebra.UnitaryExtension.exists_rectangular_polar_contraction M
  exact ⟨W, by simpa [hA] using hM, hW⟩

/-- The product of two rectangular contractions, with the second adjointed, is a contraction. -/
lemma l2_opNorm_mul_conjTranspose_le_one
    {d a : ℕ} {W V : Matrix (Fin d) (Fin a) ℂ}
    (hW : ‖W‖ ≤ 1) (hV : ‖V‖ ≤ 1) :
    ‖W * V.conjTranspose‖ ≤ 1 := by
  have hV_adj : ‖V.conjTranspose‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hV
  calc
    ‖W * V.conjTranspose‖ ≤ ‖W‖ * ‖V.conjTranspose‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ 1 * 1 := by
      exact mul_le_mul hW hV_adj (norm_nonneg _) zero_le_one
    _ = 1 := by norm_num

end Math.LinearAlgebra.UnitaryExtension
