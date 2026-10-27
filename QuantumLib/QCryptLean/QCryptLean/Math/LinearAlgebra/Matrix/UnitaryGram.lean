import QCryptLean.Math.LinearAlgebra.UnitaryExtension

/-!
# Native unitary extension for finite matrix registers

The range isometry is extended in Euclidean space on the given finite row type.
No enumeration of the register enters the proof. Norms are Euclidean vector
norms; no matrix norm instance is installed.
-/

noncomputable section

namespace Matrix

/-- A matrix whose Euclidean linear map is a linear isometry equivalence is unitary. -/
theorem isUnitary_of_toEuclideanLin_eq_linearIsometryEquiv
    {X : Type*} [Fintype X] [DecidableEq X] (U : Matrix X X ℂ)
    (e : EuclideanSpace ℂ X ≃ₗᵢ[ℂ] EuclideanSpace ℂ X)
    (hU : Matrix.toEuclideanLin U = e.toLinearMap) :
    U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 := by
  constructor
  · apply
      (Matrix.toEuclideanLin :
        Matrix X X ℂ ≃ₗ[ℂ]
          EuclideanSpace ℂ X →ₗ[ℂ] EuclideanSpace ℂ X).injective
    rw [Matrix.toLpLin_mul_same]
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint U, hU]
    rw [LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]
    simp
  · apply
      (Matrix.toEuclideanLin :
        Matrix X X ℂ ≃ₗ[ℂ]
          EuclideanSpace ℂ X →ₗ[ℂ] EuclideanSpace ℂ X).injective
    rw [Matrix.toLpLin_mul_same]
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint U, hU]
    rw [LinearIsometryEquiv.adjoint_toLinearMap_eq_symm]
    simp

/-- Equal rectangular column Gram matrices differ by left multiplication by a
square unitary on the common row space. -/
theorem exists_unitary_of_columnGram_eq
    {X Y : Type*} [Fintype X] [Finite Y] [DecidableEq X] (A B : Matrix X Y ℂ)
    (hgram : A.conjTranspose * A = B.conjTranspose * B) :
    ∃ U : Matrix X X ℂ,
      U.conjTranspose * U = 1 ∧ U * U.conjTranspose = 1 ∧ U * A = B := by
  classical
  let := Fintype.ofFinite Y
  let TA : EuclideanSpace ℂ Y →ₗ[ℂ] EuclideanSpace ℂ X :=
    Matrix.toEuclideanLin A
  let TB : EuclideanSpace ℂ Y →ₗ[ℂ] EuclideanSpace ℂ X :=
    Matrix.toEuclideanLin B
  have hnorm : ∀ x : EuclideanSpace ℂ Y, ‖TB x‖ = ‖TA x‖ := by
    intro x
    change ‖Matrix.toEuclideanLin B x‖ = ‖Matrix.toEuclideanLin A x‖
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      Math.LinearAlgebra.UnitaryExtension.inner_toEuclideanLin_toEuclideanLin,
      Math.LinearAlgebra.UnitaryExtension.inner_toEuclideanLin_toEuclideanLin, hgram]
  obtain ⟨L, hL⟩ :=
    Math.LinearAlgebra.UnitaryExtension.exists_range_isometry_of_forall_norm_eq_of_domain
      TA TB hnorm
  let Lext : EuclideanSpace ℂ X →ₗᵢ[ℂ] EuclideanSpace ℂ X :=
    LinearIsometry.extend L
  let e : EuclideanSpace ℂ X ≃ₗᵢ[ℂ] EuclideanSpace ℂ X :=
    Lext.toLinearIsometryEquiv rfl
  let U : Matrix X X ℂ :=
    (Matrix.toEuclideanLin :
      Matrix X X ℂ ≃ₗ[ℂ]
        EuclideanSpace ℂ X →ₗ[ℂ] EuclideanSpace ℂ X).symm e.toLinearMap
  have hUlin : Matrix.toEuclideanLin U = e.toLinearMap := by
    simp [U]
  obtain ⟨hleft, hright⟩ :=
    isUnitary_of_toEuclideanLin_eq_linearIsometryEquiv U e hUlin
  have hExt_apply : ∀ x : EuclideanSpace ℂ Y, e.toLinearMap (TA x) = TB x := by
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
        Matrix X Y ℂ ≃ₗ[ℂ]
          EuclideanSpace ℂ Y →ₗ[ℂ] EuclideanSpace ℂ X).injective
    rw [Matrix.toLpLin_mul_same]
    rw [hUlin]
    exact LinearMap.ext hExt_apply
  exact ⟨U, hleft, hright, hmul⟩

open scoped Classical in
/-- Equal row Grams admit a right coisometry when the target column register is larger. -/
theorem exists_coisometry_of_rowGram_eq
    {X Y Z : Type*} [Finite X] [Fintype Y] [Fintype Z]
    (A : Matrix X Y ℂ) (B : Matrix X Z ℂ)
    (hgram : A * Aᴴ = B * Bᴴ) (hdim : Fintype.card Y ≤ Fintype.card Z) :
    ∃ V : Matrix Y Z ℂ, V * Vᴴ = 1 ∧ B = A * V := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hdim
  let J : Matrix Z Y ℂ := fun z y => if z = e y then 1 else 0
  have hJ : Jᴴ * J = 1 := by
    ext y y'
    change (∑ z : Z, star (J z y) * J z y') = if y = y' then 1 else 0
    simp [J, apply_ite, e.injective.eq_iff, eq_comm]
  have hcol : (J * Aᴴ)ᴴ * (J * Aᴴ) = Bᴴᴴ * Bᴴ := by
    calc
      (J * Aᴴ)ᴴ * (J * Aᴴ) = A * (Jᴴ * J) * Aᴴ := by
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = A * Aᴴ := by rw [hJ, Matrix.mul_one]
      _ = Bᴴᴴ * Bᴴ := by simpa only [conjTranspose_conjTranspose] using hgram
  obtain ⟨U, hU, _, he⟩ := exists_unitary_of_columnGram_eq (J * Aᴴ) Bᴴ hcol
  refine ⟨(U * J)ᴴ, ?_, ?_⟩
  · calc
      (U * J)ᴴ * ((U * J)ᴴ)ᴴ = Jᴴ * (Uᴴ * U) * J := by
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = 1 := by rw [hU, Matrix.mul_one, hJ]
  · have h := congrArg Matrix.conjTranspose he
    simpa only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc] using h.symm

open scoped MatrixOrder ComplexOrder Classical in
/-- A unitary left factor sends a square matrix to the positive square root of its Gram matrix. -/
theorem exists_unitary_mul_eq_sqrt_gram
    {X : Type*} [Fintype X] (A : Matrix X X ℂ) :
    ∃ U : unitaryGroup X ℂ, U.val * A = CFC.sqrt (Aᴴ * A) := by
  classical
  have hp := nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A))
  have hg : Aᴴ * A = (CFC.sqrt (Aᴴ * A))ᴴ * CFC.sqrt (Aᴴ * A) := by
    rw [hp.isHermitian.eq, CFC.sqrt_mul_sqrt_self _ (posSemidef_conjTranspose_mul_self A).nonneg]
  obtain ⟨U, hU, hU', he⟩ := exists_unitary_of_columnGram_eq A (CFC.sqrt (Aᴴ * A)) hg
  exact ⟨⟨U, hU, hU'⟩, he⟩

open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator Classical in
/-- A rectangular matrix factors through its positive left Gram square root by an L2 contraction. -/
theorem exists_sqrt_gram_mul_contraction
    {X Y : Type*} [Fintype X] [Fintype Y] (M : Matrix X Y ℂ) :
    ∃ W : Matrix X Y ℂ, M = CFC.sqrt (M * Mᴴ) * W ∧ ‖W‖ ≤ 1 := by
  classical
  let P := CFC.sqrt (M * Mᴴ)
  have hP : Pᴴ = P := (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian.eq
  have hPP : P * P = M * Mᴴ :=
    CFC.sqrt_mul_sqrt_self _ (posSemidef_self_mul_conjTranspose M).nonneg
  let TP : EuclideanSpace ℂ X →ₗ[ℂ] EuclideanSpace ℂ X := toEuclideanLin P
  let TM : EuclideanSpace ℂ X →ₗ[ℂ] EuclideanSpace ℂ Y := toEuclideanLin Mᴴ
  have hg : Pᴴ * P = Mᴴᴴ * Mᴴ := by rw [hP, hPP, conjTranspose_conjTranspose]
  have hn (x : EuclideanSpace ℂ X) : ‖TM x‖ = ‖TP x‖ := by
    change ‖toEuclideanLin Mᴴ x‖ = ‖toEuclideanLin P x‖
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      Math.LinearAlgebra.UnitaryExtension.inner_toEuclideanLin_toEuclideanLin,
      Math.LinearAlgebra.UnitaryExtension.inner_toEuclideanLin_toEuclideanLin, hg]
  obtain ⟨L, hL⟩ :=
    Math.LinearAlgebra.UnitaryExtension.exists_range_isometry_of_forall_norm_eq_of_domain_codomain
      TP TM hn
  let K := LinearMap.range TP
  let C : EuclideanSpace ℂ X →L[ℂ] EuclideanSpace ℂ Y :=
    L.toContinuousLinearMap.comp K.orthogonalProjectionOnto
  let U : Matrix Y X ℂ := toEuclideanLin.symm C.toLinearMap
  have hU : toEuclideanLin U = C.toLinearMap := LinearEquiv.apply_symm_apply _ _
  refine ⟨Uᴴ, ?_, ?_⟩
  · have he : U * P = Mᴴ := by
      apply toEuclideanLin.injective
      apply LinearMap.ext
      intro x
      rw [toLpLin_mul_same, LinearMap.comp_apply, hU]
      exact (congrArg L (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := K)
        ⟨TP x, LinearMap.mem_range_self TP x⟩)).trans (hL x)
    have he' := congrArg Matrix.conjTranspose he
    rw [conjTranspose_mul, hP, conjTranspose_conjTranspose] at he'
    exact he'.symm
  · have hC : ‖C‖ ≤ 1 := C.opNorm_le_bound zero_le_one fun x => by
      rw [one_mul]
      exact (L.norm_map _).trans_le (K.norm_orthogonalProjectionOnto_apply_le x)
    rw [l2_opNorm_conjTranspose, l2_opNorm_def, LinearEquiv.trans_apply, hU]
    exact hC

end Matrix
