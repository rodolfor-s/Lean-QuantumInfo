import QCryptLean.Math.SpectralTheory.Matrix

/-!
# Positive pseudoinverses and rectangular Gram factorization

These proofs use the Hermitian spectral theorem on the original finite index
type. Equal row Gram matrices yield a partial isometry between arbitrary finite
column types; no dimension inequality is required for this weaker conclusion.
-/

noncomputable section

namespace Matrix

open scoped ComplexOrder

/-- A positive matrix has a Hermitian Moore--Penrose pseudoinverse. -/
theorem PosSemidef.exists_pseudoinverse
    {X : Type*} [Fintype X] {G : Matrix X X ℂ} (hG : G.PosSemidef) :
    ∃ Gp : Matrix X X ℂ,
      G * Gp * G = G ∧
      Gp * G * Gp = Gp ∧
      (G * Gp).IsHermitian ∧
      Gp.IsHermitian := by
  classical
  have hM : G.IsHermitian := hG.isHermitian
  have hSpec := hM.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hSpec
  set U : Matrix X X ℂ :=
    (hM.eigenvectorUnitary : Matrix X X ℂ) with hU_def
  set lam : X → ℝ := hM.eigenvalues with hlam_def
  set D : Matrix X X ℂ :=
    Matrix.diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ lam) with hD_def
  set Dp : Matrix X X ℂ :=
    Matrix.diagonal (fun i => if lam i = 0 then (0 : ℂ) else ((lam i : ℂ))⁻¹) with hDp_def
  have hstarU : (star U : Matrix X X ℂ) = Uᴴ := rfl
  have hGeq : G = U * D * Uᴴ := by
    have h := hSpec
    exact h
  have hUstarU : Uᴴ * U = 1 := by
    have h := Matrix.UnitaryGroup.star_mul_self hM.eigenvectorUnitary
    simpa [hU_def, Matrix.star_eq_conjTranspose] using h
  -- Algebraic identities on the diagonal matrices.
  have hDDpD : D * Dp * D = D := by
    rw [hDp_def, hD_def, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : lam i = 0
    · simp [h, Function.comp]
    · have hne : (lam i : ℂ) ≠ 0 := fun heq => h ((RCLike.ofReal_eq_zero (K := ℂ)).mp heq)
      -- simp uses the global `mul_inv_cancel` simp lemma together with `hne`.
      simp [h, Function.comp, hne]
  have hDpDDp : Dp * D * Dp = Dp := by
    rw [hDp_def, hD_def, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : lam i = 0
    · simp [h, Function.comp]
    · have hne : (lam i : ℂ) ≠ 0 := fun heq => h ((RCLike.ofReal_eq_zero (K := ℂ)).mp heq)
      simp [h, Function.comp, hne]
  -- D * Dp is the 0/1 projector diagonal (Hermitian).
  have hDDp_herm : (D * Dp).IsHermitian := by
    rw [hD_def, hDp_def, Matrix.diagonal_mul_diagonal]
    change _ᴴ = _
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    by_cases h : lam i = 0
    · simp [h, Function.comp]
    · have hne : (lam i : ℂ) ≠ 0 := fun heq => h ((RCLike.ofReal_eq_zero (K := ℂ)).mp heq)
      simp [h, hne]
  -- Dp is Hermitian (real diagonal).
  have hDp_herm : Dp.IsHermitian := by
    rw [hDp_def]
    change _ᴴ = _
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    by_cases h : lam i = 0
    · simp [h]
    · have hne : (lam i : ℂ) ≠ 0 := fun heq => h ((RCLike.ofReal_eq_zero (K := ℂ)).mp heq)
      simp only [h, ite_false, Pi.star_apply, RCLike.star_def, map_inv₀]
      rw [Complex.conj_ofReal]
  -- Hermiticity of `U * A * Uᴴ` when A is Hermitian.
  have hConjHerm : ∀ A : Matrix X X ℂ, A.IsHermitian →
      (U * A * Uᴴ).IsHermitian := by
    intro A hA
    change _ᴴ = _
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]
  refine ⟨U * Dp * Uᴴ, ?_, ?_, ?_, ?_⟩
  · -- G * Gp * G = G
    conv_lhs => rw [hGeq]
    calc (U * D * Uᴴ) * (U * Dp * Uᴴ) * (U * D * Uᴴ)
        = U * D * (Uᴴ * U) * Dp * (Uᴴ * U) * D * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = U * D * 1 * Dp * 1 * D * Uᴴ := by rw [hUstarU]
      _ = U * (D * Dp * D) * Uᴴ := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = U * D * Uᴴ := by rw [hDDpD]
      _ = G := hGeq.symm
  · -- Gp * G * Gp = Gp
    conv_lhs => rw [hGeq]
    calc (U * Dp * Uᴴ) * (U * D * Uᴴ) * (U * Dp * Uᴴ)
        = U * Dp * (Uᴴ * U) * D * (Uᴴ * U) * Dp * Uᴴ := by
          simp only [Matrix.mul_assoc]
      _ = U * Dp * 1 * D * 1 * Dp * Uᴴ := by rw [hUstarU]
      _ = U * (Dp * D * Dp) * Uᴴ := by
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = U * Dp * Uᴴ := by rw [hDpDDp]
  · -- (G * Gp).IsHermitian
    have heq : G * (U * Dp * Uᴴ) = U * (D * Dp) * Uᴴ := by
      conv_lhs => rw [hGeq]
      calc (U * D * Uᴴ) * (U * Dp * Uᴴ)
          = U * D * (Uᴴ * U) * Dp * Uᴴ := by simp only [Matrix.mul_assoc]
        _ = U * D * 1 * Dp * Uᴴ := by rw [hUstarU]
        _ = U * (D * Dp) * Uᴴ := by simp only [Matrix.mul_one, Matrix.mul_assoc]
    rw [heq]
    exact hConjHerm _ hDDp_herm
  · -- Gp.IsHermitian
    exact hConjHerm _ hDp_herm


/-- Equal row Grams give a rectangular partial-isometry factor. -/
theorem exists_partialIsometry_of_gram_eq
    {X Y Z : Type*} [Finite X] [Fintype Y] [Fintype Z]
    (W : Matrix X Y ℂ) (W' : Matrix X Z ℂ)
    (hGram : W * Wᴴ = W' * W'ᴴ) :
    ∃ V : Matrix Y Z ℂ,
      V * Vᴴ * V = V ∧ W' = W * V := by
  classical
  let := Fintype.ofFinite X
  -- Set G := W * Wᴴ.  By hypothesis G = W' * W'ᴴ as well.
  set G : Matrix X X ℂ := W * Wᴴ with hG_def
  have hG_psd : G.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose W
  have hG' : W' * W'ᴴ = G := hGram.symm
  -- Moore-Penrose pseudoinverse Gp of the PSD matrix G.
  obtain ⟨Gp, hMP1, hMP2, hMP3, hGp_herm⟩ := hG_psd.exists_pseudoinverse
  have hGp_eq : Gpᴴ = Gp := hGp_herm.eq
  -- Define V := Wᴴ * Gp * W'.
  refine ⟨Wᴴ * Gp * W', ?_, ?_⟩
  · -- Show V * Vᴴ * V = V.
    -- First simplify Vᴴ = W'ᴴ * Gp * W using hGp_eq.
    have hV_dag : (Wᴴ * Gp * W')ᴴ = W'ᴴ * Gp * W := by
      simp [Matrix.conjTranspose_mul, hGp_eq, Matrix.mul_assoc]
    -- Now compute V * Vᴴ * V step by step.
    have step :
        (Wᴴ * Gp * W') * (Wᴴ * Gp * W')ᴴ * (Wᴴ * Gp * W')
          = Wᴴ * Gp * W' := by
      calc (Wᴴ * Gp * W') * (Wᴴ * Gp * W')ᴴ * (Wᴴ * Gp * W')
          = (Wᴴ * Gp * W') * (W'ᴴ * Gp * W) * (Wᴴ * Gp * W') := by rw [hV_dag]
        _ = Wᴴ * Gp * (W' * W'ᴴ) * Gp * (W * Wᴴ) * Gp * W' := by
              simp [Matrix.mul_assoc]
        _ = Wᴴ * Gp * G * Gp * G * Gp * W' := by rw [hG', ← hG_def]
        _ = Wᴴ * (Gp * G * Gp) * G * Gp * W' := by simp [Matrix.mul_assoc]
        _ = Wᴴ * Gp * G * Gp * W' := by rw [hMP2]
        _ = Wᴴ * (Gp * G * Gp) * W' := by simp [Matrix.mul_assoc]
        _ = Wᴴ * Gp * W' := by rw [hMP2]
    exact step
  · -- Show W' = W * V, where V = Wᴴ * Gp * W'.  Equivalently, W' = G * Gp * W'.
    -- Strategy: show (1 - G * Gp) * W' = 0 by computing X * Xᴴ = 0,
    -- where X := (1 - G * Gp) * W'.
    -- Step 1: P := 1 - G * Gp is Hermitian.
    have hP_herm : ((1 : Matrix X X ℂ) - G * Gp).IsHermitian := by
      have h1H : (1 : Matrix X X ℂ).IsHermitian := Matrix.isHermitian_one
      exact h1H.sub hMP3
    -- Step 2: (1 - G * Gp) * G = 0 from hMP1.
    have hPG : ((1 : Matrix X X ℂ) - G * Gp) * G = 0 := by
      rw [sub_mul, one_mul, hMP1, sub_self]
    -- Step 3: ((1 - G * Gp) * W') * ((1 - G * Gp) * W')ᴴ = 0.
    have hXXH :
        ((1 - G * Gp) * W') * ((1 - G * Gp) * W')ᴴ = 0 := by
      have hPh : ((1 : Matrix X X ℂ) - G * Gp)ᴴ = 1 - G * Gp :=
        hP_herm.eq
      calc ((1 - G * Gp) * W') * ((1 - G * Gp) * W')ᴴ
          = ((1 - G * Gp) * W') * (W'ᴴ * (1 - G * Gp)ᴴ) := by
                rw [Matrix.conjTranspose_mul]
        _ = ((1 - G * Gp) * W') * (W'ᴴ * (1 - G * Gp)) := by rw [hPh]
        _ = (1 - G * Gp) * (W' * W'ᴴ) * (1 - G * Gp) := by
                simp [Matrix.mul_assoc]
        _ = (1 - G * Gp) * G * (1 - G * Gp) := by rw [hG']
        _ = 0 * (1 - G * Gp) := by rw [hPG]
        _ = 0 := Matrix.zero_mul _
    -- Step 4: (1 - G * Gp) * W' = 0.
    have hPW' : (1 - G * Gp) * W' = 0 :=
      Matrix.self_mul_conjTranspose_eq_zero.mp hXXH
    -- Step 5: Rearrange to W' = G * Gp * W'.
    have hW'eq : W' = G * Gp * W' := by
      have h := hPW'
      rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
      exact h
    -- Conclude W' = W * V.
    calc W' = G * Gp * W' := hW'eq
      _ = (W * Wᴴ) * Gp * W' := by rw [hG_def]
      _ = W * (Wᴴ * Gp * W') := by
            simp [Matrix.mul_assoc]


end Matrix
