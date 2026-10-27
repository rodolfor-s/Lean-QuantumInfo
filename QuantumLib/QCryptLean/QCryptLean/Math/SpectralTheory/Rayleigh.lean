import QCryptLean.Math.LinearAlgebra.SubmoduleDimension

/-! ## Eigenvalues₀-based spans and Rayleigh bounds (no Antitone requirement)

These versions select eigenvector columns based on eigenvalues₀ ordering rather than
column index ordering. This allows proving Rayleigh bounds without requiring
`Antitone hA.eigenvalues`, using only `eigenvalues₀_antitone` (which is always true).

The key insight: Column `equivOfCardEq j` of the eigenvector unitary has eigenvalue
`eigenvalues (equivOfCardEq j) = eigenvalues₀ j`. So selecting columns by eigenvalues₀
index j gives eigenvectors for the j-th largest eigenvalue.
-/

namespace Math.LinearAlgebra.SubmoduleDim

open Matrix

section Rayleigh42₀

variable {n : ℕ} [NeZero n] [DecidableEq (Fin n)]

/-- The canonical equivalence between index types. -/
private noncomputable def finCardEquiv (n : ℕ) : Fin (Fintype.card (Fin n)) ≃ Fin n :=
  Fintype.equivOfCardEq (by simp : Fintype.card (Fin (Fintype.card (Fin n))) = Fintype.card (Fin n))

/-- Span of eigenvectors for the k largest eigenvalues (eigenvalues₀ indices 0..k-1).
    Column `finCardEquiv j` has eigenvalue `eigenvalues₀ j`, so this span contains
    eigenvectors for eigenvalues₀ 0, ..., eigenvalues₀ (k-1). -/
noncomputable def eigenvecSpanFirst₀ (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (k : ℕ) (hk : k ≤ n) :
    Submodule ℂ (Fin n → ℂ) :=
  let e := finCardEquiv n
  Submodule.span ℂ (Set.range (fun j : Fin k =>
    Matrix.col (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
      (e ⟨j.val, by rw [Fintype.card_fin n]; exact j.isLt.trans_le hk⟩)))

/-- Span of eigenvectors for eigenvalues₀ indices k..n-1 (the n-k smallest eigenvalues). -/
noncomputable def eigenvecSpanFrom₀ (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (k : Fin n) :
    Submodule ℂ (Fin n → ℂ) :=
  let e := finCardEquiv n
  Submodule.span ℂ (Set.range (fun j : Fin (n - k.val) =>
    Matrix.col (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
      (e ⟨k.val + j.val, by rw [Fintype.card_fin n]; omega⟩)))

omit [NeZero n] in
/-- The eigenvectors selected by finCardEquiv for the first k eigenvalues₀ are linearly independent.
    This follows from Uᴴ * U = 1, so the columns are orthonormal. -/
private lemma linearIndependent_eigenvecSpanFirst₀
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (k : ℕ) (hk : k ≤ n) :
    LinearIndependent ℂ (fun j : Fin k =>
      Matrix.col (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
        ((finCardEquiv n) ⟨j.val, by rw [Fintype.card_fin n]; exact j.isLt.trans_le hk⟩)) := by
  let e := finCardEquiv n
  let U := hA.eigenvectorUnitary.val
  have h_UU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  rw [Fintype.linearIndependent_iffₛ]
  intro f g h_eq j
  let j_idx : Fin n := e ⟨j.val, by rw [Fintype.card_fin n]; exact j.isLt.trans_le hk⟩
  have h_dot : dotProduct (star (U · j_idx))
      (∑ i : Fin k, f i • Matrix.col U
        (e ⟨i.val, by rw [Fintype.card_fin n]; exact i.isLt.trans_le hk⟩)) =
      dotProduct (star (U · j_idx))
      (∑ i : Fin k, g i • Matrix.col U
        (e ⟨i.val, by rw [Fintype.card_fin n]; exact i.isLt.trans_le hk⟩)) := by
    rw [h_eq]
  have h_expand_l : dotProduct (star (U · j_idx))
      (∑ i : Fin k, f i • Matrix.col U
        (e ⟨i.val, by rw [Fintype.card_fin n]; exact i.isLt.trans_le hk⟩)) =
      ∑ i : Fin k, f i * dotProduct (star (U · j_idx))
        (Matrix.col U (e ⟨i.val, by rw [Fintype.card_fin n]; exact i.isLt.trans_le hk⟩)) := by
    rw [dotProduct_sum]
    congr 1
    ext i
    rw [dotProduct_smul, smul_eq_mul]
  have h_expand_r : dotProduct (star (U · j_idx))
      (∑ i : Fin k, g i • Matrix.col U
        (e ⟨i.val, by rw [Fintype.card_fin n]; exact i.isLt.trans_le hk⟩)) =
      ∑ i : Fin k, g i * dotProduct (star (U · j_idx))
        (Matrix.col U (e ⟨i.val, by rw [Fintype.card_fin n]; exact i.isLt.trans_le hk⟩)) := by
    rw [dotProduct_sum]
    congr 1
    ext i
    rw [dotProduct_smul, smul_eq_mul]
  rw [h_expand_l, h_expand_r] at h_dot
  have h_orthonormal : ∀ i : Fin k,
      dotProduct (star (U · j_idx))
        (Matrix.col U (e ⟨i.val, by rw [Fintype.card_fin n]; exact i.isLt.trans_le hk⟩)) =
      if j_idx = e ⟨i.val, by rw [Fintype.card_fin n]; exact i.isLt.trans_le hk⟩ then 1 else 0 := by
    intro i
    have h_dot_eq : dotProduct (star (U · j_idx))
        (Matrix.col U (e ⟨i.val, by rw [Fintype.card_fin n]; exact i.isLt.trans_le hk⟩)) =
        (Uᴴ * U) j_idx (e ⟨i.val, by rw [Fintype.card_fin n]; exact i.isLt.trans_le hk⟩) := by
      simp only [dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, Pi.star_apply,
                 Matrix.col_apply]
    rw [h_dot_eq, h_UU, Matrix.one_apply]
  have h_sum_f : ∑ i : Fin k,
      f i * dotProduct (star (U · j_idx))
        (Matrix.col U (e ⟨i.val, by rw [Fintype.card_fin n]; exact i.isLt.trans_le hk⟩)) = f j := by
    rw [Finset.sum_eq_single j]
    · rw [h_orthonormal j, ite_eq_left rfl, mul_one]
    · intro i _ hi_ne
      rw [h_orthonormal i]
      have h_ne : j_idx ≠ e ⟨i.val, by rw [Fintype.card_fin n]; exact i.isLt.trans_le hk⟩ := by
        intro heq
        have h_inj := e.injective heq
        rw [Fin.mk.injEq] at h_inj
        exact hi_ne (Fin.ext h_inj.symm)
      rw [ite_eq_right h_ne, mul_zero]
    · intro hj_not_mem
      exfalso
      exact hj_not_mem (Finset.mem_univ j)
  have h_sum_g : ∑ i : Fin k,
      g i * dotProduct (star (U · j_idx))
        (Matrix.col U (e ⟨i.val, by rw [Fintype.card_fin n]; exact i.isLt.trans_le hk⟩)) = g j := by
    rw [Finset.sum_eq_single j]
    · rw [h_orthonormal j, ite_eq_left rfl, mul_one]
    · intro i _ hi_ne
      rw [h_orthonormal i]
      have h_ne : j_idx ≠ e ⟨i.val, by rw [Fintype.card_fin n]; exact i.isLt.trans_le hk⟩ := by
        intro heq
        have h_inj := e.injective heq
        rw [Fin.mk.injEq] at h_inj
        exact hi_ne (Fin.ext h_inj.symm)
      rw [ite_eq_right h_ne, mul_zero]
    · intro hj_not_mem
      exfalso
      exact hj_not_mem (Finset.mem_univ j)
  rw [h_sum_f, h_sum_g] at h_dot
  exact h_dot

omit [NeZero n] in
/-- The eigenvectors selected by finCardEquiv for eigenvalues₀ indices k..n-1
    are linearly independent. Follows from Uᴴ * U = 1 (orthonormal columns). -/
private lemma linearIndependent_eigenvecSpanFrom₀
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (k : Fin n) :
    LinearIndependent ℂ (fun j : Fin (n - k.val) =>
      Matrix.col (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
        ((finCardEquiv n) ⟨k.val + j.val, by rw [Fintype.card_fin n]; omega⟩)) := by
  let e := finCardEquiv n
  let U := hA.eigenvectorUnitary.val
  have h_UU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  rw [Fintype.linearIndependent_iffₛ]
  intro f g h_eq j
  let j_idx : Fin n := e ⟨k.val + j.val, by rw [Fintype.card_fin n]; omega⟩
  have h_dot : dotProduct (star (U · j_idx))
      (∑ i : Fin (n - k.val), f i • Matrix.col U
        (e ⟨k.val + i.val, by rw [Fintype.card_fin n]; omega⟩)) =
      dotProduct (star (U · j_idx))
      (∑ i : Fin (n - k.val), g i • Matrix.col U
        (e ⟨k.val + i.val, by rw [Fintype.card_fin n]; omega⟩)) := by
    rw [h_eq]
  have h_expand_l : dotProduct (star (U · j_idx))
      (∑ i : Fin (n - k.val), f i • Matrix.col U
        (e ⟨k.val + i.val, by rw [Fintype.card_fin n]; omega⟩)) =
      ∑ i : Fin (n - k.val), f i * dotProduct (star (U · j_idx))
        (Matrix.col U (e ⟨k.val + i.val, by rw [Fintype.card_fin n]; omega⟩)) := by
    rw [dotProduct_sum]
    congr 1
    ext i
    rw [dotProduct_smul, smul_eq_mul]
  have h_expand_r : dotProduct (star (U · j_idx))
      (∑ i : Fin (n - k.val), g i • Matrix.col U
        (e ⟨k.val + i.val, by rw [Fintype.card_fin n]; omega⟩)) =
      ∑ i : Fin (n - k.val), g i * dotProduct (star (U · j_idx))
        (Matrix.col U (e ⟨k.val + i.val, by rw [Fintype.card_fin n]; omega⟩)) := by
    rw [dotProduct_sum]
    congr 1
    ext i
    rw [dotProduct_smul, smul_eq_mul]
  rw [h_expand_l, h_expand_r] at h_dot
  have h_orthonormal : ∀ i : Fin (n - k.val),
      dotProduct (star (U · j_idx))
        (Matrix.col U (e ⟨k.val + i.val, by rw [Fintype.card_fin n]; omega⟩)) =
      if j_idx = e ⟨k.val + i.val, by rw [Fintype.card_fin n]; omega⟩ then 1 else 0 := by
    intro i
    have h_dot_eq : dotProduct (star (U · j_idx))
        (Matrix.col U (e ⟨k.val + i.val, by rw [Fintype.card_fin n]; omega⟩)) =
        (Uᴴ * U) j_idx (e ⟨k.val + i.val, by rw [Fintype.card_fin n]; omega⟩) := by
      simp only [dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, Pi.star_apply,
                 Matrix.col_apply]
    rw [h_dot_eq, h_UU, Matrix.one_apply]
  have h_sum_f : ∑ i : Fin (n - k.val),
      f i * dotProduct (star (U · j_idx))
        (Matrix.col U (e ⟨k.val + i.val, by rw [Fintype.card_fin n]; omega⟩)) = f j := by
    rw [Finset.sum_eq_single j]
    · rw [h_orthonormal j, ite_eq_left rfl, mul_one]
    · intro i _ hi_ne
      rw [h_orthonormal i]
      have h_ne : j_idx ≠ e ⟨k.val + i.val, by rw [Fintype.card_fin n]; omega⟩ := by
        intro heq
        have h_inj := e.injective heq
        rw [Fin.mk.injEq] at h_inj
        exact hi_ne (Fin.ext (by omega))
      rw [ite_eq_right h_ne, mul_zero]
    · intro hj_not_mem
      exfalso
      exact hj_not_mem (Finset.mem_univ j)
  have h_sum_g : ∑ i : Fin (n - k.val),
      g i * dotProduct (star (U · j_idx))
        (Matrix.col U (e ⟨k.val + i.val, by rw [Fintype.card_fin n]; omega⟩)) = g j := by
    rw [Finset.sum_eq_single j]
    · rw [h_orthonormal j, ite_eq_left rfl, mul_one]
    · intro i _ hi_ne
      rw [h_orthonormal i]
      have h_ne : j_idx ≠ e ⟨k.val + i.val, by rw [Fintype.card_fin n]; omega⟩ := by
        intro heq
        have h_inj := e.injective heq
        rw [Fin.mk.injEq] at h_inj
        exact hi_ne (Fin.ext (by omega))
      rw [ite_eq_right h_ne, mul_zero]
    · intro hj_not_mem
      exfalso
      exact hj_not_mem (Finset.mem_univ j)
  rw [h_sum_f, h_sum_g] at h_dot
  exact h_dot

/-- **Rayleigh lower bound (eigenvalues₀ version)**: For a unit vector x in the span of
    eigenvectors for the k largest eigenvalues, the Rayleigh quotient is at least
    eigenvalues₀ (k-1). Does NOT require `Antitone hA.eigenvalues`. -/
lemma eigenvalues₀_le_re_dotProduct_mulVec_of_mem (A : Matrix (Fin n) (Fin n) ℂ) (hA :
    A.IsHermitian) (k : ℕ)
    (hk_lo : 1 ≤ k) (hk_hi : k ≤ n)
    (x : Fin n → ℂ)
    (hx_span : x ∈ eigenvecSpanFirst₀ A hA k hk_hi)
    (hx_unit : (dotProduct (star x) x).re = 1) :
    (dotProduct (star x) (A.mulVec x)).re ≥
      hA.eigenvalues₀ ⟨k - 1, by rw [Fintype.card_fin n]; omega⟩ := by
  -- Spectral decomposition setup
  have h_spec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h_spec
  let e := finCardEquiv n
  let U := hA.eigenvectorUnitary.val
  have h_UU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have h_UU' : U * Uᴴ = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  -- Transform to eigenbasis: φ = Uᴴx
  let φ_vec := Uᴴ.mulVec x
  let a := fun i => Complex.normSq (φ_vec i)
  have h_a_nonneg : ∀ i, 0 ≤ a i := fun i => Complex.normSq_nonneg _
  -- For i NOT in the image of {e ⟨j, ...⟩ : j < k}, φ_vec i = 0
  have h_φ_zero_outside : ∀ i : Fin n,
      (∀ j : Fin k, i ≠ e ⟨j.val, by rw [Fintype.card_fin n]; omega⟩) →
      φ_vec i = 0 := by
    intro i hi_not_in
    have h_orth_helper : ∀ (y : Fin n → ℂ), y ∈ eigenvecSpanFirst₀ A hA k hk_hi →
        dotProduct (star ((U · i))) y = 0 := by
      intro y hy
      have h_span_def : eigenvecSpanFirst₀ A hA k hk_hi =
          Submodule.span ℂ (Set.range (fun j : Fin k =>
            Matrix.col U (e ⟨j.val, by rw [Fintype.card_fin n]; omega⟩))) := rfl
      rw [h_span_def] at hy
      induction hy using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨j, rfl⟩ := hv
        have h_col_eq : (fun j ↦ Matrix.col U
            (e ⟨j.val, by rw [Fintype.card_fin n]; omega⟩)) j =
            (U · (e ⟨j.val, by rw [Fintype.card_fin n]; omega⟩)) := rfl
        rw [h_col_eq]
        have h_dot_eq : dotProduct (star ((U · i)))
            ((U · (e ⟨j.val, by rw [Fintype.card_fin n]; omega⟩))) =
            (Uᴴ * U) i (e ⟨j.val, by rw [Fintype.card_fin n]; omega⟩) := by
          simp only [dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, Pi.star_apply]
        rw [h_dot_eq, h_UU, Matrix.one_apply]
        have h_ne : i ≠ e ⟨j.val, by rw [Fintype.card_fin n]; omega⟩ := hi_not_in j
        simp only [ite_eq_right h_ne]
      | zero => simp only [dotProduct_zero]
      | add u' w' _ _ hu'_ih hw'_ih =>
        simp only [dotProduct_add]
        rw [hu'_ih, hw'_ih, add_zero]
      | smul c' u' _ hu'_ih =>
        simp only [dotProduct_smul]
        rw [hu'_ih, smul_zero]
    have h_φ_eq : φ_vec i = dotProduct (star ((U · i))) x := by
      unfold φ_vec
      simp only [Matrix.mulVec, Matrix.conjTranspose_apply, dotProduct]
      rfl
    rw [h_φ_eq]
    exact h_orth_helper x hx_span
  -- Weights sum to 1
  have h_a_sum : ∑ i, a i = 1 := by
    have h1 : ∑ i, a i = (star φ_vec ⬝ᵥ φ_vec).re := by
      rw [show star φ_vec ⬝ᵥ φ_vec = ∑ i, star (φ_vec i) * φ_vec i from rfl]
      rw [Complex.re_sum]
      congr 1; ext i
      rw [show star (φ_vec i) = (starRingEnd ℂ) (φ_vec i) from rfl, RCLike.conj_mul]
      simp only [a, Complex.normSq_eq_norm_sq]
      norm_cast
    have h2 : star φ_vec ⬝ᵥ φ_vec = star x ⬝ᵥ x := by
      change star (Uᴴ.mulVec x) ⬝ᵥ (Uᴴ.mulVec x) = _
      rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.conjTranspose_conjTranspose,
          Matrix.vecMul_vecMul]
      rw [show Matrix.vecMul (star x) (U * Uᴴ) = star x by rw [h_UU', Matrix.vecMul_one]]
    have h3 : (star x ⬝ᵥ x).re = 1 := hx_unit
    rw [h1, h2, h3]
  -- Express x*Ax as weighted sum of eigenvalues
  have h_quad_eq : (dotProduct (star x) (A.mulVec x)).re =
      ∑ i : Fin n, hA.eigenvalues i * a i := by
    have h_star_eq : star U = Uᴴ := by
      simp only [U, Matrix.star_eq_conjTranspose]
    have h_spec_U : A = U * (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) * Uᴴ := by
      conv_lhs => rw [h_spec]
      simp only [U, h_star_eq]
    conv_lhs => rw [h_spec_U]
    have h1 : (U * (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) * Uᴴ).mulVec x =
        U.mulVec ((Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)).mulVec φ_vec) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, φ_vec]
    rw [h1, Matrix.dotProduct_mulVec]
    have h_star_vecMul : Matrix.vecMul (star x) U = star φ_vec := by
      unfold φ_vec
      ext i
      simp only [Matrix.vecMul, dotProduct, Matrix.mulVec, Pi.star_apply,
                 Matrix.conjTranspose_apply]
      rw [star_sum]
      congr 1
      funext j
      rw [star_mul', star_star]
      ring
    rw [h_star_vecMul]
    unfold dotProduct
    have h_diag_mulVec : ∀ i, ((Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)).mulVec φ_vec) i =
        (hA.eigenvalues i : ℂ) * φ_vec i := by
      intro i
      simp only [Matrix.mulVec_diagonal, Function.comp_apply]
      norm_cast
    simp_rw [h_diag_mulVec]
    rw [Complex.re_sum]
    congr 1
    funext i
    have h_star_eq' : star φ_vec i = star (φ_vec i) := rfl
    rw [h_star_eq']
    have h_conj : star (φ_vec i) * ((hA.eigenvalues i : ℂ) * φ_vec i) =
        (hA.eigenvalues i : ℂ) * (star (φ_vec i) * φ_vec i) := by ring
    rw [h_conj]
    have h_star_is_conj : star (φ_vec i) = (starRingEnd ℂ) (φ_vec i) := rfl
    rw [h_star_is_conj, RCLike.conj_mul]
    simp only [a, Complex.normSq_eq_norm_sq]
    have h_real_mul : ((hA.eigenvalues i : ℂ) * (‖φ_vec i‖ ^ 2 : ℂ)).re =
        hA.eigenvalues i * ‖φ_vec i‖ ^ 2 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
      simp only [Complex.ofReal_re]
    exact h_real_mul
  -- The image set of finCardEquiv applied to indices < k
  let imageIndices : Finset (Fin n) :=
    Finset.image (fun j : Fin k => e ⟨j.val, by rw [Fintype.card_fin n]; omega⟩)
      Finset.univ
  have hnonempty : imageIndices.Nonempty := by
    use e ⟨0, by rw [Fintype.card_fin n]; omega⟩
    simp only [imageIndices, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨0, by omega⟩, by simp⟩
  -- Zero outside image
  have h_a_zero_outside : ∀ i : Fin n, i ∉ imageIndices → a i = 0 := by
    intro i hi
    have h_not_in_range : ∀ j : Fin k,
        i ≠ e ⟨j.val, by rw [Fintype.card_fin n]; omega⟩ := by
      intro j hcontra
      apply hi
      simp only [imageIndices, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨j, hcontra.symm⟩
    have h_φ_zero := h_φ_zero_outside i h_not_in_range
    simp only [a]
    rw [h_φ_zero, Complex.normSq_zero]
  -- Filtered sum: only imageIndices contribute
  have h_quad_eq_filtered : (dotProduct (star x) (A.mulVec x)).re =
      ∑ i ∈ imageIndices, hA.eigenvalues i * a i := by
    rw [h_quad_eq]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ imageIndices)]
    have h_zero_sum : ∑ i ∈ Finset.filter (· ∉ imageIndices) Finset.univ,
        hA.eigenvalues i * a i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [h_a_zero_outside i hi, mul_zero]
    rw [h_zero_sum, add_zero]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  -- Sum of weights over imageIndices equals 1
  have h_a_image_sum : ∑ i ∈ imageIndices, a i = 1 := by
    have h_all_sum : ∑ i : Fin n, a i = 1 := h_a_sum
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ imageIndices)] at h_all_sum
    have h_zero_sum : ∑ i ∈ Finset.filter (· ∉ imageIndices) Finset.univ, a i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact h_a_zero_outside i hi
    rw [h_zero_sum, add_zero] at h_all_sum
    convert h_all_sum using 1
    congr 1; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h_sum_pos : 0 < ∑ i ∈ imageIndices, a i := by
    rw [h_a_image_sum]; exact one_pos
  -- Apply convex combination bound (lower bound: inf ≤ centerMass)
  let a_restricted := fun i : Fin n => a i
  let ev_restricted := fun i : Fin n => hA.eigenvalues i
  have h_a_restricted_nonneg : ∀ i ∈ imageIndices, 0 ≤ a_restricted i :=
    fun i _ => h_a_nonneg i
  have h_centerMass_eq : Finset.centerMass imageIndices a_restricted ev_restricted =
      ∑ i ∈ imageIndices, a_restricted i * ev_restricted i := by
    simp only [Finset.centerMass, smul_eq_mul]
    rw [h_a_image_sum, inv_one, one_mul]
  have h_bound := Finset.inf_le_centerMass (s := imageIndices) (w := a_restricted)
      (f := ev_restricted) h_a_restricted_nonneg h_sum_pos
  rw [h_centerMass_eq] at h_bound
  -- Min over image indices ≥ eigenvalues₀(k-1)
  have h_min_ge : hA.eigenvalues₀ ⟨k - 1, by rw [Fintype.card_fin n]; omega⟩ ≤
      imageIndices.inf' hnonempty ev_restricted := by
    apply Finset.le_inf' hnonempty
    intro i hi
    simp only [imageIndices, Finset.mem_image, Finset.mem_univ, true_and] at hi
    obtain ⟨j, rfl⟩ := hi
    simp only [ev_restricted]
    -- eigenvalues (e ⟨j,...⟩) = eigenvalues₀ ⟨j,...⟩
    have h_ev_eq : hA.eigenvalues (e ⟨j.val, by rw [Fintype.card_fin n]; omega⟩) =
        hA.eigenvalues₀ ⟨j.val, by rw [Fintype.card_fin n]; omega⟩ := by
      simp only [Matrix.IsHermitian.eigenvalues.eq_1]
      congr 1
      exact Equiv.symm_apply_apply _ _
    rw [h_ev_eq]
    apply hA.eigenvalues₀_antitone
    simp only [Fin.mk_le_mk]
    omega
  calc hA.eigenvalues₀ ⟨k - 1, by rw [Fintype.card_fin n]; omega⟩
      ≤ imageIndices.inf' hnonempty ev_restricted := h_min_ge
    _ ≤ ∑ i ∈ imageIndices, a_restricted i * ev_restricted i := h_bound
    _ = ∑ i ∈ imageIndices, ev_restricted i * a_restricted i := by
        congr 1; ext i; ring
    _ = (dotProduct (star x) (A.mulVec x)).re := by
        rw [h_quad_eq_filtered]

omit [NeZero n] in
/-- **Rayleigh upper bound (eigenvalues₀ version)**: For a unit vector x in the span of
    eigenvectors for eigenvalues₀ indices k..n-1, the Rayleigh quotient is at most
    eigenvalues₀ k. Does NOT require `Antitone hA.eigenvalues`. -/
lemma re_dotProduct_mulVec_le_eigenvalues₀_of_mem (A : Matrix (Fin n) (Fin n) ℂ) (hA :
    A.IsHermitian)
    (k : Fin n)
    (x : Fin n → ℂ)
    (hx_span : x ∈ eigenvecSpanFrom₀ A hA k)
    (hx_unit : (dotProduct (star x) x).re = 1) :
    (dotProduct (star x) (A.mulVec x)).re ≤
      hA.eigenvalues₀ ⟨k.val, by rw [Fintype.card_fin n]; exact k.2⟩ := by
  -- Spectral decomposition setup
  have h_spec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h_spec
  let e := finCardEquiv n
  let U := hA.eigenvectorUnitary.val
  have h_UU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have h_UU' : U * Uᴴ = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  -- Transform to eigenbasis: φ = Uᴴx
  let φ_vec := Uᴴ.mulVec x
  let a := fun i => Complex.normSq (φ_vec i)
  have h_a_nonneg : ∀ i, 0 ≤ a i := fun i => Complex.normSq_nonneg _
  -- The set of column indices spanned by eigenvecSpanFrom₀
  -- These are {e ⟨k+j, ...⟩ | j < n - k}
  -- For i NOT in this image, φ_vec i = 0
  have h_φ_zero_outside : ∀ i : Fin n,
      (∀ j : Fin (n - k.val), i ≠ e ⟨k.val + j.val, by rw [Fintype.card_fin n]; omega⟩) →
      φ_vec i = 0 := by
    intro i hi_not_in
    have h_orth_helper : ∀ (y : Fin n → ℂ), y ∈ eigenvecSpanFrom₀ A hA k →
        dotProduct (star ((U · i))) y = 0 := by
      intro y hy
      have h_span_def : eigenvecSpanFrom₀ A hA k =
          Submodule.span ℂ (Set.range (fun j : Fin (n - k.val) =>
            Matrix.col U (e ⟨k.val + j.val, by rw [Fintype.card_fin n]; omega⟩))) := rfl
      rw [h_span_def] at hy
      induction hy using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨j, rfl⟩ := hv
        have h_col_eq : (fun j ↦ Matrix.col U
            (e ⟨k.val + j.val, by rw [Fintype.card_fin n]; omega⟩)) j =
            (U · (e ⟨k.val + j.val, by rw [Fintype.card_fin n]; omega⟩)) := rfl
        rw [h_col_eq]
        have h_dot_eq : dotProduct (star ((U · i)))
            ((U · (e ⟨k.val + j.val, by rw [Fintype.card_fin n]; omega⟩))) =
            (Uᴴ * U) i (e ⟨k.val + j.val, by rw [Fintype.card_fin n]; omega⟩) := by
          simp only [dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, Pi.star_apply]
        rw [h_dot_eq, h_UU, Matrix.one_apply]
        have h_ne : i ≠ e ⟨k.val + j.val, by rw [Fintype.card_fin n]; omega⟩ := hi_not_in j
        simp only [ite_eq_right h_ne]
      | zero => simp only [dotProduct_zero]
      | add u' w' _ _ hu'_ih hw'_ih =>
        simp only [dotProduct_add]
        rw [hu'_ih, hw'_ih, add_zero]
      | smul c' u' _ hu'_ih =>
        simp only [dotProduct_smul]
        rw [hu'_ih, smul_zero]
    have h_φ_eq : φ_vec i = dotProduct (star ((U · i))) x := by
      unfold φ_vec
      simp only [Matrix.mulVec, Matrix.conjTranspose_apply, dotProduct]
      rfl
    rw [h_φ_eq]
    exact h_orth_helper x hx_span
  -- Weights sum to 1
  have h_a_sum : ∑ i, a i = 1 := by
    have h1 : ∑ i, a i = (star φ_vec ⬝ᵥ φ_vec).re := by
      rw [show star φ_vec ⬝ᵥ φ_vec = ∑ i, star (φ_vec i) * φ_vec i from rfl]
      rw [Complex.re_sum]
      congr 1; ext i
      rw [show star (φ_vec i) = (starRingEnd ℂ) (φ_vec i) from rfl, RCLike.conj_mul]
      simp only [a, Complex.normSq_eq_norm_sq]
      norm_cast
    have h2 : star φ_vec ⬝ᵥ φ_vec = star x ⬝ᵥ x := by
      change star (Uᴴ.mulVec x) ⬝ᵥ (Uᴴ.mulVec x) = _
      rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.conjTranspose_conjTranspose,
          Matrix.vecMul_vecMul]
      rw [show Matrix.vecMul (star x) (U * Uᴴ) = star x by rw [h_UU', Matrix.vecMul_one]]
    have h3 : (star x ⬝ᵥ x).re = 1 := hx_unit
    rw [h1, h2, h3]
  -- Express x*Ax as weighted sum of eigenvalues
  have h_quad_eq : (dotProduct (star x) (A.mulVec x)).re =
      ∑ i : Fin n, hA.eigenvalues i * a i := by
    have h_star_eq : star U = Uᴴ := by
      simp only [U, Matrix.star_eq_conjTranspose]
    have h_spec_U : A = U * (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) * Uᴴ := by
      conv_lhs => rw [h_spec]
      simp only [U, h_star_eq]
    conv_lhs => rw [h_spec_U]
    have h1 : (U * (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) * Uᴴ).mulVec x =
        U.mulVec ((Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)).mulVec φ_vec) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, φ_vec]
    rw [h1, Matrix.dotProduct_mulVec]
    have h_star_vecMul : Matrix.vecMul (star x) U = star φ_vec := by
      unfold φ_vec
      ext i
      simp only [Matrix.vecMul, dotProduct, Matrix.mulVec, Pi.star_apply,
                 Matrix.conjTranspose_apply]
      rw [star_sum]
      congr 1
      funext j
      rw [star_mul', star_star]
      ring
    rw [h_star_vecMul]
    unfold dotProduct
    have h_diag_mulVec : ∀ i, ((Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)).mulVec φ_vec) i =
        (hA.eigenvalues i : ℂ) * φ_vec i := by
      intro i
      simp only [Matrix.mulVec_diagonal, Function.comp_apply]
      norm_cast
    simp_rw [h_diag_mulVec]
    rw [Complex.re_sum]
    congr 1
    funext i
    have h_star_eq' : star φ_vec i = star (φ_vec i) := rfl
    rw [h_star_eq']
    have h_conj : star (φ_vec i) * ((hA.eigenvalues i : ℂ) * φ_vec i) =
        (hA.eigenvalues i : ℂ) * (star (φ_vec i) * φ_vec i) := by ring
    rw [h_conj]
    have h_star_is_conj : star (φ_vec i) = (starRingEnd ℂ) (φ_vec i) := rfl
    rw [h_star_is_conj, RCLike.conj_mul]
    simp only [a, Complex.normSq_eq_norm_sq]
    have h_real_mul : ((hA.eigenvalues i : ℂ) * (‖φ_vec i‖ ^ 2 : ℂ)).re =
        hA.eigenvalues i * ‖φ_vec i‖ ^ 2 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
      simp only [Complex.ofReal_re]
    exact h_real_mul
  -- The image set of finCardEquiv applied to indices ≥ k
  let imageIndices : Finset (Fin n) :=
    Finset.image (fun j : Fin (n - k.val) => e ⟨k.val + j.val, by rw [Fintype.card_fin n]; omega⟩)
      Finset.univ
  have hnonempty : imageIndices.Nonempty := by
    use e ⟨k.val, by rw [Fintype.card_fin n]; exact k.2⟩
    simp only [imageIndices, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨⟨0, by omega⟩, by simp⟩
  -- Zero outside image
  have h_a_zero_outside : ∀ i : Fin n, i ∉ imageIndices → a i = 0 := by
    intro i hi
    have h_not_in_range : ∀ j : Fin (n - k.val),
        i ≠ e ⟨k.val + j.val, by rw [Fintype.card_fin n]; omega⟩ := by
      intro j hcontra
      apply hi
      simp only [imageIndices, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨j, hcontra.symm⟩
    have h_φ_zero := h_φ_zero_outside i h_not_in_range
    simp only [a]
    rw [h_φ_zero, Complex.normSq_zero]
  -- Filtered sum: only imageIndices contribute
  have h_quad_eq_filtered : (dotProduct (star x) (A.mulVec x)).re =
      ∑ i ∈ imageIndices, hA.eigenvalues i * a i := by
    rw [h_quad_eq]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ imageIndices)]
    have h_zero_sum : ∑ i ∈ Finset.filter (· ∉ imageIndices) Finset.univ,
        hA.eigenvalues i * a i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [h_a_zero_outside i hi, mul_zero]
    rw [h_zero_sum, add_zero]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  -- Sum of weights over imageIndices equals 1
  have h_a_image_sum : ∑ i ∈ imageIndices, a i = 1 := by
    have h_all_sum : ∑ i : Fin n, a i = 1 := h_a_sum
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ imageIndices)] at h_all_sum
    have h_zero_sum : ∑ i ∈ Finset.filter (· ∉ imageIndices) Finset.univ, a i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact h_a_zero_outside i hi
    rw [h_zero_sum, add_zero] at h_all_sum
    convert h_all_sum using 1
    congr 1; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h_sum_pos : 0 < ∑ i ∈ imageIndices, a i := by
    rw [h_a_image_sum]; exact one_pos
  -- Apply convex combination bound
  let a_restricted := fun i : Fin n => a i
  let ev_restricted := fun i : Fin n => hA.eigenvalues i
  have h_a_restricted_nonneg : ∀ i ∈ imageIndices, 0 ≤ a_restricted i :=
    fun i _ => h_a_nonneg i
  have h_centerMass_eq : Finset.centerMass imageIndices a_restricted ev_restricted =
      ∑ i ∈ imageIndices, a_restricted i * ev_restricted i := by
    simp only [Finset.centerMass, smul_eq_mul]
    rw [h_a_image_sum, inv_one, one_mul]
  have h_bound := Finset.centerMass_le_sup (s := imageIndices) (w := a_restricted)
      (f := ev_restricted) h_a_restricted_nonneg h_sum_pos
  rw [h_centerMass_eq] at h_bound
  -- Max over image indices ≤ eigenvalues₀ k
  -- Key: eigenvalues (e m) = eigenvalues₀ m because finCardEquiv IS the equivOfCardEq
  -- used internally by eigenvalues. Then eigenvalues₀_antitone gives the bound.
  have h_max_le : imageIndices.sup' hnonempty ev_restricted ≤
      hA.eigenvalues₀ ⟨k.val, by rw [Fintype.card_fin n]; exact k.2⟩ := by
    apply Finset.sup'_le hnonempty
    intro i hi
    simp only [imageIndices, Finset.mem_image, Finset.mem_univ, true_and] at hi
    obtain ⟨j, rfl⟩ := hi
    simp only [ev_restricted]
    -- eigenvalues (e ⟨k+j,...⟩) = eigenvalues₀ ⟨k+j,...⟩
    -- because finCardEquiv = equivOfCardEq and eigenvalues uses the same equivOfCardEq
    have h_ev_eq : hA.eigenvalues (e ⟨k.val + j.val, by rw [Fintype.card_fin n]; omega⟩) =
        hA.eigenvalues₀ ⟨k.val + j.val, by rw [Fintype.card_fin n]; omega⟩ := by
      simp only [Matrix.IsHermitian.eigenvalues.eq_1]
      congr 1
      exact Equiv.symm_apply_apply _ _
    rw [h_ev_eq]
    apply hA.eigenvalues₀_antitone
    simp only [Fin.mk_le_mk]
    omega
  calc (dotProduct (star x) (A.mulVec x)).re
      = ∑ i ∈ imageIndices, ev_restricted i * a_restricted i := by
        rw [h_quad_eq_filtered]
    _ = ∑ i ∈ imageIndices, a_restricted i * ev_restricted i := by
        congr 1; ext i; ring
    _ ≤ imageIndices.sup' hnonempty ev_restricted := h_bound
    _ ≤ hA.eigenvalues₀ ⟨k.val, by rw [Fintype.card_fin n]; exact k.2⟩ := h_max_le

omit [NeZero n] in
/-- Dimension of eigenvecSpanFirst₀. -/
lemma finrank_eigenvecSpanFirst₀ (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (k : ℕ) (hk : k ≤ n) :
    Module.finrank ℂ (eigenvecSpanFirst₀ A hA k hk) = k := by
  let e := finCardEquiv n
  have h_linindep : LinearIndependent ℂ (fun j : Fin k =>
      Matrix.col (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
        (e ⟨j.val, by rw [Fintype.card_fin n]; exact j.isLt.trans_le hk⟩)) :=
    linearIndependent_eigenvecSpanFirst₀ A hA k hk
  have h_finrank : Module.finrank ℂ (Submodule.span ℂ (Set.range (fun j : Fin k =>
      Matrix.col (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
        (e ⟨j.val, by rw [Fintype.card_fin n]; exact j.isLt.trans_le hk⟩)))) =
      Fintype.card (Fin k) :=
    finrank_span_eq_card h_linindep
  have h_card : Fintype.card (Fin k) = k := Fintype.card_fin k
  rw [h_card] at h_finrank
  simp only [eigenvecSpanFirst₀] at h_finrank ⊢
  exact h_finrank

omit [NeZero n] in
/-- Dimension of eigenvecSpanFrom₀. -/
lemma finrank_eigenvecSpanFrom₀ (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (k : Fin n) :
    Module.finrank ℂ (eigenvecSpanFrom₀ A hA k) = n - k.val := by
  let e := finCardEquiv n
  have h_linindep : LinearIndependent ℂ (fun j : Fin (n - k.val) =>
      Matrix.col (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
        (e ⟨k.val + j.val, by rw [Fintype.card_fin n]; omega⟩)) :=
    linearIndependent_eigenvecSpanFrom₀ A hA k
  have h_finrank : Module.finrank ℂ (Submodule.span ℂ (Set.range (fun j : Fin (n - k.val) =>
      Matrix.col (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
        (e ⟨k.val + j.val, by rw [Fintype.card_fin n]; omega⟩)))) =
      Fintype.card (Fin (n - k.val)) :=
    finrank_span_eq_card h_linindep
  have h_card : Fintype.card (Fin (n - k.val)) = n - k.val := Fintype.card_fin (n - k.val)
  rw [h_card] at h_finrank
  simp only [eigenvecSpanFrom₀] at h_finrank ⊢
  exact h_finrank

end Rayleigh42₀

end Math.LinearAlgebra.SubmoduleDim
