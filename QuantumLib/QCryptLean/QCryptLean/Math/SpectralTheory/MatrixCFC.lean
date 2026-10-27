import QCryptLean.Math.SpectralTheory.Eigenvalues

/-! # Matrix CFC -/


open scoped Matrix ComplexOrder MatrixOrder Kronecker
open Matrix Unitary

namespace Math.SpectralTheory

variable {n m : ℕ}


/-- For a Hermitian matrix H, its transpose equals its entry-wise conjugate.
    This follows from H = Hᴴ = (H.map star)ᵀ, so Hᵀ = H.map star. -/
lemma transpose_eq_map_star_of_isHermitian {n : Type*}
    (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    Hᵀ = H.map star := by
  have h : Hᴴ = H := hH.eq
  ext i j
  have hij := congrFun (congrFun h j) i
  simp only [conjTranspose_apply] at hij
  simp only [transpose_apply, map_apply]
  exact hij.symm

/-- Entry-wise conjugation of a Hermitian matrix is Hermitian.
    Since H.map star = Hᵀ for Hermitian H, and transpose preserves Hermiticity. -/
lemma isHermitian_map_star {n : Type*}
    (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    (H.map star).IsHermitian := by
  rw [← transpose_eq_map_star_of_isHermitian H hH]
  exact hH.transpose

/-- For a Hermitian matrix, the characteristic polynomial is preserved by entry-wise conjugation.
    This follows from charpoly(H.map star) = charpoly(Hᵀ) = charpoly(H). -/
lemma charpoly_map_star_of_isHermitian {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    (H.map star).charpoly = H.charpoly := by
  rw [← transpose_eq_map_star_of_isHermitian H hH]
  exact charpoly_transpose H

/-- For a Hermitian matrix, entry-wise conjugation preserves the eigenvalue multiset.
    Since the characteristic polynomials are equal, the roots (eigenvalues) are equal. -/
lemma eigenvalues_map_star_eq {n : ℕ}
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    let hH' := isHermitian_map_star H hH
    Finset.univ.val.map hH'.eigenvalues = Finset.univ.val.map hH.eigenvalues := by
  intro hH'
  have h_charpoly_eq := charpoly_map_star_of_isHermitian H hH
  have h_roots_H := hH.roots_charpoly_eq_eigenvalues
  have h_roots_H' := hH'.roots_charpoly_eq_eigenvalues
  have h_roots_eq : (H.map star).charpoly.roots = H.charpoly.roots := by rw [h_charpoly_eq]
  have h_eq : Multiset.map (RCLike.ofReal (K := ℂ) ∘ hH'.eigenvalues) Finset.univ.val =
      Multiset.map (RCLike.ofReal (K := ℂ) ∘ hH.eigenvalues) Finset.univ.val := by
    rw [← h_roots_H', ← h_roots_H, h_roots_eq]
  have h_eq' : Multiset.map (fun r : ℝ => (r : ℂ))
        (Multiset.map hH'.eigenvalues Finset.univ.val) =
      Multiset.map (fun r : ℝ => (r : ℂ))
        (Multiset.map hH.eigenvalues Finset.univ.val) := by
    rw [Multiset.map_map, Multiset.map_map]
    exact h_eq
  have h_inj : Function.Injective (fun r : ℝ => (r : ℂ)) := Complex.ofReal_injective
  exact Multiset.map_injective h_inj h_eq'

/-- For two Hermitian matrices that are equal, their eigenvalues are pointwise equal. -/
lemma eigenvalues_eq_of_matrix_eq {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h_eq : A = B) :
    ∀ i, hA.eigenvalues i = hB.eigenvalues i := by
  subst h_eq
  intro i
  rfl


/-- A real diagonal matrix (entries `RCLike.ofReal ∘ d`) is Hermitian. -/
lemma isHermitian_diagonal_ofReal {ι : Type*} [DecidableEq ι] (d : ι → ℝ) :
    (diagonal (fun i => (d i : ℂ))).IsHermitian := by
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  rw [IsSelfAdjoint]; ext i; simp

/-- Each diagonal entry of a real diagonal matrix is in its real spectrum. -/
lemma diagonal_ofReal_mem_spectrum {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) (i : ι) :
    (d i) ∈ spectrum ℝ (diagonal (fun i => (d i : ℂ))) := by
  rw [← spectrum.algebraMap_mem_iff ℂ (R := ℝ) (a := diagonal (fun i => (d i : ℂ))) (r := d i),
    spectrum_diagonal]
  exact ⟨i, by simp [Complex.coe_algebraMap]⟩

/-- The diagonal continuous functional calculus star algebra homomorphism: the map
sending a continuous function `g` on the spectrum to the diagonal matrix
`diagonal (RCLike.ofReal ∘ g ∘ d)`. By uniqueness of the continuous functional
calculus this agrees with `cfcHom` (see `cfc_diagonal_ofReal`). -/
noncomputable def diagonalCfcHom {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) :
    C(spectrum ℝ (diagonal (fun i => (d i : ℂ))), ℝ) →⋆ₐ[ℝ] Matrix ι ι ℂ where
  toFun g := diagonal fun i => ((g ⟨d i, diagonal_ofReal_mem_spectrum d i⟩ : ℝ) : ℂ)
  map_zero' := by simp [← diagonal_zero]
  map_one' := by simp [← diagonal_one]
  map_mul' f g := by simp [diagonal_mul_diagonal]
  map_add' f g := by simp [← diagonal_add]
  commutes' r := by
    ext i j
    have hL : (((algebraMap ℝ C(spectrum ℝ (diagonal (fun i => (d i : ℂ))), ℝ)) r)
        ⟨d i, diagonal_ofReal_mem_spectrum d i⟩ : ℝ) = r := by
      simp [Algebra.algebraMap_eq_smul_one]
    rw [diagonal_apply]
    simp only [hL]
    rw [Matrix.algebraMap_eq_diagonal, diagonal_apply]
    by_cases h : i = j <;> simp [h, Pi.algebraMap_apply]
  map_star' f := by
    rw [Matrix.star_eq_conjTranspose, diagonal_conjTranspose]
    congr 1
    ext i
    simp

@[simp]
lemma diagonalCfcHom_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ)
    (g : C(spectrum ℝ (diagonal (fun i => (d i : ℂ))), ℝ)) :
    diagonalCfcHom d g
      = diagonal fun i => ((g ⟨d i, diagonal_ofReal_mem_spectrum d i⟩ : ℝ) : ℂ) := rfl

lemma continuous_diagonalCfcHom {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) :
    Continuous (diagonalCfcHom d) := by
  apply continuous_matrix
  intro i j
  by_cases h : i = j
  · subst h
    simp only [diagonalCfcHom_apply, diagonal_apply_eq]
    exact Complex.continuous_ofReal.comp (continuous_eval_const _)
  · simp only [diagonalCfcHom_apply, diagonal_apply_ne _ h]
    exact continuous_const

lemma diagonalCfcHom_id {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) :
    diagonalCfcHom d ((ContinuousMap.id ℝ).restrict (spectrum ℝ (diagonal (fun i => (d i : ℂ)))))
      = diagonal (fun i => (d i : ℂ)) := by
  rw [diagonalCfcHom_apply]; rfl

/-- The continuous functional calculus of a real diagonal matrix is the diagonal of
`f` applied entrywise: `cfc f (diagonal (↑·d)) = diagonal (↑·(f ∘ d))`. -/
lemma cfc_diagonal_ofReal {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) (f : ℝ → ℝ) :
    cfc f (diagonal (fun i => (d i : ℂ))) = diagonal (fun i => ((f (d i) : ℝ) : ℂ)) := by
  have hsa : IsSelfAdjoint (diagonal (fun i => (d i : ℂ))) := isHermitian_diagonal_ofReal d
  have hcont : ContinuousOn f (spectrum ℝ (diagonal (fun i => (d i : ℂ)))) :=
    (diagonal (fun i => (d i : ℂ))).finite_real_spectrum.continuousOn f
  rw [cfc_apply f (diagonal (fun i => (d i : ℂ))) hsa hcont]
  have huniq : cfcHom hsa = diagonalCfcHom d :=
    cfcHom_eq_of_continuous_of_map_id hsa (diagonalCfcHom d) (continuous_diagonalCfcHom d)
      (diagonalCfcHom_id d)
  rw [huniq, diagonalCfcHom_apply]
  rfl

/-- Conjugation `x ↦ u · x · uᴴ` by a unitary matrix is continuous. -/
lemma continuous_conjStarAlgAut {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : unitary (Matrix ι ι ℂ)) :
    Continuous (conjStarAlgAut ℂ (Matrix ι ι ℂ) u) := by
  have heq : (conjStarAlgAut ℂ (Matrix ι ι ℂ) u : Matrix ι ι ℂ → _)
      = fun x => (u : Matrix ι ι ℂ) * x * star (u : Matrix ι ι ℂ) := by
    ext x; simp [conjStarAlgAut_apply]
  rw [show (conjStarAlgAut ℂ (Matrix ι ι ℂ) u : Matrix ι ι ℂ → Matrix ι ι ℂ) = _ from heq]
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

/-- The continuous functional calculus is equivariant under unitary conjugation:
`cfc f (u · A · uᴴ) = u · cfc f A · uᴴ`. -/
lemma cfc_conjStarAlgAut {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (u : unitary (Matrix ι ι ℂ)) (f : ℝ → ℝ) :
    cfc f (conjStarAlgAut ℂ _ u A) = conjStarAlgAut ℂ _ u (cfc f A) :=
  (StarAlgHomClass.map_cfc (conjStarAlgAut ℂ _ u) f A
    (hf := (A.finite_real_spectrum).continuousOn f) (hφ := continuous_conjStarAlgAut u)
    (ha := hA) (hφa := by cfc_tac)).symm

/-- Spectral form of `cfc f A` for a Hermitian matrix: conjugation of the diagonal
`diagonal (↑·(f ∘ eigenvalues))` by the eigenvector unitary. -/
lemma cfc_eq_conjStarAlgAut_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (diagonal (fun i => ((f (hA.eigenvalues i) : ℝ) : ℂ))) := by
  have hofReal : (RCLike.ofReal ∘ hA.eigenvalues : ι → ℂ)
      = fun i => ((hA.eigenvalues i : ℝ) : ℂ) := rfl
  conv_lhs => rw [hA.spectral_theorem, hofReal]
  rw [cfc_conjStarAlgAut _ (isHermitian_diagonal_ofReal hA.eigenvalues) hA.eigenvectorUnitary f,
    cfc_diagonal_ofReal]

/-- `CFC.rpow` of a positive semidefinite matrix in spectral form: conjugation of
the diagonal `diagonal (↑·(eigenvalues ^ x))` by the eigenvector unitary. -/
lemma _root_.Matrix.PosSemidef.cfcRpow_eq_conjStarAlgAut_diagonal {ι : Type*} [Fintype ι]
    [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (x : ℝ) :
    A ^ x = conjStarAlgAut ℂ _ hA.1.eigenvectorUnitary
      (diagonal (fun i => ((hA.1.eigenvalues i ^ x : ℝ) : ℂ))) := by
  rw [CFC.rpow_eq_cfc_real (a := A) (y := x) hA.nonneg,
    cfc_eq_conjStarAlgAut_diagonal A hA.1 (fun t => t ^ x)]

/-- Unitary conjugation of a diagonal matrix is the eigenprojector sum: for the
eigenvector unitary `U = hA.eigenvectorUnitary` and any scalar family `d`,
`U · diagonal d · Uᴴ = ∑ i, d i • |u_i⟩⟨u_i|` with `u_i = (hA.eigenvectorBasis i).ofLp`.
This is the entrywise generalization of `Matrix.IsHermitian.eq_sum_smul_vecMulVec` to an
arbitrary diagonal (here used at `d i = eigenvalues i ^ x`). -/
lemma conjStarAlgAut_eigenvectorUnitary_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (d : ι → ℂ) :
    conjStarAlgAut ℂ _ hA.eigenvectorUnitary (diagonal d) =
      ∑ i, d i • Matrix.vecMulVec ((hA.eigenvectorBasis i).ofLp)
        (star ((hA.eigenvectorBasis i).ofLp)) := by
  classical
  rw [conjStarAlgAut_apply]
  set U : Matrix ι ι ℂ := (↑hA.eigenvectorUnitary : Matrix ι ι ℂ) with hU_def
  ext a b
  rw [Matrix.mul_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.mul_diagonal, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
  rw [show star ((hA.eigenvectorBasis i).ofLp) b
        = star ((hA.eigenvectorBasis i).ofLp b) from rfl]
  rw [hU_def, hA.eigenvectorUnitary_apply a i, hA.eigenvectorUnitary_apply b i]
  ring

/-- **Real-exponent spectral expansion of a PSD matrix.** For positive semidefinite
`A` and real `x`, the `CFC.rpow` power is the eigenvalue-`x` weighted sum of the
rank-one eigenprojectors `|u_i⟩⟨u_i|`:
`A ^ x = ∑ i, (eigenvalues i ^ x : ℂ) • |u_i⟩⟨u_i|`.
This is the real-exponent analogue of `Matrix.IsHermitian.eq_sum_smul_vecMulVec`. -/
lemma _root_.Matrix.PosSemidef.cfcRpow_eq_sum_smul_vecMulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) (x : ℝ) :
    A ^ x = ∑ i, ((hA.1.eigenvalues i ^ x : ℝ) : ℂ) •
        Matrix.vecMulVec ((hA.1.eigenvectorBasis i).ofLp)
          (star ((hA.1.eigenvectorBasis i).ofLp)) := by
  rw [Matrix.PosSemidef.cfcRpow_eq_conjStarAlgAut_diagonal hA x,
    conjStarAlgAut_eigenvectorUnitary_diagonal hA.1
      (fun i => ((hA.1.eigenvalues i ^ x : ℝ) : ℂ))]

/-- Kronecker of two unitary matrices, bundled as a unitary element over the product
index type. -/
noncomputable def kroneckerUnitary {n m : ℕ} (u : Matrix.unitaryGroup (Fin n) ℂ)
    (v : Matrix.unitaryGroup (Fin m) ℂ) :
    unitary (Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) :=
  ⟨(u : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ (v : Matrix (Fin m) (Fin m) ℂ),
    Matrix.kronecker_mem_unitary u.2 v.2⟩

/-- Conjugation by a Kronecker unitary splits over the Kronecker product:
`(U ⊗ V) · (X ⊗ Y) · (U ⊗ V)ᴴ = (U · X · Uᴴ) ⊗ (V · Y · Vᴴ)`. -/
lemma conjStarAlgAut_kronecker {n m : ℕ} (u : Matrix.unitaryGroup (Fin n) ℂ)
    (v : Matrix.unitaryGroup (Fin m) ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin m) (Fin m) ℂ) :
    conjStarAlgAut ℂ _ (kroneckerUnitary u v) (X ⊗ₖ Y)
      = (conjStarAlgAut ℂ _ u X) ⊗ₖ (conjStarAlgAut ℂ _ v Y) := by
  simp only [conjStarAlgAut_apply]
  change ((u : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ (v : Matrix (Fin m) (Fin m) ℂ)) * (X ⊗ₖ Y)
      * star ((u : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ (v : Matrix (Fin m) (Fin m) ℂ))
    = ((u : Matrix (Fin n) (Fin n) ℂ) * X * star (u : Matrix (Fin n) (Fin n) ℂ))
        ⊗ₖ ((v : Matrix (Fin m) (Fin m) ℂ) * Y * star (v : Matrix (Fin m) (Fin m) ℂ))
  rw [star_eq_conjTranspose, conjTranspose_kronecker, Matrix.mul_kronecker_mul,
    Matrix.mul_kronecker_mul, star_eq_conjTranspose, star_eq_conjTranspose]

/-- **Real-exponent Kronecker / CFC power factorization.** For positive semidefinite
matrices `A`, `B`, the `CFC.rpow` real power distributes over the Kronecker product:
`(A ⊗ B) ^ x = A ^ x ⊗ B ^ x`. This is the real-exponent analogue of the
natural-power identity `kronecker_pow`. -/
theorem kronecker_cfcRpow {n m : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {B : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (x : ℝ) :
    (A ⊗ₖ B) ^ x = (A ^ x) ⊗ₖ (B ^ x) := by
  set UA := hA.1.eigenvectorUnitary
  set UB := hB.1.eigenvectorUnitary
  set eA := hA.1.eigenvalues with heA
  set eB := hB.1.eigenvalues with heB
  have hAB_eq : A ⊗ₖ B = conjStarAlgAut ℂ _ (kroneckerUnitary UA UB)
      ((diagonal (fun i => ((eA i : ℝ) : ℂ))) ⊗ₖ (diagonal (fun j => ((eB j : ℝ) : ℂ)))) := by
    rw [conjStarAlgAut_kronecker]
    conv_lhs => rw [hA.1.spectral_theorem, hB.1.spectral_theorem]
    rfl
  have hDD_herm : ((diagonal (fun i => ((eA i : ℝ) : ℂ)))
      ⊗ₖ (diagonal (fun j => ((eB j : ℝ) : ℂ)))).IsHermitian := by
    rw [Matrix.diagonal_kronecker_diagonal]
    exact Matrix.isHermitian_diagonal_of_self_adjoint _ (by
      rw [IsSelfAdjoint]; ext mn; simp)
  rw [CFC.rpow_eq_cfc_real (a := A ⊗ₖ B) (y := x) (hA.kronecker hB).nonneg, hAB_eq,
    cfc_conjStarAlgAut _ hDD_herm (kroneckerUnitary UA UB) (fun t => t ^ x),
    Matrix.diagonal_kronecker_diagonal]
  rw [show (fun mn : Fin n × Fin m => ((eA mn.1 : ℝ) : ℂ) * ((eB mn.2 : ℝ) : ℂ))
      = (fun mn : Fin n × Fin m => (((eA mn.1 * eB mn.2 : ℝ)) : ℂ)) by
    funext mn; push_cast; ring, cfc_diagonal_ofReal]
  rw [show (fun mn : Fin n × Fin m => (((eA mn.1 * eB mn.2) ^ x : ℝ) : ℂ))
      = (fun mn : Fin n × Fin m => ((eA mn.1 ^ x : ℝ) : ℂ) * ((eB mn.2 ^ x : ℝ) : ℂ)) by
    funext mn
    rw [Real.mul_rpow (hA.eigenvalues_nonneg mn.1) (hB.eigenvalues_nonneg mn.2)]
    push_cast; ring]
  rw [← Matrix.diagonal_kronecker_diagonal (fun i => ((eA i ^ x : ℝ) : ℂ))
      (fun j => ((eB j ^ x : ℝ) : ℂ)), conjStarAlgAut_kronecker,
    ← Matrix.PosSemidef.cfcRpow_eq_conjStarAlgAut_diagonal hA x,
    ← Matrix.PosSemidef.cfcRpow_eq_conjStarAlgAut_diagonal hB x]

/-- **Collision-trace factorization at real exponents.** For positive semidefinite
`A, B` (index `Fin n`) and `C, D` (index `Fin m`), the collision trace of the
Kronecker products factorizes:
`tr[(A ⊗ C) ^ a · (B ⊗ D) ^ b] = tr[A ^ a · B ^ b] · tr[C ^ a · D ^ b]`. -/
theorem trace_kronecker_cfcRpow_collision {n m : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℂ} {C D : Matrix (Fin m) (Fin m) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef) (hD : D.PosSemidef)
    (a b : ℝ) :
    (((A ⊗ₖ C) ^ a) * ((B ⊗ₖ D) ^ b)).trace
      = ((A ^ a) * (B ^ b)).trace * ((C ^ a) * (D ^ b)).trace := by
  rw [kronecker_cfcRpow hA hC a, kronecker_cfcRpow hB hD b,
    ← Matrix.mul_kronecker_mul (A ^ a) (B ^ b) (C ^ a) (D ^ b), Matrix.trace_kronecker]

/-- **Collision trace as an eigenprojector double sum.** For positive semidefinite
`A, B` on `Fin n` with eigendata `(eA, u)`, `(eB, v)`, the real-exponent collision
trace expands over the rank-one eigenprojectors:
`tr[A ^ a · B ^ b] = ∑ i ∑ j (eA_i ^ a) · (eB_j ^ b) · tr[|u_i⟩⟨u_i| · |v_j⟩⟨v_j|]`.
This is the operator-trace side of Renner's spectral MGF sum: combined with the
reference/block spectral resolutions it identifies the collision trace with the
eigenvalue/overlap triple sum. -/
lemma trace_cfcRpow_mul_cfcRpow_eq_eigen_double_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) (a b : ℝ) :
    ((A ^ a) * (B ^ b)).trace =
      ∑ i, ∑ j, ((hA.1.eigenvalues i ^ a : ℝ) : ℂ) * ((hB.1.eigenvalues j ^ b : ℝ) : ℂ)
        * (Matrix.vecMulVec ((hA.1.eigenvectorBasis i).ofLp)
              (star ((hA.1.eigenvectorBasis i).ofLp))
            * Matrix.vecMulVec ((hB.1.eigenvectorBasis j).ofLp)
              (star ((hB.1.eigenvectorBasis j).ofLp))).trace := by
  rw [Matrix.PosSemidef.cfcRpow_eq_sum_smul_vecMulVec hA a,
    Matrix.PosSemidef.cfcRpow_eq_sum_smul_vecMulVec hB b, Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.smul_mul, Matrix.mul_sum, Matrix.trace_smul, Matrix.trace_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc]


end Math.SpectralTheory
