import Mathlib.Analysis.Matrix.Order

/-! # Eigenvalues -/


open scoped Matrix ComplexOrder MatrixOrder Kronecker
open Matrix Unitary

namespace Math.SpectralTheory

variable {n m : ℕ}


/-- The non-unital continuous functional calculus of complex matrices (behind `CFC.sqrt`,
`CFC.abs` and the real powers `A ^ (r : ℝ)`): the restriction of the unital calculus
`Matrix.IsHermitian.instContinuousFunctionalCalculus`. It is the instance typeclass search would
find anyway; declaring it here short-circuits that search, which is otherwise slow on matrices
because it first tries, and fails, the restriction of a complex calculus
(`IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus`). -/
instance instNonUnitalContinuousFunctionalCalculusMatrix {ι : Type*} [Fintype ι]
     : NonUnitalContinuousFunctionalCalculus ℝ (Matrix ι ι ℂ) IsSelfAdjoint := by
  classical
  exact
    ContinuousFunctionalCalculus.toNonUnital


/-- Eigenvalues of a Hermitian matrix as a multiset of reals. -/
noncomputable def hermitianEigenvalues {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) : Multiset ℝ :=
  Finset.univ.val.map hA.eigenvalues

/-- Eigenvalues of a Hermitian matrix with product index type. -/
noncomputable def hermitianEigenvaluesProd {n m : ℕ}
    (A : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) (hA : A.IsHermitian) : Multiset ℝ :=
  Finset.univ.val.map hA.eigenvalues

/-- Non-zero eigenvalues of a Hermitian matrix. -/
noncomputable def nonzeroEigenvalues {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) : Multiset ℝ :=
  (hermitianEigenvalues A hA).filter (· ≠ 0)


/-- Helper: If v is an eigenvector of CCᴴ with eigenvalue lam,
then Cᴴv is an eigenvector of CᴴC with the same eigenvalue.

This is the key step in showing eigenspace correspondence. -/
lemma eigenvector_map_conjTranspose (C : Matrix (Fin n) (Fin m) ℂ)
    {v : Fin n → ℂ} {lam : ℂ} :
    (C * Cᴴ) *ᵥ v = lam • v →
    (Cᴴ * C) *ᵥ (Cᴴ *ᵥ v) = lam • (Cᴴ *ᵥ v) := by
  intro hv
  -- Use mulVec_mulVec: M *ᵥ N *ᵥ w = (M * N) *ᵥ w
  have step1 : (Cᴴ * C) *ᵥ (Cᴴ *ᵥ v) = Cᴴ *ᵥ (C *ᵥ (Cᴴ *ᵥ v)) := by
    rw [← mulVec_mulVec]
  have step2 : C *ᵥ (Cᴴ *ᵥ v) = (C * Cᴴ) *ᵥ v := by
    rw [mulVec_mulVec]
  rw [step1, step2, hv, mulVec_smul]

/-- Helper: By symmetry, eigenvectors map in the reverse direction. -/
lemma eigenvector_map_transpose (C : Matrix (Fin n) (Fin m) ℂ)
    {w : Fin m → ℂ} {lam : ℂ} :
    (Cᴴ * C) *ᵥ w = lam • w →
    (C * Cᴴ) *ᵥ (C *ᵥ w) = lam • (C *ᵥ w) := by
  intro hw
  -- Symmetric to eigenvector_map_conjTranspose
  have step1 : (C * Cᴴ) *ᵥ (C *ᵥ w) = C *ᵥ (Cᴴ *ᵥ (C *ᵥ w)) := by
    rw [← mulVec_mulVec]
  have step2 : Cᴴ *ᵥ (C *ᵥ w) = (Cᴴ * C) *ᵥ w := by
    rw [mulVec_mulVec]
  rw [step1, step2, hw, mulVec_smul]

/-- The critical fact: Cᴴv ≠ 0 when v is an eigenvector with non-zero eigenvalue.

Proof by contradiction: if Cᴴv = 0, then CCᴴv = C(Cᴴv) = C(0) = 0 = λv.
But λ ≠ 0 and v ≠ 0, so λv ≠ 0, contradiction. -/
lemma conjTranspose_mulVec_ne_zero_of_eigenvalue_ne_zero
    (C : Matrix (Fin n) (Fin m) ℂ) {v : Fin n → ℂ} {lam : ℂ}
    (hlam : lam ≠ 0) (hv : v ≠ 0) (heigen : (C * Cᴴ) *ᵥ v = lam • v) :
    Cᴴ *ᵥ v ≠ 0 := by
  intro h_contra  -- Assume Cᴴ *ᵥ v = 0
  -- Then (C * Cᴴ) *ᵥ v = C *ᵥ (Cᴴ *ᵥ v) = C *ᵥ 0 = 0
  have h1 : (C * Cᴴ) *ᵥ v = 0 := by
    rw [← mulVec_mulVec, h_contra, mulVec_zero]
  -- But heigen says (C * Cᴴ) *ᵥ v = lam • v, so lam • v = 0
  rw [heigen] at h1
  -- Since lam ≠ 0 and v ≠ 0, this is a contradiction
  have h2 : v = 0 := by
    have : lam⁻¹ • (lam • v) = lam⁻¹ • (0 : Fin n → ℂ) := by rw [h1]
    simp only [smul_zero, inv_smul_smul₀ hlam] at this
    exact this
  exact hv h2

/-- CCᴴ is Hermitian for any matrix C. -/
theorem isHermitian_mul_conjTranspose (C : Matrix (Fin n) (Fin m) ℂ) :
    (C * Cᴴ).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_mul, conjTranspose_conjTranspose]

/-- CᴴC is Hermitian for any matrix C. -/
theorem isHermitian_conjTranspose_mul (C : Matrix (Fin n) (Fin m) ℂ) :
    (Cᴴ * C).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_mul, conjTranspose_conjTranspose]

/-- CCᴴ is positive semidefinite. -/
theorem posSemidef_mul_conjTranspose (C : Matrix (Fin n) (Fin m) ℂ) :
    (C * Cᴴ).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose C

/-- CᴴC is positive semidefinite. -/
theorem posSemidef_conjTranspose_mul (C : Matrix (Fin n) (Fin m) ℂ) :
    (Cᴴ * C).PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self C

/-- The CFC square root of a matrix is Hermitian. -/
lemma cfc_sqrt_conjTranspose_eq {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) :
    (CFC.sqrt P).conjTranspose = CFC.sqrt P := by
  exact ((CFC.sqrt_nonneg (a := P)).posSemidef).isHermitian.eq

/-- **Main theorem**: CCᴴ and CᴴC have the same non-zero eigenvalues.

For any matrix C, the non-zero eigenvalues of CCᴴ equal those of CᴴC
(as multisets, counting multiplicities).

This is fundamental for Schmidt decomposition: if ρ = |ψ⟩⟨ψ| is a pure
bipartite state with coefficient matrix C, then:
- ρ_A = Tr_B(ρ) has the same spectrum as CᴴC
- ρ_B = Tr_A(ρ) has the same spectrum as CCᴴ
- Therefore ρ_A and ρ_B have the same non-zero eigenvalues.

**Proof strategy**: Algebraic approach via eigenspace bijection.

1. Key observation: If CCᴴv = λv with λ ≠ 0, then CᴴC(Cᴴv) = λ(Cᴴv)
   Proof: CᴴC(Cᴴv) = Cᴴ(CCᴴv) = Cᴴ(λv) = λ(Cᴴv)

2. Crucial fact: Cᴴv ≠ 0 when λ ≠ 0
   Proof via inner product: ⟨Cᴴv, Cᴴv⟩ = ⟨v, CCᴴv⟩ = ⟨v, λv⟩ = λ̄⟨v, v⟩
   Since λ ≠ 0 and v ≠ 0, we have ⟨Cᴴv, Cᴴv⟩ ≠ 0, thus Cᴴv ≠ 0

3. This establishes an isomorphism: eigenspace(CCᴴ, λ) ≃ eigenspace(CᴴC, λ) for λ ≠ 0

4. By symmetry (C ↔ Cᴴ), the reverse direction holds

5. Eigenspace dimensions determine multiset multiplicities, so multisets are equal

The proof uses the characteristic-polynomial identity `Matrix.charpoly_mul_comm'`.
After removing the zero roots, the characteristic polynomials have the same roots with
multiplicities, which identifies the nonzero eigenvalue multisets. -/
theorem nonzero_eigenvalues_conjTranspose_mul_eq
    (C : Matrix (Fin n) (Fin m) ℂ) :
    nonzeroEigenvalues (C * Cᴴ) (isHermitian_mul_conjTranspose C) =
    nonzeroEigenvalues (Cᴴ * C) (isHermitian_conjTranspose_mul C) := by
  -- PROOF VIA CHARACTERISTIC POLYNOMIALS
  -- The key insight is charpoly_mul_comm': X^m * charpoly(CCᴴ) = X^n * charpoly(CᴴC)
  -- This means the non-zero roots (with multiplicities) are the same.
  --
  -- Step 1: Get the characteristic polynomial relationship
  have h_charpoly := Matrix.charpoly_mul_comm' C Cᴴ
  -- h_charpoly: X^m * (C * Cᴴ).charpoly = X^n * (Cᴴ * C).charpoly
  --
  -- Step 2: Use roots_charpoly_eq_eigenvalues to connect eigenvalues to roots
  have h_roots_CC := (isHermitian_mul_conjTranspose C).roots_charpoly_eq_eigenvalues
  have h_roots_CtC := (isHermitian_conjTranspose_mul C).roots_charpoly_eq_eigenvalues
  --
  -- PROOF: Show multiset equality by counting each non-zero element
  unfold nonzeroEigenvalues hermitianEigenvalues
  ext a
  by_cases ha : a = 0
  · -- For a = 0: count in filter (· ≠ 0) is 0 on both sides
    subst ha
    simp only [ne_eq, Multiset.count_filter_of_neg, not_true_eq_false, not_false_eq_true]
  · -- For a ≠ 0: use the characteristic polynomial relationship
    simp only [Multiset.count_filter, ne_eq, ha, not_false_eq_true, ↓reduceIte]
    -- The eigenvalues multiset maps through RCLike.ofReal ∘ eigenvalues
    -- count a (map eigenvalues univ) = count (ofReal a) (map ofReal (map eigenvalues univ))
    -- = count (ofReal a) (charpoly.roots) = rootMultiplicity (ofReal a) charpoly
    --
    -- Key relation: map (f ∘ g) s = map f (map g s)
    have h_count_CC : Multiset.count a
        (Finset.univ.val.map (isHermitian_mul_conjTranspose C).eigenvalues) =
        (C * Cᴴ).charpoly.rootMultiplicity (↑a : ℂ) := by
      -- Step 1: count a (map eigenvalues univ) = count (↑a) (map ↑· (map eigenvalues univ))
      have h_step1 : Multiset.count a (Finset.univ.val.map (isHermitian_mul_conjTranspose
          C).eigenvalues) =
          Multiset.count (↑a : ℂ)
            (Multiset.map (fun r : ℝ => (r : ℂ)) (Finset.univ.val.map (isHermitian_mul_conjTranspose
                C).eigenvalues)) :=
        (Multiset.count_map_eq_count' (fun r : ℝ => (r : ℂ)) _ Complex.ofReal_injective a).symm
      -- Step 2: map ↑· (map eigenvalues univ) = map (↑· ∘ eigenvalues) univ
      have h_step2 : Multiset.map (fun r : ℝ => (r : ℂ))
          (Finset.univ.val.map (isHermitian_mul_conjTranspose C).eigenvalues) =
          Multiset.map (RCLike.ofReal ∘ (isHermitian_mul_conjTranspose C).eigenvalues)
              Finset.univ.val := by
        rw [← Multiset.map_map]; rfl
      -- Step 3: map (↑· ∘ eigenvalues) univ = charpoly.roots (by h_roots_CC)
      -- Step 4: count in roots = rootMultiplicity (by Polynomial.count_roots)
      rw [h_step1, h_step2, ← h_roots_CC, Polynomial.count_roots]
    have h_count_CtC : Multiset.count a
        (Finset.univ.val.map (isHermitian_conjTranspose_mul C).eigenvalues) =
        (Cᴴ * C).charpoly.rootMultiplicity (↑a : ℂ) := by
      have h_step1 : Multiset.count a (Finset.univ.val.map (isHermitian_conjTranspose_mul
          C).eigenvalues) =
          Multiset.count (↑a : ℂ)
            (Multiset.map (fun r : ℝ => (r : ℂ)) (Finset.univ.val.map (isHermitian_conjTranspose_mul
                C).eigenvalues)) :=
        (Multiset.count_map_eq_count' (fun r : ℝ => (r : ℂ)) _ Complex.ofReal_injective a).symm
      have h_step2 : Multiset.map (fun r : ℝ => (r : ℂ))
          (Finset.univ.val.map (isHermitian_conjTranspose_mul C).eigenvalues) =
          Multiset.map (RCLike.ofReal ∘ (isHermitian_conjTranspose_mul C).eigenvalues)
              Finset.univ.val := by
        rw [← Multiset.map_map]; rfl
      rw [h_step1, h_step2, ← h_roots_CtC, Polynomial.count_roots]
    rw [h_count_CC, h_count_CtC]
    -- Now show: (C * Cᴴ).charpoly.rootMultiplicity a = (Cᴴ * C).charpoly.rootMultiplicity a
    -- for a ≠ 0, using h_charpoly: X^m * (C * Cᴴ).charpoly = X^n * (Cᴴ * C).charpoly
    have h_a_ne : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    -- For a ≠ 0, a is not a root of X^k, so rootMultiplicity a (X^k) = 0
    have h_not_root_X_pow : ∀ k : ℕ, ¬(Polynomial.X ^ k : Polynomial ℂ).IsRoot (↑a : ℂ) := by
      intro k
      simp only [Polynomial.IsRoot, Polynomial.eval_pow, Polynomial.eval_X]
      exact pow_ne_zero k h_a_ne
    have h_rm_pow_X_ne_zero : ∀ k : ℕ, (Polynomial.X ^ k : Polynomial ℂ).rootMultiplicity (↑a : ℂ) =
        0 := by
      intro k
      exact Polynomial.rootMultiplicity_eq_zero (h_not_root_X_pow k)
    -- Key: X^k ≠ 0 in any nontrivial semiring
    have h_X_pow_ne_zero : ∀ k : ℕ, (Polynomial.X ^ k : Polynomial ℂ) ≠ 0 := by
      intro k
      exact pow_ne_zero k Polynomial.X_ne_zero
    -- Charpoly is nonzero (monic polynomials are nonzero)
    have h_charpoly_ne_zero_CC : (C * Cᴴ).charpoly ≠ 0 :=
      Polynomial.Monic.ne_zero (Matrix.charpoly_monic _)
    have h_charpoly_ne_zero_CtC : (Cᴴ * C).charpoly ≠ 0 :=
      Polynomial.Monic.ne_zero (Matrix.charpoly_monic _)
    -- Product of nonzero polynomials is nonzero
    have h_prod_ne_zero_CC : (Polynomial.X ^ Fintype.card (Fin m) : Polynomial ℂ) * (C *
        Cᴴ).charpoly ≠ 0 :=
      mul_ne_zero (h_X_pow_ne_zero _) h_charpoly_ne_zero_CC
    have h_prod_ne_zero_CtC : (Polynomial.X ^ Fintype.card (Fin n) : Polynomial ℂ) * (Cᴴ *
        C).charpoly ≠ 0 :=
      mul_ne_zero (h_X_pow_ne_zero _) h_charpoly_ne_zero_CtC
    calc (C * Cᴴ).charpoly.rootMultiplicity (↑a : ℂ)
        = 0 + (C * Cᴴ).charpoly.rootMultiplicity (↑a : ℂ) := by ring
      _ = (Polynomial.X ^ Fintype.card (Fin m) : Polynomial ℂ).rootMultiplicity (↑a : ℂ) +
          (C * Cᴴ).charpoly.rootMultiplicity (↑a : ℂ) := by rw [h_rm_pow_X_ne_zero]
      _ = ((Polynomial.X ^ Fintype.card (Fin m) : Polynomial ℂ) * (C *
          Cᴴ).charpoly).rootMultiplicity (↑a : ℂ) := by
            rw [Polynomial.rootMultiplicity_mul h_prod_ne_zero_CC]
      _ = ((Polynomial.X ^ Fintype.card (Fin n) : Polynomial ℂ) * (Cᴴ *
          C).charpoly).rootMultiplicity (↑a : ℂ) := by
            rw [h_charpoly]
      _ = (Polynomial.X ^ Fintype.card (Fin n) : Polynomial ℂ).rootMultiplicity (↑a : ℂ) +
          (Cᴴ * C).charpoly.rootMultiplicity (↑a : ℂ) := by
            rw [Polynomial.rootMultiplicity_mul h_prod_ne_zero_CtC]
      _ = 0 + (Cᴴ * C).charpoly.rootMultiplicity (↑a : ℂ) := by rw [h_rm_pow_X_ne_zero]
      _ = (Cᴴ * C).charpoly.rootMultiplicity (↑a : ℂ) := by ring

/-- Corollary: The multisets of eigenvalues of CCᴴ and CᴴC, when restricted
to non-zero values, are equal. This is stated in terms of the filter operation. -/
theorem eigenvalues_mul_conjTranspose_filter_eq
    (C : Matrix (Fin n) (Fin m) ℂ) :
    (Finset.univ.val.map (isHermitian_mul_conjTranspose C).eigenvalues).filter (· ≠ 0) =
    (Finset.univ.val.map (isHermitian_conjTranspose_mul C).eigenvalues).filter (· ≠ 0) := by
  exact nonzero_eigenvalues_conjTranspose_mul_eq C


end Math.SpectralTheory
