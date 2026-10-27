import QCryptLean.Math.SpectralTheory.Eigenvalues

/-!
# Eigenvalues of Kronecker products

Power sums identify the eigenvalue multiset of a Kronecker product as pairwise products
of the two eigenvalue families.

## Main declarations

Main results include `eigenvalues_kronecker`, `sum_eigenvalues_kronecker`.

## References

See the mathematical references in the declaration docstrings.
-/

open scoped Matrix ComplexOrder MatrixOrder Kronecker
open Matrix Unitary

namespace Math.SpectralTheory

variable {n m : ℕ}


/-- Tensor product (Kronecker product) of Hermitian matrices is Hermitian.

Note: Matrix.kroneckerMap produces Matrix (Fin n × Fin m) (Fin n × Fin m),
not Matrix (Fin (n*m)) (Fin (n*m)). -/
theorem isHermitian_kronecker
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.kroneckerMap (· * ·) A B).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_kronecker, hA.eq, hB.eq]

/-!
### Helper Lemmas for Kronecker Eigenvalues

We establish key properties of Kronecker products that support the eigenvalue theorem.
-/

/-- Power of Kronecker product: (A ⊗ B)^k = A^k ⊗ B^k.

This follows from the mixed-product property: (A ⊗ B)(C ⊗ D) = (AC) ⊗ (BD).
By induction, (A ⊗ B)^k = A^k ⊗ B^k. -/
lemma kronecker_pow
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ) (k : ℕ) :
    (Matrix.kroneckerMap (· * ·) A B) ^ k =
    Matrix.kroneckerMap (· * ·) (A ^ k) (B ^ k) := by
  induction k with
  | zero =>
    simp only [pow_zero]
    -- 1 ⊗ 1 = 1 for the product index type
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [kroneckerMap_apply, one_apply, Prod.mk.injEq]
    by_cases h1 : i₁ = j₁ <;> by_cases h2 : i₂ = j₂ <;> simp [h1, h2]
  | succ k ih =>
    rw [pow_succ, pow_succ, pow_succ, ih]
    -- Use mixed-product property: (A^k ⊗ B^k) * (A ⊗ B) = (A^k * A) ⊗ (B^k * B)
    exact (mul_kronecker_mul (A ^ k) A (B ^ k) B).symm

/-- Trace of Kronecker power: trace((A ⊗ B)^k) = trace(A^k) * trace(B^k).

Combines `kronecker_pow` with `trace_kronecker`. -/
lemma trace_kronecker_pow
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ) (k : ℕ) :
    ((Matrix.kroneckerMap (· * ·) A B) ^ k).trace = (A ^ k).trace * (B ^ k).trace := by
  rw [kronecker_pow, trace_kronecker]

/-- For Hermitian matrices, trace(A^k) = ∑ᵢ λᵢ^k where λᵢ are eigenvalues.

This connects traces to eigenvalue power sums.

**Proof sketch**: Use spectral theorem A = U * diagonal(λ) * Uᴴ, then
(A)^k = U * diagonal(λ)^k * Uᴴ, and trace is invariant under similarity. -/
lemma trace_pow_eq_sum_eigenvalues_pow
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, (hA.eigenvalues i : ℂ) ^ k := by
  -- Use spectral theorem: A = U * D * Uᴴ where D = diagonal(eigenvalues)
  have h_spec := hA.spectral_theorem
  -- Let U = eigenvectorUnitary and D = diagonal(eigenvalues)
  set U := hA.eigenvectorUnitary.val with hU_def
  set D := Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) with hD_def
  -- Spectral theorem: A = U * D * Uᴴ
  have h_A_eq : A = U * D * Uᴴ := by
    rw [hU_def, hD_def]
    -- spectral_theorem uses Unitary.conjStarAlgAut, need to convert
    have h_spec' := h_spec
    simp only [Unitary.conjStarAlgAut_apply] at h_spec'
    exact h_spec'
  -- Show A^k = U * D^k * Uᴴ by induction
  have h_pow_eq : A ^ k = U * D ^ k * Uᴴ := by
    rw [h_A_eq]
    induction k with
    | zero =>
      simp only [pow_zero]
      -- 1 = U * 1 * Uᴴ = U * Uᴴ = 1 (since U is unitary)
      have h_UU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
      rw [Matrix.mul_one, h_UU]
    | succ k ih =>
      rw [pow_succ, ih]
      -- (U * D^k * Uᴴ) * (U * D * Uᴴ) = U * D^k * (Uᴴ * U) * D * Uᴴ
      -- = U * D^k * 1 * D * Uᴴ = U * D^(k+1) * Uᴴ
      have h_UU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
      -- Associate: (U * D^k * Uᴴ) * (U * D * Uᴴ) = U * D^k * (Uᴴ * U) * D * Uᴴ
      rw [← Matrix.mul_assoc, Matrix.mul_assoc (U * D ^ k)]
      -- Now: U * D^k * ((Uᴴ * U) * D * Uᴴ) = U * D^k * (1 * D * Uᴴ) = U * D^k * D * Uᴴ
      rw [← Matrix.mul_assoc Uᴴ, h_UU, Matrix.one_mul]
      -- Now: U * D^k * D * Uᴴ = U * (D^k * D) * Uᴴ = U * D^(k+1) * Uᴴ
      -- Associate D^k and D together, then use pow_succ
      -- Normalize both sides with associativity, then use congr to show D^k * D = D^(k+1)
      simp only [Matrix.mul_assoc] at *
      congr 1
      rw [← Matrix.mul_assoc, ← pow_succ]
  -- trace(A^k) = trace(U * D^k * Uᴴ) = trace(D^k * Uᴴ * U) = trace(D^k)
  have h_trace_eq : (A ^ k).trace = (D ^ k).trace := by
    rw [h_pow_eq]
    -- trace(U * D^k * Uᴴ) = trace(D^k * Uᴴ * U) by trace_mul_cycle
    rw [Matrix.trace_mul_cycle]
    have h_UU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
    rw [h_UU, Matrix.one_mul]
  -- trace(D^k) = ∑ (diagonal entries)^k = ∑ λᵢ^k
  have h_D_trace : (D ^ k).trace = ∑ i, (hA.eigenvalues i : ℂ) ^ k := by
    rw [hD_def]
    -- D^k = diagonal(λ)^k = diagonal(λ^k)
    -- Prove by induction that diagonal(λ)^k = diagonal(λ^k)
    have h_diag_pow : ∀ k, (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) ^ k =
        Matrix.diagonal (fun i => ((hA.eigenvalues i : ℂ)) ^ k) := by
      intro k
      induction k with
      | zero => simp [pow_zero, Matrix.diagonal_one]
      | succ k ih =>
        rw [pow_succ, ih]
        ext i j
        simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
        by_cases h : i = j <;> simp [h, pow_succ]
    rw [h_diag_pow k]
    -- trace(diagonal(λ^k)) = ∑ λᵢ^k
    simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_apply]
    rw [Finset.sum_congr rfl]
    intro i _
    simp
  -- Combine: trace(A^k) = trace(D^k) = ∑ λᵢ^k
  rw [h_trace_eq, h_D_trace]

/-- Power sums of Kronecker eigenvalues equal products of power sums.

For all k: ∑ (eigenvalues of A⊗B)^k = (∑ λᵢ^k)(∑ μⱼ^k)

This follows from:
1. `trace_kronecker_pow`: trace((A ⊗ B)^k) = trace(A^k) * trace(B^k)
2. `trace_pow_eq_sum_eigenvalues_pow`: trace(M^k) = ∑ (eigenvalues)^k

**Key insight**: Since power sums determine multisets (Newton's identities),
this equality of power sums implies the multisets are equal. -/
lemma eigenvalue_power_sum_kronecker
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (k : ℕ) :
    ∑ p : Fin n × Fin m, ((isHermitian_kronecker A B hA hB).eigenvalues p : ℂ) ^ k =
    (∑ i, (hA.eigenvalues i : ℂ) ^ k) * (∑ j, (hB.eigenvalues j : ℂ) ^ k) := by
  -- PROOF STRATEGY:
  -- Step 1: ∑ eigenvalues(A⊗B)^k = trace((A ⊗ B)^k)  [trace_pow_eq_sum_eigenvalues_pow]
  -- Step 2: trace((A ⊗ B)^k) = trace(A^k) * trace(B^k)  [trace_kronecker_pow]
  -- Step 3: trace(A^k) = ∑ λᵢ^k, trace(B^k) = ∑ μⱼ^k  [trace_pow_eq_sum_eigenvalues_pow]
  -- Step 4: Combine to get the result
  -- Step 1: Connect eigenvalue power sum to trace for Kronecker product
  -- The proof is identical to trace_pow_eq_sum_eigenvalues_pow, just with product index type
  set AB := Matrix.kroneckerMap (· * ·) A B with h_AB_def
  have h_kron : AB.IsHermitian := isHermitian_kronecker A B hA hB
  -- Use the same spectral theorem approach as trace_pow_eq_sum_eigenvalues_pow
  -- The structure is identical: AB = U * D * Uᴴ, so AB^k = U * D^k * Uᴴ,
  -- and trace(AB^k) = trace(D^k) = ∑ eigenvalues^k
  have h_lhs : ∑ p : Fin n × Fin m, (h_kron.eigenvalues p : ℂ) ^ k = (AB ^ k).trace := by
    -- Apply the same proof as trace_pow_eq_sum_eigenvalues_pow
    -- The key is that IsHermitian.trace_eq_sum_eigenvalues works for any index type
    -- and the power relationship follows from the spectral theorem in the same way
    have h_spec := h_kron.spectral_theorem
    set U := h_kron.eigenvectorUnitary.val with hU_def
    set D := Matrix.diagonal (fun p => (h_kron.eigenvalues p : ℂ)) with hD_def
    have h_AB_eq : AB = U * D * Uᴴ := by
      rw [hU_def, hD_def]
      simp only [Unitary.conjStarAlgAut_apply] at h_spec
      exact h_spec
    -- Show AB^k = U * D^k * Uᴴ (same proof as trace_pow_eq_sum_eigenvalues_pow)
    have h_pow_eq : AB ^ k = U * D ^ k * Uᴴ := by
      rw [h_AB_eq]
      induction k with
      | zero =>
        simp only [pow_zero]
        have h_UU : U * Uᴴ = 1 := Unitary.coe_mul_star_self h_kron.eigenvectorUnitary
        rw [Matrix.mul_one, h_UU]
      | succ k ih =>
        rw [pow_succ, ih]
        -- Now goal: (U * D^k * Uᴴ) * (U * D * Uᴴ) = U * D^(k+1) * Uᴴ
        -- Note: (U * D * Uᴴ) is already in the goal, no need to rewrite h_AB_eq
        have h_UU : Uᴴ * U = 1 := Unitary.coe_star_mul_self h_kron.eigenvectorUnitary
        -- Associate: (U * D^k * Uᴴ) * (U * D * Uᴴ) = U * D^k * (Uᴴ * U) * D * Uᴴ
        rw [← Matrix.mul_assoc, Matrix.mul_assoc (U * D ^ k)]
        -- Now: U * D^k * ((Uᴴ * U) * D * Uᴴ) = U * D^k * (1 * D * Uᴴ) = U * D^k * D * Uᴴ
        rw [← Matrix.mul_assoc Uᴴ, h_UU, Matrix.one_mul]
        -- Now: U * D^k * D * Uᴴ = U * (D^k * D) * Uᴴ = U * D^(k+1) * Uᴴ
        -- Associate D^k and D together, then use pow_succ
        -- Normalize both sides with associativity, then use congr to show D^k * D = D^(k+1)
        simp only [Matrix.mul_assoc] at *
        congr 1
        rw [← Matrix.mul_assoc, ← pow_succ]
    -- trace(AB^k) = trace(D^k) = ∑ eigenvalues^k
    have h_trace_eq : (AB ^ k).trace = (D ^ k).trace := by
      rw [h_pow_eq, Matrix.trace_mul_cycle]
      have h_UU : Uᴴ * U = 1 := Unitary.coe_star_mul_self h_kron.eigenvectorUnitary
      rw [h_UU, Matrix.one_mul]
    -- trace(D^k) = ∑ (diagonal entries)^k = ∑ eigenvalues^k
    have h_D_trace : (D ^ k).trace = ∑ p : Fin n × Fin m, (h_kron.eigenvalues p : ℂ) ^ k := by
      rw [hD_def]
      -- D^k = diagonal(λ)^k = diagonal(λ^k) (same proof as before)
      have h_diag_pow : ∀ k, (Matrix.diagonal (fun p => (h_kron.eigenvalues p : ℂ))) ^ k =
          Matrix.diagonal (fun p => ((h_kron.eigenvalues p : ℂ)) ^ k) := by
        intro k
        induction k with
        | zero => simp [pow_zero, Matrix.diagonal_one]
        | succ k ih =>
          rw [pow_succ, ih]
          ext p q
          simp only [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply]
          by_cases h : p = q <;> simp [h, pow_succ]
      rw [h_diag_pow k]
      simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_apply]
      rw [Finset.sum_congr rfl]
      intro p _
      simp
    -- Combine: trace(AB^k) = trace(D^k) = ∑ eigenvalues^k
    rw [h_trace_eq, h_D_trace]
  -- Step 2: Trace of Kronecker power equals product of traces
  have h_trace : (AB ^ k).trace = (A ^ k).trace * (B ^ k).trace :=
    trace_kronecker_pow A B k
  -- Step 3: Traces equal eigenvalue power sums
  have h_rhs_A := trace_pow_eq_sum_eigenvalues_pow A hA k
  have h_rhs_B := trace_pow_eq_sum_eigenvalues_pow B hB k
  -- Combine: ∑ ev(A⊗B)^k = trace((A⊗B)^k) = trace(A^k) * trace(B^k) = (∑ λ^k)(∑ μ^k)
  rw [h_lhs, h_trace, h_rhs_A, h_rhs_B]

/-- **Tensor product eigenvalue theorem**: the eigenvalue multiset of the Kronecker product
`A ⊗ B` of Hermitian matrices equals the multiset of pairwise products `λᵢ · μⱼ` of the
eigenvalues of `A` and `B`.

Proved via the spectral decompositions `A = U_A · diag(λ_A) · U_Aᴴ`,
`B = U_B · diag(λ_B) · U_Bᴴ`: the Kronecker product `U_A ⊗ U_B` is unitary and conjugates
`A ⊗ B` to `diag(λ_A) ⊗ diag(λ_B) = diag(λ_A,i · λ_B,j)` (`Matrix.diagonal_kronecker_diagonal`),
so `A ⊗ B` and this diagonal matrix are similar and hence share a characteristic polynomial;
reading off the roots of both sides gives the eigenvalue multiset equality. -/
lemma eigenvalue_kronecker_multiset_eq {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Finset.univ : Finset (Fin n × Fin m)).val.map
      (fun k => (isHermitian_kronecker A B hA hB).eigenvalues k) =
    (Finset.univ : Finset (Fin n × Fin m)).val.map
      (fun ⟨i, j⟩ => hA.eigenvalues i * hB.eigenvalues j) := by
  -- PROOF VIA CHARACTERISTIC POLYNOMIALS
  -- Strategy: Show the charpolys of A⊗B and diagonal(products) are equal,
  -- which implies their eigenvalue multisets (via roots) are equal.
  --
  -- Let's abbreviate notation
  set AB := kroneckerMap (· * ·) A B with hAB_def
  set hAB := isHermitian_kronecker A B hA hB with hAB_herm_def
  -- Diagonal matrices from spectral theorem
  set D_A := diagonal ((fun r : ℝ => (r : ℂ)) ∘ hA.eigenvalues) with hD_A_def
  set D_B := diagonal ((fun r : ℝ => (r : ℂ)) ∘ hB.eigenvalues) with hD_B_def
  set D_AB := diagonal (fun p : Fin n × Fin m =>
    (hA.eigenvalues p.1 : ℂ) * (hB.eigenvalues p.2 : ℂ)) with hD_AB_def
  -- Unitary matrices from spectral theorem
  set U_A := hA.eigenvectorUnitary.val with hU_A_def
  set U_B := hB.eigenvectorUnitary.val with hU_B_def
  -- Step: D_A ⊗ D_B = D_AB (diagonal of products)
  have h_diag_kron : kroneckerMap (· * ·) D_A D_B = D_AB := by
    rw [hD_A_def, hD_B_def, hD_AB_def, diagonal_kronecker_diagonal]; rfl
  -- Spectral decompositions
  have h_A_spec : A = U_A * D_A * U_A.conjTranspose := by
    have h := hA.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at h; exact h
  have h_B_spec : B = U_B * D_B * U_B.conjTranspose := by
    have h := hB.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply] at h; exact h
  -- A⊗B = (U_A⊗U_B) * (D_A⊗D_B) * (U_Aᴴ⊗U_Bᴴ)
  have h_AB_decomp : AB = kroneckerMap (· * ·) U_A U_B *
      kroneckerMap (· * ·) D_A D_B *
      kroneckerMap (· * ·) U_A.conjTranspose U_B.conjTranspose := by
    rw [hAB_def, h_A_spec, h_B_spec, mul_kronecker_mul, mul_kronecker_mul]
  have h_star_left : (kroneckerMap (· * ·) U_A U_B).conjTranspose *
      kroneckerMap (· * ·) U_A U_B = 1 := by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul]
    have hU_A' : U_A.conjTranspose * U_A = 1 :=
      Unitary.coe_star_mul_self hA.eigenvectorUnitary
    have hU_B' : U_B.conjTranspose * U_B = 1 :=
      Unitary.coe_star_mul_self hB.eigenvectorUnitary
    rw [hU_A', hU_B', one_kronecker_one]
  -- Cyclic invariance of the characteristic polynomial cancels the unitary factors.
  have h_charpoly_eq : AB.charpoly = D_AB.charpoly := by
    rw [h_AB_decomp, h_diag_kron, ← conjTranspose_kronecker, charpoly_mul_comm,
      ← Matrix.mul_assoc, h_star_left, one_mul]
  -- D_AB is Hermitian (diagonal with real entries on diagonal)
  have h_D_AB_herm : D_AB.IsHermitian := by
    rw [hD_AB_def, isHermitian_diagonal_iff]
    intro ⟨i, j⟩
    -- Need: IsSelfAdjoint ((hA.eigenvalues i : ℂ) * (hB.eigenvalues j : ℂ))
    -- star (x * y) = star x * star y, and for real r, star (r : ℂ) = r
    simp only [IsSelfAdjoint, star_mul', RCLike.star_def, Complex.conj_ofReal]
  -- Use roots_charpoly_eq_eigenvalues
  have h_roots_AB := hAB.roots_charpoly_eq_eigenvalues
  have h_roots_D_AB := h_D_AB_herm.roots_charpoly_eq_eigenvalues
  -- Equal charpolys → equal roots
  have h_roots_eq : Multiset.map ((RCLike.ofReal (K := ℂ)) ∘ hAB.eigenvalues) Finset.univ.val =
      Multiset.map ((RCLike.ofReal (K := ℂ)) ∘ h_D_AB_herm.eigenvalues) Finset.univ.val := by
    rw [← h_roots_AB, ← h_roots_D_AB, h_charpoly_eq]
  -- By injectivity of ofReal
  have h_inj : Function.Injective (RCLike.ofReal (K := ℂ)) := RCLike.ofReal_injective
  have h_eigenvalues_eq : Finset.univ.val.map hAB.eigenvalues =
      Finset.univ.val.map h_D_AB_herm.eigenvalues := by
    apply Multiset.map_injective h_inj
    simp only [Multiset.map_map] at h_roots_eq ⊢; exact h_roots_eq
  -- For diagonal matrix D_AB, eigenvalues = diagonal entries (as multiset)
  have h_D_AB_charpoly : D_AB.charpoly = ∏ p : Fin n × Fin m,
      (Polynomial.X - Polynomial.C ((hA.eigenvalues p.1 : ℂ) * (hB.eigenvalues p.2 : ℂ))) := by
    rw [hD_AB_def, charpoly_diagonal]
  have h_D_AB_roots : D_AB.charpoly.roots = Finset.univ.val.map
      (fun p : Fin n × Fin m => (hA.eigenvalues p.1 : ℂ) * (hB.eigenvalues p.2 : ℂ)) := by
    rw [h_D_AB_charpoly]
    have h := Polynomial.roots_prod
      (fun p : Fin n × Fin m => Polynomial.X - Polynomial.C ((hA.eigenvalues p.1 : ℂ) *
          (hB.eigenvalues p.2 : ℂ)))
      Finset.univ
    have hne : ∏ p : Fin n × Fin m, (Polynomial.X - Polynomial.C ((hA.eigenvalues p.1 : ℂ) *
        (hB.eigenvalues p.2 : ℂ))) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_; intros; exact Polynomial.X_sub_C_ne_zero _
    specialize h hne
    simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton] at h
    exact h
  have h_diag_ev : Finset.univ.val.map h_D_AB_herm.eigenvalues =
      Finset.univ.val.map (fun (p : Fin n × Fin m) => hA.eigenvalues p.1 * hB.eigenvalues p.2) := by
    -- h_roots_D_AB : D_AB.charpoly.roots = Multiset.map (RCLike.ofReal ∘ h_D_AB_herm.eigenvalues)
    -- Finset.univ.val
    -- h_D_AB_roots : D_AB.charpoly.roots = Finset.univ.val.map (fun p => (hA.eigenvalues p.1 : ℂ) *
    -- (hB.eigenvalues p.2 : ℂ))
    -- First, show the complex products equal the ofReal of real products
    have h_products_real : ∀ p : Fin n × Fin m,
        (hA.eigenvalues p.1 : ℂ) * (hB.eigenvalues p.2 : ℂ) =
        RCLike.ofReal (hA.eigenvalues p.1 * hB.eigenvalues p.2) := fun p =>
      (Complex.ofReal_mul _ _).symm
    -- Now combine the two characterizations of D_AB.charpoly.roots
    have h_eq : Multiset.map ((RCLike.ofReal (K := ℂ)) ∘ h_D_AB_herm.eigenvalues) Finset.univ.val =
        Multiset.map (fun p : Fin n × Fin m => (RCLike.ofReal (K := ℂ)) (hA.eigenvalues p.1 *
            hB.eigenvalues p.2)) Finset.univ.val := by
      rw [← h_roots_D_AB, h_D_AB_roots]
      congr 1; ext p; exact h_products_real p
    have h_eq' : Multiset.map (RCLike.ofReal (K := ℂ)) (Multiset.map h_D_AB_herm.eigenvalues
        Finset.univ.val) =
        Multiset.map (RCLike.ofReal (K := ℂ)) (Multiset.map (fun (p : Fin n × Fin m) =>
            hA.eigenvalues p.1 * hB.eigenvalues p.2) Finset.univ.val) := by
      simp only [Multiset.map_map]; exact h_eq
    exact Multiset.map_injective h_inj h_eq'
  rw [h_eigenvalues_eq, h_diag_ev]

/-- **Tensor product eigenvalue theorem**: If A has eigenvalues {λᵢ} and B has
eigenvalues {μⱼ}, then A ⊗ B has eigenvalues {λᵢ · μⱼ}. See eigenvalue_kronecker_multiset_eq
for the proof justification. -/
theorem eigenvalues_kronecker
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    hermitianEigenvaluesProd (Matrix.kroneckerMap (· * ·) A B) (isHermitian_kronecker A B hA hB) =
    (hermitianEigenvalues A hA).bind (fun ev_a =>
      (hermitianEigenvalues B hB).map (· * ev_a)) := by
  -- Use eigenvalue_kronecker_multiset_eq and show the bind form equals the map form
  unfold hermitianEigenvaluesProd hermitianEigenvalues
  -- LHS: Finset.univ.val.map (kronecker.eigenvalues)
  -- RHS: (univ.val.map hA.eigenvalues).bind (λ a => (univ.val.map hB.eigenvalues).map (· * a))
  -- By eigenvalue_kronecker_multiset_eq:
  --   LHS = univ.val.map (λ ⟨i,j⟩ => hA.eigenvalues i * hB.eigenvalues j)
  -- We need: (map f).bind (λ a => (map g).map (· * a)) = map (λ ⟨i,j⟩ => f i * g j) (for products)
  rw [eigenvalue_kronecker_multiset_eq A B hA hB]
  -- Now need: map (λ ⟨i,j⟩ => λ_i * μ_j) univ = (map λ).bind (λ a => (map μ).map (· * a))
  -- Prove this by rewriting the RHS
  symm
  rw [← Finset.univ_product_univ, Finset.product_val]
  -- Now have: univ.val ×ˢ univ.val which is Multiset.product
  change ((Multiset.map hA.eigenvalues Finset.univ.val).bind fun ev_a =>
      Multiset.map (fun x => x * ev_a) (Multiset.map hB.eigenvalues Finset.univ.val)) =
    Multiset.map (fun x => match x with | (i, j) => hA.eigenvalues i * hB.eigenvalues j)
      (Multiset.product Finset.univ.val Finset.univ.val)
  rw [Multiset.product.eq_1, Multiset.map_bind, Multiset.bind_map]
  simp only [Multiset.map_map, Function.comp_apply]
  congr 1
  ext i
  rw [show (fun x : Fin m => hB.eigenvalues x * hA.eigenvalues i) =
      (fun x : Fin m => hA.eigenvalues i * hB.eigenvalues x) from
      funext (fun x => mul_comm (hB.eigenvalues x) (hA.eigenvalues i))]

/-- Sum over eigenvalues of a Kronecker product equals the double sum over the factor
eigenvalues: `∑ₖ f(eigenvalue_k(A⊗B)) = ∑ᵢ ∑ⱼ f(λᵢ · μⱼ)`, for any `f : ℝ → ℝ`.

Immediate from the multiset equality `eigenvalue_kronecker_multiset_eq`: summing the same
function over equal multisets gives equal sums. Used in proving entropy additivity; see also
`InfoTheory.VonNeumannEntropy.vonNeumannEntropy_tensor_additive`. -/
theorem sum_eigenvalues_kronecker
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f : ℝ → ℝ) :
    ∑ k : Fin n × Fin m, f ((isHermitian_kronecker A B hA hB).eigenvalues k) =
    ∑ i : Fin n, ∑ j : Fin m, f (hA.eigenvalues i * hB.eigenvalues j) := by
  -- Use eigenvalue_kronecker_multiset_eq to equate the multisets
  have h_eq := eigenvalue_kronecker_multiset_eq A B hA hB
  -- Convert RHS from double sum to single sum over product type
  rw [← Fintype.sum_prod_type']
  -- Now both sides are single sums over Fin n × Fin m
  -- LHS: ∑ k, f(eigenvalues k)
  -- RHS: ∑ k, f(λ_k.1 * μ_k.2)
  -- Convert to Multiset.sum form
  rw [← Finset.sum_map_val, ← Finset.sum_map_val]
  -- Now show: map (f ∘ eigenvalues) univ = map (f ∘ product) univ
  congr 1
  -- Use the fact that if two multisets s and t are equal,
  -- then map g s = map g t
  have h_map : ∀ (g : ℝ → ℝ) (s t : Multiset ℝ), s = t → Multiset.map g s = Multiset.map g t := by
    intros g s t h; rw [h]
  -- Rewrite using h_eq
  conv_lhs => rw [show (fun k => f ((isHermitian_kronecker A B hA hB).eigenvalues k)) =
      f ∘ (fun k => (isHermitian_kronecker A B hA hB).eigenvalues k) from rfl]
  conv_rhs => rw [show (fun x : Fin n × Fin m => f (hA.eigenvalues x.1 * hB.eigenvalues x.2)) =
      f ∘ (fun x : Fin n × Fin m => hA.eigenvalues x.1 * hB.eigenvalues x.2) from rfl]
  simp only [← Multiset.map_map]
  rw [h_eq]

/-!
## Rank Equalities (Available from Mathlib)

These are already in Mathlib and confirm that CCᴴ and CᴴC have the same rank:
- `Matrix.rank_conjTranspose_mul_self`
- `Matrix.rank_self_mul_conjTranspose`

The rank equals the number of non-zero eigenvalues, which is consistent with
our theorem `nonzero_eigenvalues_conjTranspose_mul_eq`.
-/

/-!
## Entry-wise Conjugation Preserves Eigenvalues for Hermitian Matrices

For Hermitian matrices, entry-wise conjugation (M.map star) preserves eigenvalues
because it equals the transpose (which preserves the characteristic polynomial).
-/


end Math.SpectralTheory
