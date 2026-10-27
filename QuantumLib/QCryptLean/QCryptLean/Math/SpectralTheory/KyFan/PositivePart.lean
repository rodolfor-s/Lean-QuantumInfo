import Mathlib.Analysis.Matrix.Order
import QCryptLean.Math.LinearAlgebra.SubmoduleDimension
import QCryptLean.Math.SpectralTheory.KyFan.Basic
import QCryptLean.Math.SpectralTheory.Rayleigh

/-!
# Spectral Theory: Ky Fan positive-part bounds

Positive-part bounds derived from the Ky Fan variational theory, including the
Wielandt minimax achievability lemma, per-eigenvalue Rayleigh witnesses, and
the positive-part comparison used downstream in Weyl- and Lieb-Thirring-type
arguments.

## Main statements

- `exists_restrictedTrace_eq_sum_eigenvalues₀`: achievability for sums over an
  arbitrary eigenvalue subset
- `exists_unit_le_re_dotProduct_mulVec_and_le`: simultaneous lower/upper Rayleigh witness for a
fixed
  eigenvalue index
- `eigenvalues₀_le_add_of_posSemidef`: Weyl monotonicity under PSD perturbations
- `sum_max_eigenvalues₀_sub_le`: positive-part bound in `eigenvalues₀` form
- `sum_max_eigenvalues_sub_le`: positive-part bound in `eigenvalues` form

The Ky Fan positive part bound is a key consequence of the Ky Fan upper bound.
It states that eigenvalue differences are weakly majorized by eigenvalues of the
difference matrix, which combined with trace equality implies a bound on positive parts.

**Mathematical content**:
If A, B are Hermitian with eigenvalues λᵢ(A), λᵢ(B) (sorted descending), and A - B has
eigenvalues μᵢ, then:
  ∑ max(0, λᵢ(A) - λᵢ(B)) ≤ ∑ max(0, μᵢ)

**Proof strategy** (3 ingredients):
1. **Positive part identity**: ∑ max(0, xᵢ) = (∑|xᵢ| + ∑xᵢ) / 2
2. **Trace equality**: ∑ (λᵢ(A) - λᵢ(B)) = ∑ λᵢ(A-B) (from trace additivity)
3. **Lidskii-Mirsky inequality**: ∑|λᵢ(A) - λᵢ(B)| ≤ ∑|λᵢ(A-B)|
Combining: ∑ max(0, dᵢ) = (∑|dᵢ| + ∑dᵢ)/2 ≤ (∑|cᵢ| + ∑cᵢ)/2 = ∑ max(0, cᵢ)

**Reference**: Horn & Johnson, "Matrix Analysis" (2nd ed), Theorem 4.3.45.
-/

open scoped Matrix ComplexOrder
open Matrix

namespace Math.SpectralTheory

/-- Positive part identity for finite sums: ∑ max(0, xᵢ) = (∑|xᵢ| + ∑xᵢ) / 2.
    Follows from the pointwise identity max(0, x) = (|x| + x) / 2. -/
lemma sum_max_zero_eq_add_sum_div_two {n : ℕ} (x : Fin n → ℝ) :
    ∑ i, max 0 (x i) = (∑ i, |x i| + ∑ i, x i) / 2 := by
  have h : ∀ i, max 0 (x i) = (|x i| + x i) / 2 := by
    intro i
    simp only [abs_eq_max_neg, max_def]
    split_ifs <;> linarith
  simp_rw [h]
  rw [← Finset.sum_div, Finset.sum_add_distrib]

/-- **Wielandt minimax: achievability direction.** For Hermitian M and a subset
    S ⊆ Fin (card (Fin n)) with |S| = k ≤ n, there exists a rank-k orthogonal
    projection P such that Tr(PMP).re = ∑_{i∈S} λᵢ(M).

    Proof sketch: Let P be the projection onto the span of M's eigenvectors
    indexed by S (via eigenvectorBasis). Then PMP restricted to im(P) is diagonal
    with entries {λᵢ(M) : i ∈ S}, and the trace is their sum.

    This is the "achievability" half of the Wielandt minimax formula. -/
lemma exists_restrictedTrace_eq_sum_eigenvalues₀ {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian)
    (S : Finset (Fin (Fintype.card (Fin n)))) (_hS : S.card ≤ n) :
    ∃ (P : Matrix (Fin n) (Fin n) ℂ),
      P * P = P ∧ P.IsHermitian ∧ Matrix.rank P = S.card ∧
      (restrictedTrace M P).re = ∑ i ∈ S, hM.eigenvalues₀ i := by
  -- Spectral decomposition: M = U * D * Uᴴ where D = diag(eigenvalues)
  have h_spec := hM.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h_spec
  let U := hM.eigenvectorUnitary.val
  let D := Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues : Fin n → ℂ)
  have h_M_eq : M = U * D * Uᴴ := h_spec
  have h_UU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hM.eigenvectorUnitary
  have h_UU' : Uᴴ * U = 1 := Unitary.coe_star_mul_self hM.eigenvectorUnitary
  -- Map S from Fin (Fintype.card (Fin n)) to Fin n via ftcEquiv
  let σ := eigenPerm n
  -- Selection function: sel(i) = 1 if the ftcEquiv-image of σ(i) is in S, else 0
  let sel : Fin n → ℂ := fun i => if ftcEquiv n (σ i) ∈ S then 1 else 0
  let Pk : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal sel
  let P := U * Pk * Uᴴ
  use P
  -- Pk is idempotent (0/1 diagonal)
  have hPk_idem : Pk * Pk = Pk := by
    rw [Matrix.diagonal_mul_diagonal]; congr; funext i
    simp only [sel]; by_cases h : ftcEquiv n (σ i) ∈ S <;> simp [h]
  -- Pk is Hermitian (real diagonal)
  have hPk_herm : Pkᴴ = Pk := by
    rw [Matrix.diagonal_conjTranspose]; congr; funext i
    simp only [sel]; by_cases h : ftcEquiv n (σ i) ∈ S <;> simp [h, star_one, star_zero]
  constructor
  -- 1. P * P = P
  · calc (U * Pk * Uᴴ) * (U * Pk * Uᴴ)
        = U * Pk * (Uᴴ * U) * Pk * Uᴴ := by noncomm_ring
      _ = U * Pk * 1 * Pk * Uᴴ := by rw [h_UU']
      _ = U * (Pk * Pk) * Uᴴ := by noncomm_ring
      _ = U * Pk * Uᴴ := by rw [hPk_idem]
  constructor
  -- 2. P.IsHermitian
  · change (U * Pk * Uᴴ)ᴴ = U * Pk * Uᴴ
    calc (U * Pk * Uᴴ)ᴴ
        = Uᴴᴴ * Pkᴴ * Uᴴ := by
          simp only [Matrix.conjTranspose_mul]; rw [Matrix.mul_assoc]
      _ = U * Pkᴴ * Uᴴ := by rw [Matrix.conjTranspose_conjTranspose]
      _ = U * Pk * Uᴴ := by rw [hPk_herm]
  constructor
  -- 3. rank P = S.card
  · have hPk_rank : Pk.rank = S.card := by
      calc
        Pk.rank = (Finset.univ.filter (fun i : Fin n => ftcEquiv n (σ i) ∈ S)).card := by
          simpa [Pk] using
            (rank_diagonal_indicator (n := n) (p := fun i : Fin n => ftcEquiv n (σ i) ∈ S))
        _ = (S.map ((ftcEquiv n).symm.trans σ.symm).toEmbedding).card := by
          rw [show Finset.univ.filter (fun i : Fin n => ftcEquiv n (σ i) ∈ S) =
            S.map ((ftcEquiv n).symm.trans σ.symm).toEmbedding from by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
              Equiv.toEmbedding, Function.Embedding.coeFn_mk, Equiv.trans_apply]
            constructor
            · intro h
              exact ⟨ftcEquiv n (σ i), h, by simp⟩
            · rintro ⟨j, hj, hjj⟩
              have : i = σ.symm ((ftcEquiv n).symm j) := hjj.symm
              rw [this]
              simp [hj]]
        _ = S.card := by rw [Finset.card_map]
    rw [← hPk_rank]
    exact rank_unitary_conj U h_UU h_UU' Pk
  -- 4. Tr(PMP).re = ∑ i ∈ S, hM.eigenvalues₀ i
  · have h1 : restrictedTrace M P = (Pk * D * Pk).trace :=
      restrictedTrace_unitary_conj_diagonal U Pk D M h_M_eq h_UU'
    -- Pk * D * Pk is diagonal with entries sel(i) * eigenvalues(i) * sel(i)
    have h2 : (Pk * D * Pk).trace =
        (Matrix.diagonal (fun i =>
          (sel i * (hM.eigenvalues i : ℂ) * sel i))).trace := by
      congr 1; simp only [Pk, D]
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
    have h3 : ((Matrix.diagonal (fun i =>
        (sel i * (hM.eigenvalues i : ℂ) * sel i))).trace).re =
        ∑ i : Fin n,
          (if ftcEquiv n (σ i) ∈ S then hM.eigenvalues i else 0) := by
      rw [Matrix.trace_diagonal, Complex.re_sum]
      congr 1; ext i; simp only [sel]
      split_ifs <;> simp
    -- Rewrite eigenvalues as eigenvalues₀Fin ∘ eigenPerm
    have h_ev_perm := eigenvalues_eq_eigenvalues₀Fin_comp M hM
    have h4 : ∑ i : Fin n,
        (if ftcEquiv n (σ i) ∈ S then hM.eigenvalues i else 0) =
        ∑ i : Fin n,
          (if ftcEquiv n (σ i) ∈ S
           then Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin M hM (σ i) else 0) := by
      apply Finset.sum_congr rfl; intro i _
      split_ifs with h
      · exact h_ev_perm i
      · rfl
    -- Reindex through σ: sum over {i | ftcEquiv(σ(i)) ∈ S} = sum over {j | ftcEquiv(j) ∈ S}
    have h5 : ∑ i : Fin n,
        (if ftcEquiv n (σ i) ∈ S
         then Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin M hM (σ i) else 0) =
        ∑ j : Fin n,
          (if ftcEquiv n j ∈ S
           then Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin M hM j else 0) := by
      let f : Fin n → ℝ := fun j =>
        if ftcEquiv n j ∈ S then Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin M hM j else 0
      change ∑ i, f (σ i) = ∑ j, f j
      exact Equiv.sum_comp σ f
    -- eigenvalues₀Fin j = eigenvalues₀ (ftcEquiv j)
    have h6 : ∑ j : Fin n,
        (if ftcEquiv n j ∈ S then Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin M hM j else 0) =
        ∑ j : Fin n,
          (if ftcEquiv n j ∈ S then hM.eigenvalues₀ (ftcEquiv n j) else 0) := by
      apply Finset.sum_congr rfl; intro j _
      split_ifs <;> [exact rfl; rfl]
    -- Reindex through ftcEquiv: sum over {j : Fin n | ftcEquiv j ∈ S} = ∑ i ∈ S, eigenvalues₀ i
    have h7 : ∑ j : Fin n,
        (if ftcEquiv n j ∈ S then hM.eigenvalues₀ (ftcEquiv n j) else 0) =
        ∑ i ∈ S, hM.eigenvalues₀ i := by
      rw [← Finset.sum_filter]
      rw [show Finset.univ.filter (fun j : Fin n => ftcEquiv n j ∈ S) =
        S.map (ftcEquiv n).symm.toEmbedding from by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_map, Equiv.toEmbedding, Function.Embedding.coeFn_mk]
        constructor
        · intro h; exact ⟨ftcEquiv n j, h, by simp⟩
        · rintro ⟨i, hi, rfl⟩; simp [hi]]
      rw [Finset.sum_map]; congr 1
    rw [h1, h2, h3, h4, h5, h6, h7]

/-- Linearity of restricted trace: Tr(P(A+B)P) = Tr(PAP) + Tr(PBP). -/
lemma restrictedTrace_add {n : ℕ} (A B P : Matrix (Fin n) (Fin n) ℂ) :
    restrictedTrace (A + B) P = restrictedTrace A P + restrictedTrace B P := by
  unfold restrictedTrace
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]

/-- **Per-eigenvalue Rayleigh bound via subspace intersection.**
    For each eigenvalue index s, there exists a unit vector x satisfying both:
    - ⟨x, (M₁+M₂)x⟩.re ≥ λ_s(M₁+M₂) (lower Rayleigh bound from eigenvecSpanFirst)
    - ⟨x, M₁ x⟩.re ≤ λ_s(M₁) (upper Rayleigh bound from eigenvecSpanFrom)

    Proof: Let V = eigenvecSpanFirst(M₁+M₂, s+1) with dim = s+1, and
    W = eigenvecSpanFrom(M₁, s) with dim = n-s. By sub_le_finrank_inf,
    dim(V ∩ W) ≥ (s+1) + (n-s) - n = 1. Pick nonzero x₀ ∈ V ∩ W,
    normalize to get unit x. Apply eigenvalues₀_le_re_dotProduct_mulVec_of_mem and
    re_dotProduct_mulVec_le_eigenvalues₀_of_mem.

    Reference: Wielandt (1955), key building block. -/
lemma exists_unit_le_re_dotProduct_mulVec_and_le {n : ℕ} [NeZero n]
    (M₁ M₁₂ : Matrix (Fin n) (Fin n) ℂ)
    (hM₁ : M₁.IsHermitian) (hM₁₂ : M₁₂.IsHermitian)
    (s : Fin n) :
    ∃ (x : Fin n → ℂ),
      (dotProduct (star x) x).re = 1 ∧
      (dotProduct (star x) (M₁₂.mulVec x)).re ≥
        hM₁₂.eigenvalues₀ ⟨s.val, by rw [Fintype.card_fin]; exact s.isLt⟩ ∧
      (dotProduct (star x) (M₁.mulVec x)).re ≤
        hM₁.eigenvalues₀ ⟨s.val, by rw [Fintype.card_fin]; exact s.isLt⟩ := by
  -- Step 1: Define the two subspaces
  have hs_lt : s.val < n := s.isLt
  have hs_succ_le : s.val + 1 ≤ n := by omega
  let V := Math.LinearAlgebra.SubmoduleDim.eigenvecSpanFirst₀ M₁₂ hM₁₂ (s.val + 1) hs_succ_le
  let W := Math.LinearAlgebra.SubmoduleDim.eigenvecSpanFrom₀ M₁ hM₁ s
  -- Step 2: Compute dimensions
  have hV_dim : Module.finrank ℂ V = s.val + 1 :=
    Math.LinearAlgebra.SubmoduleDim.finrank_eigenvecSpanFirst₀ M₁₂ hM₁₂ (s.val + 1) hs_succ_le
  have hW_dim : Module.finrank ℂ W = n - s.val :=
    Math.LinearAlgebra.SubmoduleDim.finrank_eigenvecSpanFrom₀ M₁ hM₁ s
  -- Step 3: Dimension of intersection ≥ 1
  have hdim_amb : Module.finrank ℂ (Fin n → ℂ) = n := Module.finrank_fin_fun ℂ
  have h_inf_ge := Math.LinearAlgebra.SubmoduleDim.sub_le_finrank_inf ℂ (Fin n → ℂ) hdim_amb V W
  have h_inf_pos : 1 ≤ Module.finrank ℂ ↥(V ⊓ W) := by
    rw [hV_dim, hW_dim] at h_inf_ge; omega
  -- Step 4: Get nonzero element from intersection
  have h_ne_bot : (V ⊓ W) ≠ ⊥ := by
    rwa [← Submodule.one_le_finrank_iff]
  obtain ⟨x₀, hx₀_mem, hx₀_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h_ne_bot
  -- Step 5: Normalize to get unit vector
  let x := Math.LinearAlgebra.SubmoduleDim.normalizeVec x₀ hx₀_ne
  use x
  have hx_unit : (dotProduct (star x) x).re = 1 :=
    Math.LinearAlgebra.SubmoduleDim.normalizeVec_unit x₀ hx₀_ne
  -- Step 6: x₀ ∈ V ⊓ W means x₀ ∈ V and x₀ ∈ W
  have hx₀_V : x₀ ∈ V := (Submodule.mem_inf.mp hx₀_mem).1
  have hx₀_W : x₀ ∈ W := (Submodule.mem_inf.mp hx₀_mem).2
  -- Step 7: normalizeVec preserves submodule membership (scalar multiple)
  have hx_eq : x = (↑(Real.sqrt (Math.LinearAlgebra.SubmoduleDim.vecNormSq x₀))⁻¹ : ℂ) • x₀ := by
    simp only [x, Math.LinearAlgebra.SubmoduleDim.normalizeVec,
      Math.LinearAlgebra.SubmoduleDim.vecNormSq]
    rfl
  have hx_V : x ∈ V := by rw [hx_eq]; exact V.smul_mem _ hx₀_V
  have hx_W : x ∈ W := by rw [hx_eq]; exact W.smul_mem _ hx₀_W
  -- Step 8: Apply Rayleigh bounds
  refine ⟨hx_unit, ?_, ?_⟩
  · -- Lower bound: x ∈ V = eigenvecSpanFirst₀(M₁₂, s+1) → ⟨x, M₁₂ x⟩.re ≥ λ_s(M₁₂)
    have h_lb := Math.LinearAlgebra.SubmoduleDim.eigenvalues₀_le_re_dotProduct_mulVec_of_mem M₁₂
      hM₁₂ (s.val + 1)
      (by omega) hs_succ_le x hx_V hx_unit
    -- eigenvalues₀_le_re_dotProduct_mulVec_of_mem gives ≥ eigenvalues₀ ⟨(s+1)-1, ...⟩ =
    -- eigenvalues₀ ⟨s, ...⟩
    simpa only [Nat.add_sub_cancel] using h_lb
  · -- Upper bound: x ∈ W = eigenvecSpanFrom₀(M₁, s) → ⟨x, M₁ x⟩.re ≤ λ_s(M₁)
    exact Math.LinearAlgebra.SubmoduleDim.re_dotProduct_mulVec_le_eigenvalues₀_of_mem M₁ hM₁ s x
      hx_W hx_unit

/-- **Weyl monotonicity**: Adding a positive semidefinite matrix can only increase
    eigenvalues. If D is PSD, then eigenvalues₀(M)(k) ≤ eigenvalues₀(M + D)(k).

    Proof: Apply exists_unit_le_re_dotProduct_mulVec_and_le with M₁ = M+D, M₁₂ = M to get a unit
    vector x
    satisfying xᴴMx ≥ λₖ(M) and xᴴ(M+D)x ≤ λₖ(M+D). Since D ≥ 0, xᴴDx ≥ 0, so
    λₖ(M) ≤ xᴴMx ≤ xᴴMx + xᴴDx = xᴴ(M+D)x ≤ λₖ(M+D). -/
lemma eigenvalues₀_le_add_of_posSemidef {n : ℕ} [NeZero n]
    (M D : Matrix (Fin n) (Fin n) ℂ)
    (hM : M.IsHermitian) (hMD : (M + D).IsHermitian) (hD_psd : D.PosSemidef)
    (s : Fin n) :
    hM.eigenvalues₀ ⟨s.val, by rw [Fintype.card_fin]; exact s.isLt⟩ ≤
    hMD.eigenvalues₀ ⟨s.val, by rw [Fintype.card_fin]; exact s.isLt⟩ := by
  -- exists_unit_le_re_dotProduct_mulVec_and_le with M₁ = M+D, M₁₂ = M gives unit x with:
  --   xᴴMx ≥ eigenvalues₀(M)(s) and xᴴ(M+D)x ≤ eigenvalues₀(M+D)(s)
  obtain ⟨x, hx_unit, hx_lb, hx_ub⟩ := exists_unit_le_re_dotProduct_mulVec_and_le (M + D) M hMD hM s
  -- xᴴDx ≥ 0 since D is PSD
  have h_Dx_nonneg : 0 ≤ (dotProduct (star x) (D.mulVec x)).re :=
    hD_psd.re_dotProduct_nonneg x
  -- (M + D).mulVec x = M.mulVec x + D.mulVec x
  have h_add_mulVec : (M + D).mulVec x = M.mulVec x + D.mulVec x :=
    Matrix.add_mulVec M D x
  -- xᴴ(M+D)x = xᴴMx + xᴴDx
  have h_split : (dotProduct (star x) ((M + D).mulVec x)).re =
      (dotProduct (star x) (M.mulVec x)).re + (dotProduct (star x) (D.mulVec x)).re := by
    rw [h_add_mulVec, dotProduct_add]
    exact Complex.add_re _ _
  -- Chain: eigenvalues₀(M)(s) ≤ xᴴMx ≤ xᴴMx + xᴴDx = xᴴ(M+D)x ≤ eigenvalues₀(M+D)(s)
  linarith

/-- **Ky Fan positive part bound (eigenvalues₀ version)**: The sum of positive parts
    of eigenvalue differences is bounded by the sum of positive eigenvalues of A - B.

    Proof via matrix positive/negative part decomposition and Weyl monotonicity.
    Let C = A - B with spectral decomposition C = U diag(λ) Uᴴ. Define
    C₊ = U diag(max(0,λ)) Uᴴ and C₋ = U diag(max(0,-λ)) Uᴴ. Then C₊, C₋ ≥ 0,
    C = C₊ - C₋, and M := A + C₋ = B + C₊. By Weyl monotonicity,
    λₖ(A) ≤ λₖ(M) and λₖ(B) ≤ λₖ(M), so max(0, λₖ(A) - λₖ(B)) ≤ λₖ(M) - λₖ(B).
    Summing: ∑ max(0, dₖ) ≤ ∑(λₖ(M) - λₖ(B)) = tr(C₊) = ∑ max(0, λₖ(C)). -/
lemma sum_max_eigenvalues₀_sub_le {n : ℕ} [NeZero n]
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : (A - B).IsHermitian) :
    ∑ i : Fin (Fintype.card (Fin n)), max 0 (hA.eigenvalues₀ i - hB.eigenvalues₀ i) ≤
    ∑ i : Fin (Fintype.card (Fin n)), max 0 (hAB.eigenvalues₀ i) := by
  have h_card : Fintype.card (Fin n) = n := Fintype.card_fin n
  -- ================================================================
  -- Step 1: Spectral decomposition of C = A - B
  -- ================================================================
  set C := A - B with hC_def
  have hA_eq_BC : A = B + C := by simp [hC_def]
  set U := hAB.eigenvectorUnitary.val with hU_def
  have hUU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hAB.eigenvectorUnitary
  have hUU' : Uᴴ * U = 1 := Unitary.coe_star_mul_self hAB.eigenvectorUnitary
  have hU_unit : IsUnit U := ⟨⟨U, Uᴴ, hUU, hUU'⟩, rfl⟩
  have h_spec := hAB.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h_spec
  set eig := hAB.eigenvalues with h_eig_def
  set D_eig := Matrix.diagonal (RCLike.ofReal ∘ eig : Fin n → ℂ) with hD_eig_def
  have hC_eq : C = U * D_eig * Uᴴ := h_spec
  -- ================================================================
  -- Step 2: Define C₊ and C₋ via positive/negative part diagonals
  -- ================================================================
  let pos_diag : Fin n → ℂ := fun i => ↑(max 0 (eig i))
  let neg_diag : Fin n → ℂ := fun i => ↑(max 0 (-eig i))
  set C_pos := U * Matrix.diagonal pos_diag * Uᴴ with hC_pos_def
  set C_neg := U * Matrix.diagonal neg_diag * Uᴴ with hC_neg_def
  -- ================================================================
  -- Step 3: C₊ and C₋ are PSD (diagonal with nonneg entries, conjugated by unitary)
  -- ================================================================
  have hC_pos_psd : C_pos.PosSemidef := by
    rw [hC_pos_def, show Uᴴ = star U from (star_eq_conjTranspose U).symm]
    exact (hU_unit.posSemidef_star_right_conjugate_iff).mpr
      (posSemidef_diagonal_iff.mpr (fun i => Complex.zero_le_real.mpr (le_max_left 0 _)))
  have hC_neg_psd : C_neg.PosSemidef := by
    rw [hC_neg_def, show Uᴴ = star U from (star_eq_conjTranspose U).symm]
    exact (hU_unit.posSemidef_star_right_conjugate_iff).mpr
      (posSemidef_diagonal_iff.mpr (fun i => Complex.zero_le_real.mpr (le_max_left 0 _)))
  -- ================================================================
  -- Step 4: Key algebraic identity C + C₋ = C₊
  -- ================================================================
  have h_diag_identity : D_eig + Matrix.diagonal neg_diag = Matrix.diagonal pos_diag := by
    rw [hD_eig_def, Matrix.diagonal_add]; congr 1; ext i
    simp only [Function.comp_apply, pos_diag, neg_diag]
    rcases le_or_gt 0 (eig i) with h | h
    · simp [max_eq_left (neg_nonpos_of_nonneg h), max_eq_right h]
    · simp [max_eq_right (le_of_lt (neg_pos.mpr h)), max_eq_left h.le]
  have h_C_decomp : C + C_neg = C_pos := by
    rw [hC_eq, hC_neg_def, hC_pos_def,
      ← Matrix.add_mul, ← Matrix.mul_add, h_diag_identity]
  -- A + C₋ = (B + C) + C₋ = B + (C + C₋) = B + C₊
  have hM_eq : A + C_neg = B + C_pos := by
    rw [hA_eq_BC, add_assoc, h_C_decomp]
  -- ================================================================
  -- Step 5: Define M and establish Hermitian proofs
  -- ================================================================
  set M := B + C_pos with hM_def
  have hM_herm : M.IsHermitian := hB.add hC_pos_psd.1
  have hM_from_A : (A + C_neg).IsHermitian := hM_eq ▸ hM_herm
  -- eigenvalues₀ of (A + C₋) = eigenvalues₀ of M since A + C₋ = M
  have h_eig_M_eq : ∀ k, hM_from_A.eigenvalues₀ k = hM_herm.eigenvalues₀ k := by
    intro k; congr 1
  -- ================================================================
  -- Step 6: Weyl monotonicity
  -- ================================================================
  have h_weyl_A : ∀ s : Fin n,
      hA.eigenvalues₀ ⟨s.val, by rw [h_card]; exact s.isLt⟩ ≤
      hM_herm.eigenvalues₀ ⟨s.val, by rw [h_card]; exact s.isLt⟩ := by
    intro s
    have := eigenvalues₀_le_add_of_posSemidef A C_neg hA hM_from_A hC_neg_psd s
    rwa [h_eig_M_eq] at this
  have h_weyl_B : ∀ s : Fin n,
      hB.eigenvalues₀ ⟨s.val, by rw [h_card]; exact s.isLt⟩ ≤
      hM_herm.eigenvalues₀ ⟨s.val, by rw [h_card]; exact s.isLt⟩ :=
    fun s => eigenvalues₀_le_add_of_posSemidef B C_pos hB hM_herm hC_pos_psd s
  -- ================================================================
  -- Step 7: Pointwise bound: max(0, λₖ(A) - λₖ(B)) ≤ λₖ(M) - λₖ(B)
  -- ================================================================
  have h_pointwise : ∀ s : Fin n,
      max 0 (hA.eigenvalues₀ ⟨s.val, by rw [h_card]; exact s.isLt⟩ -
             hB.eigenvalues₀ ⟨s.val, by rw [h_card]; exact s.isLt⟩) ≤
      hM_herm.eigenvalues₀ ⟨s.val, by rw [h_card]; exact s.isLt⟩ -
      hB.eigenvalues₀ ⟨s.val, by rw [h_card]; exact s.isLt⟩ :=
    fun s => max_le (by linarith [h_weyl_B s]) (by linarith [h_weyl_A s])
  -- ================================================================
  -- Step 8: Sum computation: ∑(λₖ(M) - λₖ(B)) = tr(C₊) = ∑ max(0, eig)
  -- ================================================================
  -- tr(C₊) = tr(U * diag(pos) * Uᴴ) = tr(diag(pos)) = ∑ pos_diag
  have h_tr_Cpos : C_pos.trace = ∑ i, pos_diag i := by
    rw [hC_pos_def, Matrix.trace_mul_cycle, hUU', Matrix.one_mul]
    simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_apply]
    apply Finset.sum_congr rfl; intro i _; simp
  -- tr(M) - tr(B) = tr(C₊)
  have h_tr_diff : M.trace - B.trace = C_pos.trace := by
    rw [hM_def, Matrix.trace_add]; ring
  -- ∑ eigenvalues₀(M) and ∑ eigenvalues₀(B) via sum_eigenvalues_eq_trace
  have h_trace_M := sum_eigenvalues_eq_trace M hM_herm
  have h_trace_B := sum_eigenvalues_eq_trace B hB
  -- Real sum of eigenvalue differences = tr(C₊).re
  have h_sum_eig_diff :
      (∑ s : Fin n, hM_herm.eigenvalues₀ ⟨s.val, by rw [h_card]; exact s.isLt⟩) -
      (∑ s : Fin n, hB.eigenvalues₀ ⟨s.val, by rw [h_card]; exact s.isLt⟩) =
      ∑ s : Fin n, max 0 (eig s) := by
    -- Go through complex traces
    have h_re_M : (∑ s : Fin n, hM_herm.eigenvalues₀ ⟨s.val, by rw [h_card]; exact s.isLt⟩ : ℝ)
        = M.trace.re := by rw [← h_trace_M, Complex.re_sum]; simp [Complex.ofReal_re]
    have h_re_B : (∑ s : Fin n, hB.eigenvalues₀ ⟨s.val, by rw [h_card]; exact s.isLt⟩ : ℝ)
        = B.trace.re := by rw [← h_trace_B, Complex.re_sum]; simp [Complex.ofReal_re]
    have h_re_Cpos : (∑ s : Fin n, max 0 (eig s) : ℝ) = C_pos.trace.re := by
      rw [h_tr_Cpos, Complex.re_sum]; simp [pos_diag, Complex.ofReal_re]
    rw [h_re_M, h_re_B, h_re_Cpos, ← Complex.sub_re, h_tr_diff]
  -- Rewrite as sum of differences
  have h_sum_as_diff :
      ∑ s : Fin n, (hM_herm.eigenvalues₀ ⟨s.val, by rw [h_card]; exact s.isLt⟩ -
        hB.eigenvalues₀ ⟨s.val, by rw [h_card]; exact s.isLt⟩) =
      ∑ s : Fin n, max 0 (eig s) := by
    rw [Finset.sum_sub_distrib]; exact h_sum_eig_diff
  -- ================================================================
  -- Step 9: Connect ∑ max(0, eig) to ∑ max(0, eigenvalues₀(C)) via reindexing
  -- ================================================================
  -- eigenvalues i = eigenvalues₀ (equivOfCardEq.symm i), so sums match via equiv
  have h_eig_sum_eq : ∑ s : Fin n, max 0 (eig s) =
      ∑ s : Fin n, max 0 (hAB.eigenvalues₀ ⟨s.val, by rw [h_card]; exact s.isLt⟩) := by
    -- Both sides reduce to ∑ j : Fin (card (Fin n)), max 0 (eigenvalues₀ j)
    -- via different equivalences Fin n ≃ Fin (card (Fin n))
    set g : Fin (Fintype.card (Fin n)) → ℝ := fun j => max 0 (hAB.eigenvalues₀ j)
    -- LHS: eig s = eigenvalues s = eigenvalues₀ (equivOfCardEq.symm s) definitionally
    have hL : ∑ s : Fin n, max 0 (eig s) = ∑ j, g j := by
      change ∑ s, g ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm s) = _
      exact Equiv.sum_comp _ g
    -- RHS: ⟨s.val, _⟩ = (finCongr h_card).symm s, so reindex via finCongr
    have hR : ∑ s : Fin n, max 0 (hAB.eigenvalues₀ ⟨s.val, by rw [h_card]; exact s.isLt⟩) =
        ∑ j, g j := by
      have h_idx : ∀ s : Fin n,
          (⟨s.val, by rw [h_card]; exact s.isLt⟩ : Fin (Fintype.card (Fin n))) =
          (finCongr h_card).symm s := fun s => Fin.ext rfl
      simp_rw [h_idx]
      exact Equiv.sum_comp _ g
    rw [hL, hR]
  -- ================================================================
  -- Step 10: Combine and convert indices
  -- ================================================================
  have h_bound_Fin_n :
      ∑ s : Fin n, max 0 (hA.eigenvalues₀ ⟨s.val, by rw [h_card]; exact s.isLt⟩ -
        hB.eigenvalues₀ ⟨s.val, by rw [h_card]; exact s.isLt⟩) ≤
      ∑ s : Fin n, max 0 (hAB.eigenvalues₀ ⟨s.val, by rw [h_card]; exact s.isLt⟩) := by
    calc ∑ s : Fin n, max 0 (hA.eigenvalues₀ ⟨s.val, by rw [h_card]; exact s.isLt⟩ -
            hB.eigenvalues₀ ⟨s.val, by rw [h_card]; exact s.isLt⟩)
        ≤ ∑ s : Fin n, (hM_herm.eigenvalues₀ ⟨s.val, by rw [h_card]; exact s.isLt⟩ -
            hB.eigenvalues₀ ⟨s.val, by rw [h_card]; exact s.isLt⟩) :=
          Finset.sum_le_sum (fun s _ => h_pointwise s)
      _ = ∑ s : Fin n, max 0 (eig s) := h_sum_as_diff
      _ = ∑ s : Fin n, max 0 (hAB.eigenvalues₀ ⟨s.val, by rw [h_card]; exact s.isLt⟩) :=
          h_eig_sum_eq
  -- Convert between Fin (Fintype.card (Fin n)) and Fin n index types
  let e := finCongr h_card
  calc ∑ i : Fin (Fintype.card (Fin n)), max 0 (hA.eigenvalues₀ i - hB.eigenvalues₀ i)
      = ∑ i : Fin n, max 0 (hA.eigenvalues₀ ⟨i.val, by rw [h_card]; exact i.isLt⟩ -
          hB.eigenvalues₀ ⟨i.val, by rw [h_card]; exact i.isLt⟩) :=
        Finset.sum_equiv e (by intro; simp) (fun i => by simp [e, finCongr])
    _ ≤ ∑ i : Fin n, max 0 (hAB.eigenvalues₀ ⟨i.val, by rw [h_card]; exact i.isLt⟩) :=
        h_bound_Fin_n
    _ = ∑ i : Fin (Fintype.card (Fin n)), max 0 (hAB.eigenvalues₀ i) :=
        (Finset.sum_equiv e (by intro; simp) (fun i => by simp [e, finCongr])).symm

/-- **Ky Fan positive part bound**: The eigenvalues version, derived from eigenvalues₀.
    Since eigenvalues k = eigenvalues₀ (equivOfCardEq.symm k), and all matrices use
    the same equivalence, the reindexing preserves the inequality. -/
lemma sum_max_eigenvalues_sub_le {n : ℕ} [NeZero n]
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : (A - B).IsHermitian) :
    ∑ i, max 0 (hA.eigenvalues i - hB.eigenvalues i) ≤ ∑ i, max 0 (hAB.eigenvalues i) := by
  -- Derive from eigenvalues₀ version via reindexing
  let e := Fintype.equivOfCardEq
    (by simp : Fintype.card (Fin (Fintype.card (Fin n))) = Fintype.card (Fin n))
  -- LHS reindexing: eigenvalues k = eigenvalues₀ (e.symm k)
  have hLHS : ∑ i, max 0 (hA.eigenvalues i - hB.eigenvalues i) =
      ∑ i, max 0 (hA.eigenvalues₀ i - hB.eigenvalues₀ i) := by
    calc ∑ i, max 0 (hA.eigenvalues i - hB.eigenvalues i)
        = ∑ i, max 0 (hA.eigenvalues₀ (e.symm i) - hB.eigenvalues₀ (e.symm i)) := rfl
      _ = ∑ i, max 0 (hA.eigenvalues₀ i - hB.eigenvalues₀ i) := by
          rw [← Equiv.sum_comp e.symm]
  -- RHS reindexing
  have hRHS : ∑ i, max 0 (hAB.eigenvalues i) = ∑ i, max 0 (hAB.eigenvalues₀ i) := by
    calc ∑ i, max 0 (hAB.eigenvalues i)
        = ∑ i, max 0 (hAB.eigenvalues₀ (e.symm i)) := rfl
      _ = ∑ i, max 0 (hAB.eigenvalues₀ i) := by rw [← Equiv.sum_comp e.symm]
  rw [hLHS, hRHS]
  exact sum_max_eigenvalues₀_sub_le A B hA hB hAB

end Math.SpectralTheory
