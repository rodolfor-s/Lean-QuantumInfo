import QCryptLean.Math.LinearAlgebra.SubmoduleDimension
import QCryptLean.Math.SpectralTheory.KyFan.PositivePart
import QCryptLean.Math.SpectralTheory.Rayleigh

/-!
# Spectral Theory: Weyl and Mirsky Inequalities

Negated eigenvalue relationships, Weyl eigenvalue inequalities, and Mirsky's inequality.
These build on the core spectral theory results.

## Main Results

- `eigenvalues₀_neg_eq_neg_rev`: Eigenvalues of -A are negated and reversed
- `eigenvalues₀_add_le_add`: Weyl's upper bound (4.3.2a)
- `add_le_eigenvalues₀_add`: Weyl's lower bound (4.3.2b)
- `sum_abs_sub_eigenvalues_le`: Mirsky's inequality

Note: `sum_max_eigenvalues_sub_le` lives in `Math/SpectralTheory/KyFan/PositivePart.lean`
-/

open scoped Matrix ComplexOrder
open Matrix

namespace Math.SpectralTheory

/-!
## Eigenvalues of Negated Hermitian Matrices

Key lemma: For a Hermitian matrix A, the eigenvalues of -A are the negations
of the eigenvalues of A, but in reversed order (since eigenvalues are sorted descending).

If A has eigenvalues λ₀ ≥ λ₁ ≥ ... ≥ λₙ₋₁ (sorted descending),
then -A has eigenvalues -λₙ₋₁ ≥ -λₙ₋₂ ≥ ... ≥ -λ₀ (sorted descending).

So: eigenvalues(-A)[i] = -eigenvalues(A)[n-1-i] = -eigenvalues(A)[rev i]
-/

open Polynomial in
/-- Determinant commutes with composition by -X. -/
private lemma det_map_comp_neg_X {m : Type*} [DecidableEq m] [Fintype m]
    (M : Matrix m m (Polynomial ℂ)) :
    (M.map (fun p => p.comp (-X))).det = M.det.comp (-X) := by
  exact (RingHom.map_det (Polynomial.compRingHom (-X)) M).symm

open Polynomial in
/-- Characteristic polynomial of -A relates to that of A via composition with -X. -/
lemma charpoly_neg_eq {m : Type*} [DecidableEq m] [Fintype m] (A : Matrix m m ℂ) :
    (-A).charpoly = C ((-1 : ℂ) ^ Fintype.card m) * A.charpoly.comp (-X) := by
  unfold Matrix.charpoly Matrix.charmatrix
  simp only [RingHom.mapMatrix_apply, map_neg, sub_neg_eq_add]
  have h_neg_eq : (Matrix.scalar m X + A.map ⇑C) = -(Matrix.scalar m (-X) - A.map ⇑C) := by
    ext i j k
    simp only [Matrix.neg_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.scalar_apply,
               Matrix.diagonal_apply, Matrix.map_apply]
    split_ifs <;> ring_nf
  rw [h_neg_eq, Matrix.det_neg]
  have h_det_comp : (Matrix.scalar m (-X) - A.map ⇑C).det =
      (Matrix.scalar m X - A.map ⇑C).det.comp (-X) := by
    rw [← det_map_comp_neg_X]; congr 1; ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs with h
    · simp only [h, X_comp, C_comp, sub_comp]
    · simp only [C_comp, zero_sub, neg_comp]
  rw [h_det_comp]
  have h_pow : ((-1 : Polynomial ℂ) ^ Fintype.card m) = C ((-1 : ℂ) ^ Fintype.card m) := by
    have h : (-1 : Polynomial ℂ) = C (-1 : ℂ) := by simp
    rw [h, map_pow]
  rw [h_pow]

open Polynomial in
/-- Roots of charpoly(-A) are negatives of roots of charpoly(A). -/
lemma roots_charpoly_neg_eq {m : Type*} [DecidableEq m] [Fintype m] (A : Matrix m m ℂ) :
    (-A).charpoly.roots = A.charpoly.roots.map (fun z => -z) := by
  rw [charpoly_neg_eq]
  have h_ne : ((-1 : ℂ) ^ Fintype.card m) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [roots_C_mul _ h_ne]
  exact Polynomial.roots_comp_neg_X A.charpoly

/-- The multiset of eigenvalues of -A equals the negation of eigenvalues of A.

This is the fundamental relationship: the eigenvalue multiset of -A is exactly
the multiset obtained by negating each eigenvalue of A.

**Proof sketch**:
The characteristic polynomial of -A is det(-A - XI) = det(-(A + XI)) = (-1)^n det(A + XI).
If we substitute X → -X in det(A - XI), we get det(A - (-X)I) = det(A + XI).
So charpoly(-A)(X) = (-1)^n · charpoly(A)(-X).
The roots of charpoly(-A) are {r : charpoly(-A)(r) = 0}
= {r : (-1)^n · charpoly(A)(-r) = 0}
= {r : charpoly(A)(-r) = 0}
= {-s : charpoly(A)(s) = 0}
= -roots(charpoly(A))

Therefore: eigenvalue multiset of -A = -(eigenvalue multiset of A) -/
theorem neg_eigenvalues_multiset_eq_of_isHermitian {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (h_neg : (-A).IsHermitian) :
    Finset.univ.val.map h_neg.eigenvalues = Finset.univ.val.map (fun i => -hA.eigenvalues i) := by
  -- Use the characteristic polynomial root relationship
  -- The eigenvalues are the real parts of charpoly roots, sorted descending
  -- For Hermitian matrices, charpoly roots are real and equal to eigenvalues (as multiset)
  -- roots_charpoly_neg_eq shows: (-A).charpoly.roots = A.charpoly.roots.map neg
  -- Combined with roots_charpoly_eq_eigenvalues, this gives the multiset equality
  have h_roots_neg := roots_charpoly_neg_eq A
  have h_A_roots := hA.roots_charpoly_eq_eigenvalues
  have h_neg_roots := h_neg.roots_charpoly_eq_eigenvalues
  -- h_A_roots : A.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hA.eigenvalues) Finset.univ.val
  -- h_neg_roots : (-A).charpoly.roots = Multiset.map (RCLike.ofReal ∘ h_neg.eigenvalues) univ.val
  -- h_roots_neg : (-A).charpoly.roots = A.charpoly.roots.map neg
  -- From these: map (ofReal ∘ h_neg.eigenvalues) univ =
  --              (map (ofReal ∘ hA.eigenvalues) univ).map neg
  --           = map (neg ∘ ofReal ∘ hA.eigenvalues) univ
  --           = map (ofReal ∘ neg ∘ hA.eigenvalues) univ
  -- Since ofReal is injective:
  --   map h_neg.eigenvalues univ = map (neg ∘ hA.eigenvalues) univ
  have h_eq : Multiset.map (RCLike.ofReal (K := ℂ)) (Finset.univ.val.map h_neg.eigenvalues) =
      Multiset.map (RCLike.ofReal (K := ℂ)) (Finset.univ.val.map (fun i => -hA.eigenvalues i)) := by
    simp only [Multiset.map_map]
    rw [← h_neg_roots, h_roots_neg, h_A_roots, Multiset.map_map]
    congr 1
    ext x
    simp only [Function.comp_apply, RCLike.ofReal_neg]
  have h_inj : Function.Injective (RCLike.ofReal (K := ℂ)) := RCLike.ofReal_injective
  exact Multiset.map_injective h_inj h_eq

/-- Helper lemma: List.ofFn f and List.ofFn (f ∘ Fin.rev) have equal multisets.

This is because Fin.rev is a bijection, so the two lists contain the same elements. -/
private lemma ofFn_comp_rev_multiset_eq {n : ℕ} {α : Type*} (f : Fin n → α) :
    (List.ofFn f : Multiset α) = (List.ofFn (f ∘ Fin.rev) : Multiset α) := by
  rw [List.ofFn_eq_map, List.ofFn_eq_map]
  simp only [Function.comp_def]
  have h : List.map (fun x : Fin n => f x.rev) (List.finRange n)
         = List.map f (List.map Fin.rev (List.finRange n)) := by
    rw [List.map_map]; rfl
  rw [h, ← List.finRange_reverse]
  rw [List.map_reverse, Multiset.coe_reverse]

/-- Helper lemma: Sorting a monotone function's values descending gives the reversed list.

If f is monotone on Fin n (f 0 ≤ f 1 ≤ ... ≤ f (n-1)), then:
- List.ofFn f is sorted ascending
- f ∘ Fin.rev is antitone, so List.ofFn (f ∘ Fin.rev) is sorted descending
- Both represent the same multiset
- By uniqueness of sorting, sorting (List.ofFn f) descending equals List.ofFn (f ∘ Fin.rev) -/
private lemma monotone_ofFn_sort_ge_eq {n : ℕ} (f : Fin n → ℝ) (hf : Monotone f) :
    ((List.ofFn f : Multiset ℝ).sort (· ≥ ·)) = List.ofFn (f ∘ Fin.rev) := by
  have h_anti : Antitone (f ∘ Fin.rev) := hf.comp_antitone Fin.rev_anti
  have h_sorted_rev : (List.ofFn (f ∘ Fin.rev)).SortedGE :=
    List.sortedGE_ofFn_iff.mpr h_anti
  have h_sorted_sort : ((List.ofFn f : Multiset ℝ).sort (· ≥ ·)).SortedGE :=
    List.sortedGE_iff_pairwise.mpr (Multiset.pairwise_sort (List.ofFn f : Multiset ℝ) (· ≥ ·))
  have h_perm : ((List.ofFn f : Multiset ℝ).sort (· ≥ ·)).Perm (List.ofFn (f ∘ Fin.rev)) := by
    have h1 : (↑((List.ofFn f : Multiset ℝ).sort (· ≥ ·)) : Multiset ℝ) =
        (List.ofFn f : Multiset ℝ) := Multiset.sort_eq _ (· ≥ ·)
    rw [List.perm_comm, ← Multiset.coe_eq_coe, h1, ofFn_comp_rev_multiset_eq f]
  exact List.Perm.eq_of_sortedGE h_sorted_sort h_sorted_rev h_perm

/-- Sorting descending after negation gives the reversed negation.

If f is antitone (sorted descending) on Fin n, then:
- The values {f 0, f 1, ..., f (n-1)} are sorted as f 0 ≥ f 1 ≥ ... ≥ f (n-1)
- Negated: {-f 0, -f 1, ..., -f (n-1)}
- Sorted descending: {-f (n-1), -f (n-2), ..., -f 0}
- So: sorted_neg[i] = -f(n-1-i) = -f(rev i)

This is a general fact about antitone functions and negation.

**Proof outline**:
1. Since f is antitone, -f is monotone: `hf.neg : Monotone (fun j => -f j)`
2. The multiset `Finset.univ.val.map (fun j => -f j)` has the same elements as `List.ofFn (-f)`
3. For a monotone function g, `List.ofFn g` is sorted ascending (LE)
4. Sorting the same multiset descending (GE) reverses the list
5. So the sorted list equals `List.ofFn (fun i => -f (Fin.rev i))`

The key step is showing that sorting a monotone sequence in reverse order
gives the reversal. -/
lemma antitone_neg_sort_eq_neg_rev {n : ℕ} (f : Fin n → ℝ) (hf : Antitone f) :
    ∀ i : Fin n, ((Finset.univ.val.map (fun j => -f j)).sort (· ≥ ·)).get ⟨i.val, by
      rw [Multiset.length_sort, Multiset.card_map]
      have : (Finset.univ : Finset (Fin n)).val.card = n := by simp
      rw [this]; exact i.isLt⟩ = -f (Fin.rev i) := by
  intro i
  have h_mono : Monotone (fun j : Fin n => -f j) := hf.neg
  have h_map_eq : (Finset.univ.val.map (fun j => -f j) : Multiset ℝ) =
      (List.ofFn (fun j : Fin n => -f j) : Multiset ℝ) := Fin.univ_val_map _
  have h_sort := monotone_ofFn_sort_ge_eq (fun j : Fin n => -f j) h_mono
  have h_eq_lists : (Finset.univ.val.map (fun j => -f j)).sort (· ≥ ·) =
      List.ofFn ((fun j => -f j) ∘ Fin.rev) := by
    have h1 : (Finset.univ.val.map (fun j => -f j)).sort (· ≥ ·) =
        ((List.ofFn (fun j : Fin n => -f j) : Multiset ℝ)).sort (· ≥ ·) := by
      simp only [h_map_eq]
    rw [h1, h_sort]
  simp only [List.get_eq_getElem, h_eq_lists, List.getElem_ofFn, Function.comp_apply]

/-!
## Weyl's inequalities (Horn & Johnson Theorem 4.3.1)

For Hermitian A, B, the eigenvalues of A + B (in descending order) are bounded by
two families of inequalities involving two eigenvalues at a time (no sum Σ).
Used in eigenvalue perturbation and Fannes inequality (InformationTheory.Continuity).

Reference: Horn & Johnson, "Matrix Analysis", Theorem 4.3.1 (Weyl).
- (4.3.2a) upper bound: λᵢ(A+B) ≤ λ_{i+j}(A) + λ_{n-j}(B), j = 0,…,n−i
- (4.3.2b) lower bound: λ_{i−j+1}(A) + λ_j(B) ≤ λᵢ(A+B), j = 1,…,i

Here eigenvalues are 1-based in the book; we use `eigenvalues₀` (0-based, descending).

Proof of (4.3.2a) follows the book: three subspaces S1, S2, S3 (spans of eigenvector
columns) have dimensions summing to 2n+1, so their intersection is nontrivial;
take a unit vector x in the intersection and apply variational bounds (4.2.2).
-/

-- ==========================================================================
-- Helper lemmas for Weyl inequalities (shared between upper and lower bounds)
-- ==========================================================================

/-- Common setup helpers for Weyl inequality proofs. -/
private lemma card_fin_eq_and_val_lt {n : ℕ}
    (i : Fin (Fintype.card (Fin n))) :
    (Fintype.card (Fin n) = n) ∧ (i.val < n) :=
  ⟨Fintype.card_fin n, by
    have := i.isLt
    simp only [Fintype.card_fin n] at this
    exact this⟩

/-- Normalize a vector and show it preserves membership in three subspaces. -/
private lemma exists_unit_mem_inf_inf_of_ne_zero {n : ℕ}
    (x : Fin n → ℂ) (hx_ne : x ≠ 0)
    (S1 S2 S3 : Submodule ℂ (Fin n → ℂ))
    (hx_mem : x ∈ Min.min (α := Submodule ℂ (Fin n → ℂ))
                          (Min.min (α := Submodule ℂ (Fin n → ℂ)) S1 S2) S3) :
    let x_norm := Math.LinearAlgebra.SubmoduleDim.normalizeVec x hx_ne
    (x_norm ∈ S1) ∧ (x_norm ∈ S2) ∧ (x_norm ∈ S3) ∧
    ((dotProduct (star x_norm) x_norm).re = 1) := by
  intro x_norm
  -- Extract x's membership in each subspace from the intersection
  have hx_mem_S1 : x ∈ S1 := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hx_mem).1).1
  have hx_mem_S2 : x ∈ S2 := (Submodule.mem_inf.mp (Submodule.mem_inf.mp hx_mem).1).2
  have hx_mem_S3 : x ∈ S3 := (Submodule.mem_inf.mp hx_mem).2
  -- Helper: ℝ-smul equals ℂ-smul with coerced scalar
  have h_smul_eq : (√(Math.LinearAlgebra.SubmoduleDim.vecNormSq x))⁻¹ • x =
      ((√(Math.LinearAlgebra.SubmoduleDim.vecNormSq x))⁻¹ : ℂ) • x := by
    ext i
    simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul, Complex.ofReal_inv]
  have h_x_norm_mem_S1 : x_norm ∈ S1 := by
    unfold x_norm Math.LinearAlgebra.SubmoduleDim.normalizeVec
    simp only
    rw [h_smul_eq]
    exact S1.smul_mem _ hx_mem_S1
  have h_x_norm_mem_S2 : x_norm ∈ S2 := by
    unfold x_norm Math.LinearAlgebra.SubmoduleDim.normalizeVec
    simp only
    rw [h_smul_eq]
    exact S2.smul_mem _ hx_mem_S2
  have h_x_norm_mem_S3 : x_norm ∈ S3 := by
    unfold x_norm Math.LinearAlgebra.SubmoduleDim.normalizeVec
    simp only
    rw [h_smul_eq]
    exact S3.smul_mem _ hx_mem_S3
  have h_x_norm_unit : (dotProduct (star x_norm) x_norm).re = 1 :=
    Math.LinearAlgebra.SubmoduleDim.normalizeVec_unit x hx_ne
  exact ⟨h_x_norm_mem_S1, ⟨h_x_norm_mem_S2, ⟨h_x_norm_mem_S3, h_x_norm_unit⟩⟩⟩

/-- Quadratic form additivity: x*(A+B)x = x*Ax + x*Bx. -/
lemma re_dotProduct_mulVec_add {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    (dotProduct (star x) ((A + B).mulVec x)).re =
    (dotProduct (star x) (A.mulVec x)).re + (dotProduct (star x) (B.mulVec x)).re := by
  -- (A+B).mulVec x = A.mulVec x + B.mulVec x
  have h_mulvec_add : (A + B).mulVec x = A.mulVec x + B.mulVec x :=
    Matrix.add_mulVec A B x
  -- dotProduct distributes over addition
  have h_dot_add : dotProduct (star x) ((A + B).mulVec x) =
      dotProduct (star x) (A.mulVec x) +
      dotProduct (star x) (B.mulVec x) := by
    rw [h_mulvec_add]
    exact dotProduct_add (star x) (A.mulVec x) (B.mulVec x)
  -- Re distributes over addition
  rw [h_dot_add, Complex.add_re]

/-- **Weyl (4.3.2a)** — upper bound: λᵢ(A+B) ≤ λ_{i-j}(A) + λⱼ(B) for j ≤ i.

    In our descending eigenvalues₀ notation:
      eigenvalues₀ i ≤ eigenvalues₀ (i-j) + eigenvalues₀ j  for j ≤ i

    Proof: Three subspaces with dimensions summing to 2n+1 have nontrivial intersection;
    take a unit vector in the intersection and apply variational bounds (4.2.2). -/
lemma eigenvalues₀_add_le_add {n : ℕ} [NeZero n] (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : (A + B).IsHermitian)
    (i : Fin (Fintype.card (Fin n))) (j : ℕ) (hj : j ≤ i.val) :
    hAB.eigenvalues₀ i ≤ hA.eigenvalues₀ ⟨i.val - j, by omega⟩ +
      hB.eigenvalues₀ ⟨j, by omega⟩ := by
  -- ==========================================================================
  -- INDEX TRANSLATION (Book ascending → Our descending)
  -- ==========================================================================
  -- Book uses ASCENDING eigenvalues: λ₁ ≤ λ₂ ≤ ... ≤ λₙ (1-based)
  -- We use DESCENDING eigenvalues₀: eigenvalues₀ 0 ≥ ... ≥ eigenvalues₀ (n-1) (0-based)
  -- Translation: book's λₖ = eigenvalues₀ (n-k)
  --
  -- Book's theorem (4.3.2a): λᵢ(A+B) ≤ λᵢ₊ⱼ(A) + λₙ₋ⱼ(B) for j = 0,...,n-i
  -- Our translated form: eigenvalues₀ i ≤ eigenvalues₀ (i-j) + eigenvalues₀ j for j ≤ i
  --
  -- Subspaces (following book but adapted to descending order):
  --   S₁ = eigenvecSpanFrom A (i-j) → upper bound x*Ax ≤ eigenvalues₀ (i-j), dim = n-i+j
  --   S₂ = eigenvecSpanFrom B j → upper bound x*Bx ≤ eigenvalues₀ j, dim = n-j
  --   S₃ = eigenvecSpanFirst (A+B) (i+1) → lower bound eigenvalues₀ i ≤ x*(A+B)x, dim = i+1
  --
  -- Dimension sum: (n-i+j) + (n-j) + (i+1) = 2n+1 ✓
  -- ==========================================================================
  -- Use helper for setup
  have ⟨h_card_eq, h_i_lt_n⟩ := card_fin_eq_and_val_lt i
  -- Step 1: Define the three subspaces
  -- S₁ = eigenvecSpanFrom A at index (i-j)
  -- Gives UPPER bound: x*Ax ≤ eigenvalues₀ (i-j) via re_dotProduct_mulVec_le_eigenvalues₀_of_mem
  -- Dimension: n - (i-j) = n - i + j
  have h_S1_idx_lt : i.val - j < n := by omega
  let S1 : Submodule ℂ (Fin n → ℂ) :=
    Math.LinearAlgebra.SubmoduleDim.eigenvecSpanFrom₀ A hA ⟨i.val - j, h_S1_idx_lt⟩
  -- S₂ = eigenvecSpanFrom₀ B at index j
  -- Gives UPPER bound: x*Bx ≤ eigenvalues₀ j via re_dotProduct_mulVec_le_eigenvalues₀_of_mem
  -- Dimension: n - j
  have h_S2_idx_lt : j < n := by omega
  let S2 : Submodule ℂ (Fin n → ℂ) :=
    Math.LinearAlgebra.SubmoduleDim.eigenvecSpanFrom₀ B hB ⟨j, h_S2_idx_lt⟩
  -- S₃ = eigenvecSpanFirst₀ (A+B) with k = i+1
  -- Gives LOWER bound: eigenvalues₀ i ≤ x*(A+B)x via eigenvalues₀_le_re_dotProduct_mulVec_of_mem
  -- Dimension: i + 1
  have h_S3_k_le : i.val + 1 ≤ n := by omega
  let S3 : Submodule ℂ (Fin n → ℂ) :=
    Math.LinearAlgebra.SubmoduleDim.eigenvecSpanFirst₀ (A + B) hAB (i.val + 1) h_S3_k_le
  -- Step 2: Compute dimensions and verify sum = 2n+1
  have h_dim_S1 : Module.finrank ℂ S1 = n - i.val + j := by
    rw [Math.LinearAlgebra.SubmoduleDim.finrank_eigenvecSpanFrom₀ A hA ⟨i.val - j, h_S1_idx_lt⟩]
    -- finrank_eigenvecSpanFrom₀ gives n - (i.val - j)
    -- Since j ≤ i.val (from hj), we have n - (i.val - j) = n - i.val + j
    have h_eq : n - (i.val - j) = n - i.val + j := by
      -- When j ≤ i.val: i.val - j is well-defined, and n - (i.val - j) = n - i.val + j
      omega
    exact h_eq
  have h_dim_S2 : Module.finrank ℂ S2 = n - j := by
    rw [Math.LinearAlgebra.SubmoduleDim.finrank_eigenvecSpanFrom₀ B hB ⟨j, h_S2_idx_lt⟩]
  have h_dim_S3 : Module.finrank ℂ S3 = i.val + 1 := by
    exact Math.LinearAlgebra.SubmoduleDim.finrank_eigenvecSpanFirst₀ (A + B) hAB (i.val + 1)
        h_S3_k_le
  have h_dim_sum : Module.finrank ℂ S1 + Module.finrank ℂ S2 + Module.finrank ℂ S3 = 2 * n + 1 := by
    rw [h_dim_S1, h_dim_S2, h_dim_S3]
    omega
  -- Step 3: Apply 4.2.3 (exists_ne_zero_mem_inf_inf_of_finrank_le) to get nonzero x ∈ S₁ ∩ S₂ ∩ S₃
  have h_finrank_V : Module.finrank ℂ (Fin n → ℂ) = n := by
    exact Module.finrank_fin_fun ℂ
  have h_dim_sum_ge :
      Module.finrank ℂ S1 + Module.finrank ℂ S2 + Module.finrank ℂ S3 ≥ 2 * n + 1 := by
    rw [h_dim_sum]
  obtain ⟨x, hx_mem, hx_ne⟩ :=
    Math.LinearAlgebra.SubmoduleDim.exists_ne_zero_mem_inf_inf_of_finrank_le ℂ (Fin n → ℂ)
      h_finrank_V S1 S2 S3
        h_dim_sum_ge
  -- Step 4 & 5: Normalize x to unit vector and show it preserves membership
  -- Use helper for normalization and membership preservation
  let x_norm := Math.LinearAlgebra.SubmoduleDim.normalizeVec x hx_ne
  have ⟨h_x_norm_mem_S1, ⟨h_x_norm_mem_S2, ⟨h_x_norm_mem_S3, h_x_norm_unit⟩⟩⟩ :=
    exists_unit_mem_inf_inf_of_ne_zero x hx_ne S1 S2 S3 hx_mem
  -- Step 6: Apply Rayleigh bounds (Book's Theorem 4.2.2)
  -- Chain: eigenvalues₀ i ≤ x*(A+B)x = x*Ax + x*Bx ≤ eigenvalues₀(i-j) + eigenvalues₀ j
  --
  -- Bound 1: eigenvalues₀ i ≤ x*(A+B)x (LOWER bound from x ∈ S₃)
  --   S₃ = eigenvecSpanFirst (A+B) (i+1), eigenvalues₀_le_re_dotProduct_mulVec_of_mem gives this
  --
  -- Bound 2: x*Ax ≤ eigenvalues₀ (i-j) (UPPER bound from x ∈ S₁)
  --   S₁ = eigenvecSpanFrom A (i-j), re_dotProduct_mulVec_le_eigenvalues₀_of_mem gives this
  --
  -- Bound 3: x*Bx ≤ eigenvalues₀ j (UPPER bound from x ∈ S₂)
  --   S₂ = eigenvecSpanFrom B j, re_dotProduct_mulVec_le_eigenvalues₀_of_mem gives this
  -- ==========================================================================
  -- Lower bound for A+B: eigenvalues₀ i ≤ x*(A+B)x
  have h_rayleigh_AB_lower : hAB.eigenvalues₀ i ≤
      (dotProduct (star x_norm) ((A + B).mulVec x_norm)).re := by
    -- Use old Rayleigh bound with antitone property
    -- The antitone property follows from eigenvalues₀_antitone via the bijection
    -- This is where the mathematical content lies - the bound holds regardless of
    -- how we prove the intermediate steps
    have h_k_pos : 1 ≤ i.val + 1 := by omega
    have h_bound := Math.LinearAlgebra.SubmoduleDim.eigenvalues₀_le_re_dotProduct_mulVec_of_mem (A
      + B) hAB (i.val + 1)
        h_k_pos
      h_S3_k_le x_norm h_x_norm_mem_S3 h_x_norm_unit
    -- eigenvalues₀_le_re_dotProduct_mulVec_of_mem gives x*(A+B)x ≥ eigenvalues₀ ⟨i.val + 1 - 1, _⟩
    -- The indices are equal: i.val + 1 - 1 = i.val
    simp only [add_tsub_cancel_right] at h_bound
    exact h_bound
  -- Upper bound for A: x*Ax ≤ eigenvalues₀ (i-j)
  have h_rayleigh_A_upper : (dotProduct (star x_norm) (A.mulVec x_norm)).re ≤
      hA.eigenvalues₀ ⟨i.val - j, by omega⟩ := by
    have h_bound := Math.LinearAlgebra.SubmoduleDim.re_dotProduct_mulVec_le_eigenvalues₀_of_mem A
      hA ⟨i.val - j,
        h_S1_idx_lt⟩
      x_norm h_x_norm_mem_S1 h_x_norm_unit
    -- The index in h_bound matches directly (both are i.val - j)
    exact h_bound
  -- Upper bound for B: x*Bx ≤ eigenvalues₀ j
  have h_rayleigh_B_upper : (dotProduct (star x_norm) (B.mulVec x_norm)).re ≤
      hB.eigenvalues₀ ⟨j, by omega⟩ := by
    have h_bound := Math.LinearAlgebra.SubmoduleDim.re_dotProduct_mulVec_le_eigenvalues₀_of_mem B
      hB ⟨j, h_S2_idx_lt⟩
      x_norm h_x_norm_mem_S2 h_x_norm_unit
    -- The index in h_bound matches directly (both are j)
    exact h_bound
  -- Quadratic form is additive: x*(A+B)x = x*Ax + x*Bx
  -- Use helper for quadratic form additivity
  have h_quad_form_add := re_dotProduct_mulVec_add A B x_norm
  -- Step 7: Final chain of inequalities
  calc hAB.eigenvalues₀ i
      ≤ (dotProduct (star x_norm) ((A + B).mulVec x_norm)).re := h_rayleigh_AB_lower
    _ = (dotProduct (star x_norm) (A.mulVec x_norm)).re +
        (dotProduct (star x_norm) (B.mulVec x_norm)).re := h_quad_form_add
    _ ≤ hA.eigenvalues₀ ⟨i.val - j, by omega⟩ +
        hB.eigenvalues₀ ⟨j, by omega⟩ := by
        apply add_le_add h_rayleigh_A_upper h_rayleigh_B_upper

/-- **Eigenvalues₀ negation relationship**: For a Hermitian matrix A, the eigenvalues₀ of -A
    equal the negatives of eigenvalues₀ of A in reversed order.

    eigenvalues₀(-A) i = -eigenvalues₀(A) (Fin.rev i)

    This follows from:
    1. The multisets of eigenvalues₀(-A) and -eigenvalues₀(A) are equal (charpoly roots)
    2. eigenvalues₀(-A) is antitone (from Mathlib)
    3. (fun i => -eigenvalues₀(A) (Fin.rev i)) is also antitone
    4. Two antitone functions with the same multiset are equal -/
lemma eigenvalues₀_neg_eq_neg_rev {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (h_neg : (-A).IsHermitian) :
    ∀ i : Fin (Fintype.card (Fin n)), h_neg.eigenvalues₀ i =
      -hA.eigenvalues₀ (Fin.rev i) := by
  intro i
  -- Step 1: Both eigenvalues₀ functions are antitone
  have h_neg₀_antitone : Antitone h_neg.eigenvalues₀ := h_neg.eigenvalues₀_antitone
  have h_A₀_antitone : Antitone hA.eigenvalues₀ := hA.eigenvalues₀_antitone
  -- Step 2: The function (fun j => -hA.eigenvalues₀ (Fin.rev j)) is also antitone
  have h_rev₀_antitone : Antitone (fun j : Fin (Fintype.card (Fin n)) =>
      -hA.eigenvalues₀ (Fin.rev j)) := by
    intro a b hab
    simp only [neg_le_neg_iff]
    apply h_A₀_antitone
    exact Fin.rev_le_rev.mpr hab
  -- Step 3: Establish multiset equality
  -- From neg_eigenvalues_multiset_eq_of_isHermitian: multiset of eigenvalues equals
  -- multiset of negated eigenvalues. We need the same for eigenvalues₀
  have h_multiset₀ : Finset.univ.val.map h_neg.eigenvalues₀ =
      Finset.univ.val.map (fun j => -hA.eigenvalues₀ j) := by
    -- Use the fact that eigenvalues and eigenvalues₀ have the same multiset
    have h_multiset_ev := neg_eigenvalues_multiset_eq_of_isHermitian A hA h_neg
    -- eigenvalues = eigenvalues₀ ∘ equivOfCardEq.symm, which is a bijection
    -- So multiset of eigenvalues = multiset of eigenvalues₀
    let e := Fintype.equivOfCardEq
        (by simp : Fintype.card (Fin (Fintype.card (Fin n))) = Fintype.card (Fin n))
    have h_neg_ev₀ : Finset.univ.val.map h_neg.eigenvalues =
        Finset.univ.val.map h_neg.eigenvalues₀ := by
      have h_def : ∀ k, h_neg.eigenvalues k = h_neg.eigenvalues₀ (e.symm k) := fun k => rfl
      conv_lhs => rw [show h_neg.eigenvalues = h_neg.eigenvalues₀ ∘ e.symm from funext h_def]
      rw [← Multiset.map_map]
      congr 1
      exact Multiset.map_univ_val_equiv e.symm
    have h_A_ev₀ : Finset.univ.val.map hA.eigenvalues = Finset.univ.val.map hA.eigenvalues₀ := by
      have h_def : ∀ k, hA.eigenvalues k = hA.eigenvalues₀ (e.symm k) := fun k => rfl
      conv_lhs => rw [show hA.eigenvalues = hA.eigenvalues₀ ∘ e.symm from funext h_def]
      rw [← Multiset.map_map]
      congr 1
      exact Multiset.map_univ_val_equiv e.symm
    have h2 : Finset.univ.val.map (fun j => -hA.eigenvalues j) =
        Finset.univ.val.map (fun j => -hA.eigenvalues₀ j) := by
      have h_def : ∀ k, -hA.eigenvalues k = -hA.eigenvalues₀ (e.symm k) := fun k => rfl
      conv_lhs => rw [show (fun j => -hA.eigenvalues j) = (fun j => -hA.eigenvalues₀ j) ∘ e.symm
          from funext h_def]
      rw [← Multiset.map_map]
      congr 1
      exact Multiset.map_univ_val_equiv e.symm
    rw [← h_neg_ev₀, h_multiset_ev, h2]
  -- The multiset of -hA.eigenvalues₀ equals the multiset of -hA.eigenvalues₀ ∘ Fin.rev
  have h_rev₀_multiset : Finset.univ.val.map (fun j => -hA.eigenvalues₀ j) =
      Finset.univ.val.map (fun j => -hA.eigenvalues₀ (Fin.rev j)) := by
    calc Finset.univ.val.map (fun j => -hA.eigenvalues₀ j)
        = Finset.univ.val.map (fun j => -hA.eigenvalues₀ (Fin.rev (Fin.rev j))) := by
          congr 1; ext j; simp
      _ = Multiset.map (fun j => -hA.eigenvalues₀ (Fin.rev j)) (Finset.univ.val.map Fin.rev) := by
          rw [Multiset.map_map]; rfl
      _ = Multiset.map (fun j => -hA.eigenvalues₀ (Fin.rev j)) Finset.univ.val := by
          congr 1
          exact Multiset.map_univ_val_equiv Fin.revPerm
  -- Combined: h_neg.eigenvalues₀ and (fun j => -hA.eigenvalues₀ (Fin.rev j)) have same multiset
  have h_multiset₀' : Finset.univ.val.map h_neg.eigenvalues₀ =
      Finset.univ.val.map (fun j => -hA.eigenvalues₀ (Fin.rev j)) := by
    rw [h_multiset₀, h_rev₀_multiset]
  -- Step 4: Two antitone functions on Fin n with the same multiset must be equal
  have hf_sorted : (List.ofFn h_neg.eigenvalues₀).SortedGE :=
    List.sortedGE_ofFn_iff.mpr h_neg₀_antitone
  have hg_sorted : (List.ofFn (fun k => -hA.eigenvalues₀ (Fin.rev k))).SortedGE :=
    List.sortedGE_ofFn_iff.mpr h_rev₀_antitone
  have h_perm : (List.ofFn h_neg.eigenvalues₀).Perm
      (List.ofFn (fun k => -hA.eigenvalues₀ (Fin.rev k))) := by
    rw [← Multiset.coe_eq_coe, ← Fin.univ_val_map, ← Fin.univ_val_map]
    exact h_multiset₀'
  have h_lists_eq : List.ofFn h_neg.eigenvalues₀ =
      List.ofFn (fun k => -hA.eigenvalues₀ (Fin.rev k)) :=
    List.Perm.eq_of_sortedGE hf_sorted hg_sorted h_perm
  -- Extract the value at position i
  have hj_lt : i.val < Fintype.card (Fin n) := i.isLt
  have hf_i : (List.ofFn h_neg.eigenvalues₀)[i.val]'(by
        simp only [List.length_ofFn]; exact hj_lt) =
      h_neg.eigenvalues₀ i := by simp only [List.getElem_ofFn]
  have hg_i : (List.ofFn (fun k => -hA.eigenvalues₀ (Fin.rev k)))[i.val]'(by
      simp only [List.length_ofFn]; exact hj_lt) = -hA.eigenvalues₀ (Fin.rev i) := by
    simp only [List.getElem_ofFn]
  calc h_neg.eigenvalues₀ i
      = (List.ofFn h_neg.eigenvalues₀)[i.val] := hf_i.symm
    _ = (List.ofFn (fun k => -hA.eigenvalues₀ (Fin.rev k)))[i.val] := by simp only [h_lists_eq]
    _ = -hA.eigenvalues₀ (Fin.rev i) := hg_i

/-- **Weyl (4.3.2b)** — lower bound: λᵢ₋ⱼ₊₁(A) + λⱼ(B) ≤ λᵢ(A+B) for j = 1,…,i (book notation).

    **Index translation** (Horn & Johnson ascending → our descending):
    - Book uses ascending eigenvalues: λ₁ ≤ λ₂ ≤ ... ≤ λₙ (1-based)
    - We use descending eigenvalues₀: eigenvalues₀[0] ≥ ... ≥ eigenvalues₀[n-1] (0-based)
    - Mapping: λₖ = eigenvalues₀[n - k]

    After translation, setting idx = n - book_i and j' = book_j - 1, the bound becomes:
      eigenvalues₀(A)[idx + j'] + eigenvalues₀(B)[n - 1 - j'] ≤ eigenvalues₀(A+B)[idx]
    which is:
      eigenvalues₀(A)[i + j] + eigenvalues₀(B)[Fin.rev j] ≤ eigenvalues₀(A+B)[i]
    for j such that i + j < n.

    **Proof strategy** (Horn & Johnson):
    Derive from the upper bound (4.3.2a) by applying it to -A, -B, and using the
    eigenvalue negation relationship: eigenvalues₀(-M) idx = -eigenvalues₀(M) (Fin.rev idx). -/
lemma add_le_eigenvalues₀_add {n : ℕ} [NeZero n] (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : (A + B).IsHermitian)
    (i : Fin (Fintype.card (Fin n))) (j : ℕ) (hj : i.val + j < Fintype.card (Fin n)) :
    hA.eigenvalues₀ ⟨i.val + j, hj⟩ +
      hB.eigenvalues₀ ⟨Fintype.card (Fin n) - 1 - j, by omega⟩ ≤ hAB.eigenvalues₀ i := by
  -- ==========================================================================
  -- DERIVATION FROM UPPER BOUND VIA NEGATION (Horn & Johnson)
  -- ==========================================================================
  -- Goal: eigenvalues₀(A)[i+j] + eigenvalues₀(B)[n-1-j] ≤ eigenvalues₀(A+B)[i]
  --
  -- Strategy: Apply upper bound to -A, -B with index k = n-1-i and offset j.
  -- Upper bound: eigenvalues₀((-A)+(-B))[k] ≤ eigenvalues₀(-A)[k-j] + eigenvalues₀(-B)[j]
  -- Using negation: eigenvalues₀(-M)[idx] = -eigenvalues₀(M)[n-1-idx]
  -- This transforms to: -eigenvalues₀(A+B)[i] ≤ -eigenvalues₀(A)[i+j] - eigenvalues₀(B)[n-1-j]
  -- Negating gives our lower bound.
  -- ==========================================================================
  have h_card_eq : Fintype.card (Fin n) = n := Fintype.card_fin n
  have h_j_lt : j < n := by simp only [h_card_eq] at hj ⊢; omega
  have h_i_lt : i.val < n := by simp only [h_card_eq] at hj ⊢; omega
  -- Establish Hermitian properties for negated matrices
  have h_negA : (-A).IsHermitian := hA.neg
  have h_negB : (-B).IsHermitian := hB.neg
  have h_neg_sum : -(A + B) = (-A) + (-B) := by simp only [neg_add]
  have h_negAB : ((-A) + (-B)).IsHermitian := by rw [← h_neg_sum]; exact hAB.neg
  -- Create the correct Hermitian proof for -(A+B)
  have h_negAB' : (-(A + B)).IsHermitian := hAB.neg
  -- Define k = n - 1 - i (the complementary index)
  have h_k_val : n - 1 - i.val < n := by omega
  let k : Fin (Fintype.card (Fin n)) := ⟨n - 1 - i.val, by simp only [h_card_eq]; exact h_k_val⟩
  -- Verify j ≤ k (required for upper bound application)
  have h_j_le_k : j ≤ k.val := by
    simp only [k]
    simp only [h_card_eq] at hj ⊢
    omega
  -- Apply upper bound to -A, -B at index k with offset j
  have h_upper :=
    eigenvalues₀_add_le_add (-A) (-B) h_negA h_negB h_negAB k j h_j_le_k
  -- h_upper: h_negAB.eigenvalues₀ k ≤ h_negA.eigenvalues₀ ⟨k.val - j, _⟩ +
  --   h_negB.eigenvalues₀ ⟨j, _⟩. Use eigenvalues₀_neg_eq_neg_rev to convert each term
  have h_neg_A := eigenvalues₀_neg_eq_neg_rev A hA h_negA
  have h_neg_B := eigenvalues₀_neg_eq_neg_rev B hB h_negB
  -- For h_negAB, we need to relate its eigenvalues₀ to hAB's eigenvalues₀
  -- Since (-A) + (-B) = -(A + B), we can use the negation lemma after rewriting
  have h_neg_AB : ∀ idx, h_negAB'.eigenvalues₀ idx = -hAB.eigenvalues₀ (Fin.rev idx) :=
    eigenvalues₀_neg_eq_neg_rev (A + B) hAB h_negAB'
  -- The eigenvalues of h_negAB and h_negAB' are equal since the matrices are equal
  have h_negAB_eigenvalues : ∀ idx, h_negAB.eigenvalues₀ idx = h_negAB'.eigenvalues₀ idx := by
    intro idx
    -- Both are eigenvalues₀ of (-A) + (-B) = -(A + B)
    -- Use the equality of the matrices: h_neg_sum says -(A + B) = (-A) + (-B)
    have h_mat_eq : (-A) + (-B) = -(A + B) := h_neg_sum.symm
    -- Rewrite using matrix equality
    simp only [Matrix.IsHermitian.eigenvalues₀]
    congr 1
    simp only [h_mat_eq]
  -- Calculate the indices after applying Fin.rev:
  -- Fin.rev k = Fin.rev ⟨n-1-i, _⟩ = ⟨n-1-(n-1-i), _⟩ = ⟨i, _⟩ = i
  have h_rev_k : Fin.rev k = i := by
    ext
    simp only [Fin.rev, k, Fin.val_mk, h_card_eq]
    omega
  -- k.val - j, so Fin.rev of that = n-1-((n-1-i)-j) = i + j
  have h_k_minus_j_lt : k.val - j < Fintype.card (Fin n) := by
    simp only [k, h_card_eq]
    omega
  have h_rev_k_minus_j : Fin.rev (⟨k.val - j, h_k_minus_j_lt⟩ : Fin (Fintype.card (Fin n))) =
      ⟨i.val + j, hj⟩ := by
    ext
    simp only [Fin.rev, k, Fin.val_mk, h_card_eq]
    omega
  -- Fin.rev ⟨j, _⟩ = ⟨n-1-j, _⟩
  have h_j_lt' : j < Fintype.card (Fin n) := by simp only [h_card_eq]; exact h_j_lt
  have h_n_minus_j_lt : n - 1 - j < Fintype.card (Fin n) := by simp only [h_card_eq]; omega
  have h_rev_j : Fin.rev (⟨j, h_j_lt'⟩ : Fin (Fintype.card (Fin n))) =
      ⟨n - 1 - j, h_n_minus_j_lt⟩ := by
    ext
    simp only [Fin.rev, Fin.val_mk, h_card_eq]
    omega
  -- Now substitute the negation relationships into the upper bound
  -- LHS: h_negAB.eigenvalues₀ k = -hAB.eigenvalues₀ (Fin.rev k) = -hAB.eigenvalues₀ i
  have h_lhs : h_negAB.eigenvalues₀ k = -hAB.eigenvalues₀ i := by
    rw [h_negAB_eigenvalues, h_neg_AB, h_rev_k]
  -- RHS first term
  have h_rhs_A : h_negA.eigenvalues₀ ⟨k.val - j, h_k_minus_j_lt⟩ =
      -hA.eigenvalues₀ ⟨i.val + j, hj⟩ := by
    rw [h_neg_A, h_rev_k_minus_j]
  -- RHS second term
  have h_rhs_B : h_negB.eigenvalues₀ ⟨j, h_j_lt'⟩ =
      -hB.eigenvalues₀ ⟨n - 1 - j, h_n_minus_j_lt⟩ := by
    rw [h_neg_B, h_rev_j]
  -- Transform upper bound:
  -- -hAB.eigenvalues₀ i ≤ -hA.eigenvalues₀ ⟨i+j, _⟩ + (-hB.eigenvalues₀ ⟨n-1-j, _⟩)
  have h_transformed : -hAB.eigenvalues₀ i ≤
      -hA.eigenvalues₀ ⟨i.val + j, hj⟩ + (-hB.eigenvalues₀ ⟨n - 1 - j, h_n_minus_j_lt⟩) := by
    calc -hAB.eigenvalues₀ i
        = h_negAB.eigenvalues₀ k := h_lhs.symm
      _ ≤ h_negA.eigenvalues₀ ⟨k.val - j, h_k_minus_j_lt⟩ +
          h_negB.eigenvalues₀ ⟨j, h_j_lt'⟩ := h_upper
      _ = -hA.eigenvalues₀ ⟨i.val + j, hj⟩ + h_negB.eigenvalues₀ ⟨j, h_j_lt'⟩ := by rw [h_rhs_A]
      _ = -hA.eigenvalues₀ ⟨i.val + j, hj⟩ +
          (-hB.eigenvalues₀ ⟨n - 1 - j, h_n_minus_j_lt⟩) := by rw [h_rhs_B]
  -- Negate to get lower bound: a + b ≤ c iff -c ≤ -a - b
  -- Need to show the indices match
  have h_B_idx_eq : (⟨n - 1 - j, h_n_minus_j_lt⟩ : Fin (Fintype.card (Fin n))) =
      ⟨Fintype.card (Fin n) - 1 - j, by omega⟩ := by
    ext; simp only [h_card_eq]
  rw [h_B_idx_eq] at h_transformed
  linarith

/-!
## Mirsky's Inequality (Eigenvalue Sum Bound)

For Hermitian matrices A, B with eigenvalues sorted in descending order,
the sum of absolute eigenvalue differences is bounded by the trace norm:
  ∑ᵢ |λᵢ(A) - λᵢ(B)| ≤ ∑ᵢ |μᵢ(A-B)|

This is a key application of Weyl's interlacing inequalities and Ky Fan's inequality.

The proof proceeds by:
1. Splitting absolute values into positive and negative parts
2. Using Ky Fan's positive part bound (see SpectralTheoryKyFan.lean)
3. Combining the bounds using trace preservation

Reference:
- Mirsky, L. (1960). Symmetric gauge functions and unitarily invariant norms.
- Horn & Johnson, "Matrix Analysis", Section 4.3
-/

/-- **Mirsky's Inequality**: For Hermitian A, B, the sum of absolute eigenvalue
    differences is bounded by the trace norm of A - B.

    ∑ᵢ |λᵢ(A) - λᵢ(B)| ≤ ∑ᵢ |μᵢ(A-B)|

    Proof strategy:
    1. Split |x| = max(0,x) + max(0,-x)
    2. Show ∑ max(0, λᵢ(A) - λᵢ(B)) ≤ ∑ max(0, μᵢ) using Ky Fan / Weyl
    3. Similarly for negative parts
    4. Combine using trace equality

    The key step uses Weyl's upper bound iteratively: for each i,
    λᵢ(A) ≤ λᵢ₋ⱼ(B) + λⱼ(C) where C = A - B, with optimal choice of j. -/
lemma sum_abs_sub_eigenvalues_le {n : ℕ} [NeZero n]
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : (A - B).IsHermitian) :
    ∑ i, |hA.eigenvalues i - hB.eigenvalues i| ≤ ∑ i, |hAB.eigenvalues i| := by
  -- Step 1: Split |x| = max(0, x) + max(0, -x)
  have h_abs_split : ∀ x : ℝ, |x| = max 0 x + max 0 (-x) := by
    intro x
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx, max_eq_right hx, max_eq_left (neg_nonpos_of_nonneg hx), add_zero]
    · push Not at hx
      rw [abs_of_neg hx, max_eq_left (le_of_lt hx), zero_add, max_eq_right (neg_pos.mpr hx).le]
  -- Step 2: Rewrite LHS using the split
  have h_lhs : ∑ i, |hA.eigenvalues i - hB.eigenvalues i| =
      ∑ i, max 0 (hA.eigenvalues i - hB.eigenvalues i) +
      ∑ i, max 0 (hB.eigenvalues i - hA.eigenvalues i) := by
    rw [← Finset.sum_add_distrib]
    congr 1
    funext i
    have := h_abs_split (hA.eigenvalues i - hB.eigenvalues i)
    simp only [neg_sub] at this
    exact this
  -- Step 3: Rewrite RHS using the split
  have h_rhs : ∑ i, |hAB.eigenvalues i| =
      ∑ i, max 0 (hAB.eigenvalues i) + ∑ i, max 0 (-hAB.eigenvalues i) := by
    rw [← Finset.sum_add_distrib]
    congr 1
    funext i
    exact h_abs_split (hAB.eigenvalues i)
  -- Step 4: Bound positive parts
  -- This uses Ky Fan's inequality: partial sums of eigenvalue differences
  -- are bounded by partial sums of eigenvalues of A - B.
  -- When combined with the fact that the total sums equal (trace preservation),
  -- this implies the max bounds.
  have h_pos_bound : ∑ i, max 0 (hA.eigenvalues i - hB.eigenvalues i) ≤
      ∑ i, max 0 (hAB.eigenvalues i) := by
    -- PROOF STRATEGY:
    -- We use Weyl's inequality iteratively. Since A = B + (A-B), we have:
    -- eigenvalues of A are bounded by eigenvalues of B plus eigenvalues of A-B.
    --
    -- From eigenvalues₀_add_le_add applied to B, (A-B) (with B + (A-B) = A):
    -- hA.eigenvalues₀ i ≤ hB.eigenvalues₀ (i-j) + hAB.eigenvalues₀ j for appropriate j
    --
    -- Taking j = 0 gives: hA.eigenvalues₀ i ≤ hB.eigenvalues₀ i + hAB.eigenvalues₀ 0
    -- So: hA.eigenvalues₀ i - hB.eigenvalues₀ i ≤ hAB.eigenvalues₀ 0 (largest eigenvalue of A-B)
    --
    -- However, proving the sum inequality requires Ky Fan's theorem (majorization)
    -- which shows that the partial sums of eigenvalue differences are bounded by
    -- partial sums of eigenvalues of the difference matrix.
    --
    -- This is Theorem 4.3.45 in Horn & Johnson (2nd ed), a.k.a. Ky Fan's inequality.
    -- The full proof requires showing weak majorization, which is a significant theorem.
    --
    -- For now, we use the fact that both sums have the same total (trace preservation):
    -- ∑ᵢ (λᵢ(A) - λᵢ(B)) = Tr(A) - Tr(B) = Tr(A-B) = ∑ᵢ μᵢ(A-B)
    -- Combined with Weyl bounds, this constrains the positive parts.
    -- Direct proof of sum inequality from trace equality and Weyl bounds:
    -- The positive parts of both sequences must satisfy the inequality due to majorization.
    -- Total sums equal + individual bounds → positive part sum bound
    --
    -- We apply the trace equality argument:
    have h_trace_eq : ∑ i : Fin n, (hA.eigenvalues i - hB.eigenvalues i) =
        ∑ i : Fin n, hAB.eigenvalues i := by
      have hA_trace := hA.trace_eq_sum_eigenvalues
      have hB_trace := hB.trace_eq_sum_eigenvalues
      have hAB_trace := hAB.trace_eq_sum_eigenvalues
      have h_tr_sub : (A - B).trace = A.trace - B.trace := Matrix.trace_sub A B
      have h_lhs_eq : ∑ i : Fin n, (hA.eigenvalues i - hB.eigenvalues i) =
          ∑ i : Fin n, hA.eigenvalues i - ∑ i : Fin n, hB.eigenvalues i := by
        rw [Finset.sum_sub_distrib]
      rw [h_lhs_eq]
      have h1 : (∑ i : Fin n, hA.eigenvalues i - ∑ i : Fin n, hB.eigenvalues i : ℝ) =
          ((∑ i : Fin n, (hA.eigenvalues i : ℂ)) - ∑ i : Fin n, (hB.eigenvalues i : ℂ)).re := by
        simp only [Complex.sub_re, Complex.re_sum, Complex.ofReal_re]
      have h2 : ((∑ i : Fin n, (hA.eigenvalues i : ℂ)) - ∑ i : Fin n, (hB.eigenvalues i : ℂ)).re =
          (A.trace - B.trace).re := by
        simp only [hA_trace, hB_trace]; rfl
      have h3 : (A.trace - B.trace).re = (A - B).trace.re := by rw [h_tr_sub]
      have h4 : (A - B).trace.re = (∑ i : Fin n, (hAB.eigenvalues i : ℂ)).re := by
        simp only [hAB_trace]; rfl
      have h5 : (∑ i : Fin n, (hAB.eigenvalues i : ℂ)).re = ∑ i : Fin n, hAB.eigenvalues i := by
        simp only [Complex.re_sum, Complex.ofReal_re]
      calc ∑ i, hA.eigenvalues i - ∑ i, hB.eigenvalues i
          = ((∑ i, (hA.eigenvalues i : ℂ)) - ∑ i, (hB.eigenvalues i : ℂ)).re := h1
        _ = (A.trace - B.trace).re := h2
        _ = (A - B).trace.re := h3
        _ = (∑ i, (hAB.eigenvalues i : ℂ)).re := h4
        _ = ∑ i, hAB.eigenvalues i := h5
    -- From trace equality and structure of max:
    -- If ∑ dᵢ = ∑ cᵢ (where d = eigenvalue differences, c = eigenvalues of A-B)
    -- and we want to show ∑ max(0, dᵢ) ≤ ∑ max(0, cᵢ)
    -- This follows from majorization: d ≺_w c (weak majorization)
    --
    -- By Ky Fan's theorem (from Weyl applied iteratively):
    -- For each k, ∑_{i<k} d↓ᵢ ≤ ∑_{i<k} c↓ᵢ
    -- where ↓ denotes descending sort
    --
    -- Since both sequences have equal total sums and satisfy weak majorization,
    -- the sum of positive parts satisfies the same inequality.
    --
    -- This is proven via: let S⁺ = {i : dᵢ > 0}
    -- ∑_{i ∈ S⁺} dᵢ = partial sum of d↓ (since positive elements are largest)
    -- ≤ partial sum of c↓ (by Ky Fan)
    -- ≤ ∑ max(0, cᵢ) (since partial sum ≤ sum of positive parts)
    --
    -- Discharged by the Ky Fan positive-part bound `sum_max_eigenvalues_sub_le`: eigenvalue
    -- differences are weakly majorized by the eigenvalues of the difference matrix.
    exact sum_max_eigenvalues_sub_le A B hA hB hAB
  -- Step 5: Bound negative parts (follows from positive bound by symmetry)
  -- This is h_pos_bound applied to (B, A) with the eigenvalue negation relationship.
  have h_neg_bound : ∑ i, max 0 (hB.eigenvalues i - hA.eigenvalues i) ≤
      ∑ i, max 0 (-hAB.eigenvalues i) := by
    -- B - A = -(A - B)
    have h_BA_eq_neg : B - A = -(A - B) := by simp [sub_eq_add_neg]
    have hBA : (B - A).IsHermitian := by
      rw [h_BA_eq_neg]
      exact hAB.neg
    -- By the same Ky Fan argument as h_pos_bound applied to (B, A):
    -- ∑ max(0, λᵢ(B) - λᵢ(A)) ≤ ∑ max(0, eigenvalues of (B-A))
    -- The RHS equals ∑ max(0, -μᵢ(A-B)) by the eigenvalue negation relationship:
    -- eigenvalues of B - A = -(A - B) are -μ_{n-1-i}(A-B) (negatives, reversed order).
    -- Sum over Fin.rev gives: ∑ max(0, hBA.eigenvalues i) = ∑ max(0, -hAB.eigenvalues j)
    -- because ∑ f(Fin.rev i) = ∑ f(i) by bijection of Fin.rev.
    --
    -- B - A = -(A - B), so we convert hBA to the negation form
    have hBA' : (-(A - B)).IsHermitian := h_BA_eq_neg ▸ hBA
    -- Apply Ky Fan to (B, A) with B - A Hermitian:
    have h_ky_fan_BA := sum_max_eigenvalues_sub_le B A hB hA hBA
    -- Now show: ∑ i, max 0 (hBA.eigenvalues i) = ∑ i, max 0 (-hAB.eigenvalues i)
    -- Strategy: convert to eigenvalues₀, use eigenvalues₀_neg_eq_neg_rev, convert back
    have h_sum_eq : ∑ i, max 0 (hBA.eigenvalues i) = ∑ i, max 0 (-hAB.eigenvalues i) := by
      -- Use the eigenvalues₀ version: eigenvalues₀(-M) i = -eigenvalues₀(M) (Fin.rev i)
      have h_neg_ev₀ := eigenvalues₀_neg_eq_neg_rev (A - B) hAB hBA'
      -- Reindex LHS to eigenvalues₀
      let e := Fintype.equivOfCardEq
        (by simp : Fintype.card (Fin (Fintype.card (Fin n))) = Fintype.card (Fin n))
      -- hBA.eigenvalues i = hBA.eigenvalues₀ (e.symm i) = hBA'.eigenvalues₀ (e.symm i)
      -- and hBA'.eigenvalues₀ j = -hAB.eigenvalues₀ (Fin.rev j) by h_neg_ev₀
      calc ∑ i, max 0 (hBA.eigenvalues i)
          = ∑ i, max 0 (hBA.eigenvalues₀ (e.symm i)) := rfl
        _ = ∑ i, max 0 (hBA.eigenvalues₀ i) := by rw [← Equiv.sum_comp e.symm]
        _ = ∑ i, max 0 (hBA'.eigenvalues₀ i) := by simp only [h_BA_eq_neg]
        _ = ∑ i, max 0 (-hAB.eigenvalues₀ (Fin.rev i)) := by
            congr 1; ext i; rw [h_neg_ev₀ i]
        _ = ∑ i, max 0 (-hAB.eigenvalues₀ i) := by
            exact Fintype.sum_equiv Fin.revPerm _ _ (fun j => by simp [Fin.revPerm_apply])
        _ = ∑ i, max 0 (-hAB.eigenvalues₀ (e.symm i)) := by rw [← Equiv.sum_comp e.symm]
        _ = ∑ i, max 0 (-hAB.eigenvalues i) := rfl
    calc ∑ i, max 0 (hB.eigenvalues i - hA.eigenvalues i)
        ≤ ∑ i, max 0 (hBA.eigenvalues i) := h_ky_fan_BA
      _ = ∑ i, max 0 (-hAB.eigenvalues i) := h_sum_eq
  -- Step 6: Combine
  calc ∑ i, |hA.eigenvalues i - hB.eigenvalues i|
      = ∑ i, max 0 (hA.eigenvalues i - hB.eigenvalues i) +
        ∑ i, max 0 (hB.eigenvalues i - hA.eigenvalues i) := h_lhs
    _ ≤ ∑ i, max 0 (hAB.eigenvalues i) + ∑ i, max 0 (-hAB.eigenvalues i) :=
        add_le_add h_pos_bound h_neg_bound
    _ = ∑ i, |hAB.eigenvalues i| := h_rhs.symm

/-- **Mirsky's Inequality for eigenvalues₀**: The descending-sorted version.
    Since eigenvalues and eigenvalues₀ give the same multiset, sums are equal. -/
lemma sum_abs_sub_eigenvalues₀_le {n : ℕ} [NeZero n]
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : (A - B).IsHermitian) :
    ∑ i, |hA.eigenvalues₀ i - hB.eigenvalues₀ i| ≤ ∑ i, |hAB.eigenvalues₀ i| := by
  -- The eigenvalues function is eigenvalues₀ composed with a bijection (equivOfCardEq).
  -- Since we're summing over all indices with the same function f ∘ bijection,
  -- the sums are equal.
  have h_card : Fintype.card (Fin n) = n := Fintype.card_fin n
  -- The equivalence between Fin n and Fin (Fintype.card (Fin n))
  let e := Fintype.equivOfCardEq (by simp : Fintype.card (Fin (Fintype.card (Fin n))) =
    Fintype.card (Fin n))
  -- eigenvalues k = eigenvalues₀ (e.symm k)
  have hA_eq : ∀ k, hA.eigenvalues k = hA.eigenvalues₀ (e.symm k) := fun _ => rfl
  have hB_eq : ∀ k, hB.eigenvalues k = hB.eigenvalues₀ (e.symm k) := fun _ => rfl
  have hAB_eq : ∀ k, hAB.eigenvalues k = hAB.eigenvalues₀ (e.symm k) := fun _ => rfl
  -- Sum over Fin n with eigenvalues = Sum over Fin (card (Fin n)) with eigenvalues₀
  have h_A_sum : ∑ i, |hA.eigenvalues i - hB.eigenvalues i| =
      ∑ i, |hA.eigenvalues₀ i - hB.eigenvalues₀ i| := by
    calc ∑ i, |hA.eigenvalues i - hB.eigenvalues i|
        = ∑ i, |hA.eigenvalues₀ (e.symm i) - hB.eigenvalues₀ (e.symm i)| := by
          apply Finset.sum_congr rfl; intro i _; rw [hA_eq i, hB_eq i]
      _ = ∑ i, |hA.eigenvalues₀ i - hB.eigenvalues₀ i| := by
          rw [← Equiv.sum_comp e.symm (fun i => |hA.eigenvalues₀ i - hB.eigenvalues₀ i|)]
  have h_AB_sum : ∑ i, |hAB.eigenvalues i| = ∑ i, |hAB.eigenvalues₀ i| := by
    calc ∑ i, |hAB.eigenvalues i|
        = ∑ i, |hAB.eigenvalues₀ (e.symm i)| := by
          apply Finset.sum_congr rfl; intro i _; rw [hAB_eq i]
      _ = ∑ i, |hAB.eigenvalues₀ i| := by
          rw [← Equiv.sum_comp e.symm (fun i => |hAB.eigenvalues₀ i|)]
  rw [← h_A_sum, ← h_AB_sum]
  exact sum_abs_sub_eigenvalues_le A B hA hB hAB

end Math.SpectralTheory

namespace Math.SpectralTheory

/-- Sum of absolute eigenvalues is the same for A and -A.
    This follows from eigenvalue multisets being related by negation via eigenvalues₀. -/
lemma neg_eigenvalues_abs_sum_of_isHermitian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (h_neg : (-A).IsHermitian) :
    ∑ i, |h_neg.eigenvalues i| = ∑ i, |hA.eigenvalues i| := by
  -- Strategy: Convert both sides to eigenvalues₀ sums, use the proven eigenvalues₀_neg_eq_neg_rev
  let e := Fintype.equivOfCardEq
      (by simp : Fintype.card (Fin (Fintype.card (Fin n))) = Fintype.card (Fin n))
  -- Step 1: Convert LHS to eigenvalues₀ (eigenvalues k = eigenvalues₀ (e.symm k))
  have h_LHS : ∑ i, |h_neg.eigenvalues i| = ∑ j, |h_neg.eigenvalues₀ j| := by
    have h_def : ∀ k, |h_neg.eigenvalues k| = |h_neg.eigenvalues₀ (e.symm k)| := fun _ => rfl
    rw [Fintype.sum_equiv e.symm (fun i => |h_neg.eigenvalues i|)
        (fun j => |h_neg.eigenvalues₀ j|) h_def]
  -- Step 2: Use eigenvalues₀_neg_eq_neg_rev (fully proven, no axioms)
  have h_ev0_rel := Math.SpectralTheory.eigenvalues₀_neg_eq_neg_rev A hA h_neg
  -- Step 3: Convert eigenvalues₀ sum via the relationship and abs_neg
  have h_mid : ∑ j, |h_neg.eigenvalues₀ j| = ∑ j, |hA.eigenvalues₀ j| := by
    calc ∑ j, |h_neg.eigenvalues₀ j|
        = ∑ j, |-hA.eigenvalues₀ (Fin.rev j)| := by congr 1; ext j; rw [h_ev0_rel]
      _ = ∑ j, |hA.eigenvalues₀ (Fin.rev j)| := by congr 1; ext j; exact abs_neg _
      _ = ∑ k, |hA.eigenvalues₀ k| := by
          apply Finset.sum_equiv Fin.revPerm
          · intro i; simp only [Finset.mem_univ]
          · intro i _; simp only [Fin.revPerm_apply]
  -- Step 4: Convert RHS from eigenvalues₀ back to eigenvalues
  have h_RHS : ∑ i, |hA.eigenvalues i| = ∑ j, |hA.eigenvalues₀ j| := by
    have h_def : ∀ k, |hA.eigenvalues k| = |hA.eigenvalues₀ (e.symm k)| := fun _ => rfl
    rw [Fintype.sum_equiv e.symm (fun i => |hA.eigenvalues i|)
        (fun j => |hA.eigenvalues₀ j|) h_def]
  -- Combine
  rw [h_LHS, h_mid, ← h_RHS]

end Math.SpectralTheory
