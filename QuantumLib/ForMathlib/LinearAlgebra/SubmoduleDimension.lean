import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Sort
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Submodule Dimension — subspace intersection bounds, eigenvector spans, eigenvalue sorting

Submodule dimension lemmas (two- and three-subspace intersection bounds) for Weyl inequalities,
eigenvector span definitions, and sorted eigenvalue infrastructure.

## Main definitions
- `eigenvecSpanFirst`: Span of the first k eigenvectors
- `eigenvecSpanFrom`: Span of eigenvectors from index j onward
- `eigenvalues₀Fin`: Sorted eigenvalues indexed by `Fin n`

## Main statements
- `eq_conj_diagonal_eigenvalues₀Fin_of_antitone`: Spectral decomposition with sorted eigenvalues
- `eigenvalues_eq_eigenvalues₀Fin`: Equivalence of eigenvalue orderings
-/

namespace Math.LinearAlgebra.SubmoduleDim

variable (𝕜 : Type*) [DivisionRing 𝕜] (V : Type*) [AddCommGroup V] [Module 𝕜 V]

/-- **0.1.7.2** Two-subspace dimension lower bound: dim(S ∩ T) ≥ dim S + dim T - dim V.
    Follows from (0.1.7.1) dim(S ∩ T) + dim(S + T) = dim S + dim T and dim(S + T) ≤ dim V. -/
lemma sub_le_finrank_inf
    {n : ℕ} [FiniteDimensional 𝕜 V]
    (hdim : Module.finrank 𝕜 V = n)
    (S T : Submodule 𝕜 V)
    [FiniteDimensional 𝕜 S] [FiniteDimensional 𝕜 T] :
    Module.finrank 𝕜 (Min.min (α := Submodule 𝕜 V) S T) ≥
      Module.finrank 𝕜 S + Module.finrank 𝕜 T - n := by
  have heq := Submodule.finrank_sup_add_finrank_inf_eq S T
  have hsup : Module.finrank 𝕜 (Max.max (α := Submodule 𝕜 V) S T) ≤ n := by
    rw [← hdim]; exact Submodule.finrank_le _
  have hle : Module.finrank 𝕜 (Max.max (α := Submodule 𝕜 V) S T) ≤
      Module.finrank 𝕜 S + Module.finrank 𝕜 T := by
    rw [← heq, Nat.add_comm]; exact Nat.le_add_left _ _
  have hsub : Module.finrank 𝕜 S + Module.finrank 𝕜 T -
      Module.finrank 𝕜 (Max.max (α := Submodule 𝕜 V) S T) =
      Module.finrank 𝕜 (Min.min (α := Submodule 𝕜 V) S T) := by
    rw [← heq, Nat.add_comm (Module.finrank 𝕜 (Max.max (α := Submodule 𝕜 V) S T))
      (Module.finrank 𝕜 (Min.min (α := Submodule 𝕜 V) S T))]; exact Nat.add_sub_cancel _ _
  rw [← hsub]
  exact Nat.sub_le_sub_left hsup (Module.finrank 𝕜 S + Module.finrank 𝕜 T)

/-- If three subspaces of an n-dimensional space have dimensions summing to at least 2n+1,
    their intersection is nontrivial (book 4.2.3).
    Proof: dim(S1 ⊓ S2) ≥ d1 + d2 - n, then dim((S1 ⊓ S2) ⊓ S3) ≥ d1 + d2 + d3 - 2n ≥ 1. -/
lemma exists_ne_zero_mem_inf_inf_of_finrank_le
    {n : ℕ} [FiniteDimensional 𝕜 V]
    (hdim : Module.finrank 𝕜 V = n)
    (S1 S2 S3 : Submodule 𝕜 V)
    [FiniteDimensional 𝕜 S1] [FiniteDimensional 𝕜 S2] [FiniteDimensional 𝕜 S3]
    (hsum : Module.finrank 𝕜 S1 + Module.finrank 𝕜 S2 + Module.finrank 𝕜 S3 ≥ 2 * n + 1) :
    ∃ x : V, x ∈ Min.min (α := Submodule 𝕜 V) (Min.min (α := Submodule 𝕜 V) S1 S2) S3 ∧ x ≠ 0 := by
  set d1 := Module.finrank 𝕜 S1
  set d2 := Module.finrank 𝕜 S2
  set d3 := Module.finrank 𝕜 S3
  set S12 := Min.min (α := Submodule 𝕜 V) S1 S2
  have h12 : Module.finrank 𝕜 S12 ≥ d1 + d2 - n := sub_le_finrank_inf 𝕜 V hdim S1 S2
  set S123 := Min.min (α := Submodule 𝕜 V) S12 S3
  have h123 : Module.finrank 𝕜 S123 ≥ d1 + d2 + d3 - 2 * n := by
    calc Module.finrank 𝕜 S123
        ≥ Module.finrank 𝕜 S12 + d3 - n := sub_le_finrank_inf 𝕜 V hdim S12 S3
      _ ≥ (d1 + d2 - n) + d3 - n := Nat.sub_le_sub_right (Nat.add_le_add_right h12 d3) n
      _ ≥ d1 + d2 + d3 - 2 * n := by omega
  have hdim_pos : Module.finrank 𝕜 S123 ≥ 1 := by
    have hsum' : d1 + d2 + d3 ≥ 2 * n + 1 := hsum
    have h_one : (2 * n + 1) - (2 * n) = 1 := by omega
    have h_low : 1 ≤ (d1 + d2 + d3) - (2 * n) := by
      rw [← h_one]; exact Nat.sub_le_sub_right hsum' (2 * n)
    exact Nat.le_trans h_low h123
  have hne_bot : S123 ≠ ⊥ := by
    intro heq
    rw [heq, finrank_bot 𝕜 V] at hdim_pos
    omega
  obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
  exact ⟨x, hx_mem, hx_ne⟩

/-!
### 4.2.2 Variational (Rayleigh) bounds (Horn & Johnson)

For a Hermitian matrix A with eigenvalues in descending order (eigenvalues₀):
- If x is a unit vector in the span of the first k eigenvectors, then the Rayleigh quotient
  (star x ⬝ᵥ (A *ᵥ x)).re is at least the k-th largest eigenvalue (index k-1 in 0-based).
- If x is a unit vector in the span of the eigenvectors for indices k,…,n-1, then the
  Rayleigh quotient is at most the k-th eigenvalue (0-based).
-/

open Matrix
section Rayleigh42

variable {n : ℕ} [NeZero n] [DecidableEq (Fin n)]

/-- Span of the first k columns of the eigenvector unitary (first k eigenvectors). -/
noncomputable def eigenvecSpanFirst (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (k : ℕ) (hk : k ≤ n) :
    Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ (Set.range (fun j : Fin k =>
    Matrix.col (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) (Fin.castLE hk j)))

/-- Span of the last (n - k) columns (eigenvectors for eigenvalues₀ indices k,…,n-1). -/
noncomputable def eigenvecSpanFrom (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (k : Fin n) :
    Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ (Set.range (fun j : Fin (n - k.val) =>
    Matrix.col (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) ⟨k.val + j.val, by omega⟩))

omit [NeZero n] in
/-- The first k columns of the eigenvector unitary are linearly independent.
    This follows from the fact that Uᴴ * U = 1, so the columns are orthonormal. -/
private lemma linearIndependent_eigenvecSpanFirst
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (k : ℕ) (hk : k ≤ n) :
    LinearIndependent ℂ (fun j : Fin k =>
      Matrix.col (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) (Fin.castLE hk j)) := by
  let U := hA.eigenvectorUnitary.val
  have h_UU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  -- Use Fintype.linearIndependent_iffₛ since Fin k is a Fintype
  rw [Fintype.linearIndependent_iffₛ]
  intro f g h_eq j
  -- We need to show f j = g j
  -- The equality h_eq says: ∑ᵢ f i • v i = ∑ᵢ g i • v i
  -- Take dot product with the j-th eigenvector
  let j_cast := Fin.castLE hk j
  have h_dot : dotProduct (star (U · j_cast))
      (∑ i : Fin k, f i • Matrix.col U (Fin.castLE hk i)) =
      dotProduct (star (U · j_cast))
      (∑ i : Fin k, g i • Matrix.col U (Fin.castLE hk i)) := by
    rw [h_eq]
  -- Expand both sides
  have h_expand_l : dotProduct (star (U · j_cast))
      (∑ i : Fin k, f i • Matrix.col U (Fin.castLE hk i)) =
      ∑ i : Fin k, f i * dotProduct (star (U · j_cast)) (Matrix.col U (Fin.castLE hk i)) := by
    rw [dotProduct_sum]
    congr 1
    ext i
    rw [dotProduct_smul, smul_eq_mul]
  have h_expand_r : dotProduct (star (U · j_cast))
      (∑ i : Fin k, g i • Matrix.col U (Fin.castLE hk i)) =
      ∑ i : Fin k, g i * dotProduct (star (U · j_cast)) (Matrix.col U (Fin.castLE hk i)) := by
    rw [dotProduct_sum]
    congr 1
    ext i
    rw [dotProduct_smul, smul_eq_mul]
  rw [h_expand_l, h_expand_r] at h_dot
  -- Now use orthonormality: dotProduct (star (U · j)) (U · i) = (Uᴴ * U) j i = δⱼᵢ
  have h_orthonormal : ∀ i : Fin k,
      dotProduct (star (U · j_cast)) (Matrix.col U (Fin.castLE hk i)) =
      if j_cast = Fin.castLE hk i then 1 else 0 := by
    intro i
    let i_cast := Fin.castLE hk i
    have h_dot_eq : dotProduct (star (U · j_cast)) (Matrix.col U i_cast) =
        (Uᴴ * U) j_cast i_cast := by
      simp only [dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, Pi.star_apply,
                 Matrix.col_apply]
    rw [h_dot_eq, h_UU, Matrix.one_apply]
  -- Simplify both sums using orthonormality
  have h_sum_f : ∑ i : Fin k,
      f i * dotProduct (star (U · j_cast)) (Matrix.col U (Fin.castLE hk i)) = f j := by
    rw [Finset.sum_eq_single j]
    · rw [h_orthonormal j]
      have h_j_eq : j_cast = Fin.castLE hk j := rfl
      simp only [h_j_eq, ite_true, mul_one]
    · intro i _ hi_ne
      rw [h_orthonormal i]
      have h_ne : j_cast ≠ Fin.castLE hk i := by
        intro heq
        have h_val_eq : j_cast.val = (Fin.castLE hk i).val := congrArg Fin.val heq
        have h_j_val : j_cast.val = j.val := rfl
        have h_i_val : (Fin.castLE hk i).val = i.val := rfl
        rw [h_j_val, h_i_val] at h_val_eq
        have h_eq_val : i.val = j.val := h_val_eq.symm
        exact hi_ne (Fin.ext h_eq_val)
      simp only [ite_eq_right h_ne, mul_zero]
    · intro hj_not_mem
      exfalso
      exact hj_not_mem (Finset.mem_univ j)
  have h_sum_g : ∑ i : Fin k,
      g i * dotProduct (star (U · j_cast)) (Matrix.col U (Fin.castLE hk i)) = g j := by
    rw [Finset.sum_eq_single j]
    · rw [h_orthonormal j]
      have h_j_eq : j_cast = Fin.castLE hk j := rfl
      simp only [h_j_eq, ite_true, mul_one]
    · intro i _ hi_ne
      rw [h_orthonormal i]
      have h_ne : j_cast ≠ Fin.castLE hk i := by
        intro heq
        have h_val_eq : j_cast.val = (Fin.castLE hk i).val := congrArg Fin.val heq
        have h_j_val : j_cast.val = j.val := rfl
        have h_i_val : (Fin.castLE hk i).val = i.val := rfl
        rw [h_j_val, h_i_val] at h_val_eq
        have h_eq_val : i.val = j.val := h_val_eq.symm
        exact hi_ne (Fin.ext h_eq_val)
      simp only [ite_eq_right h_ne, mul_zero]
    · intro hj_not_mem
      exfalso
      exact hj_not_mem (Finset.mem_univ j)
  rw [h_sum_f, h_sum_g] at h_dot
  exact h_dot

omit [NeZero n] in
/-- The eigenvectors from index k onwards are linearly independent.
    This follows from the fact that Uᴴ * U = 1, so the columns are orthonormal. -/
private lemma linearIndependent_eigenvecSpanFrom
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (k : Fin n) :
    LinearIndependent ℂ (fun j : Fin (n - k.val) =>
      Matrix.col (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) ⟨k.val + j.val, by omega⟩) := by
  let U := hA.eigenvectorUnitary.val
  have h_UU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  -- Use Fintype.linearIndependent_iffₛ since Fin (n - k.val) is a Fintype
  rw [Fintype.linearIndependent_iffₛ]
  intro f g h_eq j
  let j_idx : Fin n := ⟨k.val + j.val, by omega⟩
  -- The equality h_eq says: ∑ᵢ f i • v i = ∑ᵢ g i • v i
  -- Take dot product with the j-th eigenvector in this range
  have h_dot : dotProduct (star (U · j_idx))
      (∑ i : Fin (n - k.val), f i • Matrix.col U ⟨k.val + i.val, by omega⟩) =
      dotProduct (star (U · j_idx))
      (∑ i : Fin (n - k.val), g i • Matrix.col U ⟨k.val + i.val, by omega⟩) := by
    rw [h_eq]
  -- Expand both sides
  have h_expand_l : dotProduct (star (U · j_idx))
      (∑ i : Fin (n - k.val), f i • Matrix.col U ⟨k.val + i.val, by omega⟩) =
      ∑ i : Fin (n - k.val),
        f i * dotProduct (star (U · j_idx)) (Matrix.col U ⟨k.val + i.val, by omega⟩) := by
    rw [dotProduct_sum]
    congr 1
    ext i
    rw [dotProduct_smul, smul_eq_mul]
  have h_expand_r : dotProduct (star (U · j_idx))
      (∑ i : Fin (n - k.val), g i • Matrix.col U ⟨k.val + i.val, by omega⟩) =
      ∑ i : Fin (n - k.val),
        g i * dotProduct (star (U · j_idx)) (Matrix.col U ⟨k.val + i.val, by omega⟩) := by
    rw [dotProduct_sum]
    congr 1
    ext i
    rw [dotProduct_smul, smul_eq_mul]
  rw [h_expand_l, h_expand_r] at h_dot
  -- Use orthonormality
  have h_orthonormal : ∀ i : Fin (n - k.val),
      dotProduct (star (U · j_idx)) (Matrix.col U ⟨k.val + i.val, by omega⟩) =
      if j_idx = ⟨k.val + i.val, by omega⟩ then 1 else 0 := by
    intro i
    have h_dot_eq : dotProduct (star (U · j_idx)) (Matrix.col U ⟨k.val + i.val, by omega⟩) =
        (Uᴴ * U) j_idx ⟨k.val + i.val, by omega⟩ := by
      simp only [dotProduct, Matrix.mul_apply, Matrix.conjTranspose_apply, Pi.star_apply,
                 Matrix.col_apply]
    rw [h_dot_eq, h_UU, Matrix.one_apply]
  -- Simplify both sums using orthonormality
  have h_sum_f : ∑ i : Fin (n - k.val),
      f i * dotProduct (star (U · j_idx)) (Matrix.col U ⟨k.val + i.val, by omega⟩) = f j := by
    rw [Finset.sum_eq_single j]
    · rw [h_orthonormal j]
      have h_j_idx_eq : j_idx = ⟨k.val + j.val, by omega⟩ := by
        ext
        simp only [j_idx]
      simp only [h_j_idx_eq, ite_true, mul_one]
    · intro i _ hi_ne
      rw [h_orthonormal i]
      have h_ne : j_idx ≠ ⟨k.val + i.val, by omega⟩ := by
        intro heq
        have h_val_eq : j_idx.val = (⟨k.val + i.val, by omega⟩ : Fin n).val := congrArg Fin.val heq
        simp only [j_idx] at h_val_eq
        omega
      simp only [ite_eq_right h_ne, mul_zero]
    · intro hj_not_mem
      exfalso
      exact hj_not_mem (Finset.mem_univ j)
  have h_sum_g : ∑ i : Fin (n - k.val),
      g i * dotProduct (star (U · j_idx)) (Matrix.col U ⟨k.val + i.val, by omega⟩) = g j := by
    rw [Finset.sum_eq_single j]
    · rw [h_orthonormal j]
      have h_j_idx_eq : j_idx = ⟨k.val + j.val, by omega⟩ := by
        ext
        simp only [j_idx]
      simp only [h_j_idx_eq, ite_true, mul_one]
    · intro i _ hi_ne
      rw [h_orthonormal i]
      have h_ne : j_idx ≠ ⟨k.val + i.val, by omega⟩ := by
        intro heq
        have h_val_eq : j_idx.val = (⟨k.val + i.val, by omega⟩ : Fin n).val := congrArg Fin.val heq
        simp only [j_idx] at h_val_eq
        omega
      simp only [ite_eq_right h_ne, mul_zero]
    · intro hj_not_mem
      exfalso
      exact hj_not_mem (Finset.mem_univ j)
  rw [h_sum_f, h_sum_g] at h_dot
  exact h_dot

omit [NeZero n] in
/-- **Dimension lemma for eigenvecSpanFirst**: The span of the first k eigenvectors
    has dimension k. This follows from orthonormal vectors being linearly independent. -/
lemma finrank_eigenvecSpanFirst (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (k : ℕ) (hk : k ≤ n) :
    Module.finrank ℂ (eigenvecSpanFirst A hA k hk) = k := by
  -- The eigenvectors are linearly independent
  have h_linindep : LinearIndependent ℂ (fun j : Fin k =>
      Matrix.col (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) (Fin.castLE hk j)) :=
    linearIndependent_eigenvecSpanFirst A hA k hk
  -- Apply finrank_span_eq_card
  have h_finrank : Module.finrank ℂ (Submodule.span ℂ (Set.range (fun j : Fin k =>
      Matrix.col (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) (Fin.castLE hk j)))) =
      Fintype.card (Fin k) :=
    finrank_span_eq_card h_linindep
  -- Fintype.card (Fin k) = k
  have h_card : Fintype.card (Fin k) = k := Fintype.card_fin k
  rw [h_card] at h_finrank
  -- eigenvecSpanFirst is defined as this span
  simp only [eigenvecSpanFirst] at h_finrank ⊢
  exact h_finrank

omit [NeZero n] in
/-- **Dimension lemma for eigenvecSpanFrom**: The span of eigenvectors from index k
    has dimension n - k.val. This follows from orthonormal vectors being linearly independent. -/
lemma finrank_eigenvecSpanFrom (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (k : Fin n) :
    Module.finrank ℂ (eigenvecSpanFrom A hA k) = n - k.val := by
  -- The eigenvectors are linearly independent
  have h_linindep : LinearIndependent ℂ (fun j : Fin (n - k.val) =>
      Matrix.col (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) ⟨k.val + j.val, by omega⟩) :=
    linearIndependent_eigenvecSpanFrom A hA k
  -- Apply finrank_span_eq_card
  have h_finrank : Module.finrank ℂ (Submodule.span ℂ (Set.range (fun j : Fin (n - k.val) =>
      Matrix.col (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) ⟨k.val + j.val, by omega⟩))) =
      Fintype.card (Fin (n - k.val)) :=
    finrank_span_eq_card h_linindep
  -- Fintype.card (Fin (n - k.val)) = n - k.val
  have h_card : Fintype.card (Fin (n - k.val)) = n - k.val := Fintype.card_fin (n - k.val)
  rw [h_card] at h_finrank
  -- eigenvecSpanFrom is defined as this span
  simp only [eigenvecSpanFrom] at h_finrank ⊢
  exact h_finrank

/-!
### Vector Normalization Utilities

Helper functions for normalizing nonzero vectors to unit vectors.
These are needed for the Weyl inequality proof to normalize intersection vectors.
-/

/-- The squared norm of a vector: `(dotProduct (star x) x).re`. -/
noncomputable def vecNormSq {n : ℕ} (x : Fin n → ℂ) : ℝ := (dotProduct (star x) x).re

/-- The squared norm is non-negative. -/
lemma vecNormSq_nonneg {n : ℕ} (x : Fin n → ℂ) : 0 ≤ vecNormSq x := by
  unfold vecNormSq
  -- dotProduct (star x) x = ∑ᵢ |xᵢ|² ≥ 0
  have h_sum : dotProduct (star x) x = ∑ i : Fin n, star (x i) * x i := rfl
  rw [h_sum]
  have h_re_sum : (∑ i : Fin n, star (x i) * x i).re = ∑ i : Fin n, (star (x i) * x i).re :=
    Complex.re_sum Finset.univ (fun i => star (x i) * x i)
  rw [h_re_sum]
  apply Finset.sum_nonneg
  intro i _
  -- Each term is |xᵢ|² ≥ 0
  have h_norm_sq : (star (x i) * x i).re = Complex.normSq (x i) := by
    change ((starRingEnd ℂ) (x i) * x i).re = Complex.normSq (x i)
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  rw [h_norm_sq]
  exact Complex.normSq_nonneg (x i)

/-- The squared norm is positive for nonzero vectors. -/
lemma vecNormSq_pos {n : ℕ} (x : Fin n → ℂ) (hx : x ≠ 0) : 0 < vecNormSq x := by
  unfold vecNormSq
  -- Similar to the proof in normalizeVec
  have h_dot_pos : 0 < (dotProduct (star x) x).re := by
    have h_sum : dotProduct (star x) x = ∑ i : Fin n, star (x i) * x i := rfl
    rw [h_sum]
    have h_re_sum : (∑ i : Fin n, star (x i) * x i).re = ∑ i : Fin n, (star (x i) * x i).re :=
      Complex.re_sum Finset.univ (fun i => star (x i) * x i)
    rw [h_re_sum]
    have h_nonneg : ∀ i, 0 ≤ (star (x i) * x i).re := by
      intro i
      have h_norm_sq : (star (x i) * x i).re = Complex.normSq (x i) := by
        change ((starRingEnd ℂ) (x i) * x i).re = Complex.normSq (x i)
        rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
      rw [h_norm_sq]
      exact Complex.normSq_nonneg (x i)
    have h_pos : ∃ i, 0 < (star (x i) * x i).re := by
      by_contra h
      push Not at h
      have h_all_zero : ∀ i, x i = 0 := by
        intro i
        have h_nonpos : (star (x i) * x i).re ≤ 0 := h i
        have h_nonneg_i : 0 ≤ (star (x i) * x i).re := h_nonneg i
        have h_eq_zero : (star (x i) * x i).re = 0 := le_antisymm h_nonpos h_nonneg_i
        -- h_eq_zero says (star (x i) * x i).re = 0
        -- We need to show Complex.normSq (x i) = 0
        -- Since (star z * z).re = Complex.normSq z, we have Complex.normSq (x i) = 0
        have h_norm_sq_eq : (star (x i) * x i).re = Complex.normSq (x i) := by
          change ((starRingEnd ℂ) (x i) * x i).re = Complex.normSq (x i)
          rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
        rw [h_norm_sq_eq] at h_eq_zero
        -- Now h_eq_zero : Complex.normSq (x i) = 0
        exact Complex.normSq_eq_zero.mp h_eq_zero
      -- But then x = 0, contradicting hx
      have h_x_zero : x = 0 := by
        ext i
        exact h_all_zero i
      exact hx h_x_zero
    obtain ⟨i, hi⟩ := h_pos
    apply Finset.sum_pos'
    · exact fun i _ => h_nonneg i
    · exact ⟨i, Finset.mem_univ i, hi⟩
  exact h_dot_pos

/-- Normalize a nonzero vector `x : Fin n → ℂ` to a unit vector.
    The normalized vector satisfies `(dotProduct (star x_norm) x_norm).re = 1`.

    Definition: `x_norm = (1 / sqrt((dotProduct (star x) x).re)) • x`
    where the squared norm is `(dotProduct (star x) x).re`. -/
noncomputable def normalizeVec {n : ℕ} (x : Fin n → ℂ) (hx : x ≠ 0) : Fin n → ℂ :=
  let norm_sq := vecNormSq x
  have _h_norm_sq_pos : 0 < norm_sq := vecNormSq_pos x hx
  (Real.sqrt norm_sq)⁻¹ • x

/-- The normalized vector has unit norm:
    `(dotProduct (star (normalizeVec x hx)) (normalizeVec x hx)).re = 1`. -/
lemma normalizeVec_unit {n : ℕ} (x : Fin n → ℂ) (hx : x ≠ 0) :
    (dotProduct (star (normalizeVec x hx)) (normalizeVec x hx)).re = 1 := by
  unfold normalizeVec vecNormSq
  let norm_sq := (dotProduct (star x) x).re
  have h_norm_sq_pos : 0 < norm_sq := vecNormSq_pos x hx
  have h_sqrt_pos : 0 < Real.sqrt norm_sq := Real.sqrt_pos.mpr h_norm_sq_pos
  -- Let c = (Real.sqrt norm_sq)⁻¹, then normalizeVec x hx = c • x
  let c := (Real.sqrt norm_sq)⁻¹
  -- Step 1: dotProduct (star (c • x)) (c • x) = c * c * dotProduct (star x) x
  -- Since c is real, star (c : ℂ) = c
  have h_star_c_eq : star (c : ℂ) = (c : ℂ) := Complex.conj_ofReal c
  have h_dot : dotProduct (star (c • x)) (c • x) = (c : ℂ) * (c : ℂ) * dotProduct (star x) x := by
    -- star (c • x) = star c • star x = c • star x (since c is real)
    have h_star_smul : star (c • x) = (c : ℂ) • star x := by
      ext i
      simp only [Pi.smul_apply, Pi.star_apply]
      -- star (c • x i) = star c * star (x i) = c * star (x i) (since c is real)
      -- c • x i uses ℝ-smul on ℂ, which is (↑c : ℂ) * x i
      simp only [Complex.real_smul, star_mul', h_star_c_eq, smul_eq_mul]
    rw [h_star_smul]
    -- dotProduct (c • star x) (c • x) = c • dotProduct (star x) (c • x)
    rw [smul_dotProduct (c : ℂ) (star x) (c • x)]
    -- dotProduct (star x) (c • x) = c • dotProduct (star x) x
    have h_dot_smul : dotProduct (star x) (c • x) = (c : ℂ) • dotProduct (star x) x :=
      dotProduct_smul (c : ℂ) (star x) x
    rw [h_dot_smul]
    -- Now we have: c • (c • dotProduct (star x) x) = c * c * dotProduct (star x) x
    -- For complex numbers, c • z = c * z, so c • (c • z) = c * (c * z) = c * c * z
    -- Use smul_assoc: c • (c • z) = (c * c) • z, then smul_eq_mul
    rw [← smul_assoc]
    simp only [smul_eq_mul]
  rw [h_dot]
  -- Step 2: Take real part - we need to show (star c * c * dotProduct (star x) x).re = 1
  -- First, show that dotProduct (star x) x is real (imaginary part is 0)
  have h_im_zero : (dotProduct (star x) x).im = 0 := by
    have h_sum : dotProduct (star x) x = ∑ i : Fin n, star (x i) * x i := rfl
    rw [h_sum]
    have h_im_sum : (∑ i : Fin n, star (x i) * x i).im = ∑ i : Fin n, (star (x i) * x i).im :=
      Complex.im_sum Finset.univ (fun i => star (x i) * x i)
    rw [h_im_sum]
    apply Finset.sum_eq_zero
    intro i _
    -- (star z * z).im = 0 for any complex z
    -- (star z).re = z.re and (star z).im = -z.im
    simp only [Complex.mul_im]
    simp only [Complex.star_def, Complex.conj_re, Complex.conj_im]
    -- z.re * z.im + (-z.im) * z.re = 0
    ring
  -- Step 3: Compute the real part
  -- (c * c * dotProduct (star x) x).re = c * c * (dotProduct (star x) x).re
  have h_re : ((c : ℂ) * (c : ℂ) * dotProduct (star x) x).re = c * c * norm_sq := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [h_im_zero]
    simp only [mul_zero, sub_zero]
    -- (dotProduct (star x) x).re = norm_sq by definition
    rfl
  rw [h_re]
  -- Step 4: Show c * c * norm_sq = 1
  -- c = (Real.sqrt norm_sq)⁻¹, so c * c = (Real.sqrt norm_sq)⁻² = 1 / (Real.sqrt norm_sq)²
  have h_sqrt_sq : (Real.sqrt norm_sq) ^ 2 = norm_sq := Real.sq_sqrt h_norm_sq_pos.le
  have h_c_sq : c * c = 1 / norm_sq := by
    unfold c
    field_simp [h_sqrt_pos.ne.symm]
    rw [h_sqrt_sq]
  rw [h_c_sq]
  -- (1 / norm_sq) * norm_sq = 1
  field_simp [h_norm_sq_pos.ne.symm]

-- ==========================================================================
-- Sorted Spectral Theorem and eigenvalues antitonicity
-- ==========================================================================

/-- Cast from Fin n to Fin (Fintype.card (Fin n)). Since Fintype.card (Fin n) = n,
    this is essentially the identity on values. -/
@[simp] def finToCardFin (n : ℕ) : Fin n → Fin (Fintype.card (Fin n)) :=
  fun i => ⟨i.val, by rw [Fintype.card_fin]; exact i.isLt⟩

/-- The cast preserves values. -/
@[simp] lemma finToCardFin_val (n : ℕ) (i : Fin n) : (finToCardFin n i).val = i.val := rfl

/-- The cast is injective. -/
lemma finToCardFin_injective (n : ℕ) : Function.Injective (finToCardFin n) := by
  intro a b hab
  simp only [finToCardFin, Fin.mk.injEq] at hab
  exact Fin.ext hab

/-- The cast is surjective. -/
lemma finToCardFin_surjective (n : ℕ) : Function.Surjective (finToCardFin n) := by
  intro b
  have h_card : Fintype.card (Fin n) = n := Fintype.card_fin n
  have h_lt : b.val < n := by omega
  use ⟨b.val, h_lt⟩
  simp only [finToCardFin]

/-- The cast is a bijection. -/
lemma finToCardFin_bijective (n : ℕ) : Function.Bijective (finToCardFin n) :=
  ⟨finToCardFin_injective n, finToCardFin_surjective n⟩

/-- The cast is monotone (preserves ordering). -/
lemma finToCardFin_mono (n : ℕ) : Monotone (finToCardFin n) := by
  intro a b hab
  simp only [Fin.le_def, finToCardFin_val]
  exact hab

/-- eigenvalues₀ composed with finToCardFin gives eigenvalues indexed by Fin n. -/
noncomputable def eigenvalues₀Fin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    Fin n → ℝ :=
  hA.eigenvalues₀ ∘ finToCardFin n

/-- eigenvalues₀Fin is antitone (sorted descending). This follows directly from
    eigenvalues₀_antitone and finToCardFin_mono. -/
lemma eigenvalues₀Fin_antitone {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) : Antitone (eigenvalues₀Fin A hA) := by
  intro a b hab
  exact hA.eigenvalues₀_antitone (finToCardFin_mono n hab)

/-- **Sorted Spectral Theorem**: When eigenvalues is antitone, eigenvalues = eigenvalues₀Fin.

    This means the standard spectral decomposition A = U * diagonal(eigenvalues) * U†
    is already "sorted" in the sense that eigenvalues(i) = eigenvalues₀(i) for all i.

    The proof uses the fact that two antitone functions with the same multiset must be equal. -/
theorem eigenvalues_eq_eigenvalues₀Fin {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (h_ev_antitone : Antitone hA.eigenvalues) :
    hA.eigenvalues = eigenvalues₀Fin A hA := by
  -- Both functions are antitone, so their lists are sorted descending
  have h_sorted_ev : (List.ofFn hA.eigenvalues).SortedGE :=
    List.sortedGE_ofFn_iff.mpr h_ev_antitone
  have h_sorted_ev0Fin : (List.ofFn (eigenvalues₀Fin A hA)).SortedGE :=
    List.sortedGE_ofFn_iff.mpr (eigenvalues₀Fin_antitone A hA)
  -- The multisets are equal
  have h_multiset_eq : Finset.univ.val.map hA.eigenvalues =
      Finset.univ.val.map (eigenvalues₀Fin A hA) := by
    -- eigenvalues = eigenvalues₀ ∘ equivOfCardEq.symm
    -- eigenvalues₀Fin = eigenvalues₀ ∘ finToCardFin
    -- Both are bijective compositions with eigenvalues₀, so same multiset
    let e := Fintype.equivOfCardEq
        (by simp : Fintype.card (Fin (Fintype.card (Fin n))) = Fintype.card (Fin n))
    have h_ev_def : ∀ i, hA.eigenvalues i = hA.eigenvalues₀ (e.symm i) := fun i => rfl
    have h_ev0Fin_def : ∀ i, eigenvalues₀Fin A hA i = hA.eigenvalues₀ (finToCardFin n i) :=
      fun i => rfl
    -- Multiset via eigenvalues
    have h1 : Finset.univ.val.map hA.eigenvalues = Finset.univ.val.map hA.eigenvalues₀ := by
      conv_lhs => rw [show hA.eigenvalues = hA.eigenvalues₀ ∘ e.symm from funext h_ev_def]
      rw [← Multiset.map_map]
      congr 1
      exact Multiset.map_univ_val_equiv e.symm
    -- Multiset via eigenvalues₀Fin
    have h2 : Finset.univ.val.map (eigenvalues₀Fin A hA) = Finset.univ.val.map hA.eigenvalues₀ := by
      conv_lhs => rw [show eigenvalues₀Fin A hA = hA.eigenvalues₀ ∘ finToCardFin n
        from funext h_ev0Fin_def]
      rw [← Multiset.map_map]
      congr 1
      -- Need to show Finset.univ.val.map (finToCardFin n) = Finset.univ.val
      -- Create an equivalence from finToCardFin
      have h_card : Fintype.card (Fin n) = n := Fintype.card_fin n
      let finToCardFin_equiv : Fin n ≃ Fin (Fintype.card (Fin n)) := {
        toFun := finToCardFin n
        invFun := fun j => ⟨j.val, by omega⟩
        left_inv := fun i => by simp only [finToCardFin]
        right_inv := fun j => by simp only [finToCardFin]
      }
      exact Multiset.map_univ_val_equiv finToCardFin_equiv
    rw [h1, h2]
  -- Two sorted lists with the same multiset are equal
  have h_perm : (List.ofFn hA.eigenvalues).Perm (List.ofFn (eigenvalues₀Fin A hA)) := by
    rw [← Multiset.coe_eq_coe, ← Fin.univ_val_map, ← Fin.univ_val_map]
    exact h_multiset_eq
  have h_lists_eq : List.ofFn hA.eigenvalues = List.ofFn (eigenvalues₀Fin A hA) :=
    List.Perm.eq_of_sortedGE h_sorted_ev h_sorted_ev0Fin h_perm
  -- Extract function equality from list equality
  ext i
  have h_len_ev : (List.ofFn hA.eigenvalues).length = n := by simp
  have h_len_ev0 : (List.ofFn (eigenvalues₀Fin A hA)).length = n := by simp
  have h_i_lt_len_ev : i.val < (List.ofFn hA.eigenvalues).length := by
    simp only [List.length_ofFn]; exact i.isLt
  have h_i_lt_len_ev0 : i.val < (List.ofFn (eigenvalues₀Fin A hA)).length := by
    simp only [List.length_ofFn]; exact i.isLt
  have h_ev_i : (List.ofFn hA.eigenvalues)[i.val]'h_i_lt_len_ev = hA.eigenvalues i := by
    simp only [List.getElem_ofFn]
  have h_ev0Fin_i : (List.ofFn (eigenvalues₀Fin A hA))[i.val]'h_i_lt_len_ev0 =
      eigenvalues₀Fin A hA i := by simp only [List.getElem_ofFn]
  calc hA.eigenvalues i
      = (List.ofFn hA.eigenvalues)[i.val] := h_ev_i.symm
    _ = (List.ofFn (eigenvalues₀Fin A hA))[i.val] := by simp only [h_lists_eq]
    _ = eigenvalues₀Fin A hA i := h_ev0Fin_i

/-- **Sorted Spectral Theorem (diagonal form)**: The spectral decomposition with eigenvalues
    can be rewritten in terms of eigenvalues₀Fin when eigenvalues is antitone.

    A = U * diagonal(eigenvalues) * U† = U * diagonal(eigenvalues₀Fin) * U†

    This shows that the standard spectral theorem already provides a "sorted" decomposition. -/
theorem eq_conj_diagonal_eigenvalues₀Fin_of_antitone {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (h_ev_antitone : Antitone hA.eigenvalues) :
    A = hA.eigenvectorUnitary.val *
        Matrix.diagonal (fun i => ((eigenvalues₀Fin A hA i) : ℂ)) *
        (hA.eigenvectorUnitary.val)ᴴ := by
  -- Standard spectral theorem
  have h_spec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h_spec
  -- eigenvalues = eigenvalues₀Fin when antitone
  have h_eq := eigenvalues_eq_eigenvalues₀Fin A hA h_ev_antitone
  -- The diagonals are equal since eigenvalues = eigenvalues₀Fin
  have h_diag_eq : Matrix.diagonal (fun i => ((eigenvalues₀Fin A hA i) : ℂ)) =
      Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    congr 1
    ext i
    simp only [Function.comp_apply]
    congr 1
    exact (congrFun h_eq.symm i)
  rw [h_diag_eq]
  exact h_spec

-- ==========================================================================
-- Helper lemmas relating eigenvalues and eigenvalues₀
-- ==========================================================================

/-- Helper lemma: In a sorted descending list, if two positions have equal values and one is
  strictly before the other, then all positions between them also have that value. -/
lemma eq_of_sortedGE_of_eq_endpoints
    {n : ℕ} {α : Type*} [PartialOrder α] (f : Fin n → α)
    (h_sorted : (List.ofFn f).SortedGE)
    (i j : Fin n) (h_eq : f i = f j) :
    ∀ k : Fin n, i.val ≤ k.val → k.val ≤ j.val → f k = f i := by
  intro k h_ik h_kj
  -- Convert to Fin indices for the list
  have h_i_lt : i.val < (List.ofFn f).length := by simp only [List.length_ofFn]; exact i.isLt
  have h_j_lt : j.val < (List.ofFn f).length := by simp only [List.length_ofFn]; exact j.isLt
  have h_k_lt : k.val < (List.ofFn f).length := by simp only [List.length_ofFn]; exact k.isLt
  -- Convert List.getElem to f
  have h_f_i : (List.ofFn f)[i.val]'(h_i_lt) = f i := by simp only [List.getElem_ofFn]
  have h_f_j : (List.ofFn f)[j.val]'(h_j_lt) = f j := by simp only [List.getElem_ofFn]
  have h_f_k : (List.ofFn f)[k.val]'(h_k_lt) = f k := by simp only [List.getElem_ofFn]
  -- Use sorted property: in a descending list, if i ≤ k ≤ j, then f i ≥ f k ≥ f j
  have h_ge_ik : (List.ofFn f)[i.val]'(h_i_lt) ≥ (List.ofFn f)[k.val]'(h_k_lt) :=
    h_sorted.getElem_ge_getElem_of_le h_ik
  have h_ge_kj : (List.ofFn f)[k.val]'(h_k_lt) ≥ (List.ofFn f)[j.val]'(h_j_lt) :=
    h_sorted.getElem_ge_getElem_of_le h_kj
  -- Convert to f using the equalities
  rw [h_f_i, h_f_k] at h_ge_ik
  rw [h_f_k, h_f_j] at h_ge_kj
  -- Combine: f i ≥ f k ≥ f j and f i = f j, so f k = f i
  -- From h_ge_ik: f i ≥ f k, so f k ≤ f i
  -- From h_ge_kj and h_eq: f k ≥ f j = f i, so f k ≥ f i
  -- Therefore f k = f i
  have h_le1 : f k ≤ f i := h_ge_ik
  have h_le2 : f i ≤ f k := by
    rw [← h_eq] at h_ge_kj
    exact h_ge_kj
  -- Use antisymmetry
  exact le_antisymm h_le1 h_le2

end Rayleigh42

end Math.LinearAlgebra.SubmoduleDim
