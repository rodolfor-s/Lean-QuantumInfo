import Mathlib.Analysis.InnerProductSpace.Trace
import QCryptLean.Math.LinearAlgebra.SubmoduleDimension

/-!
# Spectral Theory: Ky Fan inequalities and variational characterization

Ky Fan inequalities, the variational characterization of eigenvalue sums, and
the trace/rank infrastructure used to compare Hermitian spectra by projection
arguments.

## Main definitions

- `eigenvaluePartialSum`: Sum of the first k eigenvalues
- `eigenvaluePartialSumBottom`: Sum of the last k eigenvalues
- `restrictedTrace`: trace of a matrix restricted to a projected subspace

## Main statements

- `eigenvaluePartialSum_add_le`: Ky Fan upper bound on partial eigenvalue sums
- `add_le_eigenvaluePartialSumBottom_add`: Ky Fan lower bound
- `eigenvaluePartialSum_add_card`: Trace equality (k=n case)
- `re_restrictedTrace_le_eigenvaluePartialSum`: Variational characterization upper bound
- `exists_restrictedTrace_eq_eigenvaluePartialSum`: Variational characterization achievability
-/

open scoped Matrix ComplexOrder
open Matrix

namespace Math.SpectralTheory

-- ==========================================================================
-- Ky Fan Inequalities
-- ==========================================================================

/-!
## Ky Fan Inequalities

The Ky Fan inequalities (also called Ky Fan maximum principle) bound the partial sums of
eigenvalues of a sum of Hermitian matrices in terms of the partial sums of eigenvalues
of the summands.

**Main result**: For Hermitian matrices A, B with eigenvalues sorted descending:
  ∑_{i=0}^{k-1} λᵢ(A+B) ≤ ∑_{i=0}^{k-1} λᵢ(A) + ∑_{i=0}^{k-1} λᵢ(B)

**Proof approaches**:
1. **Variational**: Sum of top k eigenvalues = max{Tr(PAP) : P is rank-k projection}
2. **Via Weyl**: Carefully sum the Weyl upper bound inequalities

**Applications**:
- Fannes inequality (entropy continuity)
- Matrix concentration inequalities
- Quantum information theory bounds

**Reference**: Horn & Johnson, "Matrix Analysis", Corollary 4.3.18
-/

/-- Sum of the first k eigenvalues (0-indexed: eigenvalues 0, 1, ..., k-1).
    For k = 0, returns 0. For k ≥ n, returns sum of all eigenvalues.
    Uses Fin (min k n) to naturally handle bounds. -/
noncomputable def eigenvaluePartialSum {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (k : ℕ) : ℝ :=
  ∑ i : Fin (min k n), hA.eigenvalues₀ ⟨i.val, by
    have := i.isLt
    simp only [Fintype.card_fin] at this ⊢
    exact Nat.lt_of_lt_of_le this (min_le_right k n)⟩

/-- When k ≤ n, the partial sum is over the first k eigenvalues.

    Technical note: This converts between Fin (min k n) and Fin k index types. -/
lemma eigenvaluePartialSum_of_le {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (k : ℕ) (hk : k ≤ n) :
    eigenvaluePartialSum A hA k =
      ∑ i : Fin k, hA.eigenvalues₀ ⟨i.val, by
        rw [Fintype.card_fin]; exact Nat.lt_of_lt_of_le i.isLt hk⟩ := by
  exact Finset.sum_equiv (finCongr (Nat.min_eq_left hk))
    (by intro; simp) (by intro; simp [finCongr])

lemma eigenvaluePartialSum_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    eigenvaluePartialSum A hA 0 = 0 := by
  rw [eigenvaluePartialSum_of_le A hA 0 (Nat.zero_le n)]
  simp

lemma eigenvaluePartialSum_one_eq_top_eigenvalue {n : ℕ} [NeZero n]
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    eigenvaluePartialSum A hA 1 = hA.eigenvalues₀ 0 := by
  have h1 : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne n))
  rw [eigenvaluePartialSum_of_le A hA 1 h1]
  simp

/-- Eigenvalue partial sum from the bottom: sum of eigenvalues from index (n-k) to (n-1).
    This is the sum of the k smallest eigenvalues. -/
noncomputable def eigenvaluePartialSumBottom {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (k : ℕ) (hk : k ≤ n) : ℝ :=
  ∑ i : Fin k, hA.eigenvalues₀ ⟨n - k + i.val, by
    rw [Fintype.card_fin]; omega⟩

-- add_le_eigenvaluePartialSumBottom_add is proved below, after eigenvaluePartialSum_add_le

/-- Equivalence between Fin n and Fin (Fintype.card (Fin n)), essentially the identity. -/
noncomputable def ftcEquiv (n : ℕ) :
    Fin n ≃ Fin (Fintype.card (Fin n)) where
  toFun := Math.LinearAlgebra.SubmoduleDim.finToCardFin n
  invFun := fun j => ⟨j.val, by have := Fintype.card_fin n; omega⟩
  left_inv := fun i => by ext; simp [Math.LinearAlgebra.SubmoduleDim.finToCardFin]
  right_inv := fun j => by ext; simp [Math.LinearAlgebra.SubmoduleDim.finToCardFin]

/-- Permutation relating eigenvalues to eigenvalues₀Fin.
    eigenvalues(i) = eigenvalues₀Fin(eigenPerm(i)) for all i. -/
noncomputable def eigenPerm (n : ℕ) : Equiv.Perm (Fin n) :=
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (by simp)
  e.symm.trans (ftcEquiv n).symm

/-- Key property: eigenvalues = eigenvalues₀Fin ∘ eigenPerm.
    This holds without any antitonicity assumption. -/
lemma eigenvalues_eq_eigenvalues₀Fin_comp
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (i : Fin n) :
    hA.eigenvalues i =
      Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin A hA (eigenPerm n i) := by
  change hA.eigenvalues₀ _ = hA.eigenvalues₀ _
  congr 1

/-- Sum of all eigenvalues equals trace.

    Uses the standard spectral theorem and eigenPerm reindexing to relate
    eigenvalues₀Fin to the standard eigenvalues, avoiding eigenvalues_antitone. -/
lemma sum_eigenvalues_eq_trace {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    ∑ i : Fin n, (hA.eigenvalues₀ ⟨i.val, by rw [Fintype.card_fin]; exact i.isLt⟩ : ℂ) =
      A.trace := by
  -- Step 1: LHS = ∑ eigenvalues₀Fin(i)
  have h_lhs : ∑ i : Fin n, (hA.eigenvalues₀ ⟨i.val, by rw [Fintype.card_fin]; exact i.isLt⟩ : ℂ)
      = ∑ i : Fin n, (Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin A hA i : ℂ) := by
    apply Finset.sum_congr rfl; intro i _
    simp only [Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin, Function.comp_apply,
      Math.LinearAlgebra.SubmoduleDim.finToCardFin]
  rw [h_lhs]
  -- Step 2: ∑ eigenvalues₀Fin(i) = ∑ eigenvalues(i) via eigenPerm reindexing
  have h_reindex : ∑ i : Fin n, (Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin A hA i : ℂ)
      = ∑ i : Fin n, (hA.eigenvalues i : ℂ) := by
    rw [show ∑ i, (hA.eigenvalues i : ℂ) =
        ∑ i, (Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin A hA (eigenPerm n i) : ℂ) from by
      apply Finset.sum_congr rfl; intro i _
      exact_mod_cast eigenvalues_eq_eigenvalues₀Fin_comp A hA i]
    rw [← Equiv.sum_comp (eigenPerm n)]
  rw [h_reindex]
  -- Step 3: ∑ eigenvalues(i) = trace(A) via standard spectral theorem
  -- trace(A) = trace(U * diag(eigenvalues) * Uᴴ) = trace(diag(eigenvalues)) = ∑ eigenvalues
  have h_spec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h_spec
  have h_UU' : (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ *
      hA.eigenvectorUnitary = 1 :=
    Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have h_trace : A.trace =
      (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues : Fin n → ℂ)).trace := by
    conv_lhs => rw [h_spec]
    rw [Matrix.trace_mul_cycle]
    simp only [star_eq_conjTranspose, h_UU', Matrix.one_mul]
  rw [h_trace]
  simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_apply, Function.comp]
  apply Finset.sum_congr rfl; intro i _; simp

/-- **Ky Fan Trace Equality**: The sum of all eigenvalues of A+B equals
    the sum of all eigenvalues of A plus all eigenvalues of B.

    This is the k=n case of Ky Fan, and is just the additivity of trace.
    ∑ λᵢ(A+B) = ∑ λᵢ(A) + ∑ λᵢ(B) = Tr(A+B) = Tr(A) + Tr(B) -/
theorem eigenvaluePartialSum_add_card {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : (A + B).IsHermitian) :
    eigenvaluePartialSum (A + B) hAB n =
      eigenvaluePartialSum A hA n + eigenvaluePartialSum B hB n := by
  -- The sum of all eigenvalues equals the trace.
  -- Trace is additive: Tr(A+B) = Tr(A) + Tr(B).
  rw [eigenvaluePartialSum_of_le (A + B) hAB n le_rfl]
  rw [eigenvaluePartialSum_of_le A hA n le_rfl]
  rw [eigenvaluePartialSum_of_le B hB n le_rfl]
  -- Now convert to complex sums and use trace additivity
  have h_trace_add : (A + B).trace = A.trace + B.trace := Matrix.trace_add A B
  -- Use sum_eigenvalues_eq_trace for each matrix
  have h_trace_A := sum_eigenvalues_eq_trace A hA
  have h_trace_B := sum_eigenvalues_eq_trace B hB
  have h_trace_AB := sum_eigenvalues_eq_trace (A + B) hAB
  -- The result follows from trace additivity
  -- We need to show real sums are equal when complex sums are equal
  have h_eq : (∑ i : Fin n, (hAB.eigenvalues₀ ⟨i.val, by
        rw [Fintype.card_fin]; exact i.isLt⟩ : ℂ)) =
      (∑ i : Fin n, (hA.eigenvalues₀ ⟨i.val, by
        rw [Fintype.card_fin]; exact i.isLt⟩ : ℂ)) +
      (∑ i : Fin n, (hB.eigenvalues₀ ⟨i.val, by
        rw [Fintype.card_fin]; exact i.isLt⟩ : ℂ)) := by
    rw [h_trace_AB, h_trace_add, h_trace_A, h_trace_B]
  -- Extract real parts
  have h_cast : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian),
      (∑ i : Fin n, hM.eigenvalues₀ ⟨i.val, by rw [Fintype.card_fin]; exact i.isLt⟩ : ℝ) =
      (∑ i : Fin n, (hM.eigenvalues₀ ⟨i.val, by rw [Fintype.card_fin]; exact i.isLt⟩ : ℂ)).re := by
    intro M hM
    simp only [Complex.re_sum, Complex.ofReal_re]
  rw [h_cast (A + B) hAB, h_cast A hA, h_cast B hB]
  rw [h_eq]
  simp only [Complex.add_re]

/-- The full eigenvalue partial sum of a Hermitian matrix is the real part of its trace. -/
lemma eigenvaluePartialSum_full_eq_trace_re {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    eigenvaluePartialSum A hA n = A.trace.re := by
  rw [eigenvaluePartialSum_of_le A hA n le_rfl]
  have htrace := congrArg Complex.re (sum_eigenvalues_eq_trace A hA)
  simpa [Complex.re_sum] using htrace

-- ==========================================================================
-- Variational Characterization (Ky Fan Maximum Principle)
-- ==========================================================================

/-!
### Variational Characterization of Eigenvalue Sums

The key tool for proving Ky Fan inequalities is the variational (minimax)
characterization of eigenvalue partial sums:

  ∑_{i=0}^{k-1} λᵢ(A) = max{Tr(PAP) : P is rank-k orthogonal projection}

This is sometimes called the Ky Fan maximum principle or Fan-Pall theorem.

**Key Lemma (Weighted Sum Bound)**:
If λ₀ ≥ λ₁ ≥ ... ≥ λ_{n-1} are sorted descending and w₀, ..., w_{n-1} are
non-negative weights with 0 ≤ wᵢ ≤ 1 and ∑ᵢ wᵢ = k, then:
  ∑ᵢ λᵢ wᵢ ≤ ∑_{i<k} λᵢ

The maximum is achieved when wᵢ = 1 for i < k and wᵢ = 0 for i ≥ k.
-/

/-- The indices of `Fin n` below `k` are the image of `Fin k` under the canonical embedding. -/
lemma univ_filter_fin_lt_eq_map {n k : ℕ} (hk : k ≤ n) :
    Finset.univ.filter (fun x : Fin n => x.val < k) =
      (Finset.univ : Finset (Fin k)).map
        ⟨fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩,
         fun _ _ h => Fin.ext (Fin.mk.inj h)⟩ := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
  constructor
  · intro hx
    exact ⟨⟨x.val, hx⟩, rfl⟩
  · rintro ⟨y, -, rfl⟩
    exact y.isLt

/-- Pulling back the filter `{i | i < k}` through a permutation gives the corresponding image. -/
lemma univ_filter_perm_val_lt_eq_map {n k : ℕ} (σ : Equiv.Perm (Fin n)) :
    Finset.univ.filter (fun i : Fin n => (σ i).val < k) =
      (Finset.univ.filter (fun j : Fin n => j.val < k)).map
        ⟨σ.symm, σ.symm.injective⟩ := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Function.Embedding.coeFn_mk]
  constructor
  · intro hi
    exact ⟨σ i, hi, by simp⟩
  · rintro ⟨j, hj, rfl⟩
    simpa using hj

/-- **Weighted Sum Bound**: For a descending sequence f and weights w with
    0 ≤ wᵢ ≤ 1 and ∑ wᵢ = k, we have ∑ fᵢ wᵢ ≤ ∑_{i<k} fᵢ.

    This is the key lemma for the variational characterization. -/
lemma weighted_sum_le_partial_sum {n : ℕ} (f : Fin n → ℝ) (w : Fin n → ℝ)
    (hf_antitone : Antitone f)
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_le_one : ∀ i, w i ≤ 1)
    (k : ℕ) (hk : k ≤ n)
    (hw_sum : ∑ i, w i = k) :
    ∑ i, f i * w i ≤ ∑ i : Fin k, f ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ := by
  -- Rearrangement / constant-shift argument:
  -- Define ind(i) = 1 if i < k, else 0. Rewrite RHS = ∑ f * ind.
  -- Pick pivot c = f(k) (when k < n). Then:
  --   ∑ f*w - ∑ f*ind = ∑ (f - c)*(w - ind)  (since c * ∑(w - ind) = 0)
  -- Each term ≤ 0: for i < k, (f_i - c) ≥ 0 and (w_i - 1) ≤ 0;
  --                 for i ≥ k, (f_i - c) ≤ 0 and w_i ≥ 0.
  set ind : Fin n → ℝ := fun i => if i.val < k then 1 else 0 with hind_def
  -- Rewrite RHS as ∑ f * ind
  have hRHS : ∑ i : Fin k, f ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ =
      ∑ i : Fin n, f i * ind i := by
    simp only [ind, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite]
    simp only [Finset.sum_const_zero, add_zero]
    apply Finset.sum_nbij (fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩)
    · intro i _; simp [Finset.mem_filter, i.isLt]
    · intro i j _ _ h; exact Fin.ext (Fin.mk.inj h)
    · intro i hi
      have hi' : i.val < k := by simpa using hi
      exact ⟨⟨i.val, hi'⟩, by simp, Fin.ext rfl⟩
    · intros; rfl
  rw [hRHS]
  rcases Nat.eq_or_lt_of_le hk with hkn | hk_lt
  · -- Case k = n: ∑ w = n with w ≤ 1 forces w = 1; ind = 1; both sides are ∑ f
    have hw_one : ∀ i, w i = 1 := by
      intro i; by_contra h
      have hwi : w i < 1 := lt_of_le_of_ne (hw_le_one i) h
      have : ∑ j : Fin n, w j < ∑ j : Fin n, (1 : ℝ) :=
        Finset.sum_lt_sum (fun j _ => hw_le_one j) ⟨i, Finset.mem_univ i, hwi⟩
      simp at this
      have : (k : ℝ) = (n : ℝ) := by exact_mod_cast hkn
      linarith
    have hind_one : ∀ i : Fin n, ind i = 1 := by
      intro i; simp only [ind]
      exact ite_eq_left (Nat.lt_of_lt_of_le i.isLt (le_of_eq hkn.symm))
    simp only [hw_one, hind_one, mul_one]
    exact le_refl _
  · -- Case k < n: pivot on c = f(k)
    set c := f ⟨k, hk_lt⟩ with hc_def
    have hind_sum : ∑ i : Fin n, ind i = (k : ℝ) := by
      simp only [ind, Finset.sum_boole]
      congr 1
      rw [univ_filter_fin_lt_eq_map (le_of_lt hk_lt)]
      simp [Finset.card_map]
    have hsum_eq : ∑ i, w i = ∑ i, ind i := by rw [hw_sum, hind_sum]
    -- Algebra: ∑ f*w - ∑ f*ind = ∑ (f-c)*(w-ind) since c * ∑(w-ind) = 0
    suffices h : ∑ i, (f i - c) * (w i - ind i) ≤ 0 by
      have key : ∑ i, f i * w i - ∑ i, f i * ind i =
          ∑ i, (f i - c) * (w i - ind i) := by
        have h1 : ∑ i, (w i - ind i) = 0 := by
          rw [Finset.sum_sub_distrib]; linarith [hsum_eq]
        have h2 : ∀ i : Fin n, (f i - c) * (w i - ind i) =
          f i * w i - f i * ind i - c * (w i - ind i) := by intro i; ring
        simp_rw [h2, Finset.sum_sub_distrib, ← Finset.mul_sum, h1, mul_zero, sub_zero]
      linarith
    -- Each term (f i - c) * (w i - ind i) ≤ 0 by sign analysis
    apply Finset.sum_nonpos
    intro i _
    by_cases hi : i.val < k
    · -- i < k: (f i - c) ≥ 0 (antitone), (w i - 1) ≤ 0
      simp only [ind, hi, ite_true]
      exact mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr (hf_antitone (Fin.mk_le_mk.mpr (Nat.le_of_lt hi))))
        (by linarith [hw_le_one i])
    · -- i ≥ k: (f i - c) ≤ 0 (antitone), w i ≥ 0
      simp only [ind, hi, ite_false, sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (hf_antitone (Fin.mk_le_mk.mpr (Nat.not_lt.mp hi))))
        (hw_nonneg i)

/-- For a Hermitian idempotent matrix (orthogonal projection), the real part of the trace
    equals the rank. This follows from the fact that eigenvalues of a Hermitian idempotent
    are all 0 or 1, so the trace (sum of eigenvalues) equals the count of nonzero eigenvalues,
    which equals the rank. -/
lemma idempotent_trace_re_eq_rank_of_isHermitian {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : P.IsHermitian) (hProj : P * P = P) :
    P.trace.re = (Matrix.rank P : ℝ) := by
  -- trace = ∑ eigenvalues (as complex)
  have h_trace_ev : P.trace = ∑ i, (hP.eigenvalues i : ℂ) := by
    have h_spec := hP.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h_spec
    conv_lhs => rw [h_spec]
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      Unitary.coe_star_mul_self, Matrix.one_mul]
    simp [Matrix.trace_diagonal, Function.comp]
  -- Each eigenvalue is 0 or 1: conjugating `P² = P` into the eigenbasis gives `D² = D`
  have h_01 : ∀ i, hP.eigenvalues i = 0 ∨ hP.eigenvalues i = 1 := by
    have h_spec := hP.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h_spec
    let U := hP.eigenvectorUnitary.val
    let D := Matrix.diagonal (RCLike.ofReal ∘ hP.eigenvalues : Fin n → ℂ)
    have h_UU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hP.eigenvectorUnitary
    have h_UU' : Uᴴ * U = 1 := Unitary.coe_star_mul_self hP.eigenvectorUnitary
    have h_P_eq : P = U * D * Uᴴ := h_spec
    have hD_eq : Uᴴ * P * U = D := by
      rw [h_P_eq, show Uᴴ * (U * D * Uᴴ) * U = Uᴴ * U * D * (Uᴴ * U) by
        simp only [Matrix.mul_assoc], h_UU', Matrix.one_mul, Matrix.mul_one]
    have h_sq : D * D = D := by
      rw [← hD_eq, show Uᴴ * P * U * (Uᴴ * P * U) = Uᴴ * (P * (U * Uᴴ) * P) * U by
        simp only [Matrix.mul_assoc], h_UU, Matrix.mul_one, hProj]
    intro i
    -- the `(i, i)` entry of `D² = D` is `λᵢ² = λᵢ`
    have h_sq_i := congr_fun₂ h_sq i i
    simp only [D, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
      Function.comp_apply] at h_sq_i
    have h_real : hP.eigenvalues i * (hP.eigenvalues i - 1) = 0 := by
      rw [mul_sub, mul_one, sub_eq_zero]
      exact_mod_cast h_sq_i
    rcases mul_eq_zero.mp h_real with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  -- trace.re = ∑ eigenvalues (as real)
  have h_trace_re : P.trace.re = ∑ i, hP.eigenvalues i := by
    rw [h_trace_ev, Complex.re_sum]
    apply Finset.sum_congr rfl; intro i _; exact Complex.ofReal_re _
  -- ∑ eigenvalues = #{nonzero eigenvalues} since each is 0 or 1
  have h_sum_card : ∑ i, hP.eigenvalues i =
      ↑((Finset.univ.filter (fun i => hP.eigenvalues i ≠ 0)).card) := by
    rw [show (∑ i, hP.eigenvalues i) = ∑ i, if hP.eigenvalues i ≠ 0 then (1 : ℝ) else 0 from by
      apply Finset.sum_congr rfl; intro i _
      rcases h_01 i with h | h <;> simp [h]]
    rw [Finset.sum_boole]
  -- Connect to rank via rank_eq_card_non_zero_eigs
  rw [h_trace_re, h_sum_card]
  congr 1
  rw [hP.rank_eq_card_non_zero_eigs]
  exact (Fintype.subtype_card (Finset.univ.filter (fun i => hP.eigenvalues i ≠ 0))
    (by simp)).symm

/-- Trace of a matrix restricted to a subspace via projection.
    For orthogonal projection P onto subspace S: Tr(PAP) = ∑_{v ∈ basis(S)} ⟨v|A|v⟩ -/
noncomputable def restrictedTrace {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (P : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (P * A * P).trace

/-- A Hermitian idempotent matrix of rank `1` is the orthogonal projection onto a unit vector. -/
lemma exists_norm_one_vecMulVec_eq_of_rank_one_projection {n : ℕ}
    {P : Matrix (Fin n) (Fin n) ℂ}
    (hP_proj : P * P = P) (hP_herm : P.IsHermitian) (hP_rank : P.rank = 1) :
    ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧ P = Matrix.vecMulVec x.ofLp (star x.ofLp) := by
  let p : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n) := Matrix.toEuclideanLin P
  have hp_idem : IsIdempotentElem p := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, ← Matrix.toLpLin_mul_same, hP_proj]
  have hp_symm : p.IsSymmetric := by
    simpa [p] using (Matrix.isSymmetric_toEuclideanLin_iff.mpr hP_herm)
  have hp_proj : p.IsSymmetricProjection := ⟨hp_idem, hp_symm⟩
  have h_range_finrank : Module.finrank ℂ (LinearMap.range p) = 1 := by
    have h_rank_range : P.rank = Module.finrank ℂ (LinearMap.range p) := by
      exact Matrix.rank_eq_finrank_range_toLin P
        (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
    rw [← h_rank_range]
    exact hP_rank
  obtain ⟨v, hv_ne, hv_span⟩ :=
    (finrank_eq_one_iff' (K := ℂ) (V := LinearMap.range p)).mp h_range_finrank
  let x0 : EuclideanSpace ℂ (Fin n) := v
  have hx0_ne : x0 ≠ 0 := by
    intro hx0
    apply hv_ne
    exact Subtype.ext hx0
  have h_range_x0 : LinearMap.range p = ℂ ∙ x0 := by
    apply le_antisymm
    · rw [Submodule.le_span_singleton_iff]
      intro w hw
      obtain ⟨c, hc⟩ := hv_span ⟨w, hw⟩
      refine ⟨c, ?_⟩
      simpa [x0] using congrArg Subtype.val hc
    · refine Submodule.span_le.mpr ?_
      intro y hy
      rcases hy with rfl
      exact v.2
  have hx0_norm_ne : ‖x0‖ ≠ 0 := norm_ne_zero_iff.mpr hx0_ne
  let x : EuclideanSpace ℂ (Fin n) := ((‖x0‖ : ℂ)⁻¹) • x0
  have hx_norm : ‖x‖ = 1 := by
    have hpos : 0 < ‖x0‖ := norm_pos_iff.mpr hx0_ne
    dsimp [x]
    rw [norm_smul]
    simp [hpos.ne']
  have h_range_x : LinearMap.range p = ℂ ∙ x := by
    calc
      LinearMap.range p = ℂ ∙ x0 := h_range_x0
      _ = ℂ ∙ x := by
        symm
        refine Submodule.span_singleton_smul_eq ?_ x0
        exact isUnit_iff_ne_zero.mpr (inv_ne_zero (by exact_mod_cast hx0_norm_ne))
  obtain ⟨_, hp_eq_star⟩ :=
    LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hp_proj
  have hp_eq_rankOne : p = InnerProductSpace.rankOne ℂ x x := by
    apply LinearMap.ext
    intro y
    calc
      p y = (LinearMap.range p).starProjection y := by
        simpa using congrArg (fun f => f y) hp_eq_star
      _ = (ℂ ∙ x).starProjection y := by simp only [h_range_x]
      _ = InnerProductSpace.rankOne ℂ x x y := by
        rw [Submodule.starProjection_unit_singleton (𝕜 := ℂ) (v := x) hx_norm y]
        rfl
  refine ⟨x, hx_norm, ?_⟩
  -- `P = toEuclideanLin.symm p` and `p = |x⟩⟨x|`
  rw [← InnerProductSpace.symm_toEuclideanLin_rankOne, ← hp_eq_rankOne]
  exact (Matrix.toEuclideanLin.symm_apply_apply P).symm

/-- A rank-`1` Hermitian projection compresses `A` to the Rayleigh quotient of its unit vector. -/
lemma restrictedTrace_eq_compression_of_eq_vecMulVec {n : ℕ}
    (A P : Matrix (Fin n) (Fin n) ℂ)
    {x : EuclideanSpace ℂ (Fin n)}
    (hP_proj : P * P = P)
    (hP : P = Matrix.vecMulVec x.ofLp (star x.ofLp)) :
    restrictedTrace A P = star x.ofLp ⬝ᵥ (A *ᵥ x.ofLp) := by
  calc
    restrictedTrace A P = (A * P).trace := by
      unfold restrictedTrace
      calc
        (P * A * P).trace = (P * (A * P)).trace := by rw [Matrix.mul_assoc]
        _ = ((A * P) * P).trace := by rw [Matrix.trace_mul_comm]
        _ = (A * (P * P)).trace := by rw [Matrix.mul_assoc]
        _ = (A * P).trace := by rw [hP_proj]
    _ = (A * Matrix.vecMulVec x.ofLp (star x.ofLp)).trace := by rw [hP]
    _ = (Matrix.vecMulVec (A *ᵥ x.ofLp) (star x.ofLp)).trace := by rw [Matrix.mul_vecMulVec]
    _ = (A *ᵥ x.ofLp) ⬝ᵥ star x.ofLp := Matrix.trace_vecMulVec _ _
    _ = star x.ofLp ⬝ᵥ (A *ᵥ x.ofLp) := by
      simp [dotProduct, mul_comm]

/-- For any Hermitian matrix and any orthogonal projection of rank k,
    the restricted trace is at most the sum of the k largest eigenvalues. -/
theorem re_restrictedTrace_le_eigenvaluePartialSum {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (P : Matrix (Fin n) (Fin n) ℂ)
    (hP_proj : P * P = P) -- P is idempotent
    (hP_herm : P.IsHermitian) -- P is Hermitian (so orthogonal projection)
    (k : ℕ) (hk : k ≤ n)
    (hP_rank : Matrix.rank P = k) -- P has rank k
    : (restrictedTrace A P).re ≤ eigenvaluePartialSum A hA k := by
  -- PROOF STRATEGY using spectral decomposition (no sorted eigenvalues needed):
  --
  -- Step 1: Use standard spectral theorem: A = U * D * Uᴴ where D = diag(eigenvalues)
  -- Step 2: Tr(PAP) = Tr(AP²) = Tr(AP) (since P² = P)
  -- Step 3: In eigenbasis: Tr(AP) = ∑ᵢ λᵢ * wᵢ where wᵢ = (UᴴPU)ᵢᵢ
  -- Step 4: Show 0 ≤ wᵢ ≤ 1 (since UᴴPU is an orthogonal projection)
  -- Step 5: Show ∑ᵢ wᵢ = Tr(UᴴPU) = Tr(P) = k
  -- Step 6: Use eigenPerm to reindex through eigenvalues₀Fin (antitone),
  --         then apply weighted_sum_le_partial_sum
  -- Step 1: Standard spectral decomposition (no sorting needed)
  have h_spec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h_spec
  let U := hA.eigenvectorUnitary.val
  let D := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues : Fin n → ℂ)
  have h_UU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have h_UU' : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  -- Step 2: Simplify Tr(PAP) = Tr(AP) using P² = P
  have h_trace_simp : (P * A * P).trace = (A * P).trace := by
    calc (P * A * P).trace = (P * (A * P)).trace := by rw [Matrix.mul_assoc]
      _ = ((A * P) * P).trace := by rw [Matrix.trace_mul_comm]
      _ = (A * (P * P)).trace := by rw [Matrix.mul_assoc]
      _ = (A * P).trace := by rw [hP_proj]
  -- Step 3: Define Q = UᴴPU (projection in eigenbasis) and weights
  let Q := Uᴴ * P * U
  let w : Fin n → ℝ := fun i => (Q i i).re
  -- Q is an orthogonal projection
  have hQ_proj : Q * Q = Q := by
    change Uᴴ * P * U * (Uᴴ * P * U) = Uᴴ * P * U
    calc Uᴴ * P * U * (Uᴴ * P * U)
        = Uᴴ * P * (U * Uᴴ) * P * U := by noncomm_ring
      _ = Uᴴ * P * 1 * P * U := by rw [h_UU]
      _ = Uᴴ * (P * P) * U := by noncomm_ring
      _ = Uᴴ * P * U := by rw [hP_proj]
  have hQ_herm : Q.IsHermitian := by
    change (Uᴴ * P * U).IsHermitian
    rw [Matrix.IsHermitian]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [hP_herm.eq]; noncomm_ring
  -- Trace identity: Tr(AP) = Tr(DQ) = ∑ λᵢ * Q_{ii}
  have h_A_eq : A = U * D * Uᴴ := h_spec
  have h_AP_trace : (A * P).trace = (D * Q).trace := by
    calc (A * P).trace
        = ((U * D * Uᴴ) * P).trace := by rw [h_A_eq]
      _ = (U * (D * (Uᴴ * P))).trace := by noncomm_ring
      _ = (D * (Uᴴ * P) * U).trace := by
          rw [Matrix.trace_mul_comm U (D * (Uᴴ * P))]
      _ = (D * (Uᴴ * P * U)).trace := by rw [Matrix.mul_assoc]
      _ = (D * Q).trace := rfl
  -- Expand Tr(DQ) = ∑ λᵢ * Q_{ii} (D is diagonal)
  have h_DQ_expand : (D * Q).trace =
      ∑ i : Fin n, (hA.eigenvalues i : ℂ) * Q i i := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, D, Matrix.diagonal_apply]
    apply Finset.sum_congr rfl; intro i _
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ i]; simp [Function.comp]
  -- Connect trace to real weighted sum: (∑ λᵢ * Q_{ii}).re = ∑ λᵢ * w(i)
  have h_trace_re_sum : (∑ i, (hA.eigenvalues i : ℂ) * Q i i).re =
      ∑ i, hA.eigenvalues i * w i := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl; intro i _
    simp only [w, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  -- Step 4: Weight properties from Q being a Hermitian idempotent
  -- Helper: Q_{ii} = ∑_j Q_{ij} * conj(Q_{ij}) (from Q² = Q and Qᴴ = Q)
  have h_Q_diag_sum : ∀ i, Q i i = ∑ j, Q i j * starRingEnd ℂ (Q i j) := by
    intro i
    have := congr_fun₂ hQ_proj i i
    simp only [Matrix.mul_apply] at this
    conv_lhs => rw [this.symm]
    apply Finset.sum_congr rfl; intro j _
    have : Q j i = (starRingEnd ℂ) (Q i j) := by
      have h := congr_fun₂ hQ_herm.eq j i
      simp only [Matrix.conjTranspose_apply] at h
      exact h.symm
    rw [this]
  have hw_nonneg : ∀ i, 0 ≤ w i := by
    intro i
    change 0 ≤ (Q i i).re
    rw [h_Q_diag_sum, Complex.re_sum]
    apply Finset.sum_nonneg; intro j _
    rw [Complex.mul_conj]
    simp [Complex.normSq_nonneg]
  have hw_le_one : ∀ i, w i ≤ 1 := by
    intro i
    have h_real : Q i i = (Q i i).re := (hQ_herm.coe_re_apply_self i).symm
    have h2 : Complex.normSq (Q i i) ≤ (Q i i).re := by
      conv_rhs => rw [h_Q_diag_sum]
      simp_rw [Complex.mul_conj]; rw [Complex.re_sum]
      simp only [Complex.ofReal_re]
      exact Finset.single_le_sum
        (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    have h3 : Complex.normSq (Q i i) = (Q i i).re ^ 2 := by
      rw [h_real]
      simp only [Complex.normSq_ofReal, sq, Complex.ofReal_re]
    change (Q i i).re ≤ 1
    -- `x² ≤ x` forces `x ≤ 1`
    rw [h3] at h2
    by_contra hx
    exact (lt_self_pow₀ (not_le.mp hx) one_lt_two).not_ge h2
  -- Step 5: ∑ wᵢ = k (trace preservation and rank)
  have hw_sum : ∑ i, w i = k := by
    -- ∑ w(i) = ∑ (Q i i).re = Q.trace.re = P.trace.re = rank P = k
    have h_sum_trace : ∑ i, w i = Q.trace.re := by
      change ∑ i, (Q i i).re = Q.trace.re
      simp only [Matrix.trace, Matrix.diag, Complex.re_sum]
    have h_Q_trace : Q.trace = P.trace := by
      change (Uᴴ * P * U).trace = P.trace
      calc (Uᴴ * P * U).trace
          = (U * (Uᴴ * P)).trace := by rw [Matrix.trace_mul_comm]
        _ = ((U * Uᴴ) * P).trace := by rw [Matrix.mul_assoc]
        _ = (1 * P).trace := by rw [h_UU]
        _ = P.trace := by rw [Matrix.one_mul]
    have h_P_trace : P.trace.re = (k : ℝ) := by
      rw [idempotent_trace_re_eq_rank_of_isHermitian P hP_herm hP_proj, hP_rank]
    rw [h_sum_trace, h_Q_trace, h_P_trace]
  -- Step 6: Use eigenPerm to connect eigenvalues to eigenvalues₀Fin (antitone)
  -- Then apply weighted_sum_le_partial_sum
  change (P * A * P).trace.re ≤ eigenvaluePartialSum A hA k
  rw [h_trace_simp, h_AP_trace, h_DQ_expand, h_trace_re_sum]
  -- Goal: ∑ eigenvalues(i) * w(i) ≤ eigenvaluePartialSum A hA k
  rw [eigenvaluePartialSum_of_le A hA k hk]
  -- Rewrite eigenvalues via eigenPerm: eigenvalues(i) = eigenvalues₀Fin(σ(i))
  let σ := eigenPerm n
  have h_ev_perm : ∀ i, hA.eigenvalues i =
      Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin A hA (σ i) :=
    eigenvalues_eq_eigenvalues₀Fin_comp A hA
  have h_lhs_eq : ∑ i, hA.eigenvalues i * w i =
      ∑ i, Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin A hA (σ i) * w i := by
    apply Finset.sum_congr rfl; intro i _; rw [h_ev_perm i]
  rw [h_lhs_eq]
  -- Reindex: ∑ eigenvalues₀Fin(σ(i)) * w(i) = ∑ eigenvalues₀Fin(j) * w(σ⁻¹(j))
  have h_reindex : ∑ i, Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin A hA (σ i) * w i =
      ∑ j, Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin A hA j * w (σ.symm j) := by
    rw [show (fun i => Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin A hA (σ i) * w i) =
      (fun i => (fun j => Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin A hA j *
        w (σ.symm j)) (σ i)) from by ext i; simp]
    exact Equiv.sum_comp (σ : Fin n ≃ Fin n)
      (fun j => Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin A hA j * w (σ.symm j))
  rw [h_reindex]
  -- Define w' = w ∘ σ⁻¹ and verify its properties
  set w' := w ∘ σ.symm with hw'_def
  have hw'_nonneg : ∀ i, 0 ≤ w' i := fun i => hw_nonneg (σ.symm i)
  have hw'_le_one : ∀ i, w' i ≤ 1 := fun i => hw_le_one (σ.symm i)
  have hw'_sum : ∑ i, w' i = k := by
    have : ∑ i, w' i = ∑ i, w i :=
      Equiv.sum_comp σ.symm w
    linarith
  -- Connect eigenvalues₀ to eigenvalues₀Fin in the RHS
  have h_ev_eq : ∀ i : Fin k,
      hA.eigenvalues₀ ⟨i.val, by
        rw [Fintype.card_fin]; exact Nat.lt_of_lt_of_le i.isLt hk⟩ =
      Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin A hA
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ := by
    intro i
    simp only [Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin, Function.comp,
      Math.LinearAlgebra.SubmoduleDim.finToCardFin]
  simp_rw [h_ev_eq]
  -- Apply weighted_sum_le_partial_sum with antitone eigenvalues₀Fin and w'
  have h_antitone : Antitone (Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin A hA) :=
    Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin_antitone A hA
  exact weighted_sum_le_partial_sum
    (Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin A hA) w' h_antitone hw'_nonneg hw'_le_one
    k hk hw'_sum

/-- Rank of a unitary conjugate equals rank of the original matrix. -/
lemma rank_unitary_conj {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    (U * M * Uᴴ).rank = M.rank := by
  -- U is invertible, so is Uᴴ
  have hU_unit : IsUnit (det U) := by
    have h_det := congr_arg det hU
    simp only [det_mul, det_one] at h_det
    have h_star_det : det Uᴴ = star (det U) := det_conjTranspose U
    rw [h_star_det] at h_det
    exact IsUnit.of_mul_eq_one (star (det U)) h_det
  have hUH_unit : IsUnit (det Uᴴ) := by
    have h_det := congr_arg det hU'
    simp only [det_mul, det_one] at h_det
    exact IsUnit.of_mul_eq_one (det U) h_det
  -- Apply rank preservation: first eliminate Uᴴ on the right, then U on the left
  rw [Matrix.rank_mul_eq_left_of_isUnit_det Uᴴ (U * M) hUH_unit]
  rw [Matrix.rank_mul_eq_right_of_isUnit_det U M hU_unit]

/-- Helper: Converting a conditional sum over Fin n to a sum over Fin k. -/
lemma sum_ite_eq_sum_fin {n k : ℕ} (hk : k ≤ n) (f : Fin n → ℝ) :
    ∑ i : Fin n, (if i.val < k then f i else 0) =
    ∑ i : Fin k, f ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ := by
  -- Use Finset.sum_congr_set with set {i : Fin n | i.val < k}
  let s : Set (Fin n) := {i | i.val < k}
  have h_cond : ∑ i : Fin n, (if i.val < k then f i else 0) =
      ∑ i : Fin n, (if i ∈ s then f i else 0) := by
    simp only [s, Set.mem_ofPred]
  rw [h_cond]
  -- Apply sum_congr_set
  trans (∑ i : s, f i)
  · exact Finset.sum_congr_set s (fun i => if i ∈ s then f i else 0) (fun i => f i)
      (by intro x hx; simp [hx])
      (by intro x hx; simp [hx])
  -- Now bijection between s and Fin k
  let e : s ≃ Fin k := {
    toFun := fun i => ⟨i.val.val, i.prop⟩
    invFun := fun j => ⟨⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩, j.isLt⟩
    left_inv := by intro i; ext; rfl
    right_inv := by intro j; ext; rfl
  }
  rw [← Fintype.sum_equiv e (fun i : s => f i)
    (fun j : Fin k => f ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩) (by intro i; rfl)]

/-- A diagonal projection has rank equal to the cardinality of its support. -/
lemma rank_diagonal_indicator {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    Matrix.rank (Matrix.diagonal fun i => if p i then (1 : ℂ) else 0) =
      (Finset.univ.filter p).card := by
  let P : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => if p i then (1 : ℂ) else 0
  have hP_idem : P * P = P := by
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases h : p i <;> simp [P, h]
    · simp [P, hij]
  have hP_herm : P.IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases h : p i <;> simp [P, h, star_one, star_zero]
    · simp [P, hij, Ne.symm hij]
  have h_trace_eq_rank := idempotent_trace_re_eq_rank_of_isHermitian P hP_herm hP_idem
  have h_trace_re : P.trace.re = ((Finset.univ.filter p).card : ℝ) := by
    simp [P, Matrix.trace_diagonal, Finset.sum_boole]
  rw [h_trace_re] at h_trace_eq_rank
  exact Nat.cast_injective h_trace_eq_rank.symm

/-- Conjugating both a diagonalization and a projection by the same unitary preserves
    the compressed trace. -/
lemma restrictedTrace_unitary_conj_diagonal {n : ℕ}
    (U Pk D A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A = U * D * Uᴴ) (hU' : Uᴴ * U = 1) :
    restrictedTrace A (U * Pk * Uᴴ) = (Pk * D * Pk).trace := by
  unfold restrictedTrace
  rw [hA]
  have h_left : (U * Pk * Uᴴ) * (U * D * Uᴴ) = U * Pk * D * Uᴴ := by
    calc (U * Pk * Uᴴ) * (U * D * Uᴴ)
        = U * Pk * (Uᴴ * U) * D * Uᴴ := by noncomm_ring
      _ = U * Pk * D * Uᴴ := by rw [hU', Matrix.mul_one]
  have h_right : (U * Pk * D * Uᴴ) * (U * Pk * Uᴴ) = U * (Pk * D * Pk) * Uᴴ := by
    calc (U * Pk * D * Uᴴ) * (U * Pk * Uᴴ)
        = U * Pk * D * (Uᴴ * U) * Pk * Uᴴ := by noncomm_ring
      _ = U * (Pk * D * Pk) * Uᴴ := by
          rw [hU', Matrix.mul_one]
          noncomm_ring
  rw [h_left, h_right, Matrix.mul_assoc, Matrix.trace_mul_comm,
    Matrix.mul_assoc, hU', Matrix.mul_one]

/-- The sum of top k eigenvalues is achieved by projecting onto the top k eigenvectors.
    This is the converse of `re_restrictedTrace_le_eigenvaluePartialSum`. -/
theorem exists_restrictedTrace_eq_eigenvaluePartialSum {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (k : ℕ) (hk : k ≤ n) :
    ∃ (P : Matrix (Fin n) (Fin n) ℂ),
      P * P = P ∧ P.IsHermitian ∧ Matrix.rank P = k ∧
      (restrictedTrace A P).re = eigenvaluePartialSum A hA k := by
  -- PROOF STRATEGY (no sorted eigenvalues needed):
  -- Use standard spectral theorem: A = U * diagonal(eigenvalues) * Uᴴ
  -- Construct P = U * Pₖ * Uᴴ where Pₖ selects the k columns
  -- corresponding to the k LARGEST eigenvalues via eigenPerm.
  -- Pₖ(i,i) = 1 if eigenPerm(i) < k, else 0.
  have h_spec := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h_spec
  let U := hA.eigenvectorUnitary.val
  let D := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues : Fin n → ℂ)
  have h_A_eq : A = U * D * Uᴴ := h_spec
  -- Define Pk: selects columns for k largest eigenvalues via eigenPerm
  let σ := eigenPerm n
  let sel : Fin n → ℂ := fun i => if (σ i).val < k then 1 else 0
  let Pk : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal sel
  let P := U * Pk * Uᴴ
  use P
  have h_UU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have h_UU' : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  -- Helper: Pk is a diagonal 0/1 matrix (idempotent and Hermitian)
  have hPk_idem : Pk * Pk = Pk := by
    rw [Matrix.diagonal_mul_diagonal]; congr; funext i
    simp only [sel]; by_cases h : (σ i).val < k <;> simp [h]
  have hPk_herm : Pkᴴ = Pk := by
    rw [Matrix.diagonal_conjTranspose]; congr; funext i
    simp only [sel]; by_cases h : (σ i).val < k <;> simp [h, star_one, star_zero]
  constructor
  -- 1. P * P = P (idempotent)
  · change (U * Pk * Uᴴ) * (U * Pk * Uᴴ) = U * Pk * Uᴴ
    calc (U * Pk * Uᴴ) * (U * Pk * Uᴴ)
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
  -- 3. rank P = k
  · have hPk_rank : Pk.rank = k := by
      calc
        Pk.rank = (Finset.univ.filter (fun i : Fin n => (σ i).val < k)).card := by
          simpa [Pk] using
            (rank_diagonal_indicator (n := n) (p := fun i : Fin n => (σ i).val < k))
        _ = ((Finset.univ.filter (fun j : Fin n => j.val < k)).map
              ⟨σ.symm, σ.symm.injective⟩).card := by
          rw [univ_filter_perm_val_lt_eq_map σ]
        _ = (Finset.univ.filter (fun j : Fin n => j.val < k)).card := by
          rw [Finset.card_map]
        _ = k := by
          rw [univ_filter_fin_lt_eq_map hk]
          simp [Finset.card_map]
    rw [← hPk_rank]
    exact rank_unitary_conj U h_UU h_UU' Pk
  -- 4. Tr(PAP).re = eigenvaluePartialSum A hA k
  · have h1 : restrictedTrace A P = (Pk * D * Pk).trace :=
      restrictedTrace_unitary_conj_diagonal U Pk D A h_A_eq h_UU'
    -- Pk * D * Pk is diagonal with entries sel(i) * eigenvalues(i) * sel(i)
    have h2 : (Pk * D * Pk).trace =
        (Matrix.diagonal (fun i =>
          (sel i * (hA.eigenvalues i : ℂ) * sel i))).trace := by
      simp [Pk, D, Matrix.diagonal_mul_diagonal]
    have h3 : ((Matrix.diagonal (fun i =>
        (sel i * (hA.eigenvalues i : ℂ) * sel i))).trace).re =
        ∑ i : Fin n,
          (if (σ i).val < k then hA.eigenvalues i else 0) := by
      rw [Matrix.trace_diagonal, Complex.re_sum]
      congr 1; ext i; simp only [sel]
      split_ifs <;> simp
    -- Rewrite using eigenvalues = eigenvalues₀Fin ∘ eigenPerm
    have h_ev_perm := eigenvalues_eq_eigenvalues₀Fin_comp A hA
    have h4 : ∑ i : Fin n,
        (if (σ i).val < k then hA.eigenvalues i else 0) =
        ∑ i : Fin n,
          (if (σ i).val < k
           then Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin A hA (σ i) else 0) := by
      apply Finset.sum_congr rfl; intro i _
      split_ifs with h
      · exact h_ev_perm i
      · rfl
    -- Reindex through σ: sum over {i | σ(i) < k} = sum over {j | j < k}
    have h5 : ∑ i : Fin n,
        (if (σ i).val < k
         then Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin A hA (σ i) else 0) =
        ∑ j : Fin n,
          (if j.val < k
           then Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin A hA j else 0) := by
      let f : Fin n → ℝ := fun j =>
        if j.val < k then Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin A hA j else 0
      change ∑ i, f (σ i) = ∑ j, f j
      exact Equiv.sum_comp σ f
    have h6 : ∑ j : Fin n,
        (if j.val < k then Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin A hA j else 0) =
        ∑ j : Fin k, Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin A hA
          ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩ :=
      sum_ite_eq_sum_fin hk _
    have h7 : ∑ j : Fin k, Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin A hA
        ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩ =
        eigenvaluePartialSum A hA k := by
      symm; rw [eigenvaluePartialSum_of_le A hA k hk]
      apply Finset.sum_congr rfl; intro i _
      simp only [Math.LinearAlgebra.SubmoduleDim.eigenvalues₀Fin, Function.comp,
        Math.LinearAlgebra.SubmoduleDim.finToCardFin]
    rw [h1, h2, h3, h4, h5, h6, h7]

-- ==========================================================================
-- Ky Fan Upper Bound - Main Theorem
-- ==========================================================================

/-- **Ky Fan Upper Bound Inequality**: For Hermitian matrices A, B,
    ∑_{i<k} λᵢ(A+B) ≤ ∑_{i<k} λᵢ(A) + ∑_{i<k} λᵢ(B).

    Uses the variational characterization: the optimal rank-k projection for A+B
    gives restricted traces bounded by eigenvalue partial sums of A and B. -/
theorem eigenvaluePartialSum_add_le {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : (A + B).IsHermitian)
    (k : ℕ) (hk : k ≤ n) :
    eigenvaluePartialSum (A + B) hAB k ≤
      eigenvaluePartialSum A hA k + eigenvaluePartialSum B hB k := by
  -- Step 1: By exists_restrictedTrace_eq_eigenvaluePartialSum, there exists rank-k projection P
  -- such that eigenvaluePartialSum (A+B) k = (restrictedTrace (A+B) P).re
  obtain ⟨P, hP_proj, hP_herm, hP_rank, hP_trace⟩ :=
    exists_restrictedTrace_eq_eigenvaluePartialSum (A + B) hAB k hk
  -- Step 2: Linearity of trace
  have h_linearity : restrictedTrace (A + B) P = restrictedTrace A P + restrictedTrace B P := by
    unfold restrictedTrace
    calc (P * (A + B) * P).trace
        = (P * A * P + P * B * P).trace := by rw [Matrix.mul_add, Matrix.add_mul]
      _ = (P * A * P).trace + (P * B * P).trace := Matrix.trace_add _ _
  -- Step 3: Apply re_restrictedTrace_le_eigenvaluePartialSum to A and B
  have hA_bound : (restrictedTrace A P).re ≤ eigenvaluePartialSum A hA k :=
    re_restrictedTrace_le_eigenvaluePartialSum A hA P hP_proj hP_herm k hk hP_rank
  have hB_bound : (restrictedTrace B P).re ≤ eigenvaluePartialSum B hB k :=
    re_restrictedTrace_le_eigenvaluePartialSum B hB P hP_proj hP_herm k hk hP_rank
  -- Step 4: Combine
  calc eigenvaluePartialSum (A + B) hAB k
      = (restrictedTrace (A + B) P).re := hP_trace.symm
    _ = (restrictedTrace A P + restrictedTrace B P).re := by rw [h_linearity]
    _ = (restrictedTrace A P).re + (restrictedTrace B P).re := Complex.add_re _ _
    _ ≤ eigenvaluePartialSum A hA k + eigenvaluePartialSum B hB k :=
        add_le_add hA_bound hB_bound

-- ==========================================================================
-- Ky Fan Lower Bound
-- ==========================================================================

/-- Sum splitting: eigenvalue partial sum from bottom plus partial sum
    from top of the complement equals the full eigenvalue sum.
    Bottom(M,k) + Top(M,n-k) = Top(M,n). -/
private lemma bottom_add_top_complement_eq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (k : ℕ) (hk : k ≤ n) :
    eigenvaluePartialSumBottom A hA k hk +
    eigenvaluePartialSum A hA (n - k) =
    eigenvaluePartialSum A hA n := by
  rw [eigenvaluePartialSum_of_le A hA n le_rfl,
      eigenvaluePartialSum_of_le A hA (n - k) (Nat.sub_le n k)]
  simp only [eigenvaluePartialSumBottom]
  have h_card := Fintype.card_fin n
  have h_add : n - k + k = n := Nat.sub_add_cancel hk
  -- Equivalence Fin (n-k) ⊕ Fin k ≃ Fin n
  let e : Fin (n - k) ⊕ Fin k ≃ Fin n :=
    finSumFinEquiv.trans (finCongr h_add)
  -- Split: ∑ Fin n = ∑ Fin (n-k) + ∑ Fin k via the equivalence
  rw [← Equiv.sum_comp e, Fintype.sum_sum_type, add_comm]
  simp [e, finSumFinEquiv, finCongr, Fin.castAdd, Fin.natAdd]

/-- **Ky Fan Lower Bound Inequality**: The partial sum of eigenvalues
    of A+B from the bottom is at least the sum of partial sums from
    the bottom of A and B.

    ∑\_{i=n-k}^{n-1} λᵢ(A+B) ≥ ∑\_{i=n-k}^{n-1} λᵢ(A) + ∑\_{i=n-k}^{n-1} λᵢ(B)

    Equivalently, for the smallest k eigenvalues (with descending order).

    **Reference**: Horn & Johnson, Corollary 4.3.18. -/
theorem add_le_eigenvaluePartialSumBottom_add {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : (A + B).IsHermitian)
    (k : ℕ) (hk : k ≤ n) :
    eigenvaluePartialSumBottom (A + B) hAB k hk ≥
      eigenvaluePartialSumBottom A hA k hk +
        eigenvaluePartialSumBottom B hB k hk := by
  -- Strategy: Bottom(M,k) = Top(M,n) - Top(M,n-k)
  -- Then use eigenvaluePartialSum_add_le and eigenvaluePartialSum_add_card.
  have h_splitAB := bottom_add_top_complement_eq (A + B) hAB k hk
  have h_splitA := bottom_add_top_complement_eq A hA k hk
  have h_splitB := bottom_add_top_complement_eq B hB k hk
  have h_trace := eigenvaluePartialSum_add_card A B hA hB hAB
  have h_upper :=
    eigenvaluePartialSum_add_le A B hA hB hAB (n - k) (Nat.sub_le n k)
  linarith

-- ==========================================================================
-- Rank helpers: scalar multiplication and projection compression
-- ==========================================================================

/-- The rank of a matrix is preserved under multiplication by a nonzero complex scalar.

For any `n × n` complex matrix `M` and nonzero `c : ℂ`, `rank (c • M) = rank M`.

Proof: `c • M = (c • 1) * M`.  The scalar matrix `c • 1` has determinant `c^n ≠ 0`,
so it is invertible, and left multiplication by an invertible matrix preserves rank. -/
theorem rank_smul_of_ne_zero {n : ℕ}
    (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (hc : c ≠ 0) :
    Matrix.rank (c • M) = Matrix.rank M := by
  have h_smul : c • M = (c • (1 : Matrix (Fin n) (Fin n) ℂ)) * M := by
    rw [smul_mul_assoc, Matrix.one_mul]
  rw [h_smul]
  apply Matrix.rank_mul_eq_right_of_isUnit_det
  rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  exact IsUnit.pow n (Ne.isUnit hc)

end Math.SpectralTheory
