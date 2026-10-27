import Mathlib.Analysis.Matrix.PosDef

/-!
# PSD Spectral Decompositions — rank-minimal outer-product sums

This file records spectral-theorem consequences for positive semidefinite
complex matrices that are independent of quantum-channel infrastructure.

## Main statements
- `Matrix.IsHermitian.eq_sum_sqrt_eigenvalues_vecMulVec`: Hermitian matrix with
  nonnegative eigenvalues as a full eigenvector outer-product sum.
- `Matrix.PosSemidef.exists_eq_sum_vecMulVec`: PSD matrix as a sum of exactly `Matrix.rank M`
  rank-one outer products.
-/

open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

namespace Math.SpectralTheory

/-- A Hermitian matrix with nonnegative eigenvalues is the sum of outer products
of eigenvectors scaled by the square roots of those eigenvalues. -/
lemma _root_.Matrix.IsHermitian.eq_sum_sqrt_eigenvalues_vecMulVec
    {N : ℕ} {M : Matrix (Fin N) (Fin N) ℂ} (hH : M.IsHermitian)
    (h_nonneg : ∀ k : Fin N, 0 ≤ hH.eigenvalues k) :
    M =
      ∑ k : Fin N,
        Matrix.vecMulVec
          (fun i => (Real.sqrt (hH.eigenvalues k) : ℂ) *
            (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) i k)
          (star (fun i => (Real.sqrt (hH.eigenvalues k) : ℂ) *
            (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) i k)) := by
  classical
  set U : Matrix (Fin N) (Fin N) ℂ :=
    (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) with hU_def
  set lams : Fin N → ℝ := hH.eigenvalues with hlams_def
  set w : Fin N → Fin N → ℂ := fun k i =>
    (Real.sqrt (lams k) : ℂ) * U i k with hw_def
  have hM_full : M = ∑ k : Fin N, Matrix.vecMulVec (w k) (star (w k)) := by
    have hspec := hH.spectral_theorem
    rw [hspec, Unitary.conjStarAlgAut_apply]
    ext i j
    rw [Matrix.mul_apply, Matrix.sum_apply]
    have hLHS_expand :
        ∑ p : Fin N,
            ((U * Matrix.diagonal (RCLike.ofReal ∘ lams) : Matrix (Fin N) (Fin N) ℂ)
              i p) * (star U : Matrix (Fin N) (Fin N) ℂ) p j =
          ∑ k : Fin N, U i k * (lams k : ℂ) * star (U j k) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Matrix.mul_diagonal]
      simp [Function.comp, Matrix.star_apply]
    rw [hLHS_expand]
    apply Finset.sum_congr rfl
    intro k _
    have hlamk : 0 ≤ lams k := by simpa [hlams_def] using h_nonneg k
    have hsqrt :
        (Real.sqrt (lams k) : ℂ) * (Real.sqrt (lams k) : ℂ) = (lams k : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hlamk]
    have hstar : star ((Real.sqrt (lams k) : ℂ)) = (Real.sqrt (lams k) : ℂ) :=
      Complex.conj_ofReal _
    simp only [Matrix.vecMulVec_apply, Pi.star_apply, hw_def]
    have hstarprod :
        star ((Real.sqrt (lams k) : ℂ) * U j k) =
          (Real.sqrt (lams k) : ℂ) * star (U j k) := by
      rw [StarMul.star_mul, mul_comm, hstar]
    rw [hstarprod]
    calc U i k * (lams k : ℂ) * star (U j k)
        = ((Real.sqrt (lams k) : ℂ) * (Real.sqrt (lams k) : ℂ)) *
            (U i k * star (U j k)) := by rw [hsqrt]; ring
      _ = (Real.sqrt (lams k) : ℂ) * U i k *
            ((Real.sqrt (lams k) : ℂ) * star (U j k)) := by ring
  simpa [hU_def, hlams_def, hw_def] using hM_full

/-- **Rank-minimal PSD outer-product decomposition.**

    A PSD matrix `M` over `ℂ` of rank `r` can be written as a sum of *exactly* `r`
    rank-one outer products `vᵢ vᵢ†`.

    This is the standard spectral-theorem corollary: the Hermitian/PSD matrix `M`
    diagonalises as `U D U†` with `D` diagonal and entries `≥ 0`; the number of
    nonzero diagonal entries equals `Matrix.rank M`; setting
    `vᵢ = √(λᵢ) · uᵢ` for the nonzero eigenvalues yields the desired family.

    Compare `Matrix.posSemidef_iff_eq_sum_vecMulVec` (Mathlib) which only provides
    *some* `m` summands; here we pin the count to `Matrix.rank M`. -/
theorem _root_.Matrix.PosSemidef.exists_eq_sum_vecMulVec
    {N : ℕ} {M : Matrix (Fin N) (Fin N) ℂ} (hM : M.PosSemidef) :
    ∃ (v : Fin (Matrix.rank M) → Fin N → ℂ),
      M = ∑ k, Matrix.vecMulVec (v k) (star (v k)) := by
  classical
  have hH : M.IsHermitian := hM.1
  -- Convenient aliases for the spectral data.
  set U : Matrix (Fin N) (Fin N) ℂ :=
    (hH.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) with hU_def
  set lams : Fin N → ℝ := hH.eigenvalues with hlams_def
  -- Scaled eigenvectors w k i = √(λ_k) * (k-th eigenvector at coord i).
  set w : Fin N → Fin N → ℂ := fun k i =>
    (Real.sqrt (lams k) : ℂ) * U i k with hw_def
  -- Step 1: M is the full sum of outer products of scaled eigenvectors.
  have hM_full : M = ∑ k : Fin N, Matrix.vecMulVec (w k) (star (w k)) := by
    simpa [hU_def, hlams_def, hw_def] using
      Matrix.IsHermitian.eq_sum_sqrt_eigenvalues_vecMulVec hH
        (fun k => by simpa [hlams_def] using hM.eigenvalues_nonneg k)
  -- Step 2: pin the count to rank M by reindexing through the nonzero-eigenvalue
  -- subtype.  When `λ_k = 0`, `w k = 0` so the summand vanishes.
  have hcard : Matrix.rank M = Fintype.card {i : Fin N // lams i ≠ 0} :=
    hH.rank_eq_card_non_zero_eigs
  let e : Fin (Matrix.rank M) ≃ {i : Fin N // lams i ≠ 0} :=
    (Fintype.equivFinOfCardEq hcard.symm).symm
  refine ⟨fun k => w (e k).val, ?_⟩
  conv_lhs => rw [hM_full]
  -- Restrict to nonzero-eigenvalue indices.
  have hzero : ∀ k : Fin N, lams k = 0 →
      Matrix.vecMulVec (w k) (star (w k)) = 0 := by
    intro k hk
    ext i j
    simp [hw_def, Matrix.vecMulVec_apply, hk]
  have h_restrict :
      (∑ k : Fin N, Matrix.vecMulVec (w k) (star (w k))) =
        ∑ k ∈ Finset.univ.filter (fun i : Fin N => lams i ≠ 0),
          Matrix.vecMulVec (w k) (star (w k)) := by
    symm
    apply Finset.sum_filter_of_ne
    intro k _ hne hzeq
    exact hne (hzero k hzeq)
  rw [h_restrict]
  -- Convert filter sum to subtype sum, then reindex via `e`.
  have h_filter_iff :
      ∀ x : Fin N, x ∈ Finset.univ.filter (fun i : Fin N => lams i ≠ 0) ↔ lams x ≠ 0 := by
    intro x; simp
  rw [Finset.sum_subtype (s := Finset.univ.filter (fun i : Fin N => lams i ≠ 0))
        h_filter_iff (fun k => Matrix.vecMulVec (w k) (star (w k)))]
  exact (Fintype.sum_equiv e _
    (fun p => Matrix.vecMulVec (w p.val) (star (w p.val))) (fun _ => rfl)).symm

end Math.SpectralTheory

end -- noncomputable section
