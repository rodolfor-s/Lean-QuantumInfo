import Mathlib.Analysis.Matrix.Order
import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD
import QCryptLean.Math.LinearAlgebra.Matrix.Blocks
import QCryptLean.Math.LinearAlgebra.Matrix.Transport

/-!
# Spectral foundations on finite types

Spectral data are compared as multisets, since the chosen eigenvector basis need
not be preserved by reindexing. Positive square roots are compared by uniqueness.
Matrix order is selected locally; no order or norm instance is exported here.
-/

namespace Matrix

open scoped ComplexOrder MatrixOrder Kronecker

variable {X Y : Type*} [Fintype X] [Fintype Y]

section Spectrum

variable [DecidableEq X] [DecidableEq Y]

/-- Eigenvalues with multiplicities, without making an ordering part of the interface. -/
noncomputable def IsHermitian.eigenvalueMultiset {A : Matrix X X ℂ} (h : A.IsHermitian) :
    Multiset ℝ := Finset.univ.val.map h.eigenvalues

/-- The complex images of the eigenvalue multiset are exactly the characteristic roots. -/
theorem IsHermitian.map_eigenvalueMultiset
    {A : Matrix X X ℂ} (h : A.IsHermitian) :
    h.eigenvalueMultiset.map Complex.ofReal = A.charpoly.roots := by
  simpa [IsHermitian.eigenvalueMultiset, Multiset.map_map] using
    h.roots_charpoly_eq_eigenvalues.symm

/-- Relabelling the basis preserves the eigenvalue multiset, not a chosen eigenbasis. -/
theorem IsHermitian.eigenvalueMultiset_reindex {A : Matrix X X ℂ} (h : A.IsHermitian)
    (e : X ≃ Y) : (h.reindex e).eigenvalueMultiset = h.eigenvalueMultiset := by
  classical
  apply Multiset.map_injective Complex.ofReal_injective
  rw [IsHermitian.map_eigenvalueMultiset, IsHermitian.map_eigenvalueMultiset,
    charpoly_reindex]

/-- A Hermitian matrix's real trace is the sum of its eigenvalues. -/
theorem IsHermitian.sum_eigenvalueMultiset {A : Matrix X X ℂ} (h : A.IsHermitian) :
    h.eigenvalueMultiset.sum = A.trace.re := by
  rw [h.trace_eq_sum_eigenvalues]
  simp [IsHermitian.eigenvalueMultiset, Complex.re_sum]

/-- Positive semidefinite matrices have nonnegative eigenvalue multisets. -/
theorem PosSemidef.eigenvalueMultiset_nonneg {A : Matrix X X ℂ} (h : A.PosSemidef)
    {r : ℝ} (hr : r ∈ h.isHermitian.eigenvalueMultiset) : 0 ≤ r := by
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hr
  exact h.eigenvalues_nonneg i

/-- The multiplicity of a real eigenvalue is its characteristic-root multiplicity. -/
theorem IsHermitian.count_eigenvalueMultiset {A : Matrix X X ℂ} (h : A.IsHermitian) (r : ℝ) :
    h.eigenvalueMultiset.count r = A.charpoly.rootMultiplicity (r : ℂ) := by
  classical
  rw [← Multiset.count_map_eq_count' Complex.ofReal _ Complex.ofReal_injective r,
    h.map_eigenvalueMultiset, Polynomial.count_roots]

/-- The nonzero spectrum, retaining multiplicities. -/
noncomputable def IsHermitian.nonzeroEigenvalueMultiset {A : Matrix X X ℂ} (h : A.IsHermitian) :
    Multiset ℝ := h.eigenvalueMultiset.filter (· ≠ 0)

/-- Rectangular Gram matrices have the same nonzero spectrum, even for empty registers. -/
theorem nonzeroEigenvalueMultiset_gram (C : Matrix X Y ℂ) :
    (isHermitian_mul_conjTranspose_self C).nonzeroEigenvalueMultiset =
      (isHermitian_conjTranspose_mul_self C).nonzeroEigenvalueMultiset := by
  classical
  ext r
  by_cases hr : r = 0
  · subst r
    simp [IsHermitian.nonzeroEigenvalueMultiset]
  · simp only [IsHermitian.nonzeroEigenvalueMultiset, Multiset.count_filter,
      hr, ne_eq, not_false_eq_true, ite_true, IsHermitian.count_eigenvalueMultiset]
    have hz : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
    have hpow (k : ℕ) : (Polynomial.X ^ k : Polynomial ℂ).rootMultiplicity (r : ℂ) = 0 :=
      Polynomial.rootMultiplicity_eq_zero (by simpa [Polynomial.IsRoot] using pow_ne_zero k hz)
    have h := congrArg (Polynomial.rootMultiplicity (r : ℂ)) (charpoly_mul_comm' C Cᴴ)
    rw [Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
        (charpoly_monic _).ne_zero),
      Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero)
        (charpoly_monic _).ne_zero), hpow, hpow, zero_add, zero_add] at h
    exact h

/-- The multiset of a real diagonal consists of its entries. -/
theorem eigenvalueMultiset_diagonal (d : X → ℝ) :
    (isHermitian_diagonal_of_self_adjoint (fun i => (d i : ℂ))
      (by ext i; exact Complex.conj_ofReal _)).eigenvalueMultiset =
      Finset.univ.val.map d := by
  classical
  apply Multiset.map_injective Complex.ofReal_injective
  rw [IsHermitian.map_eigenvalueMultiset, charpoly_diagonal,
    Polynomial.roots_prod _ _
      (Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.X_sub_C_ne_zero _))]
  simp [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Multiset.map_map]

/-- Tensor spectra are the pairwise products of the component spectra. -/
theorem IsHermitian.eigenvalueMultiset_kronecker {A : Matrix X X ℂ} {B : Matrix Y Y ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (hA.kronecker hB).eigenvalueMultiset =
      Finset.univ.val.map (fun p : X × Y => hA.eigenvalues p.1 * hB.eigenvalues p.2) := by
  classical
  let U := hA.eigenvectorUnitary
  let V := hB.eigenvectorUnitary
  have hspec : (A ⊗ₖ B) =
      (U.val ⊗ₖ V.val) *
        diagonal (fun p : X × Y => (hA.eigenvalues p.1 : ℂ) * (hB.eigenvalues p.2 : ℂ)) *
      (U.val ⊗ₖ V.val)ᴴ := by
    conv_lhs => rw [hA.spectral_theorem, hB.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply, mul_kronecker_mul,
      diagonal_kronecker_diagonal, conjTranspose_kronecker]
    rfl
  have hunit : (U.val ⊗ₖ V.val)ᴴ * (U.val ⊗ₖ V.val) = 1 := by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul]
    change (star U.val * U.val) ⊗ₖ (star V.val * V.val) = 1
    rw [Unitary.coe_star_mul_self, Unitary.coe_star_mul_self, one_kronecker_one]
  apply Multiset.map_injective Complex.ofReal_injective
  rw [IsHermitian.map_eigenvalueMultiset, hspec, charpoly_mul_comm, ← Matrix.mul_assoc,
    hunit, one_mul, charpoly_diagonal,
    Polynomial.roots_prod _ _
      (Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.X_sub_C_ne_zero _))]
  simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Multiset.map_map,
    Function.comp_apply, Complex.ofReal_mul]

end Spectrum

/-- The positive square root commutes with a change of basis labels. -/
theorem reindex_cfcSqrt {A : Matrix X X ℂ} (h : A.PosSemidef) (e : X ≃ Y) :
    open scoped Classical in
    reindex e e (CFC.sqrt A) = CFC.sqrt (reindex e e A) := by
  classical
  symm
  apply CFC.sqrt_unique
  · change reindex e e (CFC.sqrt A) * reindex e e (CFC.sqrt A) = reindex e e A
    simp only [Matrix.reindex_apply]
    rw [submatrix_mul_equiv, CFC.sqrt_mul_sqrt_self A h.nonneg]
  · exact (posSemidef_reindex_iff e _).mpr
      (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)) |>.nonneg

/-- A positive square root gives a Gram decomposition with the same register. -/
theorem PosSemidef.eq_cfcSqrt_mul_conjTranspose {A : Matrix X X ℂ} (h : A.PosSemidef) :
    open scoped Classical in
    A = CFC.sqrt A * (CFC.sqrt A)ᴴ := by
  classical
  rw [(nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq]
  exact (CFC.sqrt_mul_sqrt_self A h.nonneg).symm

/-- A PSD matrix is the sum of the outer products of the columns of its positive square root. -/
theorem PosSemidef.eq_sum_cfcSqrt_vecMulVec {A : Matrix X X ℂ} (h : A.PosSemidef) :
    open scoped Classical in
    A = ∑ j, vecMulVec (fun i => CFC.sqrt A i j) (star (fun i => CFC.sqrt A i j)) := by
  classical
  conv_lhs => rw [h.eq_cfcSqrt_mul_conjTranspose]
  ext i j
  simp [mul_apply, Matrix.sum_apply, conjTranspose_apply, vecMulVec_apply]

end Matrix

namespace Matrix
open scoped MatrixOrder ComplexOrder
variable {X I 𝕜 : Type*} [Fintype X] [Fintype I] [DecidableEq X] [DecidableEq I] [RCLike 𝕜]
/-- The trace of functional calculus is the sum of the function on the eigenvalues. -/
theorem IsHermitian.trace_cfc {A : Matrix X X 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, (f (hA.eigenvalues i) : 𝕜) := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, trace_mul_cycle]
  simp

omit [DecidableEq X] in
/-- The positive square root acts separately on the blocks of a block diagonal matrix. -/
theorem PosSemidef.sqrt_blockDiagonal {A : I → Matrix X X ℂ}
    (hA : ∀ i, (A i).PosSemidef) :
    letI := Classical.decEq X
    CFC.sqrt (blockDiagonal A) = blockDiagonal (fun i => CFC.sqrt (A i)) := by
  classical
  apply CFC.sqrt_unique
  · rw [← blockDiagonal_mul]
    exact congrArg blockDiagonal (funext fun i => CFC.sqrt_mul_sqrt_self _ (hA i).nonneg)
  · exact (posSemidef_blockDiagonal fun i =>
      nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (A i))).nonneg
/-- Conjugation by the positive inverse square root normalizes a positive definite matrix. -/
theorem PosDef.sqrt_inv_mul_self_mul_sqrt_inv {A : Matrix X X 𝕜} (hA : A.PosDef) :
    CFC.sqrt A⁻¹ * A * CFC.sqrt A⁻¹ = 1 := by
  have hs : IsUnit (CFC.sqrt A).det := by
    have he := congrArg det (CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg)
    rw [det_mul] at he
    have hu : IsUnit A.det := hA.isUnit.map detMonoidHom
    rw [← he] at hu
    exact isUnit_of_mul_isUnit_left hu
  rw [← hA.posSemidef.inv_sqrt]
  conv_lhs => arg 1; arg 2; rw [← CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]
  rw [← mul_assoc, nonsing_inv_mul _ hs, one_mul, mul_nonsing_inv _ hs]
/-- Rectangular isometric conjugation commutes with the positive square root. -/
theorem PosSemidef.sqrt_conj_of_isometry {Y : Type*} [Fintype Y]
    {A : Matrix X X 𝕜} (hA : A.PosSemidef) (V : Matrix Y X 𝕜) (hV : Vᴴ * V = 1) :
    open scoped Classical in
    CFC.sqrt (V * A * Vᴴ) = V * CFC.sqrt A * Vᴴ := by
  classical
  apply CFC.sqrt_unique
  · calc
      _ = V * (CFC.sqrt A * (Vᴴ * V) * CFC.sqrt A) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV, mul_one, CFC.sqrt_mul_sqrt_self A hA.nonneg]
  · exact ((nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).mul_mul_conjTranspose_same V).nonneg
end Matrix

namespace Matrix
open scoped ComplexOrder MatrixOrder
variable {X Y : Type*} [Fintype X] [Fintype Y]
open scoped Classical in
/-- The positive square root preserves a direct sum of two positive matrices. -/
theorem PosSemidef.sqrt_fromBlocks_zero {A : Matrix X X ℂ} {B : Matrix Y Y ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    CFC.sqrt (fromBlocks A 0 0 B) = fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt B) := by
  apply CFC.sqrt_unique
  · rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      CFC.sqrt_mul_sqrt_self A hA.nonneg, CFC.sqrt_mul_sqrt_self B hB.nonneg]
  · exact ((nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).fromBlocks_zero
      (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B))).nonneg
end Matrix
