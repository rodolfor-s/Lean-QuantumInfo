import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Spectrum
import QCryptLean.Quantum.Operators.StateOperations

/-! # Basic -/


noncomputable section

namespace InfoTheory.VonNeumannEntropy

open Quantum.Operators Math.ClassicalEntropy Matrix

variable {Q R : Type*} [Fintype Q] [Fintype R]

/-- Von Neumann entropy in nats, with the existing zero-eigenvalue convention. -/
def vonNeumannEntropy (ρ : DensityOp Q) : ℝ := by
  classical
  exact ∑ i, entropyTerm (ρ.eigenvalues i)

/-- Density spectra have nonnegative entropy. -/
theorem vonNeumannEntropy_nonneg (ρ : DensityOp Q) : 0 ≤ vonNeumannEntropy ρ := by
  classical
  exact Finset.sum_nonneg fun i _ => entropyTerm_nonneg _
    (ρ.eigenvalues_nonneg i) (ρ.eigenvalues_le_one i)

/-- Register relabelling preserves entropy, independently of the chosen eigenbasis. -/
theorem vonNeumannEntropy_reindex (e : Q ≃ R) (ρ : DensityOp Q) :
    vonNeumannEntropy (ρ.reindex e) = vonNeumannEntropy ρ := by
  classical
  have h := congrArg (fun s : Multiset ℝ => (s.map entropyTerm).sum)
    (ρ.isHermitian.eigenvalueMultiset_reindex e)
  simpa [vonNeumannEntropy, Matrix.IsHermitian.eigenvalueMultiset,
    Multiset.map_map, DensityOp.eigenvalues, DensityOp.reindex] using h

/-- A computationally diagonal density operator has the entropy of its diagonal distribution. -/
theorem vonNeumannEntropy_eq_sum_entropyTerm_of_diagonal
    {Q : Type*} [Fintype Q] [DecidableEq Q] (ρ : DensityOp Q) (d : Q → ℝ)
    (h : ρ.toOp = Matrix.diagonal (fun i => (d i : ℂ))) :
    vonNeumannEntropy ρ = ∑ i, entropyTerm (d i) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Q) (Classical.decEq Q)
  classical
  have he : ρ.isHermitian.eigenvalueMultiset = Finset.univ.val.map d := by
    rcases ρ with ⟨A, hA, ht⟩
    dsimp only at h ⊢
    subst A
    exact Matrix.eigenvalueMultiset_diagonal d
  have hs := congrArg (fun s : Multiset ℝ => (s.map entropyTerm).sum) he
  simpa [vonNeumannEntropy, Matrix.IsHermitian.eigenvalueMultiset,
    DensityOp.eigenvalues, Multiset.map_map] using hs

/-- An orthonormal spectral decomposition computes entropy from its weights. -/
theorem vonNeumannEntropy_eq_sum_entropyTerm_of_diagonalization
    {Q : Type*} [Fintype Q] [DecidableEq Q] (ρ : DensityOp Q)
    (U : Matrix Q Q ℂ) (hU : Uᴴ * U = 1) (d : Q → ℝ)
    (h : ρ.toOp = U * Matrix.diagonal (fun i => (d i : ℂ)) * Uᴴ) :
    vonNeumannEntropy ρ = ∑ i, entropyTerm (d i) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Q) (Classical.decEq Q)
  classical
  have he : ρ.isHermitian.eigenvalueMultiset = Finset.univ.val.map d := by
    apply Multiset.map_injective Complex.ofReal_injective
    rw [Matrix.IsHermitian.map_eigenvalueMultiset, h, Matrix.charpoly_mul_comm,
      ← Matrix.mul_assoc, hU, Matrix.one_mul, Matrix.charpoly_diagonal,
      Polynomial.roots_prod _ _
        (Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.X_sub_C_ne_zero _))]
    simp [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Multiset.map_map]
  have hs := congrArg (fun s : Multiset ℝ => (s.map entropyTerm).sum) he
  simpa [vonNeumannEntropy, Matrix.IsHermitian.eigenvalueMultiset,
    DensityOp.eigenvalues, Multiset.map_map] using hs

end InfoTheory.VonNeumannEntropy
