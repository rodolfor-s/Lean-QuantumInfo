import QCryptLean.InfoTheory.VonNeumannEntropy.Basic
import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.RankPurification
import QCryptLean.Quantum.Operators.Spectrum
import QCryptLean.Quantum.Operators.StateOperations

/-! # Entropy of complementary marginals of pure states -/

noncomputable section
namespace InfoTheory.VonNeumannEntropy
open Quantum.Operators Matrix Math.ClassicalEntropy
variable {X Y : Type*} [Fintype X] [Fintype Y]

open scoped Classical in
/-- Zero eigenvalues do not contribute to entropy. -/
theorem vonNeumannEntropy_eq_sum_nonzeroEigenvalueMultiset (ρ : DensityOp X) :
    vonNeumannEntropy ρ =
      (ρ.isHermitian.nonzeroEigenvalueMultiset.map entropyTerm).sum := by
  classical
  have hf (s : Multiset ℝ) : (s.map entropyTerm).sum =
      ((s.filter (· ≠ 0)).map entropyTerm).sum := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons x s ih =>
      by_cases hx : x = 0 <;> simp [hx, ih, entropyTerm]
  simpa [vonNeumannEntropy, DensityOp.eigenvalues, IsHermitian.nonzeroEigenvalueMultiset,
    IsHermitian.eigenvalueMultiset, Multiset.map_map] using hf ρ.isHermitian.eigenvalueMultiset

/-- Complementary Gram states have equal entropy, including different register sizes. -/
theorem vonNeumannEntropy_eq_of_gram (ρ : DensityOp X) (σ : DensityOp Y)
    (A : Matrix X Y ℂ) (hρ : ρ.toOp = A * Aᴴ) (hσ : σ.toOp = (Aᴴ * A)ᵀ) :
    vonNeumannEntropy ρ = vonNeumannEntropy σ := by
  classical
  have he : σ.isHermitian.eigenvalueMultiset =
      (isHermitian_conjTranspose_mul_self A).eigenvalueMultiset := by
    apply Multiset.map_injective Complex.ofReal_injective
    rw [IsHermitian.map_eigenvalueMultiset, IsHermitian.map_eigenvalueMultiset,
      hσ, Matrix.charpoly_transpose]
  have hr : ρ.isHermitian.nonzeroEigenvalueMultiset =
      (isHermitian_mul_conjTranspose_self A).nonzeroEigenvalueMultiset := by
    rcases ρ with ⟨M,hM,ht⟩
    dsimp only at hρ ⊢
    subst M
    rfl
  rw [vonNeumannEntropy_eq_sum_nonzeroEigenvalueMultiset,
    vonNeumannEntropy_eq_sum_nonzeroEigenvalueMultiset, hr, nonzeroEigenvalueMultiset_gram]
  simp only [IsHermitian.nonzeroEigenvalueMultiset, he]

/-- The two marginals of a pure bipartite state have equal entropy. -/
theorem vonNeumannEntropy_partialTraceRight_eq_left (ρ : DensityOp (X × Y)) (hρ : ρ.IsPure) :
    vonNeumannEntropy ρ.partialTraceRight = vonNeumannEntropy ρ.partialTraceLeft := by
  classical
  obtain ⟨v, hv⟩ := hρ.exists_normKet ρ
  let A : Matrix X Y ℂ := fun x y => v.vec (x, y)
  apply vonNeumannEntropy_eq_of_gram _ _ A
  · rw [← hv]
    exact Ket.partialTraceRight_vectorize A
  · rw [← hv]
    exact Ket.partialTraceLeft_vectorize A
end InfoTheory.VonNeumannEntropy
