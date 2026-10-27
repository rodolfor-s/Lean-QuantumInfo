import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra

/-! # Spectrum -/


namespace Quantum.Operators

open Matrix
open scoped ComplexOrder

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The eigenvalues supplied by Mathlib's Hermitian spectral theorem. -/
noncomputable def DensityOp.eigenvalues (ρ : DensityOp X) : X → ℝ := ρ.isHermitian.eigenvalues

/-- Density eigenvalues are nonnegative. -/
theorem DensityOp.eigenvalues_nonneg (ρ : DensityOp X) (i : X) : 0 ≤ ρ.eigenvalues i :=
  ρ.posSemidef.eigenvalues_nonneg i

/-- Density eigenvalues sum to one. -/
theorem DensityOp.sum_eigenvalues (ρ : DensityOp X) : ∑ i, ρ.eigenvalues i = 1 := by
  have h := congrArg Complex.re ρ.isHermitian.trace_eq_sum_eigenvalues
  simpa [ρ.trace_one, Complex.re_sum, DensityOp.eigenvalues] using h.symm

/-- Each density eigenvalue is at most one. -/
theorem DensityOp.eigenvalues_le_one (ρ : DensityOp X) (i : X) : ρ.eigenvalues i ≤ 1 := by
  rw [← ρ.sum_eigenvalues]
  exact Finset.single_le_sum (fun j _ => ρ.eigenvalues_nonneg j) (Finset.mem_univ i)

/-- A probability spectrum together with an explicit unitary diagonalization. -/
def DensityOp.IsEigenvalueSpectrum (ρ : DensityOp X) (lams : X → ℝ) : Prop :=
  (∀ i, 0 ≤ lams i) ∧ (∑ i, lams i = 1) ∧ (∀ i, lams i ≤ 1) ∧
    ∃ U : UnitaryOp X, ρ.toOp = U.valᴴ * diagonal (fun i => (lams i : ℂ)) * U.val

/-- Mathlib's eigenvalues supply a density spectrum. -/
theorem DensityOp.isEigenvalueSpectrum_eigenvalues (ρ : DensityOp X) :
    ρ.IsEigenvalueSpectrum ρ.eigenvalues := by
  refine ⟨ρ.eigenvalues_nonneg, ρ.sum_eigenvalues, ρ.eigenvalues_le_one,
    star ρ.isHermitian.eigenvectorUnitary, ?_⟩
  change ρ.toOp = (ρ.isHermitian.eigenvectorUnitary.valᴴ)ᴴ *
    diagonal (fun i => (ρ.eigenvalues i : ℂ)) * ρ.isHermitian.eigenvectorUnitary.valᴴ
  rw [conjTranspose_conjTranspose]
  exact ρ.isHermitian.spectral_theorem

/-- Every density operator admits a probability spectrum. -/
theorem DensityOp.exists_eigenvalueSpectrum (ρ : DensityOp X) :
    ∃ lams, ρ.IsEigenvalueSpectrum lams := ⟨ρ.eigenvalues, ρ.isEigenvalueSpectrum_eigenvalues⟩

end Quantum.Operators
