import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Quantum.Channels.SubstateExtraction
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.Contractivity
import QCryptLean.Quantum.Metrics.TraceNormFinite
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Basic

/-! # Recorded unitary covariance and symmetric purification bounds

All reference and classical flag registers are finite types. Norms are explicit trace norms.
-/
noncomputable section
namespace Quantum.Channels
open Matrix Quantum.Operators Quantum.Metrics Quantum.Symmetry
open scoped Kronecker ComplexOrder
variable {X Y R : Type*} [Fintype X] [Fintype Y] [Fintype R]

omit [Fintype Y] in
/-- Covariance under a conjugation also holds after adjoining a reference. -/
theorem mapTensorId_conj_eq_of_covariance [DecidableEq R]
    (Δ : Operation X Y) (K : Operation Y Y) (U : Op X)
    (h : ∀ A, Δ (U * A * Uᴴ) = K (Δ A)) (A : Op (X × R)) :
    mapTensorId Δ R ((U ⊗ₖ (1 : Op R)) * A * (U ⊗ₖ (1 : Op R))ᴴ) =
      mapTensorId K R (mapTensorId Δ R A) := by
  ext p q
  change Δ (Matrix.of fun i j => ((U ⊗ₖ (1 : Op R)) * A * (U ⊗ₖ (1 : Op R))ᴴ)
    (i, p.2) (j, q.2)) p.1 q.1 =
      K (Δ (fun i j => A (i, p.2) (j, q.2))) p.1 q.1
  have he : (Matrix.of fun i j => ((U ⊗ₖ (1 : Op R)) * A * (U ⊗ₖ (1 : Op R))ᴴ)
      (i, p.2) (j, q.2) : Op X) = U * (Matrix.of fun i j => A (i, p.2) (j, q.2)) * Uᴴ := by
    ext i j
    simp [Matrix.of_apply, mul_apply, kroneckerMap_apply, one_apply,
      conjTranspose_apply, Fintype.sum_prod_type, apply_ite]
  rw [he]
  exact congrFun (congrFun (h _) p.1) q.1

/-- Permutation covariance preserves the amplified output trace norm. -/
theorem traceNorm_mapTensorId_perm_conj [DecidableEq R] {T : Type*} [Fintype T] [DecidableEq T]
    {k : ℕ} (Δ : Operation (Fin k → T) Y) (hΔ : PermutationCovariant Δ)
    (σ : Equiv.Perm (Fin k)) (A : Op ((Fin k → T) × R)) :
    traceNorm (mapTensorId Δ R ((permutationRepresentation σ ⊗ₖ (1 : Op R)) * A *
      (permutationRepresentation σ ⊗ₖ (1 : Op R))ᴴ)) = traceNorm (mapTensorId Δ R A) := by
  classical
  have hle (π : Equiv.Perm (Fin k)) (B : Op ((Fin k → T) × R)) :
      traceNorm (mapTensorId Δ R ((permutationRepresentation π ⊗ₖ (1 : Op R)) * B *
        (permutationRepresentation π ⊗ₖ (1 : Op R))ᴴ)) ≤ traceNorm (mapTensorId Δ R B) := by
    obtain ⟨K, hK, he⟩ := hΔ.covariance π
    rw [mapTensorId_conj_eq_of_covariance Δ K _ he]
    exact traceNorm_apply_le_of_isCompletelyPositive_of_trace_le _ hK.1.mapTensorId
      (fun B _ => (congrArg Complex.re (hK.2.mapTensorId B)).le) _
  apply le_antisymm (hle σ A)
  have h := hle σ⁻¹ ((permutationRepresentation σ ⊗ₖ (1 : Op R)) * A *
    (permutationRepresentation σ ⊗ₖ (1 : Op R))ᴴ)
  have hu : (permutationRepresentation (X := T) σ⁻¹ ⊗ₖ (1 : Op R)) *
      (permutationRepresentation σ ⊗ₖ (1 : Op R)) = 1 := by
    rw [← mul_kronecker_mul, Matrix.one_mul]
    change (tensorPermutation σ⁻¹ * tensorPermutation σ) ⊗ₖ (1 : Op R) = 1
    rw [tensorPermutation_mul, inv_mul_cancel, tensorPermutation_one, one_kronecker_one]
  have he : (permutationRepresentation σ⁻¹ ⊗ₖ (1 : Op R)) *
      ((permutationRepresentation σ ⊗ₖ (1 : Op R)) * A *
        (permutationRepresentation σ ⊗ₖ (1 : Op R))ᴴ) *
      (permutationRepresentation σ⁻¹ ⊗ₖ (1 : Op R))ᴴ = A := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc
      (permutationRepresentation σ⁻¹ ⊗ₖ (1 : Op R))]
    simp only [← Matrix.mul_assoc, hu, Matrix.one_mul]
    rw [Matrix.mul_assoc, ← conjTranspose_mul, hu, conjTranspose_one, Matrix.mul_one]
  rwa [he] at h

end Quantum.Channels
