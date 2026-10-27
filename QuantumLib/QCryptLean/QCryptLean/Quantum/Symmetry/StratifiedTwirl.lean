import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Stratified

/-!
# Stratified blocking on dependent function registers

Within-stratum permutations act independently on their actual function factors.
The average is normalized by the product of factorials and preserves any linear
postprocessor's adjoint symmetry. No enumeration appears in the construction.
-/

noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators Quantum.Channels

variable {X Y : Type*} [Fintype X] [DecidableEq X] {k : ℕ} (n : Fin k → ℕ)

/-- The within-stratum action respects the product group law. -/
theorem youngRepresentation_mul (σ τ : ∀ j, Equiv.Perm (Fin (n j))) :
    youngRepresentation (X := X) n (σ * τ) =
      youngRepresentation n σ * youngRepresentation n τ := by
  rw [youngRepresentation, youngRepresentation, youngRepresentation, piTensorProduct_mul]
  congr 1
  funext j
  exact (tensorPermutation_mul (σ j) (τ j)).symm

/-- Covariance restricted to within-stratum permutations. -/
structure StratifiedPermutationCovariant [Fintype Y]
    (F : Operation ((j : Fin k) → Fin (n j) → X) Y) : Prop where
  /-- Each within-stratum permutation admits an output correction channel. -/
  covariance : ∀ σ : (∀ j, Equiv.Perm (Fin (n j))), ∃ K : Operation Y Y, IsChannel K ∧
    ∀ A, F (youngRepresentation n σ * A * (youngRepresentation n σ)ᴴ) = K (F A)

/-- Linear conjugation by the action of a site permutation. -/
def youngConjLin (σ : (∀ j, Equiv.Perm (Fin (n j)))) :
    Operation ((j : Fin k) → Fin (n j) → X) ((j : Fin k) → Fin (n j) → X) where
  toFun A := youngRepresentation n σ * A * (youngRepresentation n σ)ᴴ
  map_add' A B := by rw [mul_add, add_mul]
  map_smul' c A := by simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

/-- Average the internal permutation seed before a fixed linear postprocessor. -/
def stratifiedBlockingTwirl (F : Operation ((j : Fin k) → Fin (n j) → X) Y) :
    Operation ((j : Fin k) → Fin (n j) → X) Y :=
  ((∏ j, Nat.factorial (n j) : ℕ) : ℂ)⁻¹ •
    ∑ σ : (∀ j, Equiv.Perm (Fin (n j))), F.comp (youngConjLin n σ)

/-- The blocking map is the average of its permutation-conjugated inputs. -/
theorem stratifiedBlockingTwirl_apply (F : Operation ((j : Fin k) → Fin (n j) → X) Y)
    (A : Op ((j : Fin k) → Fin (n j) → X)) :
    stratifiedBlockingTwirl n F A = ((∏ j, Nat.factorial (n j) : ℕ) : ℂ)⁻¹ •
      ∑ σ : (∀ j, Equiv.Perm (Fin (n j))),
        F (youngRepresentation n σ * A * (youngRepresentation n σ)ᴴ) := by
  simp only [stratifiedBlockingTwirl, LinearMap.smul_apply, LinearMap.coe_sum,
    Finset.sum_apply, LinearMap.comp_apply, youngConjLin, LinearMap.coe_mk, AddHom.coe_mk]

/-- Input site permutations are absorbed by the uniform average. -/
theorem stratifiedBlockingTwirl_perm_invariant (F : Operation ((j : Fin k) → Fin (n j) → X) Y)
    (τ : (∀ j, Equiv.Perm (Fin (n j)))) (A : Op ((j : Fin k) → Fin (n j) → X)) :
    stratifiedBlockingTwirl n F
      (youngRepresentation n τ * A * (youngRepresentation n τ)ᴴ) =
        stratifiedBlockingTwirl n F A := by
  rw [stratifiedBlockingTwirl_apply, stratifiedBlockingTwirl_apply]
  apply congrArg (((∏ j, Nat.factorial (n j) : ℕ) : ℂ)⁻¹ • ·)
  have ht (σ : (∀ j, Equiv.Perm (Fin (n j)))) :
      youngRepresentation n σ *
        (youngRepresentation n τ * A * (youngRepresentation n τ)ᴴ) *
        (youngRepresentation n σ)ᴴ =
      youngRepresentation n (σ * τ) * A * (youngRepresentation n (σ * τ))ᴴ := by
    rw [youngRepresentation_mul]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  simp_rw [ht]
  exact Equiv.sum_comp (Equiv.mulRight τ) (fun σ =>
    F (youngRepresentation n σ * A * (youngRepresentation n σ)ᴴ))

/-- Every randomized blocking map has the identity CKR correction channel. -/
theorem stratifiedBlockingTwirl_permutationCovariant [Fintype Y]
    (F : Operation ((j : Fin k) → Fin (n j) → X) Y) :
    StratifiedPermutationCovariant n (stratifiedBlockingTwirl n F) where
  covariance σ := ⟨LinearMap.id, isChannel_id, stratifiedBlockingTwirl_perm_invariant n F σ⟩

/-- Adjoint preservation passes through the random permutation average. -/
theorem stratifiedBlockingTwirl_conjTranspose (F : Operation ((j : Fin k) → Fin (n j) → X) Y)
    (hF : ∀ A, F Aᴴ = (F A)ᴴ) (A : Op ((j : Fin k) → Fin (n j) → X)) :
    stratifiedBlockingTwirl n F Aᴴ = (stratifiedBlockingTwirl n F A)ᴴ := by
  rw [stratifiedBlockingTwirl_apply, stratifiedBlockingTwirl_apply,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  simp only [star_inv₀, star_natCast]
  apply congrArg (((∏ j, Nat.factorial (n j) : ℕ) : ℂ)⁻¹ • ·)
  apply Finset.sum_congr rfl
  intro σ _
  rw [← hF, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    Matrix.mul_assoc]

end Quantum.Symmetry
