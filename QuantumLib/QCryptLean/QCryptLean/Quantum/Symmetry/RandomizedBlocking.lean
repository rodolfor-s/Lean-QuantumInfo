import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.KrausAlgebra
import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Twirl

/-! # Randomized Blocking -/


noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators Quantum.Channels

variable {X Y : Type*} [Fintype X] [DecidableEq X] {k : ℕ}

/-- Linear conjugation by the action of a site permutation. -/
def permConjLin (σ : Equiv.Perm (Fin k)) : Operation (Fin k → X) (Fin k → X) where
  toFun A := permutationRepresentation σ * A * (permutationRepresentation σ)ᴴ
  map_add' A B := by rw [mul_add, add_mul]
  map_smul' c A := by simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

/-- A site permutation acts by a unitary channel on the function register. -/
theorem isChannel_permConjLin (σ : Equiv.Perm (Fin k)) : IsChannel (permConjLin (X := X) σ) := by
  change IsChannel (Matrix.conjLinearMap (permutationRepresentation σ))
  apply (isChannel_conjLinearMap_iff _).mpr
  convert (tensorPermutation_unitary (X := X) (R := ℂ) σ).1 using 1
  ext i j
  simp [Matrix.one_apply]

/-- Average the internal permutation seed before a fixed linear postprocessor. -/
def randomizedBlockingTwirl (F : Operation (Fin k → X) Y) : Operation (Fin k → X) Y :=
  (Nat.factorial k : ℂ)⁻¹ • ∑ σ : Equiv.Perm (Fin k), F.comp (permConjLin σ)

/-- The blocking map is the average of its permutation-conjugated inputs. -/
theorem randomizedBlockingTwirl_apply (F : Operation (Fin k → X) Y) (A : Op (Fin k → X)) :
    randomizedBlockingTwirl F A = (Nat.factorial k : ℂ)⁻¹ •
      ∑ σ : Equiv.Perm (Fin k),
        F (permutationRepresentation σ * A * (permutationRepresentation σ)ᴴ) := by
  simp only [randomizedBlockingTwirl, LinearMap.smul_apply, LinearMap.coe_sum,
    Finset.sum_apply, LinearMap.comp_apply, permConjLin, LinearMap.coe_mk, AddHom.coe_mk]

/-- Input site permutations are absorbed by the uniform average. -/
theorem randomizedBlockingTwirl_perm_invariant (F : Operation (Fin k → X) Y)
    (τ : Equiv.Perm (Fin k)) (A : Op (Fin k → X)) :
    randomizedBlockingTwirl F
      (permutationRepresentation τ * A * (permutationRepresentation τ)ᴴ) =
        randomizedBlockingTwirl F A := by
  rw [randomizedBlockingTwirl_apply, randomizedBlockingTwirl_apply]
  apply congrArg ((Nat.factorial k : ℂ)⁻¹ • ·)
  have ht (σ : Equiv.Perm (Fin k)) :
      permutationRepresentation σ *
        (permutationRepresentation τ * A * (permutationRepresentation τ)ᴴ) *
        (permutationRepresentation σ)ᴴ =
      permutationRepresentation (σ * τ) * A * (permutationRepresentation (σ * τ))ᴴ := by
    simp only [permutationRepresentation]
    rw [← tensorPermutation_mul]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  simp_rw [ht]
  exact Equiv.sum_comp (Equiv.mulRight τ) (fun σ =>
    F (permutationRepresentation σ * A * (permutationRepresentation σ)ᴴ))

/-- Every randomized blocking map has the identity CKR correction channel. -/
theorem randomizedBlockingTwirl_permutationCovariant [Fintype Y]
    (F : Operation (Fin k → X) Y) : PermutationCovariant (randomizedBlockingTwirl F) where
  covariance σ := ⟨LinearMap.id, isChannel_id, randomizedBlockingTwirl_perm_invariant F σ⟩

/-- Adjoint preservation passes through the random permutation average. -/
theorem randomizedBlockingTwirl_conjTranspose (F : Operation (Fin k → X) Y)
    (hF : ∀ A, F Aᴴ = (F A)ᴴ) (A : Op (Fin k → X)) :
    randomizedBlockingTwirl F Aᴴ = (randomizedBlockingTwirl F A)ᴴ := by
  rw [randomizedBlockingTwirl_apply, randomizedBlockingTwirl_apply,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  simp only [star_inv₀, star_natCast]
  apply congrArg ((Nat.factorial k : ℂ)⁻¹ • ·)
  apply Finset.sum_congr rfl
  intro σ _
  rw [← hF, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    Matrix.mul_assoc]

end Quantum.Symmetry
