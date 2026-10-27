import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.BellReference

/-!
# Stratified Bell references on dependent function registers

Each public stratum keeps its own site type. The tensor family has no reversal
or arithmetic dimension cast. Its paired reference is a canonical purification
of the product of per-stratum Bell references.
-/

noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators

variable {k : ℕ}

/-- The product of the Bell references of the public strata. -/
def stratifiedBellDeFinettiDensity (n : Fin k → ℕ) :
    DensityOp ((j : Fin k) → Fin (n j) → Bool × Bool) :=
  DensityOp.tensorFamily (fun j => bellDeFinettiDensity (n j))

/-- The square-root purification of the stratified product reference. -/
def stratifiedCKRPurification (n : Fin k → ℕ) :
    DensityOp (((j : Fin k) → Fin (n j) → Bool × Bool) ×
      ((j : Fin k) → Fin (n j) → Bool × Bool)) :=
  (stratifiedBellDeFinettiDensity n).purification

/-- Purity and the specified stratified marginal on an arbitrary finite reference type. -/
structure IsStratifiedCKRDeFinettiPurification {R : Type*} [Fintype R]
    (n : Fin k → ℕ) (τ : DensityOp (((j : Fin k) → Fin (n j) → Bool × Bool) × R)) : Prop where
  /-- The joint reference is pure. -/
  isPure : τ.IsPure
  /-- Its signal marginal is the product reference. -/
  marginal : τ.partialTraceRight = stratifiedBellDeFinettiDensity n

/-- The canonical reference is a stratified CKR purification, including empty strata. -/
theorem isStratifiedCKRDeFinettiPurification_stratified (n : Fin k → ℕ) :
    IsStratifiedCKRDeFinettiPurification n (stratifiedCKRPurification n) :=
  ⟨(stratifiedBellDeFinettiDensity n).isPure_purification,
    (stratifiedBellDeFinettiDensity n).partialTraceRight_purification⟩

/-- The product of the per-stratum Bell occupation-type counts. -/
def stratifiedDeFinettiPrefactor (n : Fin k → ℕ) : ℕ := ∏ j, (n j + 3).choose 3

/-- Every stratified prefactor is strictly positive, including zero strata. -/
theorem stratifiedDeFinettiPrefactor_pos (n : Fin k → ℕ) :
    0 < stratifiedDeFinettiPrefactor n :=
  Finset.prod_pos (fun j _ => Nat.choose_pos (by omega))

/-- Independent within-stratum permutation actions as a tensor family. -/
def youngRepresentation {X : Type*} [DecidableEq X] (n : Fin k → ℕ)
    (g : ∀ j, Equiv.Perm (Fin (n j))) :
    Op ((j : Fin k) → Fin (n j) → X) :=
  piTensorProduct (fun j => permutationRepresentation (X := X) (g j))

/-- Independent within-stratum permutations act unitarily. -/
theorem youngRepresentation_unitary {X : Type*} [Fintype X] [DecidableEq X]
    (n : Fin k → ℕ) (g : ∀ j, Equiv.Perm (Fin (n j))) :
    (youngRepresentation (X := X) n g)ᴴ * youngRepresentation n g = 1 := by
  rw [youngRepresentation, conjTranspose_piTensorProduct, piTensorProduct_mul]
  simp only [permutationRepresentation, (tensorPermutation_unitary _).1, piTensorProduct_one]

end Quantum.Symmetry
