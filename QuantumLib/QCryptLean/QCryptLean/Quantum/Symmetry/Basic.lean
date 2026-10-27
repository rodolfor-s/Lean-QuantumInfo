import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor

/-! # Basic -/


noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators
open scoped ComplexOrder

variable {X : Type*} [Fintype X] [DecidableEq X] {k : ℕ}

/-- The representation of site permutations on a tensor power. -/
abbrev permutationRepresentation (σ : Equiv.Perm (Fin k)) : Op (Fin k → X) :=
  Matrix.tensorPermutation σ

/-- The fixed vectors of all site permutations form the symmetric subspace. -/
def symmetricSubspace (X : Type*) (k : ℕ) :
    Submodule ℂ ((Fin k → X) → ℂ) where
  carrier := {v | ∀ σ : Equiv.Perm (Fin k), ∀ x, v (x ∘ σ) = v x}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw σ x; simp [hv σ x, hw σ x]
  smul_mem' := by intro c v hv σ x; simp [hv σ x]

/-- A density operator is invariant under conjugation by each site permutation. -/
def IsPermutationInvariant (ρ : DensityOp (Fin k → X)) : Prop :=
  ∀ σ : Equiv.Perm (Fin k),
    permutationRepresentation σ * ρ.toOp * (permutationRepresentation σ)ᴴ = ρ.toOp

/-- Invariance is equivalent to the entrywise relabelling identity. -/
theorem isPermutationInvariant_iff (ρ : DensityOp (Fin k → X)) :
    IsPermutationInvariant ρ ↔
      ∀ σ : Equiv.Perm (Fin k), ∀ x y, ρ.toOp (x ∘ σ) (y ∘ σ) = ρ.toOp x y := by
  constructor
  · intro h σ x y
    simpa only [tensorPermutation_conj_apply] using congrFun (congrFun (h σ) x) y
  · intro h σ
    ext x y
    exact (tensorPermutation_conj_apply σ ρ.toOp x y).trans (h σ x y)

/-- Relabelling each local register preserves permutation invariance. -/
theorem IsPermutationInvariant.reindex {Y : Type*} [Fintype Y] [DecidableEq Y]
    {ρ : DensityOp (Fin k → X)} (hρ : IsPermutationInvariant ρ) (e : X ≃ Y) :
    IsPermutationInvariant (ρ.reindex (Equiv.piCongrRight fun _ => e)) := by
  apply (isPermutationInvariant_iff _).mpr
  intro σ x y
  exact (isPermutationInvariant_iff ρ).mp hρ σ (e.symm ∘ x) (e.symm ∘ y)

/-- Identical tensor factors give a permutation-invariant density operator. -/
theorem isPermutationInvariant_tensorPow (ρ : DensityOp X) :
    IsPermutationInvariant (ρ.tensorPow k) := by
  intro σ
  exact tensorPermutation_conj_piTensorProduct σ (fun _ => ρ.toOp)

/-- The average of all site permutations is the symmetric projector. -/
def symmetricProjector (X : Type*) [DecidableEq X] (k : ℕ) :
    Op (Fin k → X) :=
  (1 / (Nat.factorial k : ℂ)) • ∑ σ : Equiv.Perm (Fin k), permutationRepresentation σ

/-- Left multiplication by a permutation preserves the symmetric projector. -/
theorem permutationRepresentation_mul_symmetricProjector (σ : Equiv.Perm (Fin k)) :
    permutationRepresentation σ * symmetricProjector X k = symmetricProjector X k := by
  simp only [symmetricProjector, Matrix.mul_smul, Finset.mul_sum, permutationRepresentation,
    tensorPermutation_mul]
  congr 1
  exact Fintype.sum_bijective (σ * ·) (Group.mulLeft_bijective σ) _ _ (fun _ => rfl)

/-- The symmetric projector is idempotent. -/
theorem symmetricProjector_mul_self :
    symmetricProjector X k * symmetricProjector X k = symmetricProjector X k := by
  conv_lhs => lhs; unfold symmetricProjector
  rw [Matrix.smul_mul, Finset.sum_mul]
  simp only [permutationRepresentation_mul_symmetricProjector, Finset.sum_const,
    Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [one_div_mul_cancel (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)), one_smul]

omit [Fintype X] in
/-- The symmetric projector is Hermitian. -/
theorem symmetricProjector_isHermitian : (symmetricProjector X k).IsHermitian := by
  change (symmetricProjector X k)ᴴ = symmetricProjector X k
  simp only [symmetricProjector, conjTranspose_smul, conjTranspose_sum,
    permutationRepresentation, tensorPermutation_conjTranspose,
    star_div₀, star_one, star_natCast]
  congr 1
  exact Fintype.sum_bijective (·⁻¹) inv_involutive.bijective _ _ (fun _ => rfl)

omit [Fintype X] in
/-- A Hermitian idempotent is positive: the projector is its own Gram matrix. -/
theorem symmetricProjector_posSemidef [Finite X] : (symmetricProjector X k).PosSemidef := by
  classical
  let := Fintype.ofFinite X
  have h := posSemidef_conjTranspose_mul_self (symmetricProjector X k)
  rwa [symmetricProjector_isHermitian.eq, symmetricProjector_mul_self] at h

/-- The averaged projector fixes precisely the symmetric vectors. -/
theorem symmetricProjector_mulVec_eq_iff (v : (Fin k → X) → ℂ) :
    symmetricProjector X k *ᵥ v = v ↔ v ∈ symmetricSubspace X k := by
  constructor
  · intro h σ x
    have hp : permutationRepresentation σ *ᵥ v = v := by
      conv_lhs => rw [← h]
      rw [Matrix.mulVec_mulVec, permutationRepresentation_mul_symmetricProjector, h]
    simpa only [permutationRepresentation, tensorPermutation_mulVec] using congrFun hp x
  · intro h
    change ∀ σ : Equiv.Perm (Fin k), ∀ x, v (x ∘ σ) = v x at h
    ext x
    simp only [symmetricProjector, Matrix.smul_mulVec, Matrix.sum_mulVec, Pi.smul_apply,
      Finset.sum_apply, permutationRepresentation, tensorPermutation_mulVec]
    simp only [smul_eq_mul]
    simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      nsmul_eq_mul]
    rw [← mul_assoc, one_div_mul_cancel (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)),
      one_mul]

end Quantum.Symmetry
