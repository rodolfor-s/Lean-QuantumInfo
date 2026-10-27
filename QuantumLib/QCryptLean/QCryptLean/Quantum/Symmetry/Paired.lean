import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Symmetry.Basic

/-!
# Paired symmetric registers and canonical reference states

Pointwise pairing identifies functions into a product with pairs of functions.
The paired reference is the normalized symmetric projector under this structural
identification. Its marginal is the mixed CKR reference, distinct from the
single-register symmetric projector. Positivity uses the PSD predicate directly.
-/

noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators
open scoped ComplexOrder Kronecker

variable {X Y : Type*} [Fintype X] [DecidableEq X] {k : ℕ}

/-- Group the first and second components of a function into separate registers. -/
def pairFunctions (X Y : Type*) (k : ℕ) :
    (Fin k → X × Y) ≃ (Fin k → X) × (Fin k → Y) :=
  Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => X) (fun _ => Y)

omit [Fintype X] in
/-- Pairing intertwines the site action with the simultaneous action on both registers. -/
theorem reindex_permutationRepresentation_pair [DecidableEq Y]
    (σ : Equiv.Perm (Fin k)) :
    Matrix.reindex (pairFunctions X Y k) (pairFunctions X Y k)
      (permutationRepresentation σ) =
    permutationRepresentation (X := X) σ ⊗ₖ permutationRepresentation (X := Y) σ := by
  ext x y
  simp only [reindex_apply, submatrix_apply, permutationRepresentation, tensorPermutation,
    of_apply, kroneckerMap_apply, pairFunctions]
  have h : (fun i => (x.1 i, x.2 i)) = (fun i => (y.1 i, y.2 i)) ∘ σ.symm ↔
      x.1 = y.1 ∘ σ.symm ∧ x.2 = y.2 ∘ σ.symm := by
    simp only [funext_iff, Function.comp_apply, Prod.mk.injEq, forall_and]
  change (if (fun i => (x.1 i, x.2 i)) = (fun i => (y.1 i, y.2 i)) ∘ σ.symm
    then (1 : ℂ) else 0) = _
  simp only [h, ite_and]
  split_ifs <;> simp

/-- Invariance under the simultaneous site action on the two tensor registers. -/
def IsPairedPermInvariant (ρ : DensityOp ((Fin k → X) × (Fin k → X))) : Prop :=
  ∀ σ : Equiv.Perm (Fin k),
    (permutationRepresentation σ ⊗ₖ permutationRepresentation σ) * ρ.toOp *
      (permutationRepresentation σ ⊗ₖ permutationRepresentation σ)ᴴ = ρ.toOp

/-- Invariance under permutations of the signal register alone. -/
def IsSignalPermInvariant {R : Type*} [Fintype R] [DecidableEq R]
    (ρ : DensityOp ((Fin k → X) × R)) : Prop :=
  ∀ σ : Equiv.Perm (Fin k),
    (permutationRepresentation σ ⊗ₖ (1 : Op R)) * ρ.toOp *
      (permutationRepresentation σ ⊗ₖ (1 : Op R))ᴴ = ρ.toOp

/-- Simultaneous site symmetry for two possibly different local registers. -/
def pairedProjectorOf (X Y : Type*) [DecidableEq X] [DecidableEq Y] (n : ℕ) :
    Op ((Fin n → X) × (Fin n → Y)) :=
  reindex (pairFunctions X Y n) (pairFunctions X Y n) (symmetricProjector (X × Y) n)

/-- The unequal-register projector is the simultaneous permutation average. -/
theorem pairedProjectorOf_eq_sum (X Y : Type*) [DecidableEq X] [DecidableEq Y] (n : ℕ) :
    pairedProjectorOf X Y n = (1 / (n.factorial : ℂ)) •
      ∑ σ : Equiv.Perm (Fin n),
        permutationRepresentation (X := X) σ ⊗ₖ permutationRepresentation (X := Y) σ := by
  unfold pairedProjectorOf symmetricProjector
  ext i j
  simp only [reindex_apply, submatrix_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  exact congrFun (congrFun (reindex_permutationRepresentation_pair (X := X) (Y := Y) σ) i) j

/-- The unequal-register projector is positive, including on empty local spaces. -/
theorem pairedProjectorOf_posSemidef (X Y : Type*) [Finite X] [Finite Y]
    [DecidableEq X] [DecidableEq Y] (n : ℕ) : (pairedProjectorOf X Y n).PosSemidef :=
  symmetricProjector_posSemidef.submatrix _

/-- The regrouped symmetric projector is idempotent. -/
theorem pairedProjectorOf_mul_self [Fintype Y] [DecidableEq Y] :
    pairedProjectorOf X Y k * pairedProjectorOf X Y k = pairedProjectorOf X Y k := by
  change (reindexAlgEquiv ℂ ℂ (pairFunctions X Y k)) _ *
    (reindexAlgEquiv ℂ ℂ (pairFunctions X Y k)) _ = (reindexAlgEquiv ℂ ℂ (pairFunctions X Y k)) _
  rw [← map_mul, symmetricProjector_mul_self]

/-- The projector for simultaneous permutations on two identical tensor registers. -/
def pairedProjector (X : Type*) [DecidableEq X] (k : ℕ) :
    Op ((Fin k → X) × (Fin k → X)) :=
  Matrix.reindex (pairFunctions X X k) (pairFunctions X X k) (symmetricProjector (X × X) k)

omit [Fintype X] in
/-- The paired projector is the uniform simultaneous-permutation average. -/
theorem pairedProjector_eq_sum :
    pairedProjector X k = (1 / (Nat.factorial k : ℂ)) • ∑ σ : Equiv.Perm (Fin k),
      permutationRepresentation (X := X) σ ⊗ₖ permutationRepresentation (X := X) σ :=
  pairedProjectorOf_eq_sum X X k

omit [Fintype X] in
/-- The paired projector is positive. -/
theorem pairedProjector_posSemidef [Finite X] : (pairedProjector X k).PosSemidef :=
  pairedProjectorOf_posSemidef X X k

omit [Fintype X] in
/-- A constant basis function has diagonal entry one in the symmetric projector. -/
theorem symmetricProjector_apply_const (x : X) :
    symmetricProjector X k (fun _ => x) (fun _ => x) = 1 := by
  simp [symmetricProjector, Matrix.smul_apply, Matrix.sum_apply, permutationRepresentation,
    tensorPermutation, Function.comp_def, Fintype.card_perm, Fintype.card_fin,
    Nat.factorial_ne_zero]

/-- On a nonempty local register the symmetric projector has nonzero trace. -/
theorem symmetricProjector_trace_ne_zero [Nonempty X] : (symmetricProjector X k).trace ≠ 0 := by
  intro h
  have hz := symmetricProjector_posSemidef.trace_eq_zero_iff.mp h
  have he := symmetricProjector_apply_const (k := k) (Classical.choice ‹Nonempty X›)
  rw [hz] at he
  exact zero_ne_one he

/-- The normalized symmetric projector is the ordinary de Finetti reference. -/
def deFinettiState (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] (k : ℕ) :
    DensityOp (Fin k → X) where
  toOp := (symmetricProjector X k).trace⁻¹ • symmetricProjector X k
  posSemidef := symmetricProjector_posSemidef.smul
    (inv_nonneg.mpr symmetricProjector_posSemidef.trace_nonneg)
  trace_one := by
    rw [trace_smul, smul_eq_mul, inv_mul_cancel₀ symmetricProjector_trace_ne_zero]

/-- The normalized paired projector, with an intrinsic definition also at zero sites. -/
def pairedDeFinettiState (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] (k : ℕ) :
    DensityOp ((Fin k → X) × (Fin k → X)) :=
  (deFinettiState (X × X) k).reindex (pairFunctions X X k)

/-- The mixed CKR reference is the system marginal of the paired reference. -/
def ckrDeFinettiState (X : Type*) [Fintype X] [DecidableEq X] [Nonempty X] (k : ℕ) :
    DensityOp (Fin k → X) := (pairedDeFinettiState X k).partialTraceRight

/-- Entries of the CKR reference are sums over the second word register. -/
private theorem ckrDeFinettiState_apply (X : Type*) [Fintype X] [DecidableEq X]
    [Nonempty X] (k : ℕ) (a b : Fin k → X) :
    (ckrDeFinettiState X k).toOp a b =
      ∑ r : Fin k → X, (symmetricProjector (X × X) k).trace⁻¹ *
        symmetricProjector (X × X) k (fun i => (a i, r i)) (fun i => (b i, r i)) := rfl

/-- The marginal of the paired symmetric reference is permutation invariant. -/
theorem isPermutationInvariant_ckrDeFinettiState (X : Type*) [Fintype X] [DecidableEq X]
    [Nonempty X] (k : ℕ) : IsPermutationInvariant (ckrDeFinettiState X k) := by
  have hi (σ : Equiv.Perm (Fin k)) (a b : Fin k → X × X) :
      symmetricProjector (X × X) k (a ∘ σ) (b ∘ σ) = symmetricProjector (X × X) k a b := by
    have hl := permutationRepresentation_mul_symmetricProjector (X := X × X) σ
    have hr : symmetricProjector (X × X) k *
        (permutationRepresentation (X := X × X) σ)ᴴ = symmetricProjector (X × X) k := by
      simpa only [conjTranspose_mul,
        (symmetricProjector_isHermitian (X := X × X) (k := k)).eq] using
          congrArg Matrix.conjTranspose hl
    have hh : permutationRepresentation σ * symmetricProjector (X × X) k *
        (permutationRepresentation σ)ᴴ = symmetricProjector (X × X) k := by rw [hl, hr]
    simpa only [tensorPermutation_conj_apply] using congrFun (congrFun hh a) b
  apply (isPermutationInvariant_iff _).mpr
  intro σ x y
  rw [ckrDeFinettiState_apply, ckrDeFinettiState_apply]
  symm
  apply Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl X))
  intro r
  exact congrArg ((symmetricProjector (X × X) k).trace⁻¹ * ·)
    (hi σ (fun i => (x i, r i)) (fun i => (y i, r i))).symm

end Quantum.Symmetry
