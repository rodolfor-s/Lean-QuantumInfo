import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.Probability.MatrixHaarAverage
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.BipartiteCommutant
import QCryptLean.Quantum.Symmetry.EmbeddedEntanglement
import QCryptLean.Quantum.Symmetry.EmbeddedEntanglementAlgebra
import QCryptLean.Quantum.Symmetry.Paired
import QCryptLean.Quantum.Symmetry.SymmetricMarginal
import QCryptLean.Quantum.Symmetry.TensorUnitaryCommutant

/-! # Native Schur--Weyl flattening of the embedded entangled Haar average

The inverse marginal of the symmetric projector is the flattening operator.
The proof identifies trace pairings on the tensor-permutation commutant.
-/
noncomputable section
namespace Quantum.Symmetry
open Matrix Quantum.Operators
open scoped Kronecker ComplexOrder
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [Nonempty X] {k : ℕ}

/-- The entangled Haar average equals the symmetric projector multiplied by its inverse marginal. -/
theorem unitaryHaarAverage_embeddedMaxEntangled_eq (e : X ↪ Y) :
    unitaryHaarAverage (tensorUnitaryRepresentation (Fin k → X) Y k)
        (embeddedMaxEntangled (e.arrowCongrRight : (Fin k → X) ↪ (Fin k → Y))).projector =
      ((partialTraceRight (pairedProjectorOf X Y k))⁻¹ ⊗ₖ (1 : Op (Fin k → Y))) *
        pairedProjectorOf X Y k := by
  let U := tensorUnitaryRepresentation (Fin k → X) Y k
  let Θ := (embeddedMaxEntangled (e.arrowCongrRight : (Fin k → X) ↪ (Fin k → Y))).projector
  let P := pairedProjectorOf X Y k
  let Ω := partialTraceRight P
  let κ := Ω⁻¹
  let T := unitaryHaarAverage U Θ
  let F := (κ ⊗ₖ (1 : Op (Fin k → Y))) * P
  have hΩ : Ω.PosDef := posDef_partialTraceRight_pairedProjectorOf e
  have hκΩ : κ * Ω = 1 :=
    Matrix.nonsing_inv_mul Ω ((Matrix.isUnit_iff_isUnit_det Ω).mp hΩ.isUnit)
  have hκ (σ : Equiv.Perm (Fin k)) : Commute κ (permutationRepresentation (X := X) σ) := by
    let := Classical.choice hΩ.isUnit.nonempty_invertible
    have h := (permutationRepresentation_commute_partialTraceRight_pairedProjectorOf
      (X := X) (Y := Y) σ).invOf_right
    simpa only [Matrix.invOf_eq_nonsing_inv] using h.symm
  have hF (D : Op (Fin k → X)) (σ : Equiv.Perm (Fin k)) :
      ((D ⊗ₖ permutationRepresentation (X := Y) σ) * F).trace =
        (D * permutationRepresentation (X := X) σ⁻¹).trace := by
    change ((D ⊗ₖ permutationRepresentation (X := Y) σ) *
      ((κ ⊗ₖ (1 : Op (Fin k → Y))) * P)).trace = _
    rw [← Matrix.mul_assoc, ← mul_kronecker_mul, Matrix.mul_one,
      ← trace_partialTraceRight, partialTraceRight_kronecker_permutation_mul_pairedProjectorOf]
    change (D * κ * permutationRepresentation (X := X) σ⁻¹ * Ω).trace = _
    rw [Matrix.mul_assoc D κ, (hκ σ⁻¹).eq, ← Matrix.mul_assoc D,
      Matrix.mul_assoc, hκΩ, Matrix.mul_one]
  have hT (D : Op (Fin k → X)) (σ : Equiv.Perm (Fin k)) :
      ((D ⊗ₖ permutationRepresentation (X := Y) σ) * T).trace =
        (D * permutationRepresentation (X := X) σ⁻¹).trace := by
    have h := trace_mul_unitaryHaarAverage U
      (continuous_tensorUnitaryRepresentation _ _ _) Θ (D ⊗ₖ permutationRepresentation σ)
      (fun g => (tensorUnitaryRepresentation_commute_generator D σ g).symm)
    rw [trace_mul_comm _ Θ, trace_embeddedMaxEntangled_mul_tensor_permutation] at h
    exact h
  have hpair (D : Op (Fin k → X)) (σ : Equiv.Perm (Fin k)) :
      ((D ⊗ₖ permutationRepresentation (X := Y) σ) * (T - F)).trace = 0 := by
    rw [Matrix.mul_sub, trace_sub, hT, hF, sub_self]
  have hcomm (g : unitaryGroup Y ℂ) : Commute (U g).val (T - F) := by
    have ht := commute_unitaryHaarAverage U (continuous_tensorUnitaryRepresentation _ _ _) Θ g
    have hc : Commute (U g).val (κ ⊗ₖ (1 : Op (Fin k → Y))) := by
      change ((1 : Op (Fin k → X)) ⊗ₖ Op.tensorPow g.val k) * _ =
        _ * ((1 : Op (Fin k → X)) ⊗ₖ Op.tensorPow g.val k)
      rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul, Matrix.mul_one]
    exact ht.sub_right (hc.mul_right (tensorUnitaryRepresentation_commute_pairedProjectorOf g))
  have hspan := mem_tensorPermSpan_of_commute_unitary (T - F) hcomm
  have horth (S : Op ((Fin k → X) × (Fin k → Y)))
      (hS : S ∈ Submodule.span ℂ {Z | ∃ (D : Op (Fin k → X)) (σ : Equiv.Perm (Fin k)),
        Z = D ⊗ₖ permutationRepresentation (X := Y) σ}) : (Sᴴ * (T - F)).trace = 0 := by
    induction hS using Submodule.span_induction with
    | mem S hS =>
        obtain ⟨D, σ, rfl⟩ := hS
        rw [conjTranspose_kronecker, permutationRepresentation, tensorPermutation_conjTranspose]
        exact hpair Dᴴ σ⁻¹
    | zero => simp
    | add S₁ S₂ _ _ h₁ h₂ =>
        rw [conjTranspose_add, Matrix.add_mul, trace_add, h₁, h₂, add_zero]
    | smul c S _ h => rw [conjTranspose_smul, Matrix.smul_mul, trace_smul, h, smul_zero]
  exact sub_eq_zero.mp (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (horth _ hspan))

end Quantum.Symmetry
