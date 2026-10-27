import QCryptLean.Math.LinearAlgebra.Matrix.ProjectionOrder
import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Positivity
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.EmbeddedEntanglement
import QCryptLean.Quantum.Symmetry.Paired

/-! # The positive-definite marginal of a bipartite symmetric projector -/
noncomputable section
namespace Quantum.Symmetry
open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder Kronecker
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] {k : ℕ}

omit [Fintype X] in
/-- The symmetric marginal is the character-weighted permutation sum. -/
theorem partialTraceRight_pairedProjectorOf :
    partialTraceRight (pairedProjectorOf X Y k) =
      (1 / (Nat.factorial k : ℂ)) • ∑ σ : Equiv.Perm (Fin k),
        (permutationRepresentation (X := Y) σ).trace • permutationRepresentation (X := X) σ := by
  rw [pairedProjectorOf_eq_sum, partialTraceRight_smul, partialTraceRight_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  exact partialTraceRight_kronecker _ _

omit [Fintype X] in
/-- An embedding witnesses strict positivity of the symmetric marginal. -/
theorem posDef_partialTraceRight_pairedProjectorOf [Finite X] [Nonempty X] (e : X ↪ Y) :
    (partialTraceRight (pairedProjectorOf X Y k)).PosDef := by
  let := Fintype.ofFinite X
  let v := embeddedMaxEntangled (e.arrowCongrRight : (Fin k → X) ↪ (Fin k → Y))
  let c : ℂ := (Fintype.card (Fin k → X) : ℂ)⁻¹
  have hc : 0 < c := inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hcn : (Fintype.card (Fin k → X) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have ht : v.projector.trace = (Fintype.card (Fin k → X) : ℂ) := by
    rw [← trace_partialTraceRight, partialTraceRight_embeddedMaxEntangled, trace_one]
  have hs : pairedProjectorOf X Y k * (c • v.projector) = c • v.projector := by
    rw [Matrix.mul_smul, pairedProjectorOf_mul_embeddedMaxEntangled]
  have htrace : (c • v.projector).trace.re ≤ 1 := by
    rw [trace_smul, ht, smul_eq_mul, inv_mul_cancel₀ hcn]
    norm_num
  have hp := Matrix.le_iff.mp ((v.posSemidef_projector.smul hc.le).le_projection_of_trace_le_one
    htrace (pairedProjectorOf_posSemidef X Y k).isHermitian
    pairedProjectorOf_mul_self hs)
  have hm := hp.partialTraceRight
  rw [partialTraceRight_sub, partialTraceRight_smul, partialTraceRight_embeddedMaxEntangled] at hm
  have hone := (Matrix.PosDef.one (n := Fin k → X) (R := ℂ)).smul hc
  have h := hone.add_posSemidef hm
  simpa only [add_sub_cancel] using h

/-- Every site permutation commutes with the symmetric marginal. -/
theorem permutationRepresentation_commute_partialTraceRight_pairedProjectorOf
    (σ : Equiv.Perm (Fin k)) :
    Commute (permutationRepresentation (X := X) σ)
      (partialTraceRight (pairedProjectorOf X Y k)) := by
  have htrace (τ : Equiv.Perm (Fin k)) :
      (permutationRepresentation (X := Y) (σ * τ * σ⁻¹)).trace =
        (permutationRepresentation (X := Y) τ).trace := by
    simp only [permutationRepresentation, ← tensorPermutation_mul]
    rw [trace_mul_cycle, tensorPermutation_mul, inv_mul_cancel, tensorPermutation_one,
      Matrix.one_mul]
  have hconj : permutationRepresentation (X := X) σ *
      partialTraceRight (pairedProjectorOf X Y k) *
        (permutationRepresentation (X := X) σ)ᴴ =
      partialTraceRight (pairedProjectorOf X Y k) := by
    rw [partialTraceRight_pairedProjectorOf, Matrix.mul_smul, Matrix.smul_mul,
      Finset.mul_sum, Finset.sum_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, permutationRepresentation,
      tensorPermutation_conjTranspose, tensorPermutation_mul]
    congr 1
    exact Fintype.sum_bijective (fun τ : Equiv.Perm (Fin k) => σ * τ * σ⁻¹)
      ((Group.mulRight_bijective σ⁻¹).comp (Group.mulLeft_bijective σ)) _ _
      (fun τ => by rw [htrace])
  have h := congrArg (· * permutationRepresentation (X := X) σ) hconj
  change permutationRepresentation σ * partialTraceRight (pairedProjectorOf X Y k) = _
  simpa only [Matrix.mul_assoc, permutationRepresentation,
    (tensorPermutation_unitary (X := X) (R := ℂ) σ).1, Matrix.mul_one] using h

end Quantum.Symmetry
