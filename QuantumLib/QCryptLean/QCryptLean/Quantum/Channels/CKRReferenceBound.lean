import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Channels.CKRReference
import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Quantum.Channels.PostselectionBound
import QCryptLean.Quantum.DeFinetti.CKRMixture
import QCryptLean.Quantum.DeFinetti.FullRank
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Algebra
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.PurificationStabilizer
import QCryptLean.Quantum.Operators.RankPurification
import QCryptLean.Quantum.Operators.ReferenceTransport
import QCryptLean.Quantum.Operators.ReferenceTransportBounds
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.CKRCentral
import QCryptLean.Quantum.Symmetry.Paired
import QCryptLean.Quantum.Symmetry.Purification

/-! # CKRReference Bound -/


noncomputable section

namespace Quantum.Channels

open Matrix Quantum.Operators Quantum.Symmetry
open scoped ComplexOrder MatrixOrder Kronecker

variable {X R : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype R]
variable {d r k : ℕ}

/-- The CKR marginal is strictly positive. -/
theorem posDef_ckrDeFinettiState :
    (Quantum.Symmetry.ckrDeFinettiState X k).toOp.PosDef := by
  let x : X := Classical.choice ‹Nonempty X›
  rw [← Quantum.DeFinetti.integralTensorPower_ckrMixtureMeasure x k]
  exact Quantum.DeFinetti.posDef_integralTensorPower_of_isOpenPosMeasure
    _ (Quantum.DeFinetti.isOpenPosMeasure_ckrMixtureMeasure x) k

/-- Strict positivity gives the full function-register rank. -/
theorem rank_ckrDeFinettiState :
    (Quantum.Symmetry.ckrDeFinettiState X k).toOp.rank = Fintype.card X ^ k := by
  simpa using Matrix.rank_of_isUnit _ (posDef_ckrDeFinettiState (X := X)).isUnit

/-- Every CKR purification needs a reference at least as large as the function register. -/
theorem IsCKRDeFinettiPurification.card_le
    (τ : DensityOp ((Fin k → X) × R)) (hτ : IsCKRDeFinettiPurification τ) :
    Fintype.card X ^ k ≤ Fintype.card R := by
  obtain ⟨v, hv⟩ := DensityOp.IsPure.exists_normKet τ hτ.isPure
  let V : Matrix (Fin k → X) R ℂ := fun i j => v.vec (i, j)
  have he : (Quantum.Symmetry.ckrDeFinettiState X k).toOp = V * Vᴴ := by
    rw [← hτ.marginal, ← hv]
    exact Ket.partialTraceRight_vectorize V
  rw [← rank_ckrDeFinettiState (X := X) (k := k), he]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

/-- The canonical CKR purification is paired-permutation invariant. -/
theorem isPairedPermInvariant_ckrDeFinettiCanonicalPurification :
    IsPairedPermInvariant (ckrDeFinettiCanonicalPurification X k) := by
  exact isPairedPermInvariant_purification _
    (Quantum.Symmetry.isPermutationInvariant_ckrDeFinettiState X k)

/-- Square-ancilla CKR purifications differ by a reference unitary. -/
theorem ckrDeFinetti_squareAncilla_unitary_transport
    (τ : DensityOp ((Fin k → X) × (Fin k → X))) (hτ : IsCKRDeFinettiPurification τ) :
    ∃ U : UnitaryOp (Fin k → X), τ.toOp =
      rightTensorUnitaryConj U (ckrDeFinettiCanonicalPurification X k).toOp :=
  (Quantum.Symmetry.ckrDeFinettiState X k).exists_reference_unitary
    τ hτ.isPure hτ.marginal

/-- Paired-invariant CKR purifications have the CKR reference as their other marginal too. -/
theorem ckrDeFinetti_partialTraceLeft_of_pairedPermInvariant
    (τ : DensityOp ((Fin k → X) × (Fin k → X))) (hτ : IsCKRDeFinettiPurification τ)
    (hinv : IsPairedPermInvariant τ) :
    τ.partialTraceLeft = Quantum.Symmetry.ckrDeFinettiState X k := by
  classical
  let ρ := Quantum.Symmetry.ckrDeFinettiState X k
  obtain ⟨W, hW⟩ := ckrDeFinetti_squareAncilla_unitary_transport τ hτ
  let S := CFC.sqrt ρ.toOp
  have hS : IsUnit S := (CFC.isUnit_sqrt_iff ρ.toOp ρ.posSemidef.nonneg).mpr
    (posDef_ckrDeFinettiState (X := X) (k := k)).isUnit
  have hp : τ.toOp = (Ket.vectorize (S * W.valᵀ)).projector := by
    rw [hW]
    change (1 ⊗ₖ W.val) * (Ket.vectorize S).projector * (1 ⊗ₖ W.val)ᴴ = _
    have hv : (1 ⊗ₖ W.val) *ᵥ (Ket.vectorize S).vec =
        (Ket.vectorize (S * W.valᵀ)).vec := by
      change (1 ⊗ₖ W.val) *ᵥ Matrix.vec Sᵀ = Matrix.vec (S * W.valᵀ)ᵀ
      rw [kronecker_mulVec_vec, transpose_one, Matrix.mul_one, transpose_mul, transpose_transpose]
    change (1 ⊗ₖ W.val) * vecMulVec (Ket.vectorize S).vec (star (Ket.vectorize S).vec) *
      (1 ⊗ₖ W.val)ᴴ = vecMulVec _ (star _)
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec, hv]
  have hc (σ : Equiv.Perm (Fin k)) : Commute (permutationRepresentation σ) W.valᵀ := by
    have hρ : Commute (permutationRepresentation σ) ρ.toOp := by
      have h := congrArg (· * permutationRepresentation (X := X) σ)
        ((Quantum.Symmetry.isPermutationInvariant_ckrDeFinettiState X k) σ)
      change permutationRepresentation σ * ρ.toOp = ρ.toOp * permutationRepresentation σ
      simpa only [Matrix.mul_assoc, (tensorPermutation_unitary σ).1,
        Matrix.mul_one] using h
    have hs : Commute (permutationRepresentation σ) S := by
      exact (hρ.symm.cfcₙ_nnreal NNReal.sqrt).symm
    have ho : (permutationRepresentation (X := X) σ)ᵀ * permutationRepresentation σ = 1 := by
      change (tensorPermutation (X := X) (R := ℂ) σ)ᵀ * tensorPermutation σ = 1
      rw [tensorPermutation_transpose, tensorPermutation_mul, inv_mul_cancel, tensorPermutation_one]
    apply commute_transpose_of_paired_projector_fixed _ S W.val hS Unitary.isUnit_coe hs ho
      (trace_permutationRepresentation_ne_zero σ)
    rw [← hp]
    exact hinv σ
  have hm := commute_ckrDeFinettiState_of_commute W.valᵀ (fun σ => (hc σ).symm)
  have hm' : Commute W.val ρ.toOpᵀ := by
    have h := congrArg Matrix.transpose hm.eq
    change W.val * ρ.toOpᵀ = ρ.toOpᵀ * W.val
    simpa only [transpose_mul, transpose_transpose] using h.symm
  apply DensityOp.ext
  change partialTraceLeft τ.toOp = ρ.toOp
  rw [hW]
  change partialTraceLeft (rightTensorUnitaryConj W ρ.purification.toOp) = ρ.toOp
  rw [partialTraceLeft_rightTensorUnitaryConj_purification, hm'.eq, Matrix.mul_assoc,
    show W.val * W.valᴴ = 1 from W.property.2, Matrix.mul_one]
  exact transpose_ckrDeFinettiState

end Quantum.Channels
