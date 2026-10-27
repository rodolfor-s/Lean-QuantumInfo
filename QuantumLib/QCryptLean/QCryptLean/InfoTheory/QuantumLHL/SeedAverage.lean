import QCryptLean.InfoTheory.QuantumLHL.RandomnessExtractor
import QCryptLean.InfoTheory.QuantumLHL.Extractor
import QCryptLean.InfoTheory.SmoothMinEntropy.CQOperations
import QCryptLean.InfoTheory.SmoothMinEntropy.CQState
import QCryptLean.Math.LinearAlgebra.BlockDiagonalPSD
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Channels.PartialTrace
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.Contractivity
import QCryptLean.Quantum.Operators.Basic

/-! # Forgetting a public seed contracts generalized trace distance -/
noncomputable section
namespace InfoTheory.QuantumLHL.SeedKey
open Matrix Quantum.Operators Quantum.Channels Quantum.Metrics
open InfoTheory.SmoothMinEntropy
variable {S C Z Q : Type*} [Fintype S] [Nonempty S] [Fintype C]
  [Fintype Z] [DecidableEq Z] [Nonempty Z] [Fintype Q]

open Classical in
/-- Discarding the public seed cannot increase the hashing distance to a uniform key. -/
theorem extractorDistance_le_outputDistance (H : HashFamily S C Z) (ρ : CQState C Q)
    (σ : SubDensityOp Q) :
    traceDistanceGen (extractorOutputState H ρ).toJointDensity.toOp
      (uniformCQState (C := Z) σ).toJointDensity.toOp ≤
    traceDistanceGen (output H ρ).toJointDensity.toOp
      (uniformCQState (C := S × Z) σ).toJointDensity.toOp := by
  classical
  let e : Q × (S × Z) ≃ (Q × Z) × S :=
    { toFun := fun p => ((p.1, p.2.2), p.2.1)
      invFun := fun p => (p.1.1, p.2, p.1.2)
      left_inv := by rintro ⟨q, s, z⟩; rfl
      right_inv := by rintro ⟨⟨q, z⟩, s⟩; rfl }
  have ho : partialTraceRight (reindex e e (output H ρ).toJointDensity.toOp) =
      (extractorOutputState H ρ).toJointDensity.toOp := by
    ext ⟨q, z⟩ ⟨r, w⟩
    by_cases hz : z = w
    · subst w
      simp only [partialTraceRight_apply, reindex_apply, submatrix_apply, e,
        Equiv.coe_fn_symm_mk, CQState.toJointDensity, CQState.toJointOp,
        Matrix.blockDiagonal_apply, output, extractorOutputState, CQState.ofBlocks,
        weightedOp, extractorWeightedOp, ite_true]
      simp only [Matrix.smul_apply, Matrix.sum_apply]
      rw [Finset.smul_sum]
    · simp [partialTraceRight_apply, reindex_apply, e, CQState.toJointDensity,
        CQState.toJointOp, Matrix.blockDiagonal_apply, hz]
  have hu : partialTraceRight (reindex e e
      (uniformCQState (C := S × Z) σ).toJointDensity.toOp) =
        (uniformCQState (C := Z) σ).toJointDensity.toOp := by
    ext ⟨q, z⟩ ⟨r, w⟩
    by_cases hz : z = w
    · subst w
      have hs : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      have hz : (Fintype.card Z : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      simp [partialTraceRight_apply, reindex_apply, e, CQState.toJointDensity,
        CQState.toJointOp, Matrix.blockDiagonal_apply, uniformCQState, CQState.ofBlocks,
        Matrix.smul_apply, Fintype.card_prod, nsmul_eq_mul, smul_eq_mul]
      field_simp
    · simp [partialTraceRight_apply, reindex_apply, e, CQState.toJointDensity,
        CQState.toJointOp, Matrix.blockDiagonal_apply, hz]
  have hh := traceDistanceGen_apply_le (partialTraceRightLinearMap (S := ℂ))
    (isChannel_partialTraceRight (X := Q × Z) (R := S))
    (reindex e e (output H ρ).toJointDensity.toOp)
    (reindex e e (uniformCQState (C := S × Z) σ).toJointDensity.toOp)
  change traceDistanceGen (partialTraceRight _) (partialTraceRight _) ≤ _ at hh
  rw [ho, hu] at hh
  simpa only [traceDistanceGen, traceDistance_reindex, trace_reindex_self] using hh

end InfoTheory.QuantumLHL.SeedKey
