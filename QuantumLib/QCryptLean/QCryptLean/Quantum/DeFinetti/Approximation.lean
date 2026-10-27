import QCryptLean.Quantum.DeFinetti.PureState.CoherentState
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.CKMRBound
import QCryptLean.Quantum.DeFinetti.CKMRMeasure
import QCryptLean.Quantum.DeFinetti.MarginalMixture
import QCryptLean.Math.LinearAlgebra.Matrix.Reindex
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.PartialTrace
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Dimension
import QCryptLean.Quantum.Symmetry.Paired
import QCryptLean.Quantum.Symmetry.Purification

/-! # Theorem -/


noncomputable section

namespace Quantum.DeFinetti

open Matrix Quantum.Operators Quantum.Symmetry Quantum.Metrics

variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n : ℕ} [NeZero n]

/-- The symmetric-support CKMR bound has the smaller local-dimension constant.
The input can be any density operator supported on the symmetric subspace. -/
theorem pure_state_deFinetti_symmetric (ρ : DensityOp (Fin n → X))
    (hρ : symmetricProjector X n * ρ.toOp * symmetricProjector X n = ρ.toOp) :
    ∃ μ : DensityMeasure X, ∀ (k : ℕ) [NeZero k] (hk : k ≤ n),
      traceDistance (partialTraceLast hk ρ).toOp (integralTensorPower k μ) ≤
        2 * (Fintype.card X : ℝ) * k / n := by
  classical
  let x : X := Classical.choice ‹Nonempty X›
  refine ⟨coherentMeasure x ρ hρ, fun k _ hk => ?_⟩
  apply (traceDistance_coherentMeasure_le x ρ hρ hk).trans
  have h := Quantum.DeFinetti.PureState.dim_ratio_bound (Fintype.card X) n k
    Fintype.card_pos (Nat.pos_of_ne_zero (NeZero.ne n)) hk
  calc
    _ ≤ 2 * ((Fintype.card X : ℝ) * k / n) := by linarith
    _ = 2 * (Fintype.card X : ℝ) * k / n := by ring

/-- CKMR II.7 on a natural local register, with one measure for all marginal sizes.
The native marginal argument uses the symmetric-support theorem. -/
theorem quantum_deFinetti (ρ : DensityOp (Fin n → X)) (hρ : IsPermutationInvariant ρ) :
    ∃ μ : DensityMeasure X, ∀ (k : ℕ) [NeZero k] (hk : k ≤ n),
      traceDistance (partialTraceLast hk ρ).toOp (integralTensorPower k μ) ≤
        2 * k * (Fintype.card X : ℝ) ^ 2 / n := by
  classical
  let e := pairFunctions X X n
  let Ψ := ρ.purification.reindex e.symm
  have hΨ : symmetricProjector (X × X) n * Ψ.toOp * symmetricProjector (X × X) n =
      Ψ.toOp := by
    apply (Matrix.reindex e e).injective
    have he : Matrix.reindex e e Ψ.toOp = ρ.purification.toOp := by
      ext i j
      simp [Ψ, DensityOp.reindex, Matrix.reindex_apply]
    simpa only [Matrix.reindex_mul, he, e, pairedProjector] using
      purification_in_paired_symmetric_subspace ρ hρ
  obtain ⟨ν, hν⟩ := pure_state_deFinetti_symmetric Ψ hΨ
  refine ⟨ν.partialTraceRight, fun k _ hk => ?_⟩
  have hm : (Ψ.reindex e).partialTraceRight = ρ := by
    have he : Ψ.reindex e = ρ.purification := by
      apply DensityOp.ext
      ext i j
      simp [Ψ, DensityOp.reindex, Matrix.reindex_apply]
    rw [he, ρ.partialTraceRight_purification]
  have hcomm := partialTraceLast_partialTraceRight hk Ψ
  rw [hm] at hcomm
  rw [hcomm, integralTensorPower_partialTraceRight]
  apply le_trans (traceDistance_partialTraceRight_le _ _)
  change traceDistance (Matrix.reindex (pairFunctions X X k) (pairFunctions X X k)
    (partialTraceLast hk Ψ).toOp) (Matrix.reindex (pairFunctions X X k) (pairFunctions X X k)
    (integralTensorPower k ν)) ≤ _
  rw [Quantum.Metrics.traceDistance_reindex]
  have h := hν k hk
  simpa only [Fintype.card_prod, Nat.cast_mul, pow_two, mul_assoc, mul_comm,
    mul_left_comm] using h


end Quantum.DeFinetti
