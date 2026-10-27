import QCryptLean.InfoTheory.Postselection.FixedMarginalMeasure
import QCryptLean.InfoTheory.Postselection.FixedMarginalMixed
import QCryptLean.Math.Combinatorics.DeFinettiPrefactor
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Quantum.Channels.Ancilla
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.CovariantBound
import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Quantum.Channels.RecordedConjugation
import QCryptLean.Quantum.DeFinetti.Integral
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Operators.Tensor
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Paired
import QCryptLean.Quantum.Symmetry.SymmetrizeMarginal
import QCryptLean.Quantum.Symmetry.Twirl

/-! # Fixed-marginal postselection for covariant operations -/
noncomputable section
namespace InfoTheory.Postselection
open Matrix Quantum.Operators Quantum.DeFinetti
  Quantum.Symmetry Quantum.Channels Quantum.Metrics
  Math.Combinatorics
open scoped ComplexOrder MatrixOrder
variable {A B O R : Type*} [Fintype A] [Fintype B] [Fintype O] [Fintype R]
  [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B] [Nonempty O] [Nonempty R]

omit [Nonempty O] [Nonempty R] in
/-- A covariant operation on any fixed-marginal input is controlled by the purified Haar mixture. -/
theorem traceNorm_mapTensorId_le_fixedMarginal (σA : DensityOp A) (hσA : σA.toOp.PosDef)
    (e : A ↪ B × (A × B)) (k : ℕ) (Δ : Operation (Fin k → A × B) O)
    (hΔ : PermutationCovariant Δ) (ρ : DensityOp ((Fin k → A × B) × R))
    (hmarg : partialTraceRight (reindex (pairFunctions A B k) (pairFunctions A B k)
      (partialTraceRight ρ.toOp)) = (σA.tensorPow k).toOp) :
    traceNorm (mapTensorId Δ R ρ.toOp) ≤
      (deFinettiPrefactor (Fintype.card A ^ 2 * Fintype.card B ^ 2) k : ℝ) *
        traceNorm (mapTensorId Δ (Fin k → A × B)
          (integralTensorPowerDensity k (fixedMarginalHaarMeasure σA e)).purification.toOp) := by
  classical
  let U : Equiv.Perm (Fin k) → Op (Fin k → A × B) := permutationRepresentation
  let D := recordedConjugation U ρ.toOp
  let σ := symmetrize ρ.partialTraceRight
  have hD : D.PosSemidef := recordedConjugation_posSemidef U ρ.toOp ρ.posSemidef
  have hd : partialTraceRight D = σ.toOp := by
    rw [partialTraceRight_recordedConjugation]
    change _ = twirl permutationUnitary ρ.partialTraceRight.toOp
    rw [twirl_apply]
    rfl
  have hm : partialTraceRight (reindex (pairFunctions A B k) (pairFunctions A B k) σ.toOp) =
      (σA.tensorPow k).toOp := by
    have hmρ : (ρ.partialTraceRight.reindex (pairFunctions A B k)).partialTraceRight =
        σA.tensorPow k := DensityOp.ext hmarg
    change ((symmetrize ρ.partialTraceRight).reindex
      (pairFunctions A B k)).partialTraceRight.toOp = _
    rw [partialTraceRight_reindex_symmetrize, hmρ,
      symmetrize_eq_self _ (isPermutationInvariant_tensorPow σA)]
  have hdom := le_integralTensorPower_fixedMarginalHaarMeasure σA hσA e k σ
    (isPermutationInvariant_symmetrize _) hm
  have hn : traceNorm (mapTensorId Δ (R × Equiv.Perm (Fin k)) D) =
      traceNorm (mapTensorId Δ R ρ.toOp) := by
    rw [traceNorm_mapTensorId_recordedConjugation]
    simp only [U, traceNorm_mapTensorId_perm_conj Δ hΔ, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]
  rw [← hn]
  apply traceNorm_mapTensorId_substate_bound Δ D hD _ (DensityOp.isPure_purification _)
    _ (by exact_mod_cast deFinettiPrefactor_pos _ _)
  rw [DensityOp.partialTraceRight_purification, hd]
  simpa only [Complex.ofReal_natCast, integralTensorPowerDensity] using Matrix.le_iff.mp hdom

end InfoTheory.Postselection
