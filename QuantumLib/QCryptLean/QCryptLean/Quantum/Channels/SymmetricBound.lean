import QCryptLean.Math.LinearAlgebra.Matrix.PositiveTrace
import QCryptLean.Math.LinearAlgebra.Matrix.ProjectionOrder
import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Positivity
import QCryptLean.Math.LinearAlgebra.PartialTrace.Sandwich
import QCryptLean.Quantum.Channels.Ancilla
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Quantum.Channels.SymmetricSupport
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Paired

/-! # Native trace-norm bounds for supported symmetric marginals -/
noncomputable section
namespace Quantum.Channels
open Matrix Quantum.Operators Quantum.Symmetry Quantum.Metrics
open scoped ComplexOrder MatrixOrder Kronecker
variable {X Y R S : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
  [Fintype Y] [Nonempty Y] [Fintype R] [Nonempty R] [Fintype S] [Nonempty S] {k : ℕ}

omit [Nonempty Y] [Nonempty R] [Nonempty S] in
/-- A supported positive marginal is controlled by a purification of the symmetric reference,
with the exact trace of the symmetric projector as coefficient. -/
theorem traceNorm_mapTensorId_le_of_symmetric_support
    (Δ : Operation (Fin k → X) Y) (A : Op ((Fin k → X) × S))
    (hA : A.PosSemidef) (ht : A.trace.re ≤ 1)
    (τ : DensityOp ((Fin k → X) × R)) (hτ : IsDeFinettiPurification τ)
    (hs : symmetricProjector X k * partialTraceRight A = partialTraceRight A) :
    traceNorm (mapTensorId Δ S A) ≤
      (symmetricProjector X k).trace.re * ckrTraceNorm Δ τ := by
  let P := symmetricProjector X k
  have hP : P.PosSemidef := symmetricProjector_posSemidef
  have hr : P.trace = (P.trace.re : ℂ) := by
    apply Complex.ext <;> simp [(Complex.nonneg_iff.mp hP.trace_nonneg).2.symm]
  have hp : 0 < P.trace.re := by
    refine lt_of_le_of_ne (Complex.nonneg_iff.mp hP.trace_nonneg).1 ?_
    intro he
    apply Quantum.Symmetry.symmetricProjector_trace_ne_zero (X := X) (k := k)
    rw [hr, ← he, Complex.ofReal_zero]
  apply traceNorm_mapTensorId_substate_bound Δ A hA τ hτ.isPure _ hp
  rw [hτ.marginal]
  change ((P.trace.re : ℂ) • (P.trace⁻¹ • P) - partialTraceRight A).PosSemidef
  rw [smul_smul, ← hr, mul_inv_cancel₀
    (Quantum.Symmetry.symmetricProjector_trace_ne_zero (X := X) (k := k)), one_smul]
  exact Matrix.le_iff.mp (hA.partialTraceRight.le_projection_of_trace_le_one
    (by rwa [trace_partialTraceRight]) hP.isHermitian symmetricProjector_mul_self hs)

omit [Fintype R] [Nonempty R] [Nonempty X] [Nonempty Y] [Nonempty S] in
/-- Symmetric compression preserves positivity and the trace cap, and operations factoring
through it give the same amplified output. -/
theorem PermutationCovariantSymmetricSupport.exists_supported_input
    (Δ : Operation (Fin k → X) Y) (hΔ : PermutationCovariantSymmetricSupport Δ)
    (A : Op ((Fin k → X) × S)) (hA : A.PosSemidef) (ht : A.trace.re ≤ 1) :
    ∃ B : Op ((Fin k → X) × S), B.PosSemidef ∧ B.trace.re ≤ 1 ∧
      symmetricProjector X k * partialTraceRight B = partialTraceRight B ∧
      mapTensorId Δ S B = mapTensorId Δ S A := by
  classical
  let P := symmetricProjector X k
  let L := P ⊗ₖ (1 : Op S)
  let B := L * A * L
  have hP : P.IsHermitian := symmetricProjector_isHermitian
  have hPP : P * P = P := symmetricProjector_mul_self
  have hL : L.IsHermitian := hP.kronecker isHermitian_one
  have hB : B.PosSemidef := by
    simpa only [hL.eq] using hA.mul_mul_conjTranspose_same L
  have hm : partialTraceRight B = P * partialTraceRight A * P :=
    partialTraceRight_kronecker_one_sandwich P A P
  refine ⟨B, hB, ?_, ?_, ?_⟩
  · have hp : IsStarProjection P := ⟨hPP, hP⟩
    have hn : (1 - P).PosSemidef := Matrix.nonneg_iff_posSemidef.mp hp.one_sub.nonneg
    have hh := (Complex.nonneg_iff.mp (hn.trace_mul_nonneg hA.partialTraceRight)).1
    rw [Matrix.sub_mul, Matrix.one_mul, trace_sub, Complex.sub_re,
      trace_partialTraceRight] at hh
    have he : B.trace = (P * partialTraceRight A).trace := by
      rw [← trace_partialTraceRight B, hm, trace_mul_cycle, hPP]
    rw [he]
    linarith
  · rw [hm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP]
  · ext ⟨y, r⟩ ⟨z, s⟩
    have he : (Matrix.of fun i j => B (i, r) (j, s)) =
        P * (Matrix.of fun i j => A (i, r) (j, s)) * P := by
      ext i j
      simp [B, L, mul_apply, kroneckerMap_apply, Fintype.sum_prod_type,
        Matrix.one_apply, apply_ite]
    change Δ (Matrix.of fun i j => B (i, r) (j, s)) y z = _
    rw [he]
    exact congrFun (congrFun (hΔ.factors_through_sym _) y) z

end Quantum.Channels
