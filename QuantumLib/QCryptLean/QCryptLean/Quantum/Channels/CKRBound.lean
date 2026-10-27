import QCryptLean.Math.LinearAlgebra.Matrix.ProjectionOrder
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Positivity
import QCryptLean.Quantum.Channels.Ancilla
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.CovariantBound
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Channels.Postselection
import QCryptLean.Quantum.Channels.RecordedConjugation
import QCryptLean.Quantum.Channels.SubstateExtraction
import QCryptLean.Quantum.Channels.SymmetricBound
import QCryptLean.Math.LinearAlgebra.Matrix.Reindex
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification
import QCryptLean.Quantum.Operators.StateOperations
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Paired
import QCryptLean.Quantum.Symmetry.Twirl

/-! # Native CKR reduction for covariant channels

Record the permutation average, purify its invariant marginal, and apply the
paired-projector trace cap. All reference registers remain finite types.
-/
noncomputable section
namespace Quantum.Channels
open Matrix Quantum.Operators Quantum.Metrics Quantum.Symmetry
open scoped Kronecker ComplexOrder MatrixOrder
variable {X Y R : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
  [Fintype Y] [Nonempty Y] [Fintype R] [Nonempty R] {k : ℕ}

omit [Fintype R] [Nonempty R] [Nonempty Y] in
/-- Recording permutations reduces positive inputs to invariant purifications. -/
theorem PermutationCovariant.exists_invariant_purification_bound
    (Δ : Operation (Fin k → X) Y) (hΔ : PermutationCovariant Δ)
    (A : Op ((Fin k → X) × (Fin k → X))) (hA : A.PosSemidef) (ht : A.trace.re ≤ 1) :
    ∃ σ : DensityOp (Fin k → X), IsPermutationInvariant σ ∧
      traceNorm (mapTensorId Δ (Fin k → X) A) ≤
        traceNorm (mapTensorId Δ (Fin k → X) σ.purification.toOp) := by
  classical
  let C := partialTraceRight A
  have hC : C.PosSemidef := hA.partialTraceRight
  have hc : C.trace.re ≤ 1 := by simpa only [C, trace_partialTraceRight] using ht
  let ω : DensityOp (Fin k → X) := DensityOp.maxMixed
  let σ : DensityOp (Fin k → X) :=
    { toOp := C + ((1 - C.trace.re : ℝ) : ℂ) • ω.toOp
      posSemidef := hC.add (ω.posSemidef.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr hc)))
      trace_one := by
        rw [trace_add, trace_smul, ω.trace_one, smul_eq_mul, mul_one]
        apply Complex.ext
        · simp
        · simpa using (Complex.nonneg_iff.mp hC.trace_nonneg).2.symm }
  let U : Equiv.Perm (Fin k) → Op (Fin k → X) := permutationRepresentation
  let D := recordedConjugation U A
  have hD : D.PosSemidef := recordedConjugation_posSemidef U A hA
  have hd : partialTraceRight D = twirl permutationUnitary C := by
    rw [partialTraceRight_recordedConjugation, twirl_apply]
    rfl
  have hσC : (σ.toOp - C).PosSemidef := by
    change (C + ((1 - C.trace.re : ℝ) : ℂ) • ω.toOp - C).PosSemidef
    rw [add_sub_cancel_left]
    exact ω.posSemidef.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr hc))
  have hdom : ((symmetrize σ).toOp - partialTraceRight D).PosSemidef := by
    rw [hd]
    change (twirl permutationUnitary σ.toOp - twirl permutationUnitary C).PosSemidef
    rw [← map_sub]
    exact (isChannel_twirl permutationUnitary).1.posSemidef hσC
  have hn : traceNorm (mapTensorId Δ ((Fin k → X) × Equiv.Perm (Fin k)) D) =
      traceNorm (mapTensorId Δ (Fin k → X) A) := by
    rw [traceNorm_mapTensorId_recordedConjugation]
    simp only [U, traceNorm_mapTensorId_perm_conj Δ hΔ, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]
  refine ⟨symmetrize σ, isPermutationInvariant_symmetrize σ, ?_⟩
  rw [← hn]
  apply traceNorm_mapTensorId_le_of_partialTraceRight_le Δ D hD
    (symmetrize σ).purificationKet.toKet
  change ((symmetrize σ).purification.partialTraceRight.toOp - partialTraceRight D).PosSemidef
  rw [DensityOp.partialTraceRight_purification]
  exact hdom

omit [Nonempty Y] [Nonempty R] in
/-- Paired symmetric support gives the exact projector-trace CKR estimate. -/
theorem traceNorm_mapTensorId_le_of_paired_support
    (Δ : Operation (Fin k → X) Y)
    (A : Op ((Fin k → X) × (Fin k → X))) (hA : A.PosSemidef) (ht : A.trace.re ≤ 1)
    (hs : pairedProjector X k * A * pairedProjector X k = A)
    (τ : DensityOp ((Fin k → X) × R)) (hτ : IsCKRDeFinettiPurification τ) :
    traceNorm (mapTensorId Δ (Fin k → X) A) ≤
      (symmetricProjector (X × X) k).trace.re * ckrTraceNorm Δ τ := by
  let P := pairedProjector X k
  let Q := symmetricProjector (X × X) k
  have hP : P.PosSemidef := pairedProjector_posSemidef
  have hPP : P * P = P := by
    change reindex _ _ Q * reindex _ _ Q = reindex _ _ Q
    rw [← reindex_mul, symmetricProjector_mul_self]
  have hPA : P * A = A := by
    change P * A * P = A at hs
    calc
      P * A = P * (P * A * P) := congrArg (P * ·) hs.symm
      _ = P * A * P := by simp only [← Matrix.mul_assoc, hPP]
      _ = A := hs
  have hd := hA.le_projection_of_trace_le_one ht hP.isHermitian hPP hPA
  have hQ : Q.PosSemidef := Quantum.Symmetry.symmetricProjector_posSemidef
  have hr : Q.trace = (Q.trace.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using (Complex.nonneg_iff.mp hQ.trace_nonneg).2.symm
  have hp : 0 < Q.trace.re := by
    refine lt_of_le_of_ne (Complex.nonneg_iff.mp hQ.trace_nonneg).1 ?_
    intro he
    apply Quantum.Symmetry.symmetricProjector_trace_ne_zero (X := X × X) (k := k)
    rw [hr, ← he, Complex.ofReal_zero]
  apply traceNorm_mapTensorId_substate_bound Δ A hA τ hτ.isPure _ hp
  rw [hτ.marginal]
  have he : (Quantum.Symmetry.ckrDeFinettiState X k).toOp =
      Q.trace⁻¹ • partialTraceRight P := by
    change partialTraceRight (reindex (pairFunctions X X k) (pairFunctions X X k)
      (Q.trace⁻¹ • Q)) = _
    change partialTraceRight (Q.trace⁻¹ • P) = _
    exact partialTraceRight_smul _ _
  rw [he, smul_smul, ← hr, mul_inv_cancel₀
    (Quantum.Symmetry.symmetricProjector_trace_ne_zero
      (X := X × X) (k := k)),
    one_smul, ← partialTraceRight_sub]
  exact (Matrix.le_iff.mp hd).partialTraceRight

end Quantum.Channels
