import QCryptLean.Math.LinearAlgebra.Matrix.DominatedFactor
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.Kraus
import QCryptLean.Quantum.Channels.LeftAmplification
import QCryptLean.Quantum.Channels.SubchannelCompletion
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.Contractivity
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification

/-!
# Native extraction from a dominated marginal

Rectangular Gram domination yields a finite Kraus family on the reference.
Positivity uses local matrix star order; no matrix norm is selected.
-/
noncomputable section
namespace Quantum.Channels
open Matrix Quantum.Operators Quantum.Metrics
open scoped Kronecker ComplexOrder MatrixOrder
variable {X Y R S : Type*} [Fintype X] [Fintype Y] [Fintype R] [Fintype S]

omit [Fintype X] [Fintype Y] [Fintype R] [Fintype S] in
/-- Operations on distinct product factors commute. -/
theorem mapTensorId_mapIdTensor [Finite X] [Finite R] (Φ : Operation X Y) (Ψ : Operation R S)
    (A : Op (X × R)) :
    mapTensorId Φ S (mapIdTensor X Ψ A) = mapIdTensor Y Ψ (mapTensorId Φ R A) := by
  classical
  let := Fintype.ofFinite X
  let := Fintype.ofFinite R
  have hΦ (B : Op X) :
      Φ B = ∑ i, ∑ j, B i j • Φ (single i j 1) := by
    have hB : B = ∑ i, ∑ j, B i j • single i j 1 := by
      simpa only [smul_single, smul_eq_mul, mul_one] using matrix_eq_sum_single B
    conv_lhs => rw [hB]
    simp only [map_sum, map_smul]
  have hΨ (B : Op R) :
      Ψ B = ∑ i, ∑ j, B i j • Ψ (single i j 1) := by
    have hB : B = ∑ i, ∑ j, B i j • single i j 1 := by
      simpa only [smul_single, smul_eq_mul, mul_one] using matrix_eq_sum_single B
    conv_lhs => rw [hB]
    simp only [map_sum, map_smul]
  ext ⟨y, s⟩ ⟨z, t⟩
  change Φ (fun (i j : X) => Ψ (fun (r q : R) => A (i, r) (j, q)) s t) y z =
    Ψ (fun (r q : R) => Φ (fun (i j : X) => A (i, r) (j, q)) y z) s t
  have hl := congrFun (congrFun (hΦ
    (fun (i j : X) => Ψ (fun (r q : R) => A (i, r) (j, q)) s t)) y) z
  have hr := congrFun (congrFun (hΨ
    (fun (r q : R) => Φ (fun (i j : X) => A (i, r) (j, q)) y z)) s) t
  rw [hl, hr]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [hΨ (fun r q => A (_, r) (_, q)), hΦ (fun i j => A (i, _) (j, _))]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [Fintype X] in
/-- A positive operator whose marginal is dominated by a pure marginal is obtained
by a trace-nonincreasing reference operation. -/
theorem exists_reference_subchannel_of_partialTraceRight_le [Finite X]
    (A : Op (X × R)) (hA : A.PosSemidef) (v : Ket (X × S))
    (hdom : (partialTraceRight v.projector - partialTraceRight A).PosSemidef) :
    ∃ Ψ : Operation S R, IsCompletelyPositive Ψ ∧
      (∀ B, B.PosSemidef → (Ψ B).trace.re ≤ B.trace.re) ∧
      A = mapIdTensor X Ψ v.projector := by
  classical
  let := Fintype.ofFinite X
  let C := CFC.sqrt A
  have hC : C * Cᴴ = A := hA.eq_cfcSqrt_mul_conjTranspose.symm
  let P : Matrix X S ℂ := fun x s => v.vec (x, s)
  let B : Matrix X (R × (X × R)) ℂ := fun x p => C (x, p.1) p.2
  have hP : P * Pᴴ = partialTraceRight v.projector := by
    ext x y
    rfl
  have hB : B * Bᴴ = partialTraceRight A := by
    rw [← hC]
    ext x y
    change (∑ p : R × (X × R), C (x, p.1) p.2 * star (C (y, p.1) p.2)) =
      ∑ r, (C * Cᴴ) (x, r) (y, r)
    simp only [Fintype.sum_prod_type, mul_apply, conjTranspose_apply]
  obtain ⟨W, hW, hc⟩ := exists_mul_eq_of_posSemidef_rowGram_sub P B (by
    rwa [hP, hB])
  let K : (X × R) → Matrix R S ℂ := fun i r s => W s (r, i)
  have hK : ∑ i, (K i)ᴴ * K i = (W * Wᴴ)ᵀ := by
    ext s t
    simp only [Matrix.sum_apply]
    change (∑ i : X × R, ∑ r, star (W s (r, i)) * W t (r, i)) =
      ∑ p : R × (X × R), W t p * star (W s p)
    conv_rhs => rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  refine ⟨krausMap K, isCompletelyPositive_krausMap K, ?_, ?_⟩
  · apply (trace_krausMap_le_iff K).mpr
    rw [hK]
    apply Matrix.le_iff.mpr
    simpa only [transpose_sub, transpose_one] using hc.transpose
  · have he (x : X) (r : R) (i : X × R) :
        C (x, r) i = ∑ s, v.vec (x, s) * K i r s :=
      congrFun (congrFun hW x) (r, i)
    rw [← hC]
    ext ⟨x, r⟩ ⟨y, q⟩
    change (∑ i, C (x, r) i * star (C (y, q) i)) =
      (∑ i, K i * (Matrix.of fun s t => v.vec (x, s) * star (v.vec (y, t))) * (K i)ᴴ) r q
    simp only [Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [he, he]
    simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum, mul_apply,
      conjTranspose_apply, Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring

omit [Fintype X] in
/-- A dominated pure marginal controls any operation's output trace norm. -/
theorem traceNorm_mapTensorId_le_of_partialTraceRight_le [Finite X]
    (Δ : Operation X Y) (A : Op (X × R)) (hA : A.PosSemidef)
    (v : Ket (X × S))
    (hdom : (partialTraceRight v.projector - partialTraceRight A).PosSemidef) :
    traceNorm (mapTensorId Δ R A) ≤ traceNorm (mapTensorId Δ S v.projector) := by
  obtain ⟨Ψ, hΨ, ht, he⟩ := exists_reference_subchannel_of_partialTraceRight_le A hA v hdom
  rw [he, mapTensorId_mapIdTensor]
  exact traceNorm_apply_le_of_isCompletelyPositive_of_trace_le _ hΨ.mapIdTensor
    (trace_mapIdTensor_le Ψ ht) _

end Quantum.Channels
