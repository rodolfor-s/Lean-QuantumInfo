import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Positivity
import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Channels.DiamondBounds
import QCryptLean.Quantum.Channels.SubstateExtraction
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceNorm
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.BraKet
import QCryptLean.Quantum.Operators.Purification

/-!
# Trace-norm stability with arbitrary finite reference types

Positive inputs reduce to a square pure extension through native substate extraction.
Hermitian decomposition and Boolean dilation preserve the exact constant.
No matrix norm instance is selected.
-/
noncomputable section
namespace Quantum.Channels
open Matrix Quantum.Operators Quantum.Metrics
open scoped ComplexOrder MatrixOrder
variable {X Y R : Type*} [Fintype X] [Fintype Y] [Fintype R]

/-- A square-reference positive unit-ball bound controls positive inputs at every reference. -/
theorem traceNorm_mapTensorId_le_mul_trace_of_posSemidef
    (Δ : Operation X Y) (b : ℝ)
    (hbound : ∀ P : Op (X × X), P.PosSemidef → P.trace.re ≤ 1 →
      traceNorm (mapTensorId Δ X P) ≤ b)
    (A : Op (X × R)) (hA : A.PosSemidef) :
    traceNorm (mapTensorId Δ R A) ≤ b * A.trace.re := by
  classical
  have hscale (P : Op (X × X)) (hP : P.PosSemidef) :
      traceNorm (mapTensorId Δ X P) ≤ b * P.trace.re := by
    by_cases ht : P.trace = 0
    · rw [hP.trace_eq_zero_iff.mp ht, map_zero, traceNorm_zero, trace_zero, Complex.zero_re,
        mul_zero]
    have hp : 0 < P.trace.re := by
      refine lt_of_le_of_ne (Complex.nonneg_iff.mp hP.trace_nonneg).1 ?_
      intro he
      apply ht
      apply Complex.ext
      · simpa using he.symm
      · simpa using (Complex.nonneg_iff.mp hP.trace_nonneg).2.symm
    let Q : Op (X × X) := (P.trace.re : ℂ)⁻¹ • P
    have hQ : Q.PosSemidef := hP.smul (inv_nonneg.mpr (Complex.zero_le_real.mpr hp.le))
    have hreal : P.trace = (P.trace.re : ℂ) := by
      apply Complex.ext <;> simp [(Complex.nonneg_iff.mp hP.trace_nonneg).2.symm]
    have hQt : Q.trace.re ≤ 1 := by
      dsimp only [Q]
      rw [trace_smul, hreal, Complex.ofReal_re, smul_eq_mul, inv_mul_cancel₀]
      · simp
      · exact_mod_cast hp.ne'
    have he : (P.trace.re : ℂ) • Q = P :=
      smul_inv_smul₀ (by exact_mod_cast hp.ne') P
    calc
      traceNorm (mapTensorId Δ X P) = P.trace.re * traceNorm (mapTensorId Δ X Q) := by
        conv_lhs => rw [← he]
        rw [map_smul, traceNorm_smul, Complex.norm_real, Real.norm_of_nonneg hp.le]
      _ ≤ P.trace.re * b := mul_le_mul_of_nonneg_left (hbound Q hQ hQt) hp.le
      _ = b * P.trace.re := mul_comm _ _
  let M := CFC.sqrt (partialTraceRight A)
  let v := Ket.vectorize M
  have hm : partialTraceRight v.projector = partialTraceRight A := by
    rw [Ket.partialTraceRight_vectorize]
    exact hA.partialTraceRight.eq_cfcSqrt_mul_conjTranspose.symm
  have ht : v.projector.trace = A.trace := by
    rw [← trace_partialTraceRight v.projector, hm, trace_partialTraceRight]
  exact (traceNorm_mapTensorId_le_of_partialTraceRight_le Δ A hA v
    (by rw [hm, sub_self]; exact PosSemidef.zero)).trans (by
      simpa only [ht] using hscale v.projector v.posSemidef_projector)

/-- A square-reference positive bound controls Hermitian inputs with their trace norm. -/
theorem traceNorm_mapTensorId_le_mul_of_isHermitian
    (Δ : Operation X Y) (b : ℝ)
    (hbound : ∀ P : Op (X × X), P.PosSemidef → P.trace.re ≤ 1 →
      traceNorm (mapTensorId Δ X P) ≤ b)
    (A : Op (X × R)) (hA : A.IsHermitian) :
    traceNorm (mapTensorId Δ R A) ≤ b * traceNorm A := by
  obtain ⟨P, Q, hP, hQ, he, hn⟩ := exists_posSemidef_sub_traceNorm_eq A hA
  rw [he, map_sub]
  calc
    _ ≤ traceNorm (mapTensorId Δ R P) + traceNorm (mapTensorId Δ R Q) := traceNorm_sub_le _ _
    _ ≤ b * P.trace.re + b * Q.trace.re := add_le_add
      (traceNorm_mapTensorId_le_mul_trace_of_posSemidef Δ b hbound P hP)
      (traceNorm_mapTensorId_le_mul_trace_of_posSemidef Δ b hbound Q hQ)
    _ = b * traceNorm (P - Q) := by rw [← he, hn, Complex.add_re]; ring

/-- A positive square-reference bound controls an input and its adjoint together. -/
theorem traceNorm_mapTensorId_add_adjoint_le
    (Δ : Operation X Y) (b : ℝ)
    (hbound : ∀ P : Op (X × X), P.PosSemidef → P.trace.re ≤ 1 →
      traceNorm (mapTensorId Δ X P) ≤ b) (A : Op (X × R)) :
    traceNorm (mapTensorId Δ R A) + traceNorm (mapTensorId Δ R Aᴴ) ≤
      2 * b * traceNorm A := by
  classical
  let e : ((X × R) ⊕ (X × R)) ≃ X × (Bool × R) :=
    (Equiv.boolProdEquivSum (X × R)).symm.trans
      { toFun := fun p => (p.2.1, p.1, p.2.2)
        invFun := fun p => (p.2.1, p.1, p.2.2)
        left_inv := by rintro ⟨b, x, r⟩; rfl
        right_inv := by rintro ⟨x, b, r⟩; rfl }
  let f : ((Y × R) ⊕ (Y × R)) ≃ Y × (Bool × R) :=
    (Equiv.boolProdEquivSum (Y × R)).symm.trans
      { toFun := fun p => (p.2.1, p.1, p.2.2)
        invFun := fun p => (p.2.1, p.1, p.2.2)
        left_inv := by rintro ⟨b, y, r⟩; rfl
        right_inv := by rintro ⟨y, b, r⟩; rfl }
  let D := reindex e e (fromBlocks 0 A Aᴴ 0)
  let B := mapTensorId Δ R A
  let C := mapTensorId Δ R Aᴴ
  have hD : D.IsHermitian := by
    apply IsHermitian.reindex
    simp [Matrix.IsHermitian, fromBlocks_conjTranspose]
  have hn : traceNorm D = 2 * traceNorm A := by
    rw [traceNorm_reindex, traceNorm_fromBlocks_dilation]
  have he : mapTensorId Δ (Bool × R) D = reindex f f (fromBlocks 0 B C 0) := by
    ext ⟨y, b, r⟩ ⟨z, c, s⟩
    cases b <;> cases c
    · change Δ 0 y z = 0
      rw [map_zero]
      rfl
    · rfl
    · rfl
    · change Δ 0 y z = 0
      rw [map_zero]
      rfl
  have hh := traceNorm_mapTensorId_le_mul_of_isHermitian Δ b hbound D hD
  rw [he, traceNorm_reindex, traceNorm_fromBlocks_offDiagonal, hn] at hh
  dsimp only [B, C] at hh
  linarith

/-- Adjoint preservation makes the reference-stability bound exact on all operators. -/
theorem traceNorm_mapTensorId_le_mul_of_map_conjTranspose
    (Δ : Operation X Y) (b : ℝ) (hstar : ∀ A, Δ Aᴴ = (Δ A)ᴴ)
    (hbound : ∀ P : Op (X × X), P.PosSemidef → P.trace.re ≤ 1 →
      traceNorm (mapTensorId Δ X P) ≤ b) (A : Op (X × R)) :
    traceNorm (mapTensorId Δ R A) ≤ b * traceNorm A := by
  have he : mapTensorId Δ R Aᴴ = (mapTensorId Δ R A)ᴴ := by
    ext ⟨y, r⟩ ⟨z, s⟩
    exact congrFun (congrFun (hstar (Matrix.of fun i j => A (i, s) (j, r))) y) z
  have hh := traceNorm_mapTensorId_add_adjoint_le Δ b hbound A
  rw [he, traceNorm_conjTranspose] at hh
  linarith

end Quantum.Channels
