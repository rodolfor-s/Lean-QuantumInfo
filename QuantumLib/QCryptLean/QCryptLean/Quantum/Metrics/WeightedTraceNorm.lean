import QCryptLean.Math.LinearAlgebra.Matrix.HilbertSchmidt
import QCryptLean.Math.LinearAlgebra.Matrix.UnitaryGram
import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceDuality

/-! # Weighted Trace Norm -/


noncomputable section
namespace Quantum.Metrics
open Matrix
open scoped ComplexOrder MatrixOrder

open Classical in
/-- Hilbert-Schmidt bound for the polar-unitary factor in the squared-sandwich
Cauchy-Schwarz step.  If `F = σ^{-1/4}` and `P = F⁻¹`, then
`‖P U P‖₂² ≤ Tr(σ)` for every unitary `U`. -/
private lemma weightedUnitary_trace_le
    {X : Type*} [Fintype X]
    {σ : Matrix X X ℂ} (hσ : σ.PosDef) (U : Matrix.unitaryGroup X ℂ) :
    ((((CFC.sqrt (CFC.sqrt σ⁻¹)))⁻¹ * U.val * ((CFC.sqrt (CFC.sqrt σ⁻¹)))⁻¹) *
        ((((CFC.sqrt (CFC.sqrt σ⁻¹)))⁻¹ * U.val *
          ((CFC.sqrt (CFC.sqrt σ⁻¹)))⁻¹).conjTranspose)).trace.re ≤
      σ.trace.re := by
  set F : Matrix X X ℂ := (CFC.sqrt (CFC.sqrt σ⁻¹))
  set P : Matrix X X ℂ := F⁻¹
  set C : Matrix X X ℂ := P * P
  set Y : Matrix X X ℂ := U.val * C * U.val.conjTranspose
  have hG : F * F * σ * (F * F) = 1 := by
    rw [show F * F = CFC.sqrt σ⁻¹ from
      CFC.sqrt_mul_sqrt_self _ (CFC.sqrt_nonneg _)]
    exact hσ.sqrt_inv_mul_self_mul_sqrt_inv
  have hF_unit : IsUnit F :=
    IsUnit.of_mul_eq_one_right _ (show (F * F * σ * F) * F = 1 by
      simpa only [Matrix.mul_assoc] using hG)
  have hF_det : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).mp hF_unit
  have hFP : F * P = 1 := Matrix.mul_nonsing_inv F hF_det
  have hPF : P * F = 1 := Matrix.nonsing_inv_mul F hF_det
  have hP_herm : P.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian.inv
  have hC_psd : C.PosSemidef := by
    have h := Matrix.posSemidef_self_mul_conjTranspose P
    rwa [hP_herm.eq] at h
  have hC_herm : C.IsHermitian := hC_psd.isHermitian
  have hC_sq : C * C = σ := by
    calc C * C = (P * P) * (F * F * σ * (F * F)) * (P * P) := by rw [hG, Matrix.mul_one]
      _ = (P * (P * F) * F) * σ * (F * (F * P) * P) := by simp only [Matrix.mul_assoc]
      _ = σ := by
        rw [hPF, hFP, Matrix.mul_one, Matrix.mul_one, hPF, hFP, Matrix.one_mul, Matrix.mul_one]
  have hUleft : U.valᴴ * U.val = 1 := U.property.1
  have hAA_trace :
      ((((CFC.sqrt (CFC.sqrt σ⁻¹)))⁻¹ * U.val * ((CFC.sqrt (CFC.sqrt σ⁻¹)))⁻¹) *
          ((((CFC.sqrt (CFC.sqrt σ⁻¹)))⁻¹ * U.val *
            ((CFC.sqrt (CFC.sqrt σ⁻¹)))⁻¹).conjTranspose)).trace =
        (C * Y).trace := by
    calc ((P * U.val * P) * (P * U.val * P).conjTranspose).trace
        = ((P * U.val * P) * (P * U.val.conjTranspose * P)).trace := by
            simp only [Matrix.conjTranspose_mul, hP_herm.eq, Matrix.mul_assoc]
      _ = (P * (U.val * C * U.val.conjTranspose) * P).trace := by
            simp only [C, Matrix.mul_assoc]
      _ = (C * Y).trace := by
            rw [Matrix.trace_mul_cycle P (U.val * C * U.val.conjTranspose) P]
  have hY_trace :
      (Y.conjTranspose * Y).trace.re = (C * C).trace.re := by
    have hY_conj : Y.conjTranspose = Y := by
      change (U.val * C * U.val.conjTranspose).conjTranspose = U.val * C * U.val.conjTranspose
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        hC_herm.eq, ← Matrix.mul_assoc]
    rw [hY_conj]
    have htrace : (Y * Y).trace = (C * C).trace := by
      calc (Y * Y).trace
          = ((U.val * C * U.val.conjTranspose) *
              (U.val * C * U.val.conjTranspose)).trace := rfl
        _ = (U.val * C * (U.val.conjTranspose * U.val) *
              C * U.val.conjTranspose).trace := by
              simp only [Matrix.mul_assoc]
        _ = (U.val * C * 1 * C * U.val.conjTranspose).trace := by
              rw [hUleft]
        _ = (U.val * (C * C) * U.val.conjTranspose).trace := by
              simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = (U.val.conjTranspose * U.val * (C * C)).trace := by
              rw [Matrix.trace_mul_cycle U.val (C * C) U.val.conjTranspose]
        _ = (C * C).trace := by rw [hUleft, Matrix.one_mul]
    exact congrArg Complex.re htrace
  have hHS := Matrix.norm_trace_mul_sq_le_trace_mul_trace_conjTranspose C Y
  have hHS' :
      ‖(C * Y).trace‖ ^ 2 ≤ (C * C).trace.re ^ 2 := by
    rwa [hC_herm.eq, hY_trace, ← sq] at hHS
  have hT_nn : 0 ≤ (C * C).trace.re := by
    rw [hC_sq]
    exact (Complex.nonneg_iff.mp hσ.posSemidef.trace_nonneg).1
  have hnorm_le : ‖(C * Y).trace‖ ≤ (C * C).trace.re :=
    le_of_sq_le_sq hHS' hT_nn
  have hre_le_norm : (C * Y).trace.re ≤ ‖(C * Y).trace‖ :=
    (le_abs_self (C * Y).trace.re).trans (Complex.abs_re_le_norm (C * Y).trace)
  calc ((((CFC.sqrt (CFC.sqrt σ⁻¹)))⁻¹ * U.val * ((CFC.sqrt (CFC.sqrt σ⁻¹)))⁻¹) *
          ((((CFC.sqrt (CFC.sqrt σ⁻¹)))⁻¹ * U.val *
            ((CFC.sqrt (CFC.sqrt σ⁻¹)))⁻¹).conjTranspose)).trace.re
      = (C * Y).trace.re := congrArg Complex.re hAA_trace
    _ ≤ ‖(C * Y).trace‖ := hre_le_norm
    _ ≤ (C * C).trace.re := hnorm_le
    _ = σ.trace.re := by rw [hC_sq]

open Classical in
/-- Weighted Hilbert–Schmidt control of the Hermitian trace norm.
The CFC inverse fourth root is evaluated in the local matrix order. -/
theorem traceNorm_sq_le_re_trace_mul_re_trace_sandwich_sq
    {X : Type*} [Fintype X]
    {σ : Matrix X X ℂ} (hσ : σ.PosDef) {D : Matrix X X ℂ} (hD : D.IsHermitian) :
    (traceNorm D) ^ 2 ≤
      σ.trace.re *
        (((CFC.sqrt (CFC.sqrt σ⁻¹)) * D * (CFC.sqrt (CFC.sqrt σ⁻¹))) *
          ((CFC.sqrt (CFC.sqrt σ⁻¹)) * D * (CFC.sqrt (CFC.sqrt σ⁻¹)))).trace.re := by
  classical
  set F : Matrix X X ℂ := (CFC.sqrt (CFC.sqrt σ⁻¹)) with hF_def
  set P : Matrix X X ℂ := F⁻¹ with hP_def
  have hF_herm : F.IsHermitian := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian
  have hG : F * F * σ * (F * F) = 1 := by
    rw [show F * F = CFC.sqrt σ⁻¹ from
      CFC.sqrt_mul_sqrt_self _ (CFC.sqrt_nonneg _)]
    exact hσ.sqrt_inv_mul_self_mul_sqrt_inv
  have hF_unit : IsUnit F :=
    IsUnit.of_mul_eq_one_right _ (show (F * F * σ * F) * F = 1 by
      simpa only [Matrix.mul_assoc] using hG)
  have hF_det : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).mp hF_unit
  have hFP : F * P = 1 := Matrix.mul_nonsing_inv F hF_det
  have hPF : P * F = 1 := Matrix.nonsing_inv_mul F hF_det
  obtain ⟨U, hU⟩ := Matrix.exists_unitary_mul_eq_sqrt_gram D
  have h_norm_eqD : traceNorm D = (U.val * D).trace.re := by
    rw [hU, traceNorm_eq_trace_sqrt]
  set A : Matrix X X ℂ := P * U.val * P with hA_def
  set B : Matrix X X ℂ := F * D * F with hB_def
  have h_trace_rewrite : (U.val * D).trace = (A * B).trace := by
    symm
    calc (A * B).trace
        = (P * U.val * P * (F * D * F)).trace := by rw [hA_def, hB_def]
      _ = (P * U.val * D * F).trace := by
            simp only [← Matrix.mul_assoc]
            rw [Matrix.mul_assoc (P * U.val) P F, hPF, Matrix.mul_one]
      _ = (F * (P * U.val) * D).trace := Matrix.trace_mul_cycle (P * U.val) D F
      _ = (U.val * D).trace := by
            rw [← Matrix.mul_assoc, hFP, Matrix.one_mul]
  have hB_herm : B.IsHermitian := by
    change (F * D * F).conjTranspose = F * D * F
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hF_herm.eq, hD.eq, Matrix.mul_assoc]
  have hAA_le : (A * A.conjTranspose).trace.re ≤ σ.trace.re :=
    weightedUnitary_trace_le hσ U
  have hBB_nonneg : 0 ≤ (B.conjTranspose * B).trace.re :=
    (Complex.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self B).trace_nonneg).1
  have hCS := Matrix.norm_trace_mul_sq_le_trace_mul_trace_conjTranspose A B
  have h_re_sq_le_norm_sq :
      ((U.val * D).trace.re) ^ 2 ≤ ‖(U.val * D).trace‖ ^ 2 := by
    have habs := Complex.abs_re_le_norm (U.val * D).trace
    have h_sq : ((U.val * D).trace.re) ^ 2 =
        |((U.val * D).trace.re)| ^ 2 := by rw [sq_abs]
    rw [h_sq]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  calc traceNorm D ^ 2
      = ((U.val * D).trace.re) ^ 2 := by rw [h_norm_eqD]
    _ ≤ ‖(U.val * D).trace‖ ^ 2 := h_re_sq_le_norm_sq
    _ = ‖(A * B).trace‖ ^ 2 := by rw [h_trace_rewrite]
    _ ≤ (A * A.conjTranspose).trace.re * (B.conjTranspose * B).trace.re := hCS
    _ ≤ σ.trace.re * (B.conjTranspose * B).trace.re :=
        mul_le_mul_of_nonneg_right hAA_le hBB_nonneg
    _ = σ.trace.re * (B * B).trace.re := by rw [hB_herm.eq]
    _ = σ.trace.re *
          (((CFC.sqrt (CFC.sqrt σ⁻¹)) * D * (CFC.sqrt (CFC.sqrt σ⁻¹))) *
            ((CFC.sqrt (CFC.sqrt σ⁻¹)) * D * (CFC.sqrt (CFC.sqrt σ⁻¹)))).trace.re := rfl


end Quantum.Metrics
