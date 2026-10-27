import QCryptLean.Math.LinearAlgebra.Matrix.FilteredProjection
import QCryptLean.Math.LinearAlgebra.Matrix.TensorSqrt
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Sandwich
import QCryptLean.Math.SpectralTheory.Matrix

/-! # Fixed-marginal bounds on a finite-dimensional support projector

The proof whitens the prescribed marginal and the projector marginal, applies
the supported trace cap, and restores the filters. Matrix star order is local.
-/
noncomputable section
namespace Matrix
open scoped Kronecker ComplexOrder MatrixOrder
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- A supported positive matrix with a fixed faithful marginal obeys the filtered projector cap. -/
theorem PosSemidef.le_fixedMarginal_projection {A P : Matrix (X × Y) (X × Y) ℂ}
    {M : Matrix X X ℂ} (hA : A.PosSemidef) (hM : M.PosDef)
    (hP : P.IsHermitian) (hPP : P * P = P) (hPA : P * A = A)
    (hAM : partialTraceRight A = M) (hΩ : (partialTraceRight P).PosDef)
    (hMP : Commute (M ⊗ₖ (1 : Matrix Y Y ℂ)) P)
    (hΩP : Commute (partialTraceRight P ⊗ₖ (1 : Matrix Y Y ℂ)) P) :
    A ≤ (P.trace.re : ℂ) •
      ((CFC.sqrt M ⊗ₖ (1 : Matrix Y Y ℂ)) *
        ((partialTraceRight P)⁻¹ ⊗ₖ (1 : Matrix Y Y ℂ)) * P *
          (CFC.sqrt M ⊗ₖ (1 : Matrix Y Y ℂ))ᴴ) := by
  let D := CFC.sqrt M
  let H := CFC.sqrt (partialTraceRight P)
  have hD : D.PosSemidef := nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg M)
  have hH : H.PosSemidef := nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (partialTraceRight P))
  have hDu : IsUnit D := (CFC.isUnit_sqrt_iff _ hM.posSemidef.nonneg).mpr hM.isUnit
  have hHu : IsUnit H := (CFC.isUnit_sqrt_iff _ hΩ.posSemidef.nonneg).mpr hΩ.isUnit
  have hDDi : D * D⁻¹ = 1 := mul_nonsing_inv _ (hDu.map detMonoidHom)
  have hDiD : D⁻¹ * D = 1 := nonsing_inv_mul _ (hDu.map detMonoidHom)
  have hHHi : H * H⁻¹ = 1 := mul_nonsing_inv _ (hHu.map detMonoidHom)
  have hHiH : H⁻¹ * H = 1 := nonsing_inv_mul _ (hHu.map detMonoidHom)
  have hDP : Commute (D ⊗ₖ (1 : Matrix Y Y ℂ)) P :=
    hM.posSemidef.commute_sqrt_kronecker_one hMP
  have hHP : Commute (H ⊗ₖ (1 : Matrix Y Y ℂ)) P :=
    hΩ.posSemidef.commute_sqrt_kronecker_one hΩP
  have hinv (V : Matrix X X ℂ) (hV : IsUnit V)
      (hc : Commute (V ⊗ₖ (1 : Matrix Y Y ℂ)) P) :
      Commute (V⁻¹ ⊗ₖ (1 : Matrix Y Y ℂ)) P := by
    have hv : IsUnit (V ⊗ₖ (1 : Matrix Y Y ℂ)) := by
      refine ⟨⟨V ⊗ₖ (1 : Matrix Y Y ℂ), V⁻¹ ⊗ₖ (1 : Matrix Y Y ℂ), ?_, ?_⟩, rfl⟩
      · rw [← mul_kronecker_mul, Matrix.one_mul,
          mul_nonsing_inv _ (hV.map detMonoidHom), one_kronecker_one]
      · rw [← mul_kronecker_mul, Matrix.one_mul,
          nonsing_inv_mul _ (hV.map detMonoidHom), one_kronecker_one]
    let := Classical.choice hv.nonempty_invertible
    simpa only [invOf_eq_nonsing_inv, inv_kronecker, inv_one] using hc.invOf_left
  let S := (D * H⁻¹) ⊗ₖ (1 : Matrix Y Y ℂ)
  let T := (H * D⁻¹) ⊗ₖ (1 : Matrix Y Y ℂ)
  have hST : S * T = 1 := by
    change (_ ⊗ₖ _) * (_ ⊗ₖ _) = _
    rw [← mul_kronecker_mul, Matrix.one_mul]
    have he : (D * H⁻¹) * (H * D⁻¹) = 1 := by
      rw [Matrix.mul_assoc D, ← Matrix.mul_assoc H⁻¹, hHiH, Matrix.one_mul, hDDi]
    rw [he, one_kronecker_one]
  have hTP : Commute T P := by
    have hc := hHP.mul_left (hinv D hDu hDP)
    simpa only [← mul_kronecker_mul, Matrix.one_mul] using hc
  have ht : (T * A * Tᴴ).trace = P.trace := by
    change (((H * D⁻¹) ⊗ₖ (1 : Matrix Y Y ℂ)) * A *
      ((H * D⁻¹) ⊗ₖ (1 : Matrix Y Y ℂ))ᴴ).trace = _
    rw [← trace_partialTraceRight, conjTranspose_kronecker, conjTranspose_one,
      partialTraceRight_kronecker_one_sandwich, hAM, conjTranspose_mul,
      hD.isHermitian.inv.eq, hH.isHermitian.eq]
    have he : D⁻¹ * M * D⁻¹ = 1 := by
      rw [show D⁻¹ = CFC.sqrt M⁻¹ from hM.posSemidef.inv_sqrt]
      exact hM.sqrt_inv_mul_self_mul_sqrt_inv
    calc
      _ = (H * (D⁻¹ * M * D⁻¹) * H).trace := by simp only [Matrix.mul_assoc]
      _ = (H * H).trace := by rw [he, Matrix.mul_one]
      _ = P.trace := by
        rw [show H * H = partialTraceRight P from CFC.sqrt_mul_sqrt_self _ hΩ.posSemidef.nonneg,
          trace_partialTraceRight]
  have hs : S * P * Sᴴ = (D ⊗ₖ (1 : Matrix Y Y ℂ)) *
      ((partialTraceRight P)⁻¹ ⊗ₖ (1 : Matrix Y Y ℂ)) * P *
        (D ⊗ₖ (1 : Matrix Y Y ℂ))ᴴ := by
    have hSi : S = (D ⊗ₖ (1 : Matrix Y Y ℂ)) * (H⁻¹ ⊗ₖ (1 : Matrix Y Y ℂ)) := by
      rw [← mul_kronecker_mul, Matrix.one_mul]
    have hiherm : (H⁻¹ ⊗ₖ (1 : Matrix Y Y ℂ))ᴴ = H⁻¹ ⊗ₖ (1 : Matrix Y Y ℂ) := by
      rw [conjTranspose_kronecker, hH.isHermitian.inv.eq, conjTranspose_one]
    have hi2 : H⁻¹ * H⁻¹ = (partialTraceRight P)⁻¹ := by
      rw [show H⁻¹ = CFC.sqrt (partialTraceRight P)⁻¹ from hΩ.posSemidef.inv_sqrt,
        CFC.sqrt_mul_sqrt_self _ hΩ.posSemidef.inv.nonneg]
    rw [hSi, conjTranspose_mul, hiherm]
    calc
      _ = (D ⊗ₖ (1 : Matrix Y Y ℂ)) *
          ((H⁻¹ ⊗ₖ (1 : Matrix Y Y ℂ)) * (H⁻¹ ⊗ₖ (1 : Matrix Y Y ℂ))) * P *
            (D ⊗ₖ (1 : Matrix Y Y ℂ))ᴴ := by
        let J := H⁻¹ ⊗ₖ (1 : Matrix Y Y ℂ)
        let L := D ⊗ₖ (1 : Matrix Y Y ℂ)
        change L * J * P * (J * Lᴴ) = L * (J * J) * P * Lᴴ
        calc
          _ = L * J * ((P * J) * Lᴴ) := by simp only [Matrix.mul_assoc]
          _ = L * J * ((J * P) * Lᴴ) := by rw [← (hinv H hHu hHP).eq]
          _ = _ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [← mul_kronecker_mul, Matrix.one_mul, hi2]
  have h := hA.le_trace_smul_filtered_projection hP hPP hPA hST hTP
  rw [ht, hs] at h
  exact h

end Matrix
