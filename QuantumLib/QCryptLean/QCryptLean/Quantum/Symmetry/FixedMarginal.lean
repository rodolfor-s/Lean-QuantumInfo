import QCryptLean.Math.LinearAlgebra.Matrix.ProjectionOrder
import QCryptLean.Math.LinearAlgebra.Matrix.TensorSqrt
import QCryptLean.Math.LinearAlgebra.Matrix.Transport
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Sandwich
import QCryptLean.Math.SpectralTheory.Matrix
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.UnitaryCentralizer

/-!
# Fixed-marginal projection domination on product registers

All square roots use the local Löwner order. Positivity is stated directly with
`Matrix.PosSemidef`; no matrix norm is selected. The trace multiplier is the
actual rank/trace parameter of the projection, not an ambient register dimension.
-/

noncomputable section

namespace Quantum.Symmetry

open Matrix Quantum.Operators
open scoped ComplexOrder MatrixOrder Kronecker

variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- The fixed-marginal domination theorem. -/
theorem fixedMarginal_projection_domination {g : ℕ}
    (Q T : Op (X × Y)) {A K : Op X} (hA : A.PosDef) (hK : K.PosDef)
    (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (hT : T.PosSemidef) (hQT : Q * T = T) (hmarg : partialTraceRight T = A)
    (hAcomm : Commute (A ⊗ₖ (1 : Op Y)) Q)
    (hKcomm : Commute (K ⊗ₖ (1 : Op Y)) Q)
    (hKinv : K⁻¹ = partialTraceRight Q) (htr : Q.trace = (g : ℂ)) (hg : g ≠ 0) :
    let S := CFC.sqrt A ⊗ₖ (1 : Op Y)
    let W := CFC.sqrt K ⊗ₖ (1 : Op Y)
    (S * (W * Q * W) * S).PosSemidef ∧
      ((g : ℂ) • (S * (W * Q * W) * S) - T).PosSemidef := by
  by_cases hz : g = 0
  · exact (hg hz).elim
  let SA := CFC.sqrt A
  let SK := CFC.sqrt K
  have hSA : SA.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hSK : SK.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg K)
  have hSAu : IsUnit SA := (CFC.isUnit_sqrt_iff A hA.posSemidef.nonneg).mpr hA.isUnit
  have hSKu : IsUnit SK := (CFC.isUnit_sqrt_iff K hK.posSemidef.nonneg).mpr hK.isUnit
  have hSAi : SA * SA⁻¹ = 1 := mul_nonsing_inv _ (isUnit_iff_isUnit_det _ |>.mp hSAu)
  have hiSA : SA⁻¹ * SA = 1 := nonsing_inv_mul _ (isUnit_iff_isUnit_det _ |>.mp hSAu)
  have hSKi : SK * SK⁻¹ = 1 := mul_nonsing_inv _ (isUnit_iff_isUnit_det _ |>.mp hSKu)
  have hiSK : SK⁻¹ * SK = 1 := nonsing_inv_mul _ (isUnit_iff_isUnit_det _ |>.mp hSKu)
  have hSAsq : SA * SA = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hSKsq : SK * SK = K := CFC.sqrt_mul_sqrt_self K hK.posSemidef.nonneg
  let S := SA ⊗ₖ (1 : Op Y)
  let Si := SA⁻¹ ⊗ₖ (1 : Op Y)
  let W := SK ⊗ₖ (1 : Op Y)
  let Wi := SK⁻¹ ⊗ₖ (1 : Op Y)
  have hSSi : S * Si = 1 := by
    rw [← mul_kronecker_mul, hSAi, Matrix.one_mul, one_kronecker_one]
  have hSiS : Si * S = 1 := by
    rw [← mul_kronecker_mul, hiSA, Matrix.one_mul, one_kronecker_one]
  have hWWi : W * Wi = 1 := by
    rw [← mul_kronecker_mul, hSKi, Matrix.one_mul, one_kronecker_one]
  have hWiW : Wi * W = 1 := by
    rw [← mul_kronecker_mul, hiSK, Matrix.one_mul, one_kronecker_one]
  have hSH : S.IsHermitian := hSA.isHermitian.kronecker isHermitian_one
  have hWH : W.IsHermitian := hSK.isHermitian.kronecker isHermitian_one
  have hSiH : Si.IsHermitian := by
    apply IsHermitian.kronecker _ isHermitian_one
    rw [Matrix.IsHermitian, conjTranspose_nonsing_inv, hSA.isHermitian.eq]
  have hWiH : Wi.IsHermitian := by
    apply IsHermitian.kronecker _ isHermitian_one
    rw [Matrix.IsHermitian, conjTranspose_nonsing_inv, hSK.isHermitian.eq]
  have hSQ : Commute S Q := Matrix.PosSemidef.commute_sqrt_kronecker_one hA.posSemidef hAcomm
  have hWQ : Commute W Q := Matrix.PosSemidef.commute_sqrt_kronecker_one hK.posSemidef hKcomm
  have hSiQ : Commute Si Q := Commute.units_inv_left (u := ⟨S, Si, hSSi, hSiS⟩) hSQ
  have hWiQ : Commute Wi Q := Commute.units_inv_left (u := ⟨W, Wi, hWWi, hWiW⟩) hWQ
  let C := S * W
  let D := Wi * Si
  have hCD : C * D = 1 := by
    change (S * W) * (Wi * Si) = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc W Wi Si, hWWi, Matrix.one_mul, hSSi]
  have hDQ : Commute D Q := hWiQ.mul_left hSiQ
  have htrD : (D * T * Dᴴ).trace = (g : ℂ) := by
    change ((Wi * Si) * T * (Wi * Si)ᴴ).trace = _
    rw [conjTranspose_mul, hSiH.eq, hWiH.eq]
    change (((SK⁻¹ ⊗ₖ (1 : Op Y)) * (SA⁻¹ ⊗ₖ (1 : Op Y))) * T *
      ((SA⁻¹ ⊗ₖ (1 : Op Y)) * (SK⁻¹ ⊗ₖ (1 : Op Y)))).trace = _
    rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul,
      ← trace_partialTraceRight, partialTraceRight_kronecker_one_sandwich, hmarg]
    have he : SK⁻¹ * SA⁻¹ * A * (SA⁻¹ * SK⁻¹) = SK⁻¹ * SK⁻¹ := by
      rw [← hSAsq]
      calc
        _ = SK⁻¹ * (SA⁻¹ * SA) * (SA * SA⁻¹) * SK⁻¹ := by noncomm_ring
        _ = _ := by rw [hiSA, hSAi, Matrix.mul_one, Matrix.mul_one]
    rw [he, ← Matrix.mul_inv_rev, hSKsq, hKinv, trace_partialTraceRight, htr]
  have hDT : (D * T * Dᴴ).PosSemidef := hT.mul_mul_conjTranspose_same D
  have hQT' : Q * (D * T * Dᴴ) = D * T * Dᴴ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← hDQ.eq, Matrix.mul_assoc D Q T, hQT]
  have hb := hDT.le_re_trace_smul_projection hQ hQQ hQT'
  rw [htrD, Complex.natCast_re, Complex.ofReal_natCast] at hb
  have hd := (Matrix.le_iff.mp hb).mul_mul_conjTranspose_same C
  have he : C * (D * T * Dᴴ) * Cᴴ = T := by
    calc
      _ = (C * D) * T * (C * D)ᴴ := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = T := by rw [hCD, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, he] at hd
  have hQp : Q.PosSemidef := by
    have hp : IsStarProjection Q := ⟨hQQ, hQ⟩
    exact Matrix.nonneg_iff_posSemidef.mp hp.nonneg
  have hp := hQp.mul_mul_conjTranspose_same C
  have hc : C * Q * Cᴴ = S * (W * Q * W) * S := by
    simp only [C, conjTranspose_mul, hSH.eq, hWH.eq, Matrix.mul_assoc]
  rw [hc] at hp hd
  exact ⟨hp, hd⟩

end Quantum.Symmetry
