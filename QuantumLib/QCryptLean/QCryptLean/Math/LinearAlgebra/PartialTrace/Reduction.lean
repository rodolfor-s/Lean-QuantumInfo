import Mathlib.LinearAlgebra.Matrix.Kronecker
import QCryptLean.Math.LinearAlgebra.Matrix.QuadraticSum
import QCryptLean.Math.LinearAlgebra.PartialTrace.Basic
import QCryptLean.Math.LinearAlgebra.PartialTrace.Positivity

/-! # The dimension bound for positive matrices and a partial trace

The local matrix star order expresses the operator inequality. No norm is installed.
-/
namespace Matrix
open scoped ComplexOrder MatrixOrder Kronecker
variable {X Y : Type*} [Finite X] [Fintype Y] [DecidableEq Y]

/-- A positive matrix is at most the discarded dimension times its marginal with an identity. -/
theorem PosSemidef.le_card_smul_partialTraceRight_kronecker_one
    {A : Matrix (X × Y) (X × Y) ℂ} (hA : A.PosSemidef) :
    A ≤ (Fintype.card Y : ℂ) • (Matrix.partialTraceRight A ⊗ₖ (1 : Matrix Y Y ℂ)) := by
  classical
  let := Fintype.ofFinite X
  apply Matrix.le_iff.mpr
  apply (posSemidef_iff_dotProduct_mulVec).mpr
  have hH := ((hA.partialTraceRight.kronecker PosSemidef.one).smul
    (by positivity : (0 : ℂ) ≤ (Fintype.card Y : ℂ))).isHermitian.sub hA.isHermitian
  refine ⟨hH, ?_⟩
  intro v
  let z : Y → (X × Y) → ℂ := fun r p => if p.2 = r then v p else 0
  have hz : ∑ r, z r = v := by
    funext p
    simp [z]
  have hblock (r : Y) :
      (star (z r) ⬝ᵥ A *ᵥ z r).re ≤
        (star (fun x => v (x, r)) ⬝ᵥ Matrix.partialTraceRight A *ᵥ (fun x => v (x, r))).re := by
    let B := A.submatrix (fun x => (x, r)) (fun x => (x, r))
    have hB : B ≤ Matrix.partialTraceRight A := by
      rw [partialTraceRight_eq_sum]
      exact Finset.single_le_sum (fun s _ => (hA.submatrix (fun x => (x, s))).nonneg)
        (Finset.mem_univ r)
    have hq := (Complex.nonneg_iff.mp ((Matrix.le_iff.mp hB).dotProduct_mulVec_nonneg
      (fun x => v (x, r)))).1
    have he : star (z r) ⬝ᵥ A *ᵥ z r =
        star (fun x => v (x, r)) ⬝ᵥ B *ᵥ (fun x => v (x, r)) := by
      simp [z, B, dotProduct, mulVec, Fintype.sum_prod_type, Finset.mul_sum,
        ite_mul, apply_ite]
    rw [he]
    simpa only [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re, sub_nonneg] using hq
  have he : (star v ⬝ᵥ (Matrix.partialTraceRight A ⊗ₖ (1 : Matrix Y Y ℂ)) *ᵥ v).re =
      ∑ r : Y, (star (fun x => v (x, r)) ⬝ᵥ Matrix.partialTraceRight A *ᵥ
        (fun x => v (x, r))).re := by
    simp only [dotProduct, mulVec, Fintype.sum_prod_type, kroneckerMap_apply, Matrix.one_apply,
      mul_ite, mul_one, mul_zero, zero_mul, ite_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
      Pi.star_apply, Complex.re_sum]
    exact Finset.sum_comm
  have h := hA.re_dotProduct_sum_le z
  rw [hz] at h
  have hs := (Finset.sum_le_sum (s := Finset.univ) fun (r : Y) _ => hblock r)
  have hle := h.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))
  rw [← he] at hle
  have him : (star v ⬝ᵥ ((Fintype.card Y : ℂ) •
      (Matrix.partialTraceRight A ⊗ₖ (1 : Matrix Y Y ℂ)) - A) *ᵥ v).im = 0 := by
    have hc := congrArg Complex.im (hH.star_dotProduct_mulVec_comm v v)
    simp only [Complex.star_def, Complex.conj_im] at hc
    linarith
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, him.symm⟩
  simpa only [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero, sub_nonneg] using hle

end Matrix
