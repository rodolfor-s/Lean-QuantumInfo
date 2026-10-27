import Mathlib.Analysis.Matrix.Order
import QCryptLean.Math.LinearAlgebra.Matrix.PositiveTrace
import QCryptLean.Math.SpectralTheory.CfcSpectral

/-! # Trace domination against a support pseudoinverse

The matrix star order is selected locally; no norm instance is exported.
-/
noncomputable section
namespace Matrix
open scoped MatrixOrder ComplexOrder
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A dominated positive matrix has inverse-reference collision trace at most its trace.
The real power is the support pseudoinverse, including singular references. -/
theorem PosSemidef.trace_sq_mul_rpow_neg_one_le {A B : Matrix X X ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hAB : A ≤ B) :
    (A * A * B ^ (-1 : ℝ)).trace.re ≤ A.trace.re := by
  let K := B ^ (-1 : ℝ)
  have hK : K.IsHermitian := (nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := B)
    (y := (-1 : ℝ)))).isHermitian
  have hKBK : K * B * K = K := by
    dsimp [K]
    rw [CFC.rpow_eq_cfc_real hB.nonneg]
    conv_lhs => arg 1; arg 2; rw [← cfc_id ℝ B]
    rw [← cfc_mul _ _ B (Math.SpectralTheory.CfcSpectral.continuousOn_spectrum B _)
      (Math.SpectralTheory.CfcSpectral.continuousOn_spectrum B _),
      ← cfc_mul _ _ B (Math.SpectralTheory.CfcSpectral.continuousOn_spectrum B _)
      (Math.SpectralTheory.CfcSpectral.continuousOn_spectrum B _)]
    apply cfc_congr
    intro x _
    simp only [Real.rpow_neg_one, id_eq]
    by_cases hx : x = 0 <;> simp [hx]
  have hp := (hA.conjTranspose_mul_mul_same (1 - K * A)).add
    ((le_iff.mp hAB).conjTranspose_mul_mul_same (K * A))
  have he : (1 - K * A)ᴴ * A * (1 - K * A) +
      (K * A)ᴴ * (B - A) * (K * A) = A - A * K * A := by
    simp only [conjTranspose_sub, conjTranspose_one, conjTranspose_mul, hA.isHermitian.eq, hK.eq]
    calc
      _ = A - A * K * A - A * K * A + A * (K * B * K) * A := by noncomm_ring
      _ = _ := by rw [hKBK]; abel
  rw [he] at hp
  have ht := (Complex.nonneg_iff.mp hp.trace_nonneg).1
  rw [trace_sub, Complex.sub_re, trace_mul_cycle A K A] at ht
  linarith

end Matrix
