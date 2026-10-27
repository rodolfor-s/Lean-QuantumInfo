import QCryptLean.Quantum.DeFinetti.PureState.CoherentState
import QCryptLean.Quantum.DeFinetti.Basic
import QCryptLean.Quantum.DeFinetti.CKMRAffine
import QCryptLean.Quantum.DeFinetti.CKMRMeasure
import QCryptLean.Quantum.DeFinetti.Integral
import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceNorm
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Symmetry.Basic
import QCryptLean.Quantum.Symmetry.Dimension

/-! # Native CKMR trace-distance bound for the coherent measure -/
noncomputable section
namespace Quantum.DeFinetti
open Matrix Quantum.Operators Quantum.Symmetry Quantum.Metrics
open scoped ComplexOrder
variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X] {n k : ℕ}

/-- The coherent-measure error is twice the deficit in symmetric dimensions. -/
theorem traceDistance_coherentMeasure_le (x : X) (ρ : DensityOp (Fin n → X))
    (hρ : symmetricProjector X n * ρ.toOp * symmetricProjector X n = ρ.toOp) (hk : k ≤ n) :
    traceDistance (partialTraceLast hk ρ).toOp
      (integralTensorPower k (coherentMeasure x ρ hρ)) ≤
      2 * (1 - ((n - k + Fintype.card X - 1).choose (Fintype.card X - 1) : ℝ) /
        (n + Fintype.card X - 1).choose (Fintype.card X - 1)) := by
  let r := ((n - k + Fintype.card X - 1).choose (Fintype.card X - 1) : ℝ) /
    (n + Fintype.card X - 1).choose (Fintype.card X - 1)
  have hr1 : r ≤ 1 := Quantum.DeFinetti.PureState.dim_ratio_le_one hk
  have ht (j : ℕ) : (symmetricProjector X j).trace =
      ((j + Fintype.card X - 1).choose (Fintype.card X - 1) : ℂ) := by
    apply Complex.ext
    · exact symmetricSubspace_dim
    · simpa only [Complex.natCast_im] using
        (Complex.nonneg_iff.mp
          (symmetricProjector_posSemidef (X := X) (k := j)).trace_nonneg).2.symm
  have hr : (r : ℂ) * (symmetricProjector X n).trace =
      (symmetricProjector X (n - k)).trace := by
    rw [ht, ht]
    dsimp only [r]
    push_cast
    exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (by omega))))
  let A := (partialTraceLast hk ρ).toOp
  let B := integralTensorPower k (coherentMeasure x ρ hρ)
  let G := (1 - 2 * r : ℂ) • A + (r : ℂ) • B
  have hG : G.PosSemidef := coherent_affine_posSemidef x ρ hρ hk r hr
  let P := ((2 * (1 - r) : ℝ) : ℂ) • A
  let Q := G + ((1 - r : ℝ) : ℂ) • B
  have hP : P.PosSemidef := (partialTraceLast hk ρ).posSemidef.smul
    (Complex.zero_le_real.mpr (mul_nonneg (by norm_num) (sub_nonneg.mpr hr1)))
  have hQ : Q.PosSemidef := hG.add ((posSemidef_integralTensorPower _ _).smul
    (Complex.zero_le_real.mpr (sub_nonneg.mpr hr1)))
  have he : A - B = P - Q := by
    ext i j
    simp only [P, Q, G, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have hA : A.trace = 1 := (partialTraceLast hk ρ).trace_one
  have hB : B.trace = 1 := trace_integralTensorPower _ _
  have htrace : (P.trace + Q.trace).re = 4 * (1 - r) := by
    simp only [P, Q, G, trace_add, trace_smul, smul_eq_mul, hA, hB, mul_one,
      Complex.add_re, Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    norm_num
    ring
  have h := traceNorm_sub_posSemidef_le P Q hP hQ
  rw [htrace, ← he] at h
  change (1/2 : ℝ) * traceNorm (A - B) ≤ 2 * (1 - r)
  linarith

end Quantum.DeFinetti
