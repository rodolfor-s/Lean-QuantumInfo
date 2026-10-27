import Mathlib.Analysis.Matrix.Order
import QCryptLean.Math.SpectralTheory.CfcSpectral

/-!
# Spectral projectors and kernels of real powers

Spectral projectors and kernels of real powers.
-/

open Matrix Math.SpectralTheory.CfcSpectral
open scoped ComplexOrder MatrixOrder

noncomputable section

/-- **Real power acts by the eigenvalue on a spectral projector.** For a PSD `B` and
an indicator spectral projector `specProj B l`, the CFC real power satisfies
`B ^ r · specProj B l = (l ^ r) • specProj B l`. Both sides are `cfc`-functions of
`B`; the indicator forces the argument to equal `l`, so the integrand `x ^ r` may be
replaced by `l ^ r`. -/
lemma _root_.Math.SpectralTheory.CfcSpectral.rpow_mul_specProj {n : Type*} [Fintype n] [DecidableEq
    n]
    (B : Matrix n n ℂ) (hB : 0 ≤ B) (r l : ℝ) :
    B ^ r * specProj B l = (l ^ r : ℝ) • specProj B l := by
  simp only [specProj]
  rw [CFC.rpow_eq_cfc_real hB,
    ← cfc_mul _ _ B (continuousOn_spectrum B _) (continuousOn_spectrum B _),
    ← cfc_const_mul (l ^ r : ℝ) _ B (continuousOn_spectrum B _)]
  apply cfc_congr
  intro x _
  by_cases hxl : x = l <;> simp [Set.indicator, hxl]

/-- **Right kernel invariance under a real power.** For a PSD operator `B`,
right-multiplication by the CFC power `B ^ r` annihilates exactly the operators
annihilated by right-multiplication by `B`: `M * B ^ r = 0 → M * B = 0`. The `r`-th
power preserves positive eigenvalues and fixes the zero eigenspace, so
`range (B ^ r) = range B`.

Proven through the indicator spectral resolution `B = Σ_l l • specProj B l`: for each
eigenvalue `l ≠ 0` (hence `l > 0` by PSD), `rpow_mul_specProj` gives
`M * B ^ r * specProj B l = l ^ r • (M * specProj B l)` with `l ^ r ≠ 0`, so
`M * specProj B l = 0`; the `l = 0` term vanishes by the scalar. -/
lemma _root_.Math.SpectralTheory.CfcSpectral.mul_eq_zero_of_mul_rpow_eq_zero {n : Type*} [Fintype
    n] [DecidableEq n]
    {M B : Matrix n n ℂ}
    (hB : B.PosSemidef) {r : ℝ} (_hr : r ≠ 0) (h : M * B ^ r = 0) :
    M * B = 0 := by
  classical
  have hBnn : (0 : Matrix n n ℂ) ≤ B := Matrix.nonneg_iff_posSemidef.mpr hB
  have hBsa : IsSelfAdjoint B := hB.isHermitian
  have hdecomp : B = ∑ l ∈ specFinset B, (l : ℂ) • specProj B l :=
    eq_sum_specProj B hBsa
  -- each projector with nonzero eigenvalue is annihilated on the right by `M`
  have hkey : ∀ l ∈ specFinset B, (l : ℂ) • (M * specProj B l) = 0 := by
    intro l hl
    by_cases hl0 : l = 0
    · simp [hl0]
    · have hlpos : 0 < l :=
        lt_of_le_of_ne (spectrum_nonneg_of_nonneg hBnn (mem_specFinset.mp hl))
          (Ne.symm hl0)
      have hlr : (l ^ r : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hlpos r)
      have hmsp : M * specProj B l = 0 := by
        have h1 : M * (B ^ r * specProj B l) = 0 := by
          rw [← Matrix.mul_assoc, h, Matrix.zero_mul]
        rw [rpow_mul_specProj B hBnn r l, mul_smul_comm] at h1
        -- `h1 : (l ^ r : ℝ) • (M * specProj B l) = 0`, and `l ^ r ≠ 0`
        have h2 := congrArg (fun X => (l ^ r : ℝ)⁻¹ • X) h1
        simpa only [smul_zero, smul_smul, inv_mul_cancel₀ hlr, one_smul] using h2
      rw [hmsp, smul_zero]
  calc M * B
      = M * ∑ l ∈ specFinset B, (l : ℂ) • specProj B l := by rw [← hdecomp]
    _ = ∑ l ∈ specFinset B, (l : ℂ) • (M * specProj B l) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun l _ => by rw [mul_smul_comm])
    _ = 0 := Finset.sum_eq_zero hkey

end
