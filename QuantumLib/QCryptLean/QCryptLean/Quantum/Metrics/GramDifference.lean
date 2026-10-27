import QCryptLean.Quantum.Metrics.Basic
import QCryptLean.Quantum.Metrics.TraceNorm
import QCryptLean.Quantum.Operators.Basic

/-!
# Native Gram-difference trace-norm bound

The proof optimizes a scaled positive-minus-positive decomposition. All matrix
norms are explicit trace expressions; no matrix norm instance is installed.
-/

noncomputable section
namespace Quantum.Metrics
open Matrix Quantum.Operators
open scoped ComplexOrder
variable {α : Type*} [Fintype α]

/-- Expanding the two symmetrized factors recovers twice the Gram difference. -/
private lemma sub_mulConjTranspose_eq_half_symmetrised (X Y : Op α) :
    (X + Y) * (X - Y)ᴴ + (X - Y) * (X + Y)ᴴ = (X * Xᴴ - Y * Yᴴ) + (X * Xᴴ - Y * Yᴴ) := by
  classical
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub]
  noncomm_ring

/-- Step 3 of the derivation: with a free scale `a, b` subject to `4 a b = 1`, the difference of
two Gram operators is itself a difference of two Gram operators. -/
private lemma symmetrised_eq_posSemidef_difference (X Y : Op α) {a b : ℝ} (hab : 4 * a * b = 1) :
    X * Xᴴ - Y * Yᴴ
      = ((a : ℂ) • (X + Y) + (b : ℂ) • (X - Y)) * ((a : ℂ) • (X + Y) + (b : ℂ) • (X - Y))ᴴ
        - ((a : ℂ) • (X + Y) - (b : ℂ) • (X - Y)) * ((a : ℂ) • (X + Y) - (b : ℂ) • (X - Y))ᴴ := by
  classical
  have hstar : ∀ (c : ℝ) (A : Op α), ((c : ℂ) • A)ᴴ = (c : ℂ) • Aᴴ := by
    intro c A
    simp [Matrix.conjTranspose_smul]
  have hexpand :
      ((a : ℂ) • (X + Y) + (b : ℂ) • (X - Y)) * ((a : ℂ) • (X + Y) + (b : ℂ) • (X - Y))ᴴ
        - ((a : ℂ) • (X + Y) - (b : ℂ) • (X - Y)) * ((a : ℂ) • (X + Y) - (b : ℂ) • (X - Y))ᴴ
        = ((2 * a * b : ℝ) : ℂ) • ((X + Y) * (X - Y)ᴴ + (X - Y) * (X + Y)ᴴ) := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, hstar, add_mul, mul_add,
      sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, smul_sub]
    match_scalars <;> ring
  have hcoeff : ((2 * a * b : ℝ) : ℂ) + ((2 * a * b : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_add]
    norm_cast
    linarith
  rw [hexpand, sub_mulConjTranspose_eq_half_symmetrised X Y, smul_add, ← add_smul, hcoeff,
    one_smul]

/-! ### The scaled trace-norm bound -/

/-- Step 4 of the derivation: for every scale `a, b` with `4 a b = 1`, the trace norm of the
difference of two Gram operators is bounded by the scaled sum of the two Frobenius squares. -/
theorem traceNorm_sub_le_half_scaled_frobenius (X Y : Op α) {a b : ℝ}
    (hab : 4 * a * b = 1) :
    traceNorm (X * Xᴴ - Y * Yᴴ)
      ≤ 2 * a ^ 2 * ((X + Y) * (X + Y)ᴴ).trace.re
        + 2 * b ^ 2 * ((X - Y) * (X - Y)ᴴ).trace.re := by
  classical
  have hstar : ∀ (c : ℝ) (A : Op α), ((c : ℂ) • A)ᴴ = (c : ℂ) • Aᴴ := by
    intro c A
    simp [Matrix.conjTranspose_smul]
  set U : Op α := X + Y with hU
  set V : Op α := X - Y with hV
  set Wp : Op α := (a : ℂ) • U + (b : ℂ) • V with hWp
  set Wm : Op α := (a : ℂ) • U - (b : ℂ) • V with hWm
  have hsplit : X * Xᴴ - Y * Yᴴ = Wp * Wpᴴ - Wm * Wmᴴ :=
    symmetrised_eq_posSemidef_difference X Y hab
  have hPp : (Wp * Wpᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose Wp
  have hPm : (Wm * Wmᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose Wm
  have htri := traceNorm_sub_posSemidef_le _ _ hPp hPm
  -- the two Gram traces add up to the scaled Frobenius sum
  have hsumMat : Wp * Wpᴴ + Wm * Wmᴴ
      = ((2 * a ^ 2 : ℝ) : ℂ) • (U * Uᴴ) + ((2 * b ^ 2 : ℝ) : ℂ) • (V * Vᴴ) := by
    simp only [hWp, hWm, Matrix.conjTranspose_add, Matrix.conjTranspose_sub, hstar, add_mul,
      mul_add, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    match_scalars <;> ring
  have htrace : (Wp * Wpᴴ).trace.re + (Wm * Wmᴴ).trace.re
      = 2 * a ^ 2 * (U * Uᴴ).trace.re + 2 * b ^ 2 * (V * Vᴴ).trace.re := by
    have h0 : (Wp * Wpᴴ + Wm * Wmᴴ).trace
        = (((2 * a ^ 2 : ℝ) : ℂ) • (U * Uᴴ) + ((2 * b ^ 2 : ℝ) : ℂ) • (V * Vᴴ)).trace :=
      congrArg Matrix.trace hsumMat
    rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      smul_eq_mul, smul_eq_mul] at h0
    have hre := congrArg Complex.re h0
    rw [Complex.add_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul] at hre
    exact hre
  rw [hsplit]
  exact htri.trans_eq (by rw [Complex.add_re]; exact htrace)

/-- Steps 4 and 8′ of the derivation: optimising the scale gives the Cauchy–Schwarz form
`‖X Xᴴ − Y Yᴴ‖₁ ≤ ‖X + Y‖_F · ‖X − Y‖_F`. -/
theorem traceNorm_sub_mulConjTranspose_le_frobenius (X Y : Op α) :
    traceNorm (X * Xᴴ - Y * Yᴴ)
      ≤ Real.sqrt (((X + Y) * (X + Y)ᴴ).trace.re * ((X - Y) * (X - Y)ᴴ).trace.re) := by
  classical
  have hzero : ∀ W : Op α, (W * Wᴴ).trace.re = 0 → W = 0 := by
    intro W hW
    have hpsd : (W * Wᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose W
    have hnn := hpsd.trace_nonneg
    have him : (W * Wᴴ).trace.im = 0 := ((Complex.nonneg_iff.mp hnn).2).symm
    exact Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp (Complex.ext hW him)
  set U : Op α := X + Y with hU
  set V : Op α := X - Y with hV
  set nU : ℝ := (U * Uᴴ).trace.re with hnU
  set nV : ℝ := (V * Vᴴ).trace.re with hnV
  have hUpsd : (U * Uᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose U
  have hVpsd : (V * Vᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose V
  have hnU0 : 0 ≤ nU := (Complex.nonneg_iff.mp hUpsd.trace_nonneg).1
  have hnV0 : 0 ≤ nV := (Complex.nonneg_iff.mp hVpsd.trace_nonneg).1
  rcases eq_or_lt_of_le hnU0 with hU0 | hUpos
  · -- `X + Y = 0`, so the two Gram operators coincide
    have hUeq : U = 0 := hzero U hU0.symm
    have hXY : Y = -X := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hUeq
    have hMzero : X * Xᴴ - Y * Yᴴ = 0 := by
      rw [hXY, Matrix.conjTranspose_neg, neg_mul_neg]
      abel
    rw [hMzero, traceNorm_zero]
    exact Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hnV0 with hV0 | hVpos
  · -- `X − Y = 0`, same conclusion
    have hVeq : V = 0 := hzero V hV0.symm
    have hXY : Y = X := (sub_eq_zero.mp hVeq).symm
    have hMzero : X * Xᴴ - Y * Yᴴ = 0 := by rw [hXY]; abel
    rw [hMzero, traceNorm_zero]
    exact Real.sqrt_nonneg _
  -- the generic branch: the scale that equalises the two terms
  have hUne : nU ≠ 0 := ne_of_gt hUpos
  have hVne : nV ≠ 0 := ne_of_gt hVpos
  set r : ℝ := Real.sqrt (nU * nV) with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr (mul_pos hUpos hVpos)
  set a : ℝ := Real.sqrt (r / (4 * nU)) with ha
  set b : ℝ := Real.sqrt (r / (4 * nV)) with hb
  have hrU : 0 ≤ r / (4 * nU) := div_nonneg hrpos.le (mul_pos zero_lt_four hUpos).le
  have hrV : 0 ≤ r / (4 * nV) := div_nonneg hrpos.le (mul_pos zero_lt_four hVpos).le
  have ha2 : a ^ 2 = r / (4 * nU) := by rw [ha, Real.sq_sqrt hrU]
  have hb2 : b ^ 2 = r / (4 * nV) := by rw [hb, Real.sq_sqrt hrV]
  have hr2 : r ^ 2 = nU * nV := by rw [hr, Real.sq_sqrt (mul_pos hUpos hVpos).le]
  have hab : 4 * a * b = 1 := by
    -- `a b = √(r² / (16 nU nV)) = 1/4`.
    have hprod : a * b = Real.sqrt ((r / (4 * nU)) * (r / (4 * nV))) := by
      rw [ha, hb, ← Real.sqrt_mul hrU]
    have harg : (r / (4 * nU)) * (r / (4 * nV)) = (1 / 4 : ℝ) ^ 2 := by
      rw [div_mul_div_comm, ← pow_two, hr2]
      field_simp
    rw [mul_assoc, hprod, harg, Real.sqrt_sq (by norm_num)]
    norm_num
  have hbound := traceNorm_sub_le_half_scaled_frobenius X Y hab
  rw [← hU, ← hV, ← hnU, ← hnV] at hbound
  refine hbound.trans (le_of_eq ?_)
  rw [ha2, hb2]
  field_simp
  ring


end Quantum.Metrics
