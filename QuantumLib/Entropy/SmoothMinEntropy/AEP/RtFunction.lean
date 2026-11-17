import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Renner thesis §sec:rt — Properties of the function `r_t`

Renner 2005, Appendix `\\section{Properties of the function r_t}` (line 10421):

> The class of functions `r_t : z ↦ z^t - t · ln z - 1`, for `t ∈ ℝ`, is used
> in §sec:smoothprod for the proof of a Chernoff-style bound.

The four properties below feed
`thm:Hmincondrep` (Renner line 4561), which in turn feeds `cor:Hmincondrepclass`
and ultimately `thm:Renyisym` (line 6118 — the AEP needed by the BB84
finite-size chain in place of the Tomamichel-style `extensionRadius` step).

## Main definition
- `InfoTheory.SmoothMinEntropy.rennerRt t z := z^t - t * Real.log z - 1` — defined on `(0, ∞)` for
`t ∈
ℝ`.

## Main statements
- `monotoneOn_rennerRt_Ici_one` (`lem:rtincr`, Renner line 10434): `rennerRt t` is monotone
  on `[1, ∞)` for any `t ∈ ℝ`.
- `rennerRt_le_rennerRt_abs_add_inv` (`lem:rtzz`, line 10450): `rennerRt t z ≤ rennerRt |t| (z +
z⁻¹)`
  for `t ∈ ℝ`, `z > 0`.
- `concaveOn_rennerRt_Ici_four` (`lem:rtconc`, line 10468): `rennerRt t` is concave on
  `[4, ∞)` for `t ∈ [-1/2, 1/2]`.
- `rennerRt_le_mul_log_sq_mul_sq` (`lem:rtbound`, line 10487): for `z ∈ [1, ∞)`,
  `t ∈ [-1/log z, 1/log z]`, `rennerRt t z ≤ (1 - log 2) · (log z)² · t²`.

These are all real-analytic facts — derivative computations and the tanh
inequality. No quantum content.
-/

open Real

noncomputable section

namespace InfoTheory.SmoothMinEntropy

/-- **Renner's `r_t` function.** Defined on `(0, ∞)` by `z ↦ z^t - t · ln z - 1`. -/
noncomputable def rennerRt (t z : ℝ) : ℝ := z ^ t - t * Real.log z - 1

/-- Pointwise derivative of `rennerRt t` at `z > 0`. -/
lemma hasDerivAt_rennerRt {t z : ℝ} (hz : 0 < z) :
    HasDerivAt (rennerRt t) (t * z ^ (t - 1) - t / z) z := by
  have h1 : HasDerivAt (fun z : ℝ => z ^ t) (t * z ^ (t - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hz.ne')
  have h2 : HasDerivAt Real.log z⁻¹ z := Real.hasDerivAt_log hz.ne'
  have h3 : HasDerivAt (fun z : ℝ => t * Real.log z) (t / z) z := by
    have := h2.const_mul t
    simpa [div_eq_mul_inv] using this
  exact (h1.sub h3).sub_const 1

/-- **Renner `lem:rtincr`** (line 10434). For any `t ∈ ℝ`, `rennerRt t` is
    monotonically increasing on `[1, ∞)`.

    Proof sketch (Renner line 10440): `(d/dz) rennerRt t z = t·z^{t-1} - t/z =
    (t/z)(z^t - 1)`. Nonnegative for `z ≥ 1` and any `t ∈ ℝ`. -/
theorem monotoneOn_rennerRt_Ici_one (t : ℝ) :
    MonotoneOn (rennerRt t) (Set.Ici (1 : ℝ)) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici _) ?cont ?diff ?sign
  · -- continuity on `[1, ∞)`
    intro z hz
    have hz_pos : (0 : ℝ) < z := lt_of_lt_of_le one_pos hz
    have hd := hasDerivAt_rennerRt (t := t) hz_pos
    exact hd.continuousAt.continuousWithinAt
  · -- differentiability on the interior
    rw [interior_Ici]
    intro z hz
    have hz_pos : (0 : ℝ) < z := lt_trans one_pos hz
    exact (hasDerivAt_rennerRt (t := t) hz_pos).differentiableAt.differentiableWithinAt
  · -- nonnegative derivative on the interior
    rw [interior_Ici]
    intro z hz
    have hz_one : (1 : ℝ) < z := hz
    have hz_pos : (0 : ℝ) < z := lt_trans one_pos hz_one
    have hz_le : (1 : ℝ) ≤ z := hz_one.le
    have hd := hasDerivAt_rennerRt (t := t) hz_pos
    rw [hd.deriv]
    -- Show `0 ≤ t * z^(t-1) - t / z`. Factor as `(t / z) * (z^t - 1)`.
    have hzt_pos : 0 < z ^ t := Real.rpow_pos_of_pos hz_pos t
    have hzt1_pos : 0 < z ^ (t - 1) := Real.rpow_pos_of_pos hz_pos _
    -- Key identity: `t * z^(t-1) - t/z = (t/z) * (z^t - 1)`.
    have hkey : t * z ^ (t - 1) - t / z = (t / z) * (z ^ t - 1) := by
      have hrpow : z ^ (t - 1) = z ^ t / z := by
        rw [show (t - 1) = t + (-1) from by ring, Real.rpow_add hz_pos,
          Real.rpow_neg_one]
        ring
      rw [hrpow]
      field_simp
    rw [hkey]
    rcases le_total 0 t with ht | ht
    · -- `0 ≤ t` and `1 ≤ z` give `1 ≤ z^t`, both factors nonneg.
      have h1 : (0 : ℝ) ≤ z ^ t - 1 := by
        have := Real.one_le_rpow hz_le ht
        linarith
      have h2 : (0 : ℝ) ≤ t / z := div_nonneg ht hz_pos.le
      exact mul_nonneg h2 h1
    · -- `t ≤ 0` and `1 ≤ z` give `z^t ≤ 1`, both factors nonpos, product nonneg.
      have h1 : z ^ t - 1 ≤ 0 := by
        have := Real.rpow_le_one_of_one_le_of_nonpos hz_le ht
        linarith
      have h2 : t / z ≤ 0 := div_nonpos_of_nonpos_of_nonneg ht hz_pos.le
      exact mul_nonneg_of_nonpos_of_nonpos h2 h1

/-- **AM–GM-style bound**: for `0 < z`, `1 ≤ z + z⁻¹`. -/
private lemma one_le_add_inv {z : ℝ} (hz : 0 < z) : 1 ≤ z + z⁻¹ := by
  have h1 : z * z⁻¹ = 1 := mul_inv_cancel₀ hz.ne'
  nlinarith [sq_nonneg (z - 1), hz, h1]

/-- **Symmetry of `rennerRt`**: `rennerRt (-t) z⁻¹ = rennerRt t z` for `0 < z`. -/
private lemma rennerRt_neg_inv {t z : ℝ} (hz : 0 < z) : rennerRt (-t) z⁻¹ = rennerRt t z := by
  unfold rennerRt
  rw [Real.log_inv, Real.inv_rpow hz.le, Real.rpow_neg hz.le, inv_inv]
  ring

/-- **`rennerRt` written in `exp / log` form** for `0 < z`. -/
private lemma rennerRt_eq_exp_sub_sub_one {t z : ℝ} (hz : 0 < z) :
    rennerRt t z = Real.exp (t * Real.log z) - t * Real.log z - 1 := by
  unfold rennerRt
  rw [Real.rpow_def_of_pos hz, mul_comm (Real.log z) t]

/-- **Sinh inequality** packaged: `2 * v ≤ e^v - e^{-v}` for `0 ≤ v`. -/
private lemma two_mul_le_exp_sub_exp_neg {v : ℝ} (hv : 0 ≤ v) :
    2 * v ≤ Real.exp v - Real.exp (-v) := by
  have h := Real.self_le_sinh_iff.mpr hv
  rw [Real.sinh_eq] at h
  linarith

/-- **Heart of `lem:rtzz`**: when `0 ≤ t` and `0 < z ≤ 1`, the function `rennerRt t`
    is bounded above by its value at `z⁻¹`. The argument is the sinh
    inequality `e^v - e^{-v} ≥ 2v` applied at `v = -t · ln z ≥ 0`. -/
private lemma rennerRt_le_rennerRt_inv_of_nonneg_of_le_one {t z : ℝ} (ht : 0 ≤ t)
    (hz : 0 < z) (hz_le : z ≤ 1) : rennerRt t z ≤ rennerRt t z⁻¹ := by
  have hzinv_pos : 0 < z⁻¹ := inv_pos.mpr hz
  have h_log_z_np : Real.log z ≤ 0 := Real.log_nonpos hz.le hz_le
  have h_v_nn : 0 ≤ -(t * Real.log z) := by
    rw [neg_nonneg]; exact mul_nonpos_of_nonneg_of_nonpos ht h_log_z_np
  have h_sinh := two_mul_le_exp_sub_exp_neg h_v_nn
  -- h_sinh : 2 * -(t * Real.log z) ≤ exp(-(t * Real.log z)) - exp(-(-(t * Real.log z)))
  have h_neg_neg : Real.exp (-(-(t * Real.log z))) = Real.exp (t * Real.log z) := by
    rw [neg_neg]
  rw [h_neg_neg] at h_sinh
  rw [rennerRt_eq_exp_sub_sub_one hz, rennerRt_eq_exp_sub_sub_one hzinv_pos, Real.log_inv]
  have h_eq : t * (-Real.log z) = -(t * Real.log z) := by ring
  rw [h_eq]
  linarith

/-- **`lem:rtzz` for `t ≥ 0`**. -/
private lemma rennerRt_le_rennerRt_add_inv_of_nonneg {t z : ℝ} (ht : 0 ≤ t) (hz : 0 < z) :
    rennerRt t z ≤ rennerRt t (z + z⁻¹) := by
  rcases le_total 1 z with hz1 | hz1
  · -- z ≥ 1: monotonicity directly
    have hzinv_pos : 0 < z⁻¹ := inv_pos.mpr hz
    have h_z_le : z ≤ z + z⁻¹ := by linarith
    have h_one_le_sum : 1 ≤ z + z⁻¹ := by linarith
    exact monotoneOn_rennerRt_Ici_one t (Set.mem_Ici.mpr hz1)
      (Set.mem_Ici.mpr h_one_le_sum) h_z_le
  · -- z ≤ 1: identity through z⁻¹
    have h1_le_zinv : 1 ≤ z⁻¹ := (one_le_inv₀ hz).mpr hz1
    have h_one_le_sum : 1 ≤ z + z⁻¹ := one_le_add_inv hz
    have h_zinv_le_sum : z⁻¹ ≤ z + z⁻¹ := by linarith
    have h_step1 : rennerRt t z ≤ rennerRt t z⁻¹ :=
      rennerRt_le_rennerRt_inv_of_nonneg_of_le_one ht hz hz1
    have h_step2 : rennerRt t z⁻¹ ≤ rennerRt t (z + z⁻¹) :=
      monotoneOn_rennerRt_Ici_one t (Set.mem_Ici.mpr h1_le_zinv)
        (Set.mem_Ici.mpr h_one_le_sum) h_zinv_le_sum
    linarith

/-- **Renner `lem:rtzz`** (line 10450). For any `t ∈ ℝ` and `z > 0`,
    `rennerRt t z ≤ rennerRt |t| (z + z⁻¹)`.

    Proof sketch (Renner line 10456): `rennerRt t z = rennerRt (-t) z⁻¹` (symmetry); reduce
    to `t ≥ 0`. For `z ≥ 1`, apply `monotoneOn_rennerRt_Ici_one`. For `z < 1` and
    `t ≥ 0`, set `v = -t · ln z ≥ 0`; then
    `rennerRt t z⁻¹ = e^v - v - 1`, `rennerRt t z = e^{-v} + v - 1`, and
    `e^v - e^{-v} ≥ 2v` (tanh inequality) gives `rennerRt t z ≤ rennerRt t z⁻¹`. Apply
    `monotoneOn_rennerRt_Ici_one` again. -/
theorem rennerRt_le_rennerRt_abs_add_inv (t z : ℝ) (hz : 0 < z) :
    rennerRt t z ≤ rennerRt |t| (z + z⁻¹) := by
  rcases le_total 0 t with ht | ht
  · -- t ≥ 0
    rw [abs_of_nonneg ht]
    exact rennerRt_le_rennerRt_add_inv_of_nonneg ht hz
  · -- t ≤ 0: apply nonneg case to (-t, z⁻¹)
    have ht' : 0 ≤ -t := neg_nonneg.mpr ht
    have hz' : 0 < z⁻¹ := inv_pos.mpr hz
    have h_step := rennerRt_le_rennerRt_add_inv_of_nonneg ht' hz'
    -- h_step : rennerRt (-t) z⁻¹ ≤ rennerRt (-t) (z⁻¹ + (z⁻¹)⁻¹)
    rw [rennerRt_neg_inv hz, inv_inv] at h_step
    -- h_step : rennerRt t z ≤ rennerRt (-t) (z⁻¹ + z)
    rw [abs_of_nonpos ht, add_comm z z⁻¹]
    exact h_step

/-- Lower bound `1 ≤ Real.log 4`, used in the second-derivative analysis of `rennerRt`. -/
private lemma one_le_log_four : (1 : ℝ) ≤ Real.log 4 := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    have : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
    rw [this, Real.log_pow]
    ring
  rw [h4]
  linarith

/-- Boundary inequality: for `s ∈ [0, 1/2]`, `1 + s ≤ 4^s`.
    Proven via Bernoulli's `add_one_le_exp` together with `1 ≤ Real.log 4`. -/
lemma one_add_le_four_rpow {s : ℝ} (hs0 : 0 ≤ s) (_hs : s ≤ 1 / 2) :
    1 + s ≤ (4 : ℝ) ^ s := by
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := one_le_log_four
  have hexp : 1 + s * Real.log 4 ≤ Real.exp (s * Real.log 4) := by
    have := Real.add_one_le_exp (s * Real.log 4)
    linarith
  have hbern : 1 + s ≤ 1 + s * Real.log 4 := by
    have : s ≤ s * Real.log 4 := by
      have := mul_le_mul_of_nonneg_left hlog4 hs0
      simpa [mul_comm] using this
    linarith
  have h4pos : (0 : ℝ) < 4 := by norm_num
  have hrpow : (4 : ℝ) ^ s = Real.exp (s * Real.log 4) := by
    rw [Real.rpow_def_of_pos h4pos, mul_comm]
  rw [hrpow]
  linarith

/-- Chord bound from concavity of `Real.log`: for `u ∈ [0, 1]`, `2^u ≤ 1 + u`.
    Obtained by applying concavity of `Real.log` on `(0, ∞)` to the chord
    between `1` and `2`. -/
lemma two_rpow_le_one_add_of_mem_Icc {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (2 : ℝ) ^ u ≤ 1 + u := by
  -- Use concavity of Real.log on Ioi 0.
  -- log(1 * (1 - u) + 2 * u) ≥ (1 - u) * log 1 + u * log 2 = u * log 2.
  have hconc : ConcaveOn ℝ (Set.Ioi (0:ℝ)) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn
  have h1mem : (1 : ℝ) ∈ Set.Ioi (0:ℝ) := by simp
  have h2mem : (2 : ℝ) ∈ Set.Ioi (0:ℝ) := by simp
  have ha : (0 : ℝ) ≤ 1 - u := by linarith
  have hab : (1 - u) + u = 1 := by ring
  have key : (1 - u) * Real.log 1 + u * Real.log 2 ≤ Real.log ((1 - u) * 1 + u * 2) :=
    hconc.2 h1mem h2mem ha hu0 hab
  have heq : (1 - u) * (1:ℝ) + u * 2 = 1 + u := by ring
  rw [heq, Real.log_one, mul_zero, zero_add] at key
  -- Now key : u * log 2 ≤ log (1 + u). Convert to 2^u ≤ 1 + u.
  have h1pu_pos : (0 : ℝ) < 1 + u := by linarith
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hexp_le : Real.exp (u * Real.log 2) ≤ 1 + u := by
    have := Real.exp_le_exp.mpr key
    rwa [Real.exp_log h1pu_pos] at this
  have hpow_eq : (2 : ℝ) ^ u = Real.exp (u * Real.log 2) := by
    rw [Real.rpow_def_of_pos h2pos, mul_comm]
  linarith [hpow_eq ▸ hexp_le]

/-- Boundary inequality: for `t ∈ [0, 1/2]`, `1 ≤ 4^t * (1 - t)`.
    Equivalent (via the substitution `u = 1 - 2t`) to `2^u ≤ 1 + u` for
    `u ∈ [0, 1]`, which follows from concavity of `Real.log` on `(0, ∞)`
    with chord between `1` and `2`. -/
lemma one_le_four_rpow_mul_one_sub {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    1 ≤ (4 : ℝ) ^ t * (1 - t) := by
  -- Set u = 1 - 2t ∈ [0, 1].
  set u : ℝ := 1 - 2 * t with hu_def
  have hu0 : 0 ≤ u := by simp [hu_def]; linarith
  have hu1 : u ≤ 1 := by simp [hu_def]; linarith
  have h_pow_le : (2 : ℝ) ^ u ≤ 1 + u := two_rpow_le_one_add_of_mem_Icc hu0 hu1
  -- Now translate 2^u ≤ 1 + u to 1 ≤ 4^t * (1 - t).
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have h2u_pos : (0 : ℝ) < (2 : ℝ) ^ u := Real.rpow_pos_of_pos h2pos u
  have h4eq : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℝ) : ℝ) from rfl]
    rw [show ((2 : ℝ) ^ (2 : ℝ)) = (2 : ℝ) ^ (2 : ℕ) by
      rw [← Real.rpow_natCast (2 : ℝ) 2]; norm_num]
    norm_num
  -- 4^t = (2^2)^t = 2^(2t)
  have h4t_eq : (4 : ℝ) ^ t = (2 : ℝ) ^ (2 * t) := by
    rw [h4eq, ← Real.rpow_mul h2pos.le]
  -- 2t = 1 - u
  have h2t_eq : (2 * t : ℝ) = 1 - u := by change (2 * t : ℝ) = 1 - (1 - 2 * t); ring
  -- 1 - t = (1 + u) / 2
  have h1mt_eq : 1 - t = (1 + u) / 2 := by change 1 - t = (1 + (1 - 2*t))/2; ring
  rw [h4t_eq, h2t_eq, h1mt_eq]
  -- Goal: 1 ≤ 2 ^ (1 - u) * ((1 + u) / 2)
  have hsplit : (2 : ℝ) ^ (1 - u) = 2 / (2 : ℝ) ^ u := by
    rw [Real.rpow_sub h2pos, Real.rpow_one]
  rw [hsplit, div_mul_eq_mul_div]
  rw [show ((2 : ℝ) * ((1 + u) / 2)) = 1 + u from by ring]
  rw [le_div_iff₀ h2u_pos, one_mul]
  exact h_pow_le

/-- `rennerRt t` is differentiable on `(0, ∞)`. -/
lemma differentiableOn_rennerRt (t : ℝ) :
    DifferentiableOn ℝ (rennerRt t) (Set.Ioi (0 : ℝ)) := by
  intro z hz
  exact ((InfoTheory.SmoothMinEntropy.hasDerivAt_rennerRt (Set.mem_Ioi.mp
      hz)).differentiableAt).differentiableWithinAt

/-- First derivative formula: `deriv (rennerRt t) z = t * z^(t-1) - t/z` for `z > 0`. -/
lemma deriv_rennerRt_of_pos {t z : ℝ} (hz : 0 < z) :
    deriv (rennerRt t) z = t * z ^ (t - 1) - t / z :=
  (InfoTheory.SmoothMinEntropy.hasDerivAt_rennerRt hz).deriv

/-- The first derivative of `rennerRt t` agrees with the explicit formula on a
    neighborhood of any positive point. -/
lemma deriv_rennerRt_eventuallyEq_of_pos {t z : ℝ} (hz : 0 < z) :
    deriv (rennerRt t) =ᶠ[nhds z] (fun y => t * y ^ (t - 1) - t / y) := by
  have hIoi : Set.Ioi (0 : ℝ) ∈ nhds z := IsOpen.mem_nhds isOpen_Ioi hz
  filter_upwards [hIoi] with y hy
  exact deriv_rennerRt_of_pos hy

/-- Second derivative of `rennerRt t` at `z > 0`: `t*(t-1)*z^(t-2) + t/z²`. -/
lemma hasDerivAt_deriv_rennerRt {t z : ℝ} (hz : 0 < z) :
    HasDerivAt (deriv (rennerRt t)) (t * (t - 1) * z ^ (t - 2) + t / z ^ 2) z := by
  have hz_ne : z ≠ 0 := ne_of_gt hz
  -- Derivative of (fun y => t * y^(t-1) - t / y) at z.
  have h_rpow : HasDerivAt (fun y : ℝ => y ^ (t - 1)) ((t - 1) * z ^ ((t - 1) - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hz_ne)
  have h_t_rpow : HasDerivAt (fun y : ℝ => t * y ^ (t - 1))
      (t * ((t - 1) * z ^ ((t - 1) - 1))) z := h_rpow.const_mul t
  -- d/dy (1/y) = -1/y² at z.
  have h_inv : HasDerivAt (fun y : ℝ => y⁻¹) (-1 / z ^ 2) z := by
    have h := (hasDerivAt_id z).fun_inv hz_ne
    simpa using h
  -- d/dy (t * y⁻¹) at z = t * (-1 / z^2) = -t / z^2.
  have h_div : HasDerivAt (fun y : ℝ => t * y⁻¹) (t * (-1 / z ^ 2)) z :=
    h_inv.const_mul t
  -- combine
  have h_total :
      HasDerivAt (fun y : ℝ => t * y ^ (t - 1) - t * y⁻¹)
        (t * ((t - 1) * z ^ ((t - 1) - 1)) - t * (-1 / z ^ 2)) z :=
    h_t_rpow.sub h_div
  -- Convert function form `t * y⁻¹` to `t / y`.
  have h_total' :
      HasDerivAt (fun y : ℝ => t * y ^ (t - 1) - t / y)
        (t * ((t - 1) * z ^ ((t - 1) - 1)) - t * (-1 / z ^ 2)) z := by
    have hfun : (fun y : ℝ => t * y ^ (t - 1) - t * y⁻¹) =
                (fun y : ℝ => t * y ^ (t - 1) - t / y) := by
      funext y; ring
    rw [hfun] at h_total
    exact h_total
  -- Use that `deriv (rennerRt t)` agrees with this function on a nhd of z.
  have h_eq : deriv (rennerRt t) =ᶠ[nhds z] (fun y : ℝ => t * y ^ (t - 1) - t / y) :=
    deriv_rennerRt_eventuallyEq_of_pos (t := t) hz
  have hcong : HasDerivAt (deriv (rennerRt t))
      (t * ((t - 1) * z ^ ((t - 1) - 1)) - t * (-1 / z ^ 2)) z :=
    h_total'.congr_of_eventuallyEq h_eq
  -- Now massage the derivative value.
  have hval : t * ((t - 1) * z ^ ((t - 1) - 1)) - t * (-1 / z ^ 2) =
              t * (t - 1) * z ^ (t - 2) + t / z ^ 2 := by
    have h1 : (t - 1) - 1 = t - 2 := by ring
    rw [h1]
    have hz2_ne : (z ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hz_ne
    field_simp
    ring
  rw [← hval]
  exact hcong

/-- Second derivative formula. -/
lemma deriv2_rennerRt_of_pos {t z : ℝ} (hz : 0 < z) :
    deriv^[2] (rennerRt t) z = t * (t - 1) * z ^ (t - 2) + t / z ^ 2 := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
  exact (hasDerivAt_deriv_rennerRt hz).deriv

/-- `deriv (rennerRt t)` is differentiable on `(0, ∞)`. -/
lemma differentiableOn_deriv_rennerRt (t : ℝ) :
    DifferentiableOn ℝ (deriv (rennerRt t)) (Set.Ioi (0 : ℝ)) := by
  intro z hz
  exact ((hasDerivAt_deriv_rennerRt (Set.mem_Ioi.mp hz)).differentiableAt).differentiableWithinAt

/-- `rennerRt t` is continuous on `[4, ∞)`. -/
lemma continuousOn_rennerRt_Ici_four (t : ℝ) :
    ContinuousOn (rennerRt t) (Set.Ici (4 : ℝ)) := by
  -- It is differentiable, hence continuous, on `Ioi 0 ⊇ Ici 4`.
  have h1 : ContinuousOn (rennerRt t) (Set.Ioi (0 : ℝ)) :=
    (differentiableOn_rennerRt t).continuousOn
  have h2 : Set.Ici (4 : ℝ) ⊆ Set.Ioi (0 : ℝ) := by
    intro z hz
    exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 4) hz
  exact h1.mono h2

/-- The second derivative of `rennerRt t` is nonpositive on `(4, ∞)` whenever
    `t ∈ [-1/2, 1/2]`. -/
lemma deriv2_rennerRt_nonpos {t z : ℝ}
    (ht : t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) (hz : 4 < z) :
    deriv^[2] (rennerRt t) z ≤ 0 := by
  have hz_pos : 0 < z := lt_trans (by norm_num : (0:ℝ) < 4) hz
  have hz_ne : z ≠ 0 := ne_of_gt hz_pos
  have hz2_pos : 0 < z ^ 2 := pow_pos hz_pos 2
  have hz2_ne : (z ^ 2 : ℝ) ≠ 0 := ne_of_gt hz2_pos
  have hzt_pos : 0 < z ^ t := Real.rpow_pos_of_pos hz_pos t
  rw [deriv2_rennerRt_of_pos hz_pos]
  -- Express as (t*(t-1)*z^t + t) / z^2.
  -- Note z^(t-2) * z^2 = z^t for z > 0 (where the second `^` is the rpow).
  have hpow_id : z ^ (t - 2) * z ^ (2 : ℝ) = z ^ t := by
    rw [← Real.rpow_add hz_pos]; ring_nf
  have hz2_eq : z ^ (2 : ℝ) = z ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  -- Rewrite the goal as a quotient.
  have hrewrite : t * (t - 1) * z ^ (t - 2) + t / z ^ 2
      = (t * (t - 1) * z ^ t + t) / z ^ 2 := by
    rw [eq_div_iff hz2_ne]
    have key : t * (t - 1) * z ^ (t - 2) * z ^ 2 = t * (t - 1) * z ^ t := by
      rw [← hz2_eq]
      rw [show t * (t - 1) * z ^ (t - 2) * z ^ (2 : ℝ)
            = t * (t - 1) * (z ^ (t - 2) * z ^ (2 : ℝ)) from by ring]
      rw [hpow_id]
    field_simp
    linarith [key]
  rw [hrewrite]
  -- Now: numerator ≤ 0 and denominator ≥ 0 gives quotient ≤ 0.
  apply div_nonpos_of_nonpos_of_nonneg _ (le_of_lt hz2_pos)
  -- Show t*(t-1)*z^t + t ≤ 0.
  obtain ⟨ht_lo, ht_hi⟩ := ht
  rcases lt_trichotomy t 0 with ht_neg | ht_zero | ht_pos
  · -- t < 0.  Substitute s := -t ∈ (0, 1/2].
    set s : ℝ := -t with hs_def
    have hs_pos : 0 < s := by change 0 < -t; linarith
    have hs_le : s ≤ 1 / 2 := by change -t ≤ 1 / 2; linarith
    have hs_nonneg : 0 ≤ s := le_of_lt hs_pos
    have h4s_bound : 1 + s ≤ (4 : ℝ) ^ s := one_add_le_four_rpow hs_nonneg hs_le
    have h_zs_ge : (4 : ℝ) ^ s ≤ z ^ s := by
      apply Real.rpow_le_rpow (by norm_num) (le_of_lt hz) hs_nonneg
    have h1ps_le : 1 + s ≤ z ^ s := le_trans h4s_bound h_zs_ge
    have hzs_pos : 0 < z ^ s := Real.rpow_pos_of_pos hz_pos s
    have hzs_ne : z ^ s ≠ 0 := ne_of_gt hzs_pos
    have ht_eq : t = -s := by change t = -(-t); ring
    have h_zt_eq : z ^ t = (z ^ s)⁻¹ := by
      rw [ht_eq, Real.rpow_neg (le_of_lt hz_pos)]
    -- Goal: t * (t - 1) * z^t + t ≤ 0
    -- Substitute t = -s and z^t = (z^s)⁻¹.
    rw [show z ^ t = (z ^ s)⁻¹ from h_zt_eq]
    rw [show t = -s from ht_eq]
    have key : (-s) * (-s - 1) * (z ^ s)⁻¹ + (-s) ≤ 0 := by
      have hgoal_eq : (-s) * (-s - 1) * (z ^ s)⁻¹ + (-s)
                    = (s * (s + 1) - s * z ^ s) / z ^ s := by
        field_simp; ring
      rw [hgoal_eq]
      apply div_nonpos_of_nonpos_of_nonneg _ (le_of_lt hzs_pos)
      have : s * (s + 1) ≤ s * z ^ s := by
        apply mul_le_mul_of_nonneg_left _ hs_nonneg
        linarith
      linarith
    exact key
  · -- t = 0.
    rw [ht_zero]; simp
  · -- 0 < t ≤ 1/2.
    have ht_pos_le : t ≤ 1/2 := ht_hi
    have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
    have h_4t_le : (4 : ℝ) ^ t ≤ z ^ t :=
      Real.rpow_le_rpow (by norm_num) (le_of_lt hz) ht_nonneg
    have h_main : 1 ≤ (4 : ℝ) ^ t * (1 - t) :=
      one_le_four_rpow_mul_one_sub ht_nonneg ht_pos_le
    -- Need: t*(t-1)*z^t + t ≤ 0, i.e., t * ((t-1)*z^t + 1) ≤ 0.
    rw [show (t * (t - 1) * z ^ t + t) = t * ((t - 1) * z ^ t + 1) from by ring]
    apply mul_nonpos_of_nonneg_of_nonpos ht_nonneg
    -- (t-1)*z^t + 1 ≤ 0 ⟺ 1 ≤ (1-t)*z^t.
    have h1_t_nonneg : 0 ≤ 1 - t := by linarith
    have step1 : (1 - t) * (4:ℝ)^t ≤ (1 - t) * z^t :=
      mul_le_mul_of_nonneg_left h_4t_le h1_t_nonneg
    have step2 : 1 ≤ (1 - t) * (4:ℝ)^t := by rw [mul_comm]; exact h_main
    have h_combined : 1 ≤ (1 - t) * z ^ t := le_trans step2 step1
    linarith

/-- **Renner `lem:rtconc`** (line 10468). For any `t ∈ [-1/2, 1/2]`, `rennerRt t` is
    concave on `[4, ∞)`.

    Proof sketch (Renner line 10473): `(d²/dz²) rennerRt t z = t(t-1) z^{t-2} +
    t/z²`. The condition `(d²/dz²) rennerRt t z ≤ 0` reduces to `z ≥ (1/(1-t))^{1/t}`.
    On `t ∈ [-1/2, 1/2]` this RHS is monotonically increasing in `t` and takes
    its maximum value `4` at `t = 1/2`. -/
theorem concaveOn_rennerRt_Ici_four {t : ℝ} (ht : t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    ConcaveOn ℝ (Set.Ici (4 : ℝ)) (rennerRt t) := by
  apply concaveOn_of_deriv2_nonpos (convex_Ici _) (continuousOn_rennerRt_Ici_four t)
  · -- DifferentiableOn ℝ (rennerRt t) (interior (Ici 4))
    rw [interior_Ici]
    intro z hz
    have hz_pos : 0 < z := lt_trans (by norm_num : (0:ℝ) < 4) hz
    exact ((InfoTheory.SmoothMinEntropy.hasDerivAt_rennerRt
        hz_pos).differentiableAt).differentiableWithinAt
  · -- DifferentiableOn ℝ (deriv (rennerRt t)) (interior (Ici 4))
    rw [interior_Ici]
    intro z hz
    have hz_pos : 0 < z := lt_trans (by norm_num : (0:ℝ) < 4) hz
    exact ((hasDerivAt_deriv_rennerRt hz_pos).differentiableAt).differentiableWithinAt
  · -- ∀ z ∈ interior (Ici 4), deriv^[2] (rennerRt t) z ≤ 0
    rw [interior_Ici]
    intro z hz
    exact deriv2_rennerRt_nonpos ht hz

/-- Helper: for `0 ≤ v`, `0 ≤ (v − 1) · exp v + 1`.

    This is the value at `v` of the auxiliary function `H1(v) := (v−1)·exp v + 1`
    whose derivative is `v · exp v ≥ 0` on `[0, ∞)`. Since `H1(0) = 0` and `H1`
    is monotone on `[0, ∞)`, we get `H1(v) ≥ 0`. -/
private lemma phi_aux_hp_nonneg {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ (v - 1) * Real.exp v + 1 := by
  set H1 : ℝ → ℝ := fun v => (v - 1) * Real.exp v + 1 with hH1_def
  have hderiv : ∀ x : ℝ, HasDerivAt H1 (x * Real.exp x) x := by
    intro x
    have h1 : HasDerivAt (fun v : ℝ => v - 1) 1 x :=
      (hasDerivAt_id x).sub_const 1
    have h2 : HasDerivAt Real.exp (Real.exp x) x := Real.hasDerivAt_exp x
    have h3 : HasDerivAt (fun v : ℝ => (v - 1) * Real.exp v)
              (1 * Real.exp x + (x - 1) * Real.exp x) x := h1.mul h2
    have h4 : HasDerivAt H1 (1 * Real.exp x + (x - 1) * Real.exp x) x :=
      h3.add_const 1
    convert h4 using 1
    ring
  have hcont : ContinuousOn H1 (Set.Ici (0:ℝ)) := fun x _ =>
    (hderiv x).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ H1 (interior (Set.Ici (0:ℝ))) := fun x _ =>
    (hderiv x).differentiableAt.differentiableWithinAt
  have hderiv_nn : ∀ x ∈ interior (Set.Ici (0:ℝ)), 0 ≤ deriv H1 x := by
    intro x hx
    rw [interior_Ici] at hx
    rw [(hderiv x).deriv]
    exact mul_nonneg hx.le (Real.exp_pos x).le
  have hmono : MonotoneOn H1 (Set.Ici (0:ℝ)) :=
    monotoneOn_of_deriv_nonneg (convex_Ici _) hcont hdiff hderiv_nn
  have h0 : H1 0 = 0 := by simp [H1]
  have hres := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hv) hv
  rw [h0] at hres
  exact hres

/-- Helper: for `0 ≤ v`, `0 ≤ (v − 2) · exp v + v + 2`.

    This is the value at `v` of `H(v) := (v−2)·exp v + v + 2`, whose derivative
    is `(v−1)·exp v + 1 = H1(v) ≥ 0` on `[0, ∞)` by `phi_aux_hp_nonneg`. Since
    `H(0) = 0`, monotonicity gives `H(v) ≥ 0`. -/
private lemma phi_aux_h_nonneg {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ (v - 2) * Real.exp v + v + 2 := by
  set H : ℝ → ℝ := fun v => (v - 2) * Real.exp v + v + 2 with hH_def
  have hderiv : ∀ x : ℝ, HasDerivAt H ((x - 1) * Real.exp x + 1) x := by
    intro x
    have h1 : HasDerivAt (fun v : ℝ => v - 2) 1 x :=
      (hasDerivAt_id x).sub_const 2
    have h2 : HasDerivAt Real.exp (Real.exp x) x := Real.hasDerivAt_exp x
    have h3 : HasDerivAt (fun v : ℝ => (v - 2) * Real.exp v)
              (1 * Real.exp x + (x - 2) * Real.exp x) x := h1.mul h2
    have hid : HasDerivAt (fun v : ℝ => v) 1 x := hasDerivAt_id x
    have h4 : HasDerivAt (fun v : ℝ => (v - 2) * Real.exp v + v)
              (1 * Real.exp x + (x - 2) * Real.exp x + 1) x := h3.add hid
    have h5 : HasDerivAt H (1 * Real.exp x + (x - 2) * Real.exp x + 1) x :=
      h4.add_const 2
    convert h5 using 1
    ring
  have hcont : ContinuousOn H (Set.Ici (0:ℝ)) := fun x _ =>
    (hderiv x).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ H (interior (Set.Ici (0:ℝ))) := fun x _ =>
    (hderiv x).differentiableAt.differentiableWithinAt
  have hderiv_nn : ∀ x ∈ interior (Set.Ici (0:ℝ)), 0 ≤ deriv H x := by
    intro x hx
    rw [interior_Ici] at hx
    rw [(hderiv x).deriv]
    exact phi_aux_hp_nonneg hx.le
  have hmono : MonotoneOn H (Set.Ici (0:ℝ)) :=
    monotoneOn_of_deriv_nonneg (convex_Ici _) hcont hdiff hderiv_nn
  have h0 : H 0 = 0 := by simp [H]
  have hres := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hv) hv
  rw [h0] at hres
  exact hres

/-- Helper: `g(v) := (exp v − v − 1) / v²` is monotone on `(0, ∞)`.

    By the quotient rule, `g'(v) = ((v−2)·exp v + v + 2) / v³`. The numerator
    is `≥ 0` on `[0, ∞)` by `phi_aux_h_nonneg`, and `v³ > 0` for `v > 0`. -/
private lemma phi_div_sq_monotoneOn :
    MonotoneOn (fun v : ℝ => (Real.exp v - v - 1) / v ^ 2) (Set.Ioi (0:ℝ)) := by
  set g : ℝ → ℝ := fun v => (Real.exp v - v - 1) / v ^ 2 with hg_def
  have hderiv : ∀ x ∈ Set.Ioi (0:ℝ),
      HasDerivAt g (((x - 2) * Real.exp x + x + 2) / x ^ 3) x := by
    intro x hx
    have hx_pos : 0 < x := hx
    have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    have hx2_pos : 0 < x ^ 2 := pow_pos hx_pos 2
    have hx2_ne : (x : ℝ) ^ 2 ≠ 0 := ne_of_gt hx2_pos
    -- φ(v) = exp v - v - 1 has derivative exp v - 1.
    have hphi : HasDerivAt (fun v : ℝ => Real.exp v - v - 1) (Real.exp x - 1) x := by
      have he : HasDerivAt Real.exp (Real.exp x) x := Real.hasDerivAt_exp x
      have hid : HasDerivAt (fun v : ℝ => v) 1 x := hasDerivAt_id x
      exact (he.sub hid).sub_const 1
    -- q(v) = v^2 has derivative 2 * v.
    have hq : HasDerivAt (fun v : ℝ => v ^ 2) (2 * x) x := by
      have h := hasDerivAt_pow 2 x
      simpa [pow_one] using h
    have hdiv := hphi.div hq hx2_ne
    -- hdiv : HasDerivAt (fun v => (exp v - v - 1) / v^2)
    --   (((exp x - 1) * x^2 - (exp x - x - 1) * (2 * x)) / (x^2)^2) x
    apply hdiv.congr_deriv
    have hx3_ne : x ^ 3 ≠ 0 := pow_ne_zero 3 hx_ne
    field_simp
    ring
  have hcont : ContinuousOn g (Set.Ioi (0:ℝ)) := fun x hx =>
    (hderiv x hx).continuousAt.continuousWithinAt
  have hint : interior (Set.Ioi (0:ℝ)) = Set.Ioi (0:ℝ) := interior_Ioi
  have hdiff : DifferentiableOn ℝ g (interior (Set.Ioi (0:ℝ))) := by
    rw [hint]
    intro x hx
    exact (hderiv x hx).differentiableAt.differentiableWithinAt
  have hderiv_nn : ∀ x ∈ interior (Set.Ioi (0:ℝ)), 0 ≤ deriv g x := by
    intro x hx
    rw [hint] at hx
    rw [(hderiv x hx).deriv]
    have hx_pos : 0 < x := hx
    have hx3_pos : 0 < x ^ 3 := pow_pos hx_pos 3
    have hnum : 0 ≤ (x - 2) * Real.exp x + x + 2 := phi_aux_h_nonneg hx_pos.le
    exact div_nonneg hnum hx3_pos.le
  exact monotoneOn_of_deriv_nonneg (convex_Ioi _) hcont hdiff hderiv_nn

/-- Auxiliary one-variable bound: for `|v| ≤ Real.log 2`,
    `Real.exp v − v − 1 ≤ ((1 − Real.log 2) / (Real.log 2)^2) · v^2`.

    This is the substantive analytic content of `rennerRt_le_mul_log_sq_mul_sq`. The
    proof goes via the auxiliary function `g(v) := (Real.exp v − v − 1) / v²`,
    which can be shown monotone increasing on `ℝ` with limit `1/2` at `0`; the
    maximum on `[−log 2, log 2]` is attained at `v = log 2` with value
    `(1 − log 2) / (log 2)²`. -/
lemma exp_sub_sub_one_le_mul_sq_of_pos_of_le_log_two {v : ℝ} (hv0 : 0 < v) (hv : v ≤ Real.log 2) :
    Real.exp v - v - 1 ≤ ((1 - Real.log 2) / (Real.log 2) ^ 2) * v ^ 2 := by
  set L : ℝ := Real.log 2 with hL_def
  have hL_pos : 0 < L := Real.log_pos (by norm_num)
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  have hL2_pos : 0 < L ^ 2 := pow_pos hL_pos 2
  have hL2_ne : L ^ 2 ≠ 0 := ne_of_gt hL2_pos
  have hexp_L : Real.exp L = 2 := Real.exp_log (by norm_num : (0:ℝ) < 2)
  have hv2_pos : 0 < v ^ 2 := pow_pos hv0 2
  have hv2_ne : v ^ 2 ≠ 0 := ne_of_gt hv2_pos
  -- g(v) ≤ g(L) by monotonicity.
  have hv_mem : v ∈ Set.Ioi (0:ℝ) := hv0
  have hL_mem : L ∈ Set.Ioi (0:ℝ) := hL_pos
  have hg_le : (Real.exp v - v - 1) / v ^ 2 ≤ (Real.exp L - L - 1) / L ^ 2 :=
    phi_div_sq_monotoneOn hv_mem hL_mem hv
  -- Compute g(L) = (1 - L) / L^2.
  have hgL : (Real.exp L - L - 1) / L ^ 2 = (1 - L) / L ^ 2 := by
    rw [hexp_L]; ring_nf
  rw [hgL] at hg_le
  -- Multiply by v^2.
  calc Real.exp v - v - 1
      = ((Real.exp v - v - 1) / v ^ 2) * v ^ 2 := by
        rw [div_mul_cancel₀ _ hv2_ne]
    _ ≤ ((1 - L) / L ^ 2) * v ^ 2 :=
        mul_le_mul_of_nonneg_right hg_le hv2_pos.le

/-- For `v ≤ 0`, `Real.exp v - v - 1 ≤ v² / 2`.

    Proof: let `h v := v²/2 - (exp v - v - 1)`. Then `h 0 = 0`, and
    `h'(v) = v - exp v + 1 ≤ 0` for `v < 0` by `Real.add_one_le_exp`. Hence
    `h` is antitone on `Iic 0`, giving `h 0 ≤ h v` for `v ≤ 0`. -/
lemma exp_sub_sub_one_le_sq_div_two_of_nonpos {v : ℝ} (hv : v ≤ 0) :
    Real.exp v - v - 1 ≤ v ^ 2 / 2 := by
  -- Define `h x := x²/2 - (exp x - x - 1)` and show it is antitone on `Iic 0`.
  set h : ℝ → ℝ := fun x => x ^ 2 / 2 - (Real.exp x - x - 1) with hdef
  have hcont : ContinuousOn h (Set.Iic (0 : ℝ)) := by
    change ContinuousOn (fun x : ℝ => x ^ 2 / 2 - (Real.exp x - x - 1)) _
    fun_prop
  have hdiff : DifferentiableOn ℝ h (interior (Set.Iic (0 : ℝ))) := by
    change DifferentiableOn ℝ (fun x : ℝ => x ^ 2 / 2 - (Real.exp x - x - 1)) _
    fun_prop
  have hderiv_nonpos : ∀ x ∈ interior (Set.Iic (0 : ℝ)), deriv h x ≤ 0 := by
    rw [interior_Iic]
    intro x hx
    have hxlt : x < 0 := hx
    -- `h'(x) = x - exp x + 1`.
    have e2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
      have e1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x ^ (2 - 1)) x := by
        simpa using hasDerivAt_pow 2 x
      have := e1.div_const 2
      apply this.congr_deriv
      ring
    have e3 : HasDerivAt Real.exp (Real.exp x) x := Real.hasDerivAt_exp x
    have e4 : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
    have e5 : HasDerivAt (fun y : ℝ => Real.exp y - y - 1) (Real.exp x - 1) x :=
      (e3.sub e4).sub_const 1
    have e6 : HasDerivAt h (x - (Real.exp x - 1)) x := e2.sub e5
    have hd : deriv h x = x - Real.exp x + 1 := by
      rw [e6.deriv]; ring
    rw [hd]
    have := Real.add_one_le_exp x
    linarith
  have hAnti : AntitoneOn h (Set.Iic (0 : ℝ)) :=
    antitoneOn_of_deriv_nonpos (convex_Iic 0) hcont hdiff hderiv_nonpos
  have h0_le_hv : h 0 ≤ h v := hAnti hv Set.self_mem_Iic hv
  have h0_eq : h 0 = 0 := by
    change (0 : ℝ) ^ 2 / 2 - (Real.exp 0 - 0 - 1) = 0
    rw [Real.exp_zero]; ring
  have hv_eq : h v = v ^ 2 / 2 - (Real.exp v - v - 1) := rfl
  linarith [h0_le_hv, h0_eq, hv_eq]

/-- Numerical inequality: `1/2 ≤ (1 - log 2) / (log 2)²`.

    Equivalent to `(log 2)² + 2 log 2 ≤ 2`. With `log 2 ≈ 0.693`, the left side
    is about `0.48 + 1.386 = 1.867 < 2`. -/
lemma half_le_inv_log_two_sq_mul_one_sub_log_two :
    (1 : ℝ) / 2 ≤ (1 - Real.log 2) / (Real.log 2) ^ 2 := by
  have hpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsq_pos : (0 : ℝ) < (Real.log 2) ^ 2 := pow_pos hpos 2
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hsq_pos]
  have hlt := Real.log_two_lt_d9
  have hgt := Real.log_two_gt_d9
  nlinarith [hlt, hgt, sq_nonneg (Real.log 2)]

lemma exp_sub_sub_one_le_mul_sq_of_neg {v : ℝ} (hv0 : v < 0) :
    Real.exp v - v - 1 ≤ ((1 - Real.log 2) / (Real.log 2) ^ 2) * v ^ 2 := by
  have H1 : Real.exp v - v - 1 ≤ v ^ 2 / 2 := exp_sub_sub_one_le_sq_div_two_of_nonpos hv0.le
  have H2 : (1 : ℝ) / 2 ≤ (1 - Real.log 2) / (Real.log 2) ^ 2 :=
    half_le_inv_log_two_sq_mul_one_sub_log_two
  have hsq : (0 : ℝ) ≤ v ^ 2 := sq_nonneg v
  have step : v ^ 2 / 2 ≤ ((1 - Real.log 2) / (Real.log 2) ^ 2) * v ^ 2 := by
    rw [show v ^ 2 / 2 = (1 / 2) * v ^ 2 by ring]
    exact mul_le_mul_of_nonneg_right H2 hsq
  linarith

lemma exp_sub_sub_one_le_mul_sq_of_abs_le_log_two {v : ℝ} (hv : |v| ≤ Real.log 2) :
    Real.exp v - v - 1 ≤ ((1 - Real.log 2) / (Real.log 2) ^ 2) * v ^ 2 := by
  rcases lt_trichotomy v 0 with hv_neg | hv_zero | hv_pos
  · exact exp_sub_sub_one_le_mul_sq_of_neg hv_neg
  · subst hv_zero; simp
  · have hvle : v ≤ Real.log 2 := (abs_le.mp hv).2
    exact exp_sub_sub_one_le_mul_sq_of_pos_of_le_log_two hv_pos hvle

/-- **Renner `lem:rtbound`** (line 10487, statement corrected for the
    `log` vs `log₂` translation between Renner's appendix and Mathlib). For
    `z > 1` and `|t| ≤ Real.log 2 / Real.log z`,
    `rennerRt t z ≤ ((1 − log 2) / (log 2)²) · (log z)² · t²`.

    Proof sketch (Renner line 10495): set `v = t · ln z`. Then
    `rennerRt t z = e^v − v − 1`. The hypothesis `|t| ≤ log 2 / log z` gives
    `|v| ≤ log 2`. Apply `exp_sub_sub_one_le_mul_sq_of_abs_le_log_two` to get
    `rennerRt t z ≤ ((1 − log 2)/(log 2)²) · v²`, and `v² = (log z)² · t²`. -/
theorem rennerRt_le_mul_log_sq_mul_sq {t z : ℝ} (hz_pos : 1 < z)
    (ht_lo : -(Real.log 2 / Real.log z) ≤ t)
    (ht_hi : t ≤ Real.log 2 / Real.log z) :
    rennerRt t z ≤ ((1 - Real.log 2) / (Real.log 2) ^ 2) * (Real.log z) ^ 2 * t ^ 2 := by
  have hz_ppos : (0 : ℝ) < z := lt_trans zero_lt_one hz_pos
  have hlogz_pos : 0 < Real.log z := Real.log_pos hz_pos
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Step 1: rennerRt t z = exp(t * log z) - t * log z - 1.
  have hrt_eq : rennerRt t z = Real.exp (t * Real.log z) - t * Real.log z - 1 := by
    unfold rennerRt
    rw [Real.rpow_def_of_pos hz_ppos, mul_comm (Real.log z) t]
  -- Step 2: |t * log z| ≤ log 2.
  set v : ℝ := t * Real.log z with hv_def
  have ht_abs : |t| ≤ Real.log 2 / Real.log z := abs_le.mpr ⟨ht_lo, ht_hi⟩
  have hv_abs : |v| ≤ Real.log 2 := by
    rw [hv_def, abs_mul, abs_of_pos hlogz_pos]
    have := mul_le_mul_of_nonneg_right ht_abs (le_of_lt hlogz_pos)
    rwa [div_mul_cancel₀ _ (ne_of_gt hlogz_pos)] at this
  -- Step 3: apply the helper.
  have hphi := exp_sub_sub_one_le_mul_sq_of_abs_le_log_two hv_abs
  -- Step 4: v² = t² * (log z)².
  have hv_sq : v ^ 2 = t ^ 2 * (Real.log z) ^ 2 := by
    rw [hv_def]; ring
  rw [hrt_eq]
  calc Real.exp v - v - 1
      ≤ ((1 - Real.log 2) / (Real.log 2) ^ 2) * v ^ 2 := hphi
    _ = ((1 - Real.log 2) / (Real.log 2) ^ 2) * (t ^ 2 * (Real.log z) ^ 2) := by rw [hv_sq]
    _ = ((1 - Real.log 2) / (Real.log 2) ^ 2) * (Real.log z) ^ 2 * t ^ 2 := by ring

end InfoTheory.SmoothMinEntropy

end -- noncomputable section
