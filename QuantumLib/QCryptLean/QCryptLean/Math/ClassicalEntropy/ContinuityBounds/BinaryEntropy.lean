import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import QCryptLean.Math.ClassicalEntropy.Entropy

/-!
# Binary Entropy Bounds — small-argument estimates and concavity tools

Auxiliary estimates for binary entropy that are used in entropy continuity and
BB84 applications. The main ingredients are a small-argument upper bound,
absorption of dimensional `q log d` terms into binary entropy, and strict
concavity of `binEntropy x + x^2` on `[1/2, 1]`.

## Main statements
- `binaryEntropy_le_mul_neg_log_add_two`: `H(x) ≤ x * (-log x + 2)` for `0 < x < 1 / 2`
- `mul_log_le_binaryEntropy_of_le_inv`: `q * log d ≤ H(q)` when `q ≤ 1 / d`
- `strictConcaveOn_binEntropy_add_sq`: strict concavity of `Real.binEntropy x + x^2` on `[1/2, 1]`
-/

noncomputable section

namespace Math.ClassicalEntropy

open Math.ClassicalEntropy Filter Topology

private lemma aux_function_positive (y : ℝ) (hy_gt_half : 1 / 2 < y) (hy_lt_one : y < 1) :
    0 < y * Real.log y - 2 * y + 2 := by
  have h_at_one : (1 : ℝ) * Real.log 1 - 2 * 1 + 2 = 0 := by
    simp [Real.log_one]
  have hy_pos : 0 < y := by linarith
  have h_log_neg : Real.log y < 0 := by
    apply Real.log_neg
    · exact hy_pos
    · exact hy_lt_one
  set h : ℝ → ℝ := fun x => x * Real.log x - 2 * x + 2 with h_def
  have hy_mem : y ∈ Set.Icc (1/2 : ℝ) 1 := ⟨le_of_lt hy_gt_half, le_of_lt hy_lt_one⟩
  have h_one_mem : (1 : ℝ) ∈ Set.Icc (1/2 : ℝ) 1 := by norm_num
  have h_cont : ContinuousOn h (Set.Icc (1/2 : ℝ) 1) := by
    rw [h_def]
    refine ContinuousOn.add ?_ continuousOn_const
    refine ContinuousOn.sub ?_ (continuousOn_const.mul continuousOn_id)
    apply ContinuousOn.mul continuousOn_id
    apply ContinuousOn.mono Real.continuousOn_log
    intro x hx
    have : (0 : ℝ) < x := calc
      (0 : ℝ) < 1 / 2 := by norm_num
      _ ≤ x := hx.1
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
  have h_deriv_neg : ∀ x ∈ interior (Set.Icc (1/2 : ℝ) 1), deriv h x < 0 := by
    intro x hx
    rw [interior_Icc] at hx
    have hx_pos : 0 < x := by linarith [hx.1]
    have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    have h_deriv : deriv h x = Real.log x - 1 := by
      have deriv_xlogx : deriv (fun t => t * Real.log t) x = Real.log x + 1 := by
        have eq : deriv (fun t => t * Real.log t) x =
            deriv (fun t => t) x * Real.log x + x * deriv Real.log x := by
          exact deriv_mul differentiableAt_id (Real.differentiableAt_log hx_ne)
        simp only [deriv_id'', Real.deriv_log] at eq
        calc
          deriv (fun t => t * Real.log t) x = 1 * Real.log x + x * x⁻¹ := eq
          _ = Real.log x + 1 := by field_simp
      have deriv_2x : deriv (fun t => (2 : ℝ) * t) x = 2 := by
        have eq : deriv (fun t => (2 : ℝ) * t) x = 2 * deriv (fun t => t) x := by
          exact deriv_const_mul (c := (2 : ℝ)) (d := fun t => t) (x := x) differentiableAt_id
        rw [eq, deriv_id'', mul_one]
      calc
        deriv h x = deriv (fun t => t * Real.log t - 2 * t + 2) x := by rw [h_def]
        _ = deriv (fun t => (t * Real.log t - 2 * t) + 2) x := rfl
        _ = deriv (fun t => t * Real.log t - 2 * t) x + deriv (fun _ : ℝ => (2 : ℝ)) x := by
            apply deriv_add
            · apply DifferentiableAt.sub
              · exact differentiableAt_id.mul (Real.differentiableAt_log hx_ne)
              · exact differentiableAt_id.const_mul 2
            · exact differentiableAt_const 2
        _ = deriv (fun t => t * Real.log t - 2 * t) x + 0 := by rw [deriv_const]
        _ = deriv (fun t => t * Real.log t) x - deriv (fun t => 2 * t) x := by
            rw [add_zero]
            apply deriv_sub
            · exact differentiableAt_id.mul (Real.differentiableAt_log hx_ne)
            · exact differentiableAt_id.const_mul 2
        _ = (Real.log x + 1) - 2 := by rw [deriv_xlogx, deriv_2x]
        _ = Real.log x - 1 := by ring
    rw [h_deriv]
    have : Real.log x < 0 := Real.log_neg hx_pos hx.2
    linarith
  have h_anti : StrictAntiOn h (Set.Icc (1/2 : ℝ) 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc (1/2 : ℝ) 1) h_cont h_deriv_neg
  have h_gt : h y > h 1 := h_anti hy_mem h_one_mem hy_lt_one
  change 0 < h y
  rw [h_def] at h_gt
  calc
    0 = 1 * Real.log 1 - 2 * 1 + 2 := h_at_one.symm
    _ < h y := h_gt

private lemma aux_bound_nonneg (x : ℝ) (hx_pos : 0 < x) (hx_small : x < 1 / 2) :
    0 ≤ 2 * x + (1 - x) * Real.log (1 - x) := by
  have h_one_sub_pos : 0 < 1 - x := by linarith
  have h_one_sub_ge_half : 1 / 2 < 1 - x := by linarith
  have h_one_sub_lt_one : 1 - x < 1 := by linarith
  have h_log_lb : -Real.log 2 < Real.log (1 - x) := by
    have h1 : (1 : ℝ) / 2 < 1 - x := h_one_sub_ge_half
    have h2 : Real.log ((1 : ℝ) / 2) < Real.log (1 - x) := by
      apply Real.log_lt_log
      · norm_num
      · exact h1
    have h3 : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
      rw [Real.log_div one_ne_zero two_ne_zero, Real.log_one, zero_sub]
    rw [h3] at h2
    exact h2
  have h_prod_lb : -(1 - x) * Real.log 2 < (1 - x) * Real.log (1 - x) := by
    have h : -(1 - x) * Real.log 2 = (1 - x) * (-Real.log 2) := by ring
    rw [h]
    apply mul_lt_mul_of_pos_left h_log_lb h_one_sub_pos
  let y := 1 - x
  have hy_def : y = 1 - x := rfl
  have hy_pos : 0 < y := h_one_sub_pos
  have hy_gt_half : 1 / 2 < y := h_one_sub_ge_half
  have hy_lt_one : y < 1 := h_one_sub_lt_one
  have h_rewrite : 2 * x + (1 - x) * Real.log (1 - x) = 2 * (1 - y) + y * Real.log y := by
    rw [hy_def]
    ring
  rw [h_rewrite]
  have h_rearrange : 2 * (1 - y) + y * Real.log y = 2 + y * (Real.log y - 2) := by ring
  rw [h_rearrange]
  suffices h : y * (2 - Real.log y) < 2 by
    have h_eq : 2 + y * (Real.log y - 2) = 2 - y * (2 - Real.log y) := by ring
    rw [h_eq]
    linarith
  have h_two_y : 2 * y - y * Real.log y < 2 := by
    have h_ineq := aux_function_positive y hy_gt_half hy_lt_one
    linarith
  calc
    y * (2 - Real.log y) = 2 * y - y * Real.log y := by ring
    _ < 2 := h_two_y

/-- For small `x > 0`, binary entropy satisfies `H(x) ≤ x * (-log x + 2)`. -/
lemma binaryEntropy_le_mul_neg_log_add_two (x : ℝ) (hx_pos : 0 < x) (hx_small : x < 1 / 2) :
    binaryEntropy x ≤ x * (-Real.log x + 2) := by
  unfold binaryEntropy entropyTerm
  have hx_ne : x ≠ 0 := ne_of_gt hx_pos
  simp only [hx_ne, ↓reduceIte]
  have h_one_sub_pos : 0 < 1 - x := by linarith
  have h_one_sub_ne : 1 - x ≠ 0 := ne_of_gt h_one_sub_pos
  simp only [h_one_sub_ne, ↓reduceIte]
  suffices h : -(1 - x) * Real.log (1 - x) ≤ 2 * x by
    calc
      -x * Real.log x + (-(1 - x) * Real.log (1 - x)) ≤ -x * Real.log x + 2 * x := by
        linarith
      _ = x * (-Real.log x + 2) := by ring
  have h_aux := aux_bound_nonneg x hx_pos hx_small
  linarith

/-- If `q` is at most `1 / d`, then the dimensional term `q log d` is absorbed by
    binary entropy. -/
lemma mul_log_le_binaryEntropy_of_le_inv (d q : ℝ)
    (hd_pos : 0 < d) (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1) (hq_le_inv : q ≤ 1 / d) :
    q * Real.log d ≤ binaryEntropy q := by
  by_cases hq_zero : q = 0
  · simp [hq_zero, binaryEntropy_zero]
  by_cases hd_le_one : d ≤ 1
  · have hlog_nonpos : Real.log d ≤ 0 := Real.log_nonpos hd_pos.le hd_le_one
    have hleft_nonpos : q * Real.log d ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hq_nonneg hlog_nonpos
    exact le_trans hleft_nonpos (binaryEntropy_nonneg q hq_nonneg hq_le_one)
  · have hq_pos : 0 < q := lt_of_le_of_ne hq_nonneg (Ne.symm hq_zero)
    have hd_ne : d ≠ 0 := ne_of_gt hd_pos
    have hqd_le_one : q * d ≤ 1 := by
      calc
        q * d ≤ (1 / d) * d := mul_le_mul_of_nonneg_right hq_le_inv hd_pos.le
        _ = 1 := by field_simp [hd_ne]
    have hlog_qd_nonpos : Real.log (q * d) ≤ 0 := by
      apply Real.log_nonpos
      · positivity
      · exact hqd_le_one
    have hlog_sum_nonpos : Real.log q + Real.log d ≤ 0 := by
      rw [Real.log_mul (ne_of_gt hq_pos) hd_ne] at hlog_qd_nonpos
      exact hlog_qd_nonpos
    have hmain : q * Real.log d ≤ -(q * Real.log q) := by
      have hmul : q * (Real.log q + Real.log d) ≤ q * 0 :=
        mul_le_mul_of_nonneg_left hlog_sum_nonpos hq_nonneg
      linarith [hmul]
    have hterm_le : -(q * Real.log q) ≤ binaryEntropy q := by
      unfold binaryEntropy
      have h_other_nonneg : 0 ≤ entropyTerm (1 - q) := by
        apply entropyTerm_nonneg
        · linarith
        · linarith
      rw [entropyTerm_eq_neg_mul_log q]
      linarith
    exact le_trans hmain hterm_le

/-- If `0 ≤ q ≤ 1 / d`, then the `q log d` term is absorbed by binary entropy. -/
lemma log_le_one_sub_mul_log_add_binaryEntropy {d : ℕ} [NeZero d] {q : ℝ}
    (hq_nonneg : 0 ≤ q) (hq_le_inv : q ≤ 1 / (d : ℝ)) :
    Real.log d ≤ (1 - q) * Real.log d + binaryEntropy q := by
  have hd_pos : 0 < (d : ℝ) := by
    exact Nat.cast_pos.mpr (NeZero.pos d)
  have hd_ge_one : (1 : ℝ) ≤ d := by
    exact_mod_cast Nat.succ_le_of_lt (NeZero.pos d)
  have hq_le_one : q ≤ 1 := by
    have hd_inv_le_one : 1 / (d : ℝ) ≤ 1 := by
      exact (one_div_le hd_pos zero_lt_one).2 (by simpa using hd_ge_one)
    exact le_trans hq_le_inv hd_inv_le_one
  have hq_log_le : q * Real.log d ≤ binaryEntropy q :=
    mul_log_le_binaryEntropy_of_le_inv _ _ hd_pos hq_nonneg hq_le_one hq_le_inv
  calc
    Real.log d = (1 - q) * Real.log d + q * Real.log d := by ring
    _ ≤ (1 - q) * Real.log d + binaryEntropy q := by linarith

private lemma prod_lt_quarter (t : ℝ) (ht_ne_half : t ≠ 1 / 2) :
    t * (1 - t) < 1 / 4 := by
  have h : t * (1 - t) = 1 / 4 - (t - 1 / 2) ^ 2 := by ring
  rw [h]
  have ht_sub_ne_zero : t - 1 / 2 ≠ 0 := sub_ne_zero.mpr ht_ne_half
  have hsq_pos : (t - 1 / 2) ^ 2 > 0 := sq_pos_of_ne_zero ht_sub_ne_zero
  linarith

private lemma inv_prod_gt_four (t : ℝ) (ht_lower : 1 / 2 < t) (ht_upper : t < 1) :
    (t * (1 - t))⁻¹ > 4 := by
  have ht_pos : 0 < t := by linarith
  have h1mt_pos : 0 < 1 - t := by linarith
  have hprod_pos : 0 < t * (1 - t) := mul_pos ht_pos h1mt_pos
  have hprod_lt : t * (1 - t) < 1 / 4 := prod_lt_quarter t (by linarith [ht_lower])
  have h4_eq : (4 : ℝ) = (1 / 4)⁻¹ := by norm_num
  rw [h4_eq]
  have h_quarter_pos : (0 : ℝ) < 1 / 4 := by norm_num
  have h_mem1 : t * (1 - t) ∈ Set.Ioi (0 : ℝ) := hprod_pos
  have h_mem2 : (1 / 4 : ℝ) ∈ Set.Ioi (0 : ℝ) := h_quarter_pos
  exact inv_strictAntiOn h_mem1 h_mem2 hprod_lt

/-- `x ↦ Real.binEntropy x + x^2` is strictly concave on `[1/2, 1]`. -/
lemma strictConcaveOn_binEntropy_add_sq :
    StrictConcaveOn ℝ (Set.Icc (1 / 2 : ℝ) 1) (fun x => Real.binEntropy x + x ^ 2) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc (1 / 2) 1)
  · exact Continuous.continuousOn (Real.binEntropy_continuous.add (continuous_pow 2))
  · intro t ht
    rw [interior_Icc] at ht
    have ht_lower : 1 / 2 < t := ht.1
    have ht_upper : t < 1 := ht.2
    have ht_ne_zero : t ≠ 0 := by linarith
    have ht_ne_one : t ≠ 1 := by linarith
    have ht_pos : 0 < t := by linarith
    have h1mt_pos : 0 < 1 - t := by linarith
    have hprod_pos : 0 < t * (1 - t) := mul_pos ht_pos h1mt_pos
    have hprod_lt : t * (1 - t) < 1 / 4 := prod_lt_quarter t (by linarith [ht_lower])
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    have h_deriv2_binEntropy : (deriv^[2] Real.binEntropy) t = -1 / (t * (1 - t)) :=
      Real.deriv2_binEntropy
    have h_deriv2_sq : (deriv^[2] fun x : ℝ => x ^ 2) t = 2 := by
      have h := iter_deriv_pow (𝕜 := ℝ) 2 t 2
      simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_ofNat,
        Nat.sub_self, pow_zero, Nat.cast_one] at h
      convert h using 1
      norm_num
    have h_diff_at_binEntropy : DifferentiableAt ℝ Real.binEntropy t :=
      Real.differentiableAt_binEntropy ht_ne_zero ht_ne_one
    have h_diff_at_sq : DifferentiableAt ℝ (fun x : ℝ => x ^ 2) t :=
      (differentiable_pow 2).differentiableAt
    have h_diff_deriv_binEntropy : DifferentiableAt ℝ (deriv Real.binEntropy) t := by
      have h_eq : deriv Real.binEntropy = fun x => Real.log (1 - x) - Real.log x := by
        ext x
        exact Real.deriv_binEntropy x
      rw [h_eq]
      apply DifferentiableAt.sub
      · exact (Real.differentiableAt_log h1mt_pos.ne').comp t
          (by exact DifferentiableAt.const_sub differentiableAt_id 1)
      · exact Real.differentiableAt_log ht_pos.ne'
    have h_diff_deriv_sq : DifferentiableAt ℝ (deriv fun x : ℝ => x ^ 2) t := by
      have h_eq : deriv (fun x : ℝ => x ^ 2) = fun x : ℝ => 2 * x := by
        ext x
        have h := iter_deriv_pow (𝕜 := ℝ) 2 x 1
        simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_ofNat,
          Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id] at h
        convert h using 1
        ring
      rw [h_eq]
      exact DifferentiableAt.const_mul differentiableAt_id 2
    have h_deriv2_sum : deriv (deriv fun x => Real.binEntropy x + x ^ 2) t =
        deriv (deriv Real.binEntropy) t + deriv (deriv fun x : ℝ => x ^ 2) t := by
      have h_eq : ∀ᶠ x in nhds t, deriv (fun y => Real.binEntropy y + y ^ 2) x =
          deriv Real.binEntropy x + deriv (fun y : ℝ => y ^ 2) x := by
        filter_upwards [eventually_ne_nhds (show t ≠ 0 from ht_ne_zero),
          eventually_ne_nhds (show t ≠ 1 from ht_ne_one)] with x hx0 hx1
        exact deriv_add (Real.differentiableAt_binEntropy hx0 hx1)
          (differentiable_pow 2).differentiableAt
      have h_deriv_eq := Filter.EventuallyEq.deriv_eq h_eq
      rw [h_deriv_eq]
      exact deriv_add h_diff_deriv_binEntropy h_diff_deriv_sq
    have h_iter_binEntropy : (deriv^[2] Real.binEntropy) t = deriv (deriv Real.binEntropy) t := rfl
    have h_iter_sq : (deriv^[2] fun x : ℝ => x ^ 2) t = deriv (deriv fun x : ℝ => x ^ 2) t := rfl
    rw [h_deriv2_sum, ← h_iter_binEntropy, ← h_iter_sq, h_deriv2_binEntropy, h_deriv2_sq]
    have h_inv_gt : (t * (1 - t))⁻¹ > 4 := inv_prod_gt_four t ht_lower ht_upper
    have h_neg_div : -1 / (t * (1 - t)) = -(t * (1 - t))⁻¹ := by ring
    rw [h_neg_div]
    linarith

end Math.ClassicalEntropy

end
