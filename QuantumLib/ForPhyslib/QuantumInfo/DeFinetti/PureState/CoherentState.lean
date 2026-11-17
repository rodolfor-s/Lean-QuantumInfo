import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! # Binomial coefficient ratios for coherent-state bounds -/



noncomputable section

open scoped BigOperators

namespace Quantum.DeFinetti.PureState

/-- The ratio of binomial coefficients equals a falling product:
    C(n-k+d-1,d-1) / C(n+d-1,d-1) = ∏_{i=0}^{d-2} (n-k+1+i)/(n+1+i).

    Each factor in the numerator decreases by k relative to the denominator,
    giving an explicit expression suitable for bounding. -/
lemma choose_ratio_eq_prod (d n k : ℕ) (hd : 1 ≤ d) (hk : k ≤ n) :
    (Nat.choose (n - k + d - 1) (d - 1) : ℝ) / Nat.choose (n + d - 1) (d - 1) =
      (Finset.range (d - 1)).prod (fun i => ((n - k + 1 + i : ℝ) / (n + 1 + i))) := by
  obtain ⟨r, rfl⟩ : ∃ r, d = r + 1 := ⟨d - 1, by omega⟩
  simp only [show r + 1 - 1 = r from by omega]
  induction r with
  | zero => simp
  | succ r ih =>
    have h1 : n - k + (r + 1 + 1) - 1 = (n - k + r + 1) := by omega
    have h2 : n + (r + 1 + 1) - 1 = (n + r + 1) := by omega
    rw [h1, h2, Finset.prod_range_succ]
    have ih' := ih (by omega)
    have h3 : n - k + (r + 1) - 1 = n - k + r := by omega
    have h4 : n + (r + 1) - 1 = n + r := by omega
    rw [h3, h4] at ih'
    rw [← ih']
    -- Pascal's rule `(m+1)·C(m, r) = C(m+1, r+1)·(r+1)`, solved for `C(m+1, r+1)` over `ℝ`,
    -- in the numerator (`m = n-k+r`) and the denominator (`m = n+r`)
    have hr : ((r + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr r.succ_ne_zero
    have eqA : (↑((n - k + r + 1).choose (r + 1)) : ℝ) =
        ↑(n - k + r + 1) * ↑((n - k + r).choose r) / ↑(r + 1 : ℕ) :=
      eq_div_of_mul_eq hr (by exact_mod_cast (Nat.add_one_mul_choose_eq (n - k + r) r).symm)
    have eqB : (↑((n + r + 1).choose (r + 1)) : ℝ) =
        ↑(n + r + 1) * ↑((n + r).choose r) / ↑(r + 1 : ℕ) :=
      eq_div_of_mul_eq hr (by exact_mod_cast (Nat.add_one_mul_choose_eq (n + r) r).symm)
    have cast1 : (↑(n - k + r + 1) : ℝ) = ↑n - ↑k + 1 + ↑r := by
      rw [show (n - k + r + 1 : ℕ) = (n - k) + (r + 1) from by omega,
          Nat.cast_add, Nat.cast_sub hk]; push_cast; ring
    have cast2 : (↑(n + r + 1) : ℝ) = ↑n + 1 + ↑r := by push_cast; ring
    -- the common `1/(r+1)` cancels, leaving the previous ratio times the new factor
    rw [eqA, eqB, div_div_div_cancel_right₀ hr, mul_div_mul_comm, mul_comm, cast1, cast2]

/-- Each factor in the product is at least (n-k+1)/(n+1).
    Since (n-k+1+i)/(n+1+i) is increasing in i (for fixed n,k), the minimum
    is attained at i=0. -/
lemma ratio_factor_lower_bound (n k i : ℕ) (hk : k ≤ n) :
    (n - k + 1 : ℝ) / (n + 1) ≤ (n - k + 1 + i : ℝ) / (n + 1 + i) := by
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < ↑n + 1)
    (by positivity : (0:ℝ) < ↑n + 1 + ↑i)]
  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg' i
  have hk' : (k : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hk
  nlinarith


/-- **Dimension ratio bound** (CKMR, used in Theorem II.2 proof).
    1 - dk/n ≤ C(n-k+d-1,d-1) / C(n+d-1,d-1).

    Proof: Each of the (d-1) factors is ≥ (n-k+1)/(n+1) = 1 - k/(n+1),
    so the product is ≥ (1 - k/(n+1))^{d-1} ≥ 1 - (d-1)k/(n+1) ≥ 1 - (d-1)k/n ≥ 1 - dk/n. -/
theorem dim_ratio_bound (d n k : ℕ) (hd : 1 ≤ d) (hn : 0 < n) (hk : k ≤ n) :
    1 - (d * k : ℝ) / n ≤
      (Nat.choose (n - k + d - 1) (d - 1) : ℝ) / Nat.choose (n + d - 1) (d - 1) := by
  -- The proof shows 1 - (d-1)k/n ≤ ratio, then relaxes to 1 - dk/n ≤ ratio
  suffices h : 1 - ((d - 1) * k : ℝ) / n ≤
      (Nat.choose (n - k + d - 1) (d - 1) : ℝ) / Nat.choose (n + d - 1) (d - 1) by
    have hk_nn : (0 : ℝ) ≤ (↑k : ℝ) := Nat.cast_nonneg k
    have : (↑d - 1 : ℝ) * ↑k ≤ (↑d : ℝ) * ↑k :=
      mul_le_mul_of_nonneg_right (sub_le_self _ zero_le_one) hk_nn
    have : (↑d - 1 : ℝ) * ↑k / (↑n : ℝ) ≤ ↑d * ↑k / ↑n :=
      div_le_div_of_nonneg_right this (Nat.cast_nonneg n)
    linarith
  rw [choose_ratio_eq_prod d n k hd hk]
  set x := (↑n - ↑k + 1 : ℝ) / (↑n + 1) with hx_def
  have hn_pos : (0 : ℝ) < ↑n + 1 := by positivity
  have hk_cast : (↑k : ℝ) ≤ ↑n := Nat.cast_le.mpr hk
  have hx_nonneg : 0 ≤ x := div_nonneg (by linarith only [hk_cast]) hn_pos.le
  -- Step 1: Product ≥ x^(d-1) since each factor ≥ x
  have hprod_lb : x ^ (d - 1) ≤
      (Finset.range (d - 1)).prod (fun i => ((↑n - ↑k + 1 + ↑i : ℝ) / (↑n + 1 + ↑i))) := by
    rw [show x ^ (d - 1) = (Finset.range (d - 1)).prod (fun _ => x) from
      by rw [Finset.prod_const, Finset.card_range]]
    apply Finset.prod_le_prod₀ (f := fun _ => x)
    · intro i _; exact hx_nonneg
    · intro i _; exact ratio_factor_lower_bound n k i hk
  -- Step 2: x - 1 = -k/(n+1)
  have hx_sub : x - 1 = -(↑k : ℝ) / (↑n + 1) := by
    simp only [hx_def]
    rw [div_sub_one hn_pos.ne']
    ring
  -- Step 3: Bernoulli's inequality: 1 + (d-1)*(x-1) ≤ x^(d-1)
  have hbernoulli : 1 + ↑(d - 1) * (x - 1) ≤ x ^ (d - 1) :=
    one_add_mul_sub_le_pow
      (show (-1 : ℝ) ≤ x by linarith) (d - 1)
  -- Step 4: identity ↑(d-1) and (↑d - 1 : ℝ)
  have hcast : (↑(d - 1) : ℝ) = ↑d - 1 := by rw [Nat.cast_sub hd, Nat.cast_one]
  have hn_pos' : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn
  -- Step 5: 1 - (d-1)k/n ≤ 1 + (d-1)(x-1) = 1 - (d-1)k/(n+1)
  -- because k/(n+1) ≤ k/n (bigger denominator → smaller fraction)
  have hchain : 1 - (↑d - 1 : ℝ) * ↑k / ↑n ≤ 1 + ↑(d - 1) * (x - 1) := by
    rw [hx_sub, hcast]
    -- Goal: 1 - (↑d-1)*↑k/↑n ≤ 1 + (↑d-1)*(-↑k/(↑n+1))
    -- Normalize: (↑d-1)*(-↑k/(↑n+1)) = -((↑d-1)*↑k/(↑n+1))
    have key : (↑d - 1 : ℝ) * (-↑k / (↑n + 1)) = -((↑d - 1) * ↑k / (↑n + 1)) := by ring
    rw [key]
    -- Goal: 1 - (↑d-1)*↑k/↑n ≤ 1 - (↑d-1)*↑k/(↑n+1)
    -- i.e., (↑d-1)*↑k/(↑n+1) ≤ (↑d-1)*↑k/↑n (bigger denominator → smaller fraction)
    have hineq : (↑d - 1 : ℝ) * ↑k / (↑n + 1) ≤ (↑d - 1) * ↑k / ↑n := by
      have hd_ge : (0 : ℝ) ≤ (↑d : ℝ) - 1 := by rw [← hcast]; exact Nat.cast_nonneg' (d - 1)
      exact div_le_div_of_nonneg_left (mul_nonneg hd_ge (Nat.cast_nonneg' k)) hn_pos'
        (le_add_of_nonneg_right zero_le_one)
    exact sub_le_sub_left hineq 1
  -- Chain: 1-(d-1)k/n ≤ 1+(d-1)(x-1) ≤ x^(d-1) ≤ prod
  exact hchain.trans (hbernoulli.trans hprod_lb)

/-- The dimension ratio is at most `1`.

    This is the monotonicity half of the binomial-ratio control used in the CKMR
    approximation argument. -/
lemma dim_ratio_le_one {d n k : ℕ} (hk : k ≤ n) :
    (Nat.choose (n - k + d - 1) (d - 1) : ℝ) /
      Nat.choose (n + d - 1) (d - 1) ≤ 1 := by
  rw [div_le_one (by exact_mod_cast Nat.choose_pos (by omega : d - 1 ≤ n + d - 1))]
  exact_mod_cast Nat.choose_le_choose (d - 1) (by omega)


end Quantum.DeFinetti.PureState
