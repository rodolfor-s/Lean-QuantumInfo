import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import QCryptLean.Math.ClassicalEntropy.Entropy
import QCryptLean.Math.ClassicalEntropy.KLDivergence

/-! # Basic -/


noncomputable section

namespace Math.ClassicalEntropy

open Math.ClassicalEntropy Filter Topology

/-- **Sub-additivity of negMulLog**: negMulLog(a+b) ≤ negMulLog(a) + negMulLog(b).

    Follows from concavity of negMulLog on [0,∞) with negMulLog(0) = 0.
    For concave f with f(0) = 0: f(a) ≥ (a/(a+b))·f(a+b), so f(a)+f(b) ≥ f(a+b). -/
lemma negMulLog_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.negMulLog (a + b) ≤ Real.negMulLog a + Real.negMulLog b := by
  by_cases hab : a + b = 0
  · have ha0 := le_antisymm (by linarith) ha
    have hb0 := le_antisymm (by linarith) hb
    simp [ha0, hb0, Real.negMulLog_zero]
  have hab_pos : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hab)
  have hc := Real.concaveOn_negMulLog
  have key_a : a / (a + b) * Real.negMulLog (a + b) ≤ Real.negMulLog a := by
    have h := hc.2 (Set.mem_Ici.mpr hab_pos.le) (Set.mem_Ici.mpr le_rfl)
      (div_nonneg ha hab_pos.le) (div_nonneg hb hab_pos.le) (by field_simp)
    simp only [smul_eq_mul, mul_zero, add_zero, Real.negMulLog_zero] at h
    rwa [div_mul_cancel₀ a (ne_of_gt hab_pos)] at h
  have key_b : b / (a + b) * Real.negMulLog (a + b) ≤ Real.negMulLog b := by
    have h := hc.2 (Set.mem_Ici.mpr hab_pos.le) (Set.mem_Ici.mpr le_rfl)
      (div_nonneg hb hab_pos.le) (div_nonneg ha hab_pos.le) (by field_simp; ring)
    simp only [smul_eq_mul, mul_zero, add_zero, Real.negMulLog_zero] at h
    rwa [div_mul_cancel₀ b (ne_of_gt hab_pos)] at h
  have := add_le_add key_a key_b
  rwa [← add_mul, ← add_div, div_self (ne_of_gt hab_pos), one_mul]
    at this

/-- The Fannes expression `H(t) + t log (n - 1)` is Mathlib's `qaryEntropy`. -/
lemma binaryEntropy_add_mul_log_eq_qaryEntropy (n : ℕ) (t : ℝ) :
    binaryEntropy t + t * Real.log (↑n - 1) = Real.qaryEntropy n t := by
  rw [binaryEntropy_eq_binEntropy]
  unfold Real.qaryEntropy
  rw [add_comm]
  congr 2
  norm_cast

/-- A probability vector on `n` points with a zero coordinate has entropy at most `log (n - 1)`. -/
private lemma sum_negMulLog_le_log_sub_one_of_zero {n : ℕ}
    (r : Fin n → ℝ) (hr_nonneg : ∀ i, 0 ≤ r i) (hr_sum : ∑ i, r i = 1)
    (hzero : ∃ j, r j = 0) :
    ∑ i, Real.negMulLog (r i) ≤ Real.log (↑n - 1) := by
  obtain ⟨j, hj⟩ := hzero
  set S := Finset.univ.erase j
  have h_exists_pos : ∃ k, 0 < r k := by
    by_contra h_pos
    push Not at h_pos
    have hr_zero : ∀ i, r i = 0 := fun i => le_antisymm (h_pos i) (hr_nonneg i)
    have : ∑ i, r i = 0 := by simp [hr_zero]
    linarith [hr_sum]
  obtain ⟨k, hk_pos⟩ := h_exists_pos
  have hk_ne_j : k ≠ j := by
    intro hkj
    subst hkj
    simp [hj] at hk_pos
  have hS_card : S.card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_fin]
  have hS_nonempty : S.Nonempty := ⟨k, by simp [S, hk_ne_j]⟩
  have hn_sub_pos_nat : 0 < n - 1 := by
    simpa [hS_card] using Finset.card_pos.mpr hS_nonempty
  have : NeZero n := ⟨by omega⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j),
    show Real.negMulLog (r j) = 0 from by rw [hj, Real.negMulLog_zero],
    zero_add]
  have hn_cast : (↑(n - 1) : ℝ) = ↑n - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; simp
  have hn1_pos : (0 : ℝ) < ↑n - 1 := by
    rw [← hn_cast]
    exact Nat.cast_pos.mpr hn_sub_pos_nat
  have hr_S_sum : ∑ i ∈ S, r i = 1 := by
    have := (Finset.add_sum_erase Finset.univ r (Finset.mem_univ j)).symm
    linarith [hr_sum]
  have jensen := Real.concaveOn_negMulLog.le_map_sum
    (t := S) (w := fun _ => (1 : ℝ) / (↑n - 1)) (p := r)
    (fun _ _ => div_nonneg one_pos.le hn1_pos.le)
    (by rw [Finset.sum_const, hS_card, nsmul_eq_mul, hn_cast]; field_simp)
    (fun i _ => hr_nonneg i)
  simp only [smul_eq_mul] at jensen
  rw [← Finset.mul_sum,
    show ∑ i ∈ S, (1 / (↑n - 1)) * r i = 1 / (↑n - 1) from by
      rw [← Finset.mul_sum, hr_S_sum, mul_one],
    show Real.negMulLog (1 / (↑n - 1)) =
      1 / (↑n - 1) * Real.log (↑n - 1) from by
      simp only [Real.negMulLog, one_div, Real.log_inv]; ring] at jensen
  exact le_of_mul_le_mul_left jensen (div_pos one_pos hn1_pos)

private lemma entropy_diff_coupling_bound {n : ℕ} (hn : 1 ≤ n)
    (p q : Fin n → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (hq_nonneg : ∀ i, 0 ≤ q i) (hq_sum : ∑ i, q i = 1)
    (T : ℝ) (hT_bound : T ≤ 1 - 1 / (n : ℝ))
    (h_dist : ∑ i, |p i - q i| ≤ 2 * T) :
    ∑ i, entropyTerm (p i) - ∑ i, entropyTerm (q i) ≤
      T * Real.log (↑n - 1) + binaryEntropy T := by
  have hT_nonneg : 0 ≤ T := by
    have h_dist_nonneg : 0 ≤ ∑ i, |p i - q i| := by
      exact Finset.sum_nonneg fun i _ => abs_nonneg (p i - q i)
    linarith only [h_dist_nonneg, h_dist]
  by_cases hn_two : n ≥ 2
  · have : NeZero n := ⟨by omega⟩
    have hn_cast : (2 : ℝ) ≤ n := Nat.cast_le.mpr hn_two
    have hn_pos : (0 : ℝ) < n := two_pos.trans_le hn_cast
    have h_one_sub_lt_one : 1 - 1 / (n : ℝ) < 1 := sub_lt_self 1 (one_div_pos.mpr hn_pos)
    have hT_lt : T < 1 := lt_of_le_of_lt hT_bound h_one_sub_lt_one
    have hT_le_one : T ≤ 1 := hT_lt.le
    have hp_le : ∀ i, p i ≤ 1 := fun i => by
      have h := Finset.single_le_sum (fun j _ => hp_nonneg j) (Finset.mem_univ i)
      rw [hp_sum] at h; simpa using h
    have hq_le : ∀ i, q i ≤ 1 := fun i => by
      have h := Finset.single_le_sum (fun j _ => hq_nonneg j) (Finset.mem_univ i)
      rw [hq_sum] at h; simpa using h
    let s := ∑ i, max (p i - q i) 0
    have hs_eq : 2 * s = ∑ i, |p i - q i| := by
      change 2 * ∑ i, max (p i - q i) 0 = ∑ i, |p i - q i|
      have h_abs : ∀ i, |p i - q i| = max (p i - q i) 0 + max (-(p i - q i)) 0 :=
        fun i => (max_zero_add_max_neg_zero_eq_abs_self (p i - q i)).symm
      have h_neg : ∀ i, -(p i - q i) = q i - p i := fun i => by ring
      simp_rw [h_abs, h_neg, Finset.sum_add_distrib]
      have h_eq : ∑ i, max (q i - p i) 0 = ∑ i, max (p i - q i) 0 := by
        have h_sub : ∀ i, max (p i - q i) 0 - max (q i - p i) 0 = p i - q i := fun i => by
          have := max_zero_sub_max_neg_zero_eq_self (p i - q i)
          rwa [neg_sub] at this
        have h_sum_eq : ∑ i : Fin n, (max (p i - q i) 0 - max (q i - p i) 0) = 0 := by
          simp_rw [h_sub, Finset.sum_sub_distrib, hp_sum, hq_sum, sub_self]
        linarith only [h_sum_eq,
          Finset.sum_sub_distrib (s := Finset.univ)
            (f := fun i => max (p i - q i) 0) (g := fun i => max (q i - p i) 0)]
      rw [h_eq, two_mul]
    have hs_le_T : s ≤ T := by linarith only [hs_eq, h_dist]
    have hs_nonneg : 0 ≤ s := Finset.sum_nonneg fun i _ => le_max_right _ _
    by_cases hs_zero : s = 0
    · have hp_le_q : ∀ i, p i ≤ q i := by
        intro i
        have : max (p i - q i) 0 = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (f := fun i => max (p i - q i) 0)
            (fun i _ => le_max_right (p i - q i) 0)).mp
          hs_zero i (Finset.mem_univ i)
        linarith only [le_max_left (p i - q i) 0, this]
      have hp_eq_q : p = q := by
        ext i; exact le_antisymm (hp_le_q i) (by
          have : ∑ j, (q j - p j) = 0 := by
            rw [Finset.sum_sub_distrib, hq_sum, hp_sum, sub_self]
          have h_nn : ∀ j, 0 ≤ q j - p j := fun j => sub_nonneg.mpr (hp_le_q j)
          linarith only [(Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h_nn j)).mp this i
            (Finset.mem_univ i)])
      rw [hp_eq_q, sub_self]
      apply add_nonneg
      · exact mul_nonneg hT_nonneg (Real.log_nonneg (by linarith only [hn_cast]))
      · exact binaryEntropy_nonneg T hT_nonneg hT_le_one
    have hs_pos : 0 < s := lt_of_le_of_ne hs_nonneg (Ne.symm hs_zero)
    have hs_lt_one : s < 1 := lt_of_le_of_lt hs_le_T hT_lt
    have h1s_pos : 0 < 1 - s := sub_pos.mpr hs_lt_one
    have hs_ne : s ≠ 0 := ne_of_gt hs_pos
    have h1s_ne : (1 : ℝ) - s ≠ 0 := ne_of_gt h1s_pos
    have hp_decomp : ∀ i, p i = min (p i) (q i) + max (p i - q i) 0 := by
      intro i
      rcases le_total (p i) (q i) with h | h
      · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h), add_zero]
      · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h), add_sub_cancel]
    have hm_sum : ∑ i, min (p i) (q i) = 1 - s := by
      have : ∑ i, p i = ∑ i, (min (p i) (q i) + max (p i - q i) 0) :=
        Finset.sum_congr rfl fun i _ => hp_decomp i
      rw [Finset.sum_add_distrib] at this
      linarith only [this, hp_sum]
    have hm_nonneg : ∀ i, 0 ≤ min (p i) (q i) :=
      fun i => le_min (hp_nonneg i) (hq_nonneg i)
    have hb_nonneg : ∀ i, 0 ≤ max (p i - q i) 0 := fun i => le_max_right _ _
    have h_upper : ∑ i, Real.negMulLog (p i) ≤
        ∑ i, Real.negMulLog (min (p i) (q i)) +
        ∑ i, Real.negMulLog (max (p i - q i) 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum; intro i _
      conv_lhs => rw [hp_decomp i]
      exact negMulLog_add_le _ _ (hm_nonneg i) (hb_nonneg i)
    have h_m_scale : ∑ i, Real.negMulLog (min (p i) (q i)) =
        Real.negMulLog (1 - s) +
        (1 - s) * ∑ i, Real.negMulLog (min (p i) (q i) / (1 - s)) := by
      have key : ∀ i, Real.negMulLog (min (p i) (q i)) =
          (min (p i) (q i) / (1 - s)) * Real.negMulLog (1 - s) +
          (1 - s) * Real.negMulLog (min (p i) (q i) / (1 - s)) := by
        intro i
        conv_lhs => rw [← mul_div_cancel₀ (min (p i) (q i)) h1s_ne]
        exact Real.negMulLog_mul (1 - s) (min (p i) (q i) / (1 - s))
      simp_rw [key, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      rw [show ∑ i, min (p i) (q i) / (1 - s) = 1 from by
        rw [← Finset.sum_div, hm_sum, div_self h1s_ne]]
      ring
    have hb_sum_eq : ∑ i, max (p i - q i) 0 = s := rfl
    have h_b_scale : ∑ i, Real.negMulLog (max (p i - q i) 0) =
        Real.negMulLog s +
        s * ∑ i, Real.negMulLog (max (p i - q i) 0 / s) := by
      have key : ∀ i, Real.negMulLog (max (p i - q i) 0) =
          (max (p i - q i) 0 / s) * Real.negMulLog s +
          s * Real.negMulLog (max (p i - q i) 0 / s) := by
        intro i
        conv_lhs => rw [← mul_div_cancel₀ (max (p i - q i) 0) hs_ne]
        exact Real.negMulLog_mul s (max (p i - q i) 0 / s)
      simp_rw [key, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
        show ∑ i, max (p i - q i) 0 / s = 1 from by
          rw [← Finset.sum_div, hb_sum_eq, div_self hs_ne]]
      ring
    have h_r_bound : ∑ i, Real.negMulLog (max (p i - q i) 0 / s) ≤
        Real.log (↑n - 1) := by
      have ⟨j, hj⟩ : ∃ j, max (p j - q j) 0 = 0 := by
        by_contra h; push Not at h
        have hpi : ∀ i, q i < p i := fun i => by
          by_contra h'; push Not at h'
          exact h i (max_eq_right (sub_nonpos.mpr h'))
        have : ∑ i, q i < ∑ i, p i :=
          Finset.sum_lt_sum (fun i _ => le_of_lt (hpi i))
            ⟨⟨0, by omega⟩, Finset.mem_univ _, hpi _⟩
        linarith only [this, hp_sum, hq_sum]
      let r : Fin n → ℝ := fun i => max (p i - q i) 0 / s
      have hr_nonneg : ∀ i, 0 ≤ r i :=
        fun i => div_nonneg (hb_nonneg i) hs_pos.le
      have hr_sum : ∑ i, r i = 1 := by
        change ∑ i, max (p i - q i) 0 / s = 1
        rw [← Finset.sum_div, hb_sum_eq, div_self hs_ne]
      rw [show (fun i => Real.negMulLog (max (p i - q i) 0 / s)) =
        (fun i => Real.negMulLog (r i)) from rfl]
      exact sum_negMulLog_le_log_sub_one_of_zero r hr_nonneg hr_sum
        ⟨j, by
          change max (p j - q j) 0 / s = 0
          rw [hj, zero_div]⟩
    have h_q_lower : ∑ i, Real.negMulLog (q i) ≥
        (1 - s) * ∑ i, Real.negMulLog (min (p i) (q i) / (1 - s)) := by
      have hc_nonneg : ∀ i, 0 ≤ max (q i - p i) 0 :=
        fun i => le_max_right _ _
      have hq_eq : ∀ i, q i = min (p i) (q i) + max (q i - p i) 0 := by
        intro i
        rcases le_total (p i) (q i) with h | h
        · rw [min_eq_left h, max_eq_left (sub_nonneg.mpr h), add_sub_cancel]
        · rw [min_eq_right h, max_eq_right (sub_nonpos.mpr h), add_zero]
      have hc_sum : ∑ i, max (q i - p i) 0 = s := by
        have : ∑ i, q i = ∑ i, (min (p i) (q i) + max (q i - p i) 0) :=
          Finset.sum_congr rfl fun i _ => hq_eq i
        rw [Finset.sum_add_distrib] at this; linarith only [this, hq_sum, hm_sum]
      have hq_conv : ∀ i, q i =
          (1 - s) * (min (p i) (q i) / (1 - s)) +
          s * (max (q i - p i) 0 / s) := by
        intro i
        rw [mul_div_cancel₀ _ h1s_ne, mul_div_cancel₀ _ hs_ne]
        exact hq_eq i
      have h_pw : ∀ i,
          (1 - s) * Real.negMulLog (min (p i) (q i) / (1 - s)) +
          s * Real.negMulLog (max (q i - p i) 0 / s) ≤
          Real.negMulLog (q i) := by
        intro i; conv_rhs => rw [hq_conv i]
        rw [← smul_eq_mul, ← smul_eq_mul]
        exact Real.concaveOn_negMulLog.2
          (Set.mem_Ici.mpr (div_nonneg (hm_nonneg i) h1s_pos.le))
          (Set.mem_Ici.mpr (div_nonneg (hc_nonneg i) hs_pos.le))
          h1s_pos.le hs_pos.le (sub_add_cancel 1 s)
      have h_sum :=
        Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h_pw i
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum] at h_sum
      linarith only [h_sum, show 0 ≤ s * ∑ i, Real.negMulLog (max (q i - p i) 0 / s)
        from mul_nonneg hs_pos.le (Finset.sum_nonneg fun i _ =>
          Real.negMulLog_nonneg (div_nonneg (hc_nonneg i) hs_pos.le)
            ((div_le_one hs_pos).mpr
              ((Finset.single_le_sum (fun j _ => hc_nonneg j)
                (Finset.mem_univ i)).trans (le_of_eq hc_sum))))]
    have hpq_to_nml : ∀ r : Fin n → ℝ, (∀ i, 0 ≤ r i) →
        ∑ i, entropyTerm (r i) = ∑ i, Real.negMulLog (r i) :=
      fun r hr =>
        Finset.sum_congr rfl fun i _ => entropyTerm_eq_negMulLog (r i) (hr i)
    rw [hpq_to_nml p hp_nonneg, hpq_to_nml q hq_nonneg]
    have h_diff_bound :
        ∑ i, Real.negMulLog (p i) - ∑ i, Real.negMulLog (q i) ≤
        Real.negMulLog (1 - s) + Real.negMulLog s +
        s * Real.log (↑n - 1) := by
      calc ∑ i, Real.negMulLog (p i) - ∑ i, Real.negMulLog (q i)
          ≤ (∑ i, Real.negMulLog (min (p i) (q i)) +
             ∑ i, Real.negMulLog (max (p i - q i) 0)) -
            (1 - s) * ∑ i, Real.negMulLog (min (p i) (q i) / (1 - s))
            := by linarith only [h_upper, h_q_lower]
        _ = (Real.negMulLog (1 - s) +
             (1 - s) * ∑ i, Real.negMulLog (min (p i) (q i) / (1 - s)) +
             (Real.negMulLog s +
              s * ∑ i, Real.negMulLog (max (p i - q i) 0 / s))) -
            (1 - s) * ∑ i, Real.negMulLog (min (p i) (q i) / (1 - s))
            := by rw [h_m_scale, h_b_scale]
        _ = Real.negMulLog (1 - s) + Real.negMulLog s +
            s * ∑ i, Real.negMulLog (max (p i - q i) 0 / s)
            := by ring
        _ ≤ Real.negMulLog (1 - s) + Real.negMulLog s +
            s * Real.log (↑n - 1)
            := (add_le_add_iff_left _).mpr (mul_le_mul_of_nonneg_left h_r_bound hs_pos.le)
    have h_binary :
        Real.negMulLog (1 - s) + Real.negMulLog s = binaryEntropy s := by
      unfold binaryEntropy
      rw [show entropyTerm s = Real.negMulLog s from
            entropyTerm_eq_negMulLog s hs_nonneg,
        show entropyTerm (1 - s) = Real.negMulLog (1 - s) from
            entropyTerm_eq_negMulLog (1 - s) h1s_pos.le]
      ring
    have h_mono : binaryEntropy s + s * Real.log (↑n - 1) ≤
        binaryEntropy T + T * Real.log (↑n - 1) := by
      by_cases hs_eq_T : s = T
      · rw [hs_eq_T]
      have hs_lt_T : s < T := lt_of_le_of_ne hs_le_T hs_eq_T
      have hs_bound : s ≤ 1 - 1 / (n : ℝ) := le_trans hs_le_T hT_bound
      rw [binaryEntropy_add_mul_log_eq_qaryEntropy, binaryEntropy_add_mul_log_eq_qaryEntropy]
      exact le_of_lt (Real.qaryEntropy_strictMonoOn hn_two
        ⟨hs_nonneg, hs_bound⟩ ⟨hT_nonneg, hT_bound⟩ hs_lt_T)
    linarith only [h_diff_bound, h_binary, h_mono]
  · have hn_one : n = 1 := by omega
    subst hn_one
    have hp_zero : p 0 = 1 := by simpa using hp_sum
    have hq_zero : q 0 = 1 := by simpa using hq_sum
    have hT_nonpos : T ≤ 0 := by simpa using hT_bound
    have hT_zero : T = 0 := le_antisymm hT_nonpos hT_nonneg
    simp [hp_zero, hq_zero, hT_zero, binaryEntropy_zero, entropyTerm_one]

/-- Fannes bound for probability vectors whose `L¹` distance is at most `2T`.

Under the regime `T ≤ 1 - 1 / n`, the entropy difference is bounded by
`T * log (n - 1) + binaryEntropy T`. -/
lemma abs_sub_sum_entropyTerm_le_mul_log_add_binaryEntropy {n : ℕ} (hn : 1 ≤ n)
    (p q : Fin n → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (hq_nonneg : ∀ i, 0 ≤ q i) (hq_sum : ∑ i, q i = 1)
    (T : ℝ) (hT_bound : T ≤ 1 - 1 / (n : ℝ))
    (h_dist : ∑ i, |p i - q i| ≤ 2 * T) :
    |∑ i, entropyTerm (p i) - ∑ i, entropyTerm (q i)| ≤
      T * Real.log (n - 1) + binaryEntropy T := by
  rw [abs_le]; constructor
  · -- H(q) - H(p) ≤ B
    linarith [entropy_diff_coupling_bound hn q p hq_nonneg hq_sum hp_nonneg hp_sum T
      hT_bound (by rwa [show ∑ i, |q i - p i| = ∑ i, |p i - q i| from
        Finset.sum_congr rfl fun i _ => abs_sub_comm (q i) (p i)])]
  · -- H(p) - H(q) ≤ B
    exact entropy_diff_coupling_bound hn p q hp_nonneg hp_sum hq_nonneg hq_sum T hT_bound
      h_dist

/-- Lipschitz continuity of entropy term for bounded probabilities.

    For x, y ≥ ε > 0, the entropy function f(x) = -x log x satisfies:
    |f(x) - f(y)| ≤ (|log ε| + 1) · |x - y|

    This uses the mean value theorem applied to f'(x) = -(log x + 1). -/
lemma entropyTerm_lipschitz (ε : ℝ) (hε : 0 < ε) (x y : ℝ)
    (hx : ε ≤ x) (hx' : x ≤ 1) (hy : ε ≤ y) (hy' : y ≤ 1) :
    |entropyTerm x - entropyTerm y| ≤ (|Real.log ε| + 1) * |x - y| := by
  -- Handle the trivial case x = y
  by_cases heq : x = y
  · rw [heq]
    simp
  -- Establish bounds for |log x + 1| on [ε, 1]
  have hε1 : ε ≤ 1 := le_trans hx hx'
  have abs_log_add_one_bound : ∀ z, ε ≤ z → z ≤ 1 → |Real.log z + 1| ≤ |Real.log ε| + 1 := by
    intro z hz hz'
    by_cases h : Real.log z + 1 ≥ 0
    · -- log z + 1 ≥ 0, so |log z + 1| = log z + 1
      rw [abs_of_nonneg h]
      have hlog_ε : Real.log ε ≤ 0 := Real.log_nonpos (le_of_lt hε) hε1
      have hz_pos : 0 < z := lt_of_lt_of_le hε hz
      have hlog_z : Real.log z ≤ 0 := Real.log_nonpos (le_of_lt hz_pos) hz'
      have hlog_mono : Real.log ε ≤ Real.log z := Real.log_le_log hε hz
      rw [abs_of_nonpos hlog_ε]
      linarith
    · -- log z + 1 < 0, so |log z + 1| = -(log z + 1)
      push Not at h
      rw [abs_of_neg h]
      have hlog_ε : Real.log ε ≤ 0 := Real.log_nonpos (le_of_lt hε) hε1
      rw [abs_of_nonpos hlog_ε]
      have hlog_mono : Real.log ε ≤ Real.log z := Real.log_le_log hε hz
      linarith
  -- Use MVT on the convex interval [ε, 1]
  let s := Set.Icc ε 1
  have hs_convex : Convex ℝ s := convex_Icc ε 1
  have hx_mem : x ∈ s := ⟨hx, hx'⟩
  have hy_mem : y ∈ s := ⟨hy, hy'⟩
  -- Show differentiable at all points in [ε, 1]
  have hdiff : ∀ z ∈ s, DifferentiableAt ℝ (fun t => entropyTerm t) z := by
    intro z hz
    have hz_pos : 0 < z := lt_of_lt_of_le hε hz.1
    apply DifferentiableAt.congr_of_eventuallyEq
    · apply DifferentiableAt.neg
      apply DifferentiableAt.mul differentiableAt_id (Real.differentiableAt_log (ne_of_gt hz_pos))
    · filter_upwards [isOpen_Ioi.mem_nhds hz_pos] with t ht
      unfold entropyTerm
      have ht_ne : t ≠ 0 := fun h => by linarith [show 0 < t from ht, h]
      simp [ht_ne]
  -- Bound the derivative on all points in [ε, 1]
  have hbound : ∀ z ∈ s, ‖deriv (fun t => entropyTerm t) z‖ ≤ |Real.log ε| + 1 := by
    intro z hz
    have hz_pos : 0 < z := lt_of_lt_of_le hε hz.1
    rw [Real.norm_eq_abs]
    -- Compute deriv at z
    have h_deriv : deriv (fun t => entropyTerm t) z = -(Real.log z + 1) := by
      have h_eq : ∀ᶠ t in 𝓝 z, entropyTerm t = -(t * Real.log t) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz_pos] with t ht
        unfold entropyTerm
        have ht_ne : t ≠ 0 := fun h => by linarith [show 0 < t from ht, h]
        simp [ht_ne]
      let f := fun t => t * Real.log t
      have h_deriv_aux : deriv (fun t => -(t * Real.log t)) z = -(Real.log z + 1) := by
        rw [show (fun t => -f t) = -f from rfl]
        rw [deriv.neg]
        have h_mul : deriv f z = Real.log z + 1 := by
          calc deriv f z
              = deriv (fun t => t) z * Real.log z + z * deriv (fun t => Real.log t) z := by
                exact deriv_mul (x := z) differentiableAt_id
                  (Real.differentiableAt_log (ne_of_gt hz_pos))
            _ = 1 * Real.log z + z * (1 / z) := by simp [deriv_id'', Real.deriv_log]
            _ = Real.log z + 1 := by field_simp [ne_of_gt hz_pos]
        rw [h_mul]
      rw [← h_deriv_aux]
      apply Filter.EventuallyEq.deriv_eq
      exact h_eq
    rw [h_deriv, abs_neg]
    exact abs_log_add_one_bound z hz.1 hz.2
  -- Apply MVT
  have mvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound hs_convex hx_mem
    hy_mem
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at mvt
  -- MVT gives |f(y) - f(x)| ≤ C * |y - x|, we need |f(x) - f(y)| ≤ C * |x - y|
  have h_comm1 : |entropyTerm x - entropyTerm y| = |entropyTerm y - entropyTerm x| :=
    abs_sub_comm _ _
  have h_comm2 : |x - y| = |y - x| := abs_sub_comm _ _
  rw [h_comm1, h_comm2]
  exact mvt

/-- Removing one coordinate leaves an entropy contribution controlled by the remaining mass. -/
private lemma sum_entropyTerm_erase_le {n : ℕ}
    (i₀ : Fin n) (w : Fin n → ℝ) (s : ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hsum : ∑ i ∈ Finset.univ.erase i₀, w i = s) :
    ∑ i ∈ Finset.univ.erase i₀, entropyTerm (w i) ≤
      s * Real.log (↑n - 1) + entropyTerm s := by
  have hne_zero : n ≠ 0 := by
    intro hn_zero
    subst hn_zero
    exact Fin.elim0 i₀
  have : NeZero n := ⟨hne_zero⟩
  by_cases hn_eq_1 : n = 1
  · subst hn_eq_1
    have hi0 : i₀ = 0 := by
      ext
      omega
    subst hi0
    have hs_zero : s = 0 := by simpa using hsum.symm
    rw [hs_zero]
    simp [entropyTerm_zero]
  have hn : n ≥ 2 := by omega
  have hcard : (Finset.univ.erase i₀).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_fin]
  by_cases hn_eq_2 : n = 2
  · subst hn_eq_2
    have hcard_one : (Finset.univ.erase i₀).card = 1 := by simp [hcard]
    have hone_elem : ∃ j, Finset.univ.erase i₀ = {j} := by
      rw [Finset.card_eq_one] at hcard_one
      exact hcard_one
    obtain ⟨j, hj⟩ := hone_elem
    rw [hj, Finset.sum_singleton]
    have hj_val : w j = s := by
      have : ∑ i ∈ ({j} : Finset (Fin 2)), w i = s := by
        rw [← hj]
        exact hsum
      simpa using this
    rw [hj_val]
    have hlog_zero : Real.log ((2 : ℝ) - 1) = 0 := by norm_num
    simp only [Nat.cast_ofNat] at hlog_zero ⊢
    rw [hlog_zero, mul_zero, zero_add]
  · have hn_ge_1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
    have hn_ge_3 : n ≥ 3 := by omega
    let k : ℕ := n - 1
    have hk_ge_2 : k ≥ 2 := by
      simp only [k]
      omega
    have hk_pos : (0 : ℝ) < k := by
      have : (2 : ℕ) ≤ k := hk_ge_2
      have h2 : (2 : ℝ) ≤ k := Nat.cast_le.mpr this
      linarith
    have hk_ne_zero : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
    have hs_nonneg : 0 ≤ s := by
      rw [← hsum]
      exact Finset.sum_nonneg fun i _ => hw_nonneg i
    let u : Fin n → ℝ := fun _ => (1 : ℝ) / k
    have hu_nonneg : ∀ i, 0 ≤ u i := fun _ => div_nonneg one_pos.le (le_of_lt hk_pos)
    have hu_sum : ∑ i ∈ Finset.univ.erase i₀, u i = 1 := by
      simp only [u]
      rw [Finset.sum_const, hcard]
      simp only [nsmul_eq_mul]
      have hk_eq_nm1 : (k : ℝ) = (n - 1 : ℕ) := rfl
      rw [hk_eq_nm1]
      have hnm1_ne : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
        have : (2 : ℕ) ≤ n - 1 := by omega
        have h2 : (2 : ℝ) ≤ (n - 1 : ℕ) := Nat.cast_le.mpr this
        linarith
      field_simp [hnm1_ne]
    have jensen := Real.concaveOn_negMulLog.le_map_sum
      (t := Finset.univ.erase i₀) (w := u) (p := w)
      (fun i _ => hu_nonneg i)
      hu_sum
      (fun i _ => hw_nonneg i)
    have h_sum_eq :
        ∑ i ∈ Finset.univ.erase i₀, entropyTerm (w i) =
          ∑ i ∈ Finset.univ.erase i₀, Real.negMulLog (w i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact entropyTerm_eq_negMulLog (w i) (hw_nonneg i)
    have h_lhs : ∑ i ∈ Finset.univ.erase i₀, u i • Real.negMulLog (w i) =
        (1 / k) * ∑ i ∈ Finset.univ.erase i₀, Real.negMulLog (w i) := by
      simp only [u, smul_eq_mul]
      rw [← Finset.mul_sum]
    have h_rhs_arg : ∑ i ∈ Finset.univ.erase i₀, u i • w i = s / k := by
      simp only [u, smul_eq_mul, ← Finset.mul_sum, hsum]
      ring
    rw [h_lhs, h_rhs_arg] at jensen
    rw [h_sum_eq]
    have h_mul_jensen : ∑ i ∈ Finset.univ.erase i₀, Real.negMulLog (w i) ≤
        k * Real.negMulLog (s / k) := by
      calc
        ∑ i ∈ Finset.univ.erase i₀, Real.negMulLog (w i) =
            k * ((1 / k) * ∑ i ∈ Finset.univ.erase i₀, Real.negMulLog (w i)) := by
              field_simp
        _ ≤ k * Real.negMulLog (s / k) := by
            apply mul_le_mul_of_nonneg_left jensen (le_of_lt hk_pos)
    by_cases hs_zero : s = 0
    · have h_all_zero : ∀ i ∈ Finset.univ.erase i₀, w i = 0 := by
        have h : ∑ i ∈ Finset.univ.erase i₀, w i = 0 := by simpa [hs_zero] using hsum
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hw_nonneg j)).mp h
      have h_sum_zero : ∑ i ∈ Finset.univ.erase i₀, Real.negMulLog (w i) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [h_all_zero i hi, Real.negMulLog_zero]
      rw [h_sum_zero, hs_zero, zero_mul, entropyTerm_zero]
      simp
    · have hs_pos : 0 < s := lt_of_le_of_ne hs_nonneg (Ne.symm hs_zero)
      have hs_ne : s ≠ 0 := ne_of_gt hs_pos
      have h_simplify : k * Real.negMulLog (s / k) = s * Real.log k + Real.negMulLog s := by
        rw [Real.negMulLog.eq_1 (s / k), Real.negMulLog.eq_1 s, Real.log_div hs_ne hk_ne_zero]
        field_simp [hk_ne_zero]
        ring
      have hk_eq : (k : ℝ) = (n : ℝ) - 1 := by
        simp only [k]
        rw [Nat.cast_sub hn_ge_1, Nat.cast_one]
      calc
        ∑ i ∈ Finset.univ.erase i₀, Real.negMulLog (w i) ≤ k * Real.negMulLog (s / k) :=
          h_mul_jensen
        _ = s * Real.log k + Real.negMulLog s := h_simplify
        _ = s * Real.log (↑n - 1) + Real.negMulLog s := by simp only [hk_eq]
        _ = s * Real.log (↑n - 1) + entropyTerm s := by
            rw [entropyTerm_eq_negMulLog s hs_nonneg]

/-- If one coordinate of a probability vector is at least `1 - T` in the regime
`0 ≤ T ≤ 1 - 1 / n`, then its entropy is at most
`T * log (n - 1) + binaryEntropy T`. -/
lemma sum_entropyTerm_le_of_exists_one_sub_le {n : ℕ}
    (evals : Fin n → ℝ) (hevals_nonneg : ∀ i, 0 ≤ evals i) (hevals_sum : ∑ i, evals i = 1)
    (T : ℝ) (hT_bound : T ≤ 1 - 1 / (n : ℝ))
    (h_large : ∃ i, evals i ≥ 1 - T) :
    ∑ i, entropyTerm (evals i) ≤ T * Real.log (n - 1) + binaryEntropy T := by
  obtain ⟨i_large, h_large_bound⟩ := h_large
  have hne_zero : n ≠ 0 := by
    intro hn_zero
    subst hn_zero
    exact Fin.elim0 i_large
  have : NeZero n := ⟨hne_zero⟩
  have h_large_le_one : evals i_large ≤ 1 := by
    have h := Finset.single_le_sum (f := evals)
      (fun i _ => hevals_nonneg i) (Finset.mem_univ i_large)
    simpa [hevals_sum] using h
  have hT : 0 ≤ T := by
    linarith only [h_large_le_one, h_large_bound]
  by_cases hn_eq_1 : n = 1
  · subst hn_eq_1
    have hi_large : i_large = 0 := by
      ext
      omega
    subst hi_large
    have heval_one : evals 0 = 1 := by simpa using hevals_sum
    have hT_nonpos : T ≤ 0 := by simpa using hT_bound
    have hT_zero : T = 0 := le_antisymm hT_nonpos hT
    simp [heval_one, hT_zero, binaryEntropy_zero, entropyTerm_one]
  have hn : n ≥ 2 := by omega
  have hnonempty : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
  obtain ⟨i_max, _, hi_max_is_max⟩ := Finset.exists_max_image Finset.univ evals hnonempty
  let p_max := evals i_max
  have hp_max_bound : p_max ≥ 1 - T := by
    calc p_max = evals i_max := rfl
      _ ≥ evals i_large := hi_max_is_max i_large (Finset.mem_univ i_large)
      _ ≥ 1 - T := h_large_bound
  have hp_max_le_one : p_max ≤ 1 := by
    have h := Finset.single_le_sum (f := evals) (fun i _ => hevals_nonneg i) (Finset.mem_univ i_max)
    simp only [hevals_sum] at h
    exact h
  have hsmall_sum : ∑ i ∈ Finset.univ.erase i_max, evals i = 1 - p_max := by
    have h := Finset.sum_erase_eq_sub (f := evals) (Finset.mem_univ i_max)
    simp only [hevals_sum] at h
    exact h
  have hsmall_le_T : 1 - p_max ≤ T := sub_le_comm.mp hp_max_bound
  have hT_lt : T < 1 := by
    have h_one_sub_lt_one : 1 - 1 / (n : ℝ) < 1 := by
      have h_n_pos : (0 : ℝ) < n := Nat.cast_pos'.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
      have h_inv_pos : 0 < 1 / (n : ℝ) := one_div_pos.mpr h_n_pos
      linarith only [h_inv_pos]
    exact lt_of_le_of_lt hT_bound h_one_sub_lt_one
  have hp_max_ge_inv_n : p_max ≥ 1 / (n : ℝ) := by
    by_contra h_neg
    push Not at h_neg
    have h_all_lt : ∀ i, evals i < 1 / (n : ℝ) := fun i => by
      calc evals i ≤ p_max := hi_max_is_max i (Finset.mem_univ i)
        _ < 1 / n := h_neg
    have h_sum_lt : ∑ i, evals i < ∑ _i : Fin n, (1 : ℝ) / n := Finset.sum_lt_sum
      (fun i _ => le_of_lt (h_all_lt i)) ⟨i_max, Finset.mem_univ i_max, h_all_lt i_max⟩
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at h_sum_lt
    have h_n_pos : (0 : ℝ) < n := Nat.cast_pos'.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
    have h_simp : (n : ℝ) * (1 / n) = 1 := by field_simp
    rw [h_simp, hevals_sum] at h_sum_lt
    linarith only [h_sum_lt]
  have hsum_split : ∑ i, entropyTerm (evals i) =
      entropyTerm p_max + ∑ i ∈ Finset.univ.erase i_max, entropyTerm (evals i) := by
    have h1 : Finset.univ = insert i_max (Finset.univ.erase i_max) :=
      (Finset.insert_erase (Finset.mem_univ i_max)).symm
    conv_lhs => rw [h1]
    rw [Finset.sum_insert (Finset.notMem_erase i_max Finset.univ)]
  rw [hsum_split]
  have hp_max_nonneg : 0 ≤ p_max := hevals_nonneg i_max
  have hone_minus_p_nonneg : 0 ≤ 1 - p_max := sub_nonneg.mpr hp_max_le_one
  have hbinary_p_max : entropyTerm p_max + entropyTerm (1 - p_max) = binaryEntropy p_max := by
    unfold binaryEntropy; ring
  by_cases hp_max_eq_one : p_max = 1
  · have hall_zero : ∀ i ∈ Finset.univ.erase i_max, evals i = 0 := by
      have h_total : ∑ j ∈ Finset.univ.erase i_max, evals j = 1 - p_max := hsmall_sum
      rw [hp_max_eq_one] at h_total
      simp only [sub_self] at h_total
      have h_nonneg : ∀ j ∈ Finset.univ.erase i_max, 0 ≤ evals j := fun j _ => hevals_nonneg j
      exact (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h_total
    have hsmall_entropy_zero : ∑ i ∈ Finset.univ.erase i_max, entropyTerm (evals i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hall_zero i hi]
      exact entropyTerm_zero
    rw [hsmall_entropy_zero, add_zero]
    have h1 : entropyTerm p_max = entropyTerm 1 := by rw [hp_max_eq_one]
    rw [h1, entropyTerm_one]
    apply add_nonneg
    · apply mul_nonneg hT
      apply Real.log_nonneg
      have h2n : (2 : ℝ) ≤ n := Nat.cast_le.mpr hn
      linarith only [h2n]
    · exact binaryEntropy_nonneg T hT hT_lt.le
  · have hp_max_lt_one : p_max < 1 := lt_of_le_of_ne hp_max_le_one hp_max_eq_one
    have hone_minus_p_pos : 0 < 1 - p_max := sub_pos.mpr hp_max_lt_one
    have h_small_bound : ∑ i ∈ Finset.univ.erase i_max, entropyTerm (evals i) ≤
        (1 - p_max) * Real.log (n - 1) + entropyTerm (1 - p_max) :=
      sum_entropyTerm_erase_le i_max evals (1 - p_max) hevals_nonneg hsmall_sum
    have h_mono_bound : binaryEntropy p_max + (1 - p_max) * Real.log (n - 1) ≤
        binaryEntropy (1 - T) + T * Real.log (n - 1) := by
      have hlog_nonneg : 0 ≤ Real.log (n - 1) := by
        apply Real.log_nonneg
        have h2n : (2 : ℝ) ≤ n := Nat.cast_le.mpr hn
        linarith only [h2n]
      have h1 : (1 - p_max) * Real.log (n - 1) ≤ T * Real.log (n - 1) :=
        mul_le_mul_of_nonneg_right hsmall_le_T hlog_nonneg
      by_cases hT_half : T ≤ 1/2
      · have h_1mp_le_half : 1 - p_max ≤ 1/2 := hsmall_le_T.trans hT_half
        have h_1mp_in : 1 - p_max ∈ Set.Icc 0 (2⁻¹ : ℝ) :=
          ⟨hone_minus_p_nonneg, h_1mp_le_half.trans_eq (one_div 2)⟩
        have h_T_in : T ∈ Set.Icc 0 (2⁻¹ : ℝ) := ⟨hT, hT_half.trans_eq (one_div 2)⟩
        rw [binaryEntropy_symm p_max, binaryEntropy_symm (1 - T)]
        simp only [sub_sub_cancel]
        have h2 : binaryEntropy (1 - p_max) ≤ binaryEntropy T := by
          by_cases heq : 1 - p_max = T
          · rw [heq]
          · rw [binaryEntropy_eq_binEntropy, binaryEntropy_eq_binEntropy]
            exact le_of_lt (Real.binEntropy_strictMonoOn h_1mp_in h_T_in
              (lt_of_le_of_ne hsmall_le_T heq))
        linarith only [h1, h2]
      · push Not at hT_half
        rw [binaryEntropy_symm p_max, binaryEntropy_symm (1 - T)]
        simp only [sub_sub_cancel]
        rw [binaryEntropy_add_mul_log_eq_qaryEntropy,
          binaryEntropy_add_mul_log_eq_qaryEntropy]
        by_cases hT_in_incr : T ≤ 1 - 1 / (n : ℝ)
        · have h_1mp_in : 1 - p_max ∈ Set.Icc 0 (1 - 1 / (n : ℝ)) :=
            ⟨hone_minus_p_nonneg, hsmall_le_T.trans hT_in_incr⟩
          have h_T_in : T ∈ Set.Icc 0 (1 - 1 / (n : ℝ)) := ⟨hT, hT_in_incr⟩
          by_cases heq : 1 - p_max = T
          · rw [heq]
          · exact le_of_lt (Real.qaryEntropy_strictMonoOn hn h_1mp_in h_T_in
              (lt_of_le_of_ne hsmall_le_T heq))
        · push Not at hT_in_incr
          linarith only [hT_bound, hT_in_incr]
    calc entropyTerm p_max + ∑ i ∈ Finset.univ.erase i_max, entropyTerm (evals i)
        ≤ entropyTerm p_max + ((1 - p_max) * Real.log (n - 1) + entropyTerm (1 - p_max)) :=
          (add_le_add_iff_left _).mpr h_small_bound
      _ = binaryEntropy p_max + (1 - p_max) * Real.log (n - 1) := by
          rw [← hbinary_p_max]; ring
      _ ≤ binaryEntropy (1 - T) + T * Real.log (n - 1) := h_mono_bound
      _ = T * Real.log (n - 1) + binaryEntropy T := by
          rw [binaryEntropy_symm (1 - T), sub_sub_cancel]; ring

end Math.ClassicalEntropy

end
