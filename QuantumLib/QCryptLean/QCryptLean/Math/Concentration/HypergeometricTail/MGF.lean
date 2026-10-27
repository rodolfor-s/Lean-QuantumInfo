import QCryptLean.Math.Concentration.HypergeometricTail.Basic
import QCryptLean.Math.Concentration.HypergeometricTail.TwoPoint

/-!
# Hypergeometric MGF Bound — degenerate cases, first-draw recurrence, induction

This file proves the centered hypergeometric moment-generating function bound
used by the finite Serfling counting argument.  It handles degenerate cases,
establishes the first-draw success/failure recurrence, and closes the
strong-induction proof of the Hoeffding envelope.

## Main statements
- `centeredHypergeometricMGF_first_draw`: first-draw recurrence for the
  normalized centered hypergeometric MGF.
- `hypergeometricChooseCenteredMGF_le`: centered hypergeometric MGF is bounded
  by `exp (t ^ 2 * n / 8)`.
-/

open scoped BigOperators

namespace Math.Concentration.HypergeometricTail

/-- If the population has no successes, the centered hypergeometric MGF is
deterministic. -/
lemma hypergeometricCenteredMGF_sum_of_zero_success (N n : ℕ) (t : ℝ) :
    ∑ k ∈ Finset.range (n + 1),
        chooseWeight N n 0 k *
          Real.exp (t * centeredSuccessCount N n 0 k) =
      N.choose n := by
  classical
  rw [Finset.sum_eq_single 0]
  · simp [chooseWeight, centeredSuccessCount]
  · intro k _hk hk_ne
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk_ne
    have hchoose : (0 : ℕ).choose k = 0 := Nat.choose_eq_zero_of_lt hk_pos
    simp [chooseWeight, hchoose]
  · intro hnot
    simp at hnot

/-- The centered hypergeometric MGF bound in the degenerate no-success case. -/
lemma hypergeometricChooseCenteredMGF_le_of_zero_success
    {N n : ℕ} (hN : n ≤ N) (t : ℝ) :
    (∑ k ∈ Finset.range (n + 1),
        chooseWeight N n 0 k *
          Real.exp (t * centeredSuccessCount N n 0 k)) /
      N.choose n ≤ Real.exp (t ^ 2 * n / 8) := by
  have hsum := hypergeometricCenteredMGF_sum_of_zero_success N n t
  have hden_pos_nat : 0 < N.choose n := Nat.choose_pos hN
  have hden_ne : (N.choose n : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hden_pos_nat
  have hexp_nonneg : 0 ≤ t ^ 2 * (n : ℝ) / 8 := by positivity
  calc
    (∑ k ∈ Finset.range (n + 1),
        chooseWeight N n 0 k *
          Real.exp (t * centeredSuccessCount N n 0 k)) /
      N.choose n
        = 1 := by
          rw [hsum]
          exact div_self hden_ne
    _ ≤ Real.exp (t ^ 2 * n / 8) := Real.one_le_exp hexp_nonneg

/-- If every population element is a success, the centered hypergeometric MGF is
deterministic. -/
lemma hypergeometricCenteredMGF_sum_of_success_eq_population
    {N n : ℕ} (hN : n ≤ N) (hn : n ≠ 0) (t : ℝ) :
    ∑ k ∈ Finset.range (n + 1),
        chooseWeight N n N k *
          Real.exp (t * centeredSuccessCount N n N k) =
      N.choose n := by
  classical
  have hN_pos_nat : 0 < N := lt_of_lt_of_le (Nat.pos_of_ne_zero hn) hN
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN_pos_nat
  rw [Finset.sum_eq_single n]
  · have hcenter : centeredSuccessCount N n N n = 0 := by
      unfold centeredSuccessCount
      field_simp [hN_ne]
      ring
    simp [chooseWeight, hcenter]
  · intro k hk hk_ne
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hk_lt : k < n := lt_of_le_of_ne hk_le hk_ne
    have hsub_pos : 0 < n - k := Nat.sub_pos_of_lt hk_lt
    have hchoose : (0 : ℕ).choose (n - k) = 0 := Nat.choose_eq_zero_of_lt hsub_pos
    simp [chooseWeight, hchoose]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_self n))).elim

/-- The centered hypergeometric MGF bound when all population entries are
successes. -/
lemma hypergeometricChooseCenteredMGF_le_of_success_eq_population
    {N n : ℕ} (hN : n ≤ N) (hn : n ≠ 0) (t : ℝ) :
    (∑ k ∈ Finset.range (n + 1),
        chooseWeight N n N k *
          Real.exp (t * centeredSuccessCount N n N k)) /
      N.choose n ≤ Real.exp (t ^ 2 * n / 8) := by
  have hsum := hypergeometricCenteredMGF_sum_of_success_eq_population (N := N) (n := n) hN hn t
  have hden_pos_nat : 0 < N.choose n := Nat.choose_pos hN
  have hden_ne : (N.choose n : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hden_pos_nat
  have hexp_nonneg : 0 ≤ t ^ 2 * (n : ℝ) / 8 := by positivity
  calc
    (∑ k ∈ Finset.range (n + 1),
        chooseWeight N n N k *
          Real.exp (t * centeredSuccessCount N n N k)) /
      N.choose n
        = 1 := by
          rw [hsum]
          exact div_self hden_ne
    _ ≤ Real.exp (t ^ 2 * n / 8) := Real.one_le_exp hexp_nonneg

/-- If no elements are sampled, the centered hypergeometric MGF is
deterministic. -/
lemma hypergeometricCenteredMGF_sum_of_n_eq_zero (N K : ℕ) (t : ℝ) :
    ∑ k ∈ Finset.range (0 + 1),
        chooseWeight N 0 K k *
          Real.exp (t * centeredSuccessCount N 0 K k) =
      1 := by
  simp [chooseWeight, centeredSuccessCount]

/-- The centered hypergeometric MGF bound when no elements are sampled. -/
lemma hypergeometricChooseCenteredMGF_le_of_n_eq_zero
    {N K : ℕ} (t : ℝ) :
    (∑ k ∈ Finset.range (0 + 1),
        chooseWeight N 0 K k *
          Real.exp (t * centeredSuccessCount N 0 K k)) /
      N.choose 0 ≤ Real.exp (t ^ 2 * (0 : ℕ) / 8) := by
  have hsum := hypergeometricCenteredMGF_sum_of_n_eq_zero N K t
  calc
    (∑ k ∈ Finset.range (0 + 1),
        chooseWeight N 0 K k *
          Real.exp (t * centeredSuccessCount N 0 K k)) /
      N.choose 0
        = 1 := by
          rw [hsum]
          simp
    _ ≤ Real.exp (t ^ 2 * (0 : ℕ) / 8) := by simp

/-- Centering identity for the branch where the first draw is a success. -/
lemma centeredSuccessCount_success_branch
    {N n K j : ℕ} (hNpos : 0 < N) (hnpos : 0 < n) (hKpos : 0 < K)
    (hn_lt_N : n < N) :
    centeredSuccessCount N n K (j + 1) =
      centeredSuccessCount (N - 1) (n - 1) (K - 1) j +
        ((N : ℝ) - K) * ((N : ℝ) - n) /
          ((N : ℝ) * ((N : ℝ) - 1)) := by
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hN_gt_one : 1 < N := lt_of_le_of_lt (Nat.succ_le_of_lt hnpos) hn_lt_N
  have hN_gt_one_real : (1 : ℝ) < N := by exact_mod_cast hN_gt_one
  have hNm1_ne : ((N : ℝ) - 1) ≠ 0 := ne_of_gt (sub_pos.mpr hN_gt_one_real)
  have hN_one_le : 1 ≤ N := Nat.succ_le_of_lt hNpos
  have hn_one_le : 1 ≤ n := Nat.succ_le_of_lt hnpos
  have hK_one_le : 1 ≤ K := Nat.succ_le_of_lt hKpos
  unfold centeredSuccessCount
  norm_num [Nat.cast_sub hN_one_le, Nat.cast_sub hn_one_le,
    Nat.cast_sub hK_one_le]
  field_simp [hN_ne, hNm1_ne]
  ring

/-- Centering identity for the branch where the first draw is a failure. -/
lemma centeredSuccessCount_failure_branch
    {N n K j : ℕ} (hNpos : 0 < N) (hnpos : 0 < n) (hn_lt_N : n < N) :
    centeredSuccessCount N n K j =
      centeredSuccessCount (N - 1) (n - 1) K j -
        (K : ℝ) * ((N : ℝ) - n) /
          ((N : ℝ) * ((N : ℝ) - 1)) := by
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hN_gt_one : 1 < N := lt_of_le_of_lt (Nat.succ_le_of_lt hnpos) hn_lt_N
  have hN_gt_one_real : (1 : ℝ) < N := by exact_mod_cast hN_gt_one
  have hNm1_ne : ((N : ℝ) - 1) ≠ 0 := ne_of_gt (sub_pos.mpr hN_gt_one_real)
  have hN_one_le : 1 ≤ N := Nat.succ_le_of_lt hNpos
  have hn_one_le : 1 ≤ n := Nat.succ_le_of_lt hnpos
  unfold centeredSuccessCount
  norm_num [Nat.cast_sub hN_one_le, Nat.cast_sub hn_one_le]
  field_simp [hN_ne, hNm1_ne]
  ring

/-- The first-draw success/failure offsets have a two-point MGF bounded by the
same unit-diameter Hoeffding envelope as one Bernoulli draw. -/
lemma hypergeometric_branch_offsets_mgf_le
    {N n K : ℕ} (hKN : K ≤ N) (hKpos : 0 < K) (hK_lt_N : K < N)
    (hnpos : 0 < n) (hn_lt_N : n < N) {t : ℝ} (ht : 0 ≤ t) :
    ((N - K : ℕ) : ℝ) / N *
        Real.exp (t * (-(K : ℝ) * ((N : ℝ) - n) /
          ((N : ℝ) * ((N : ℝ) - 1)))) +
      (K : ℝ) / N *
        Real.exp (t * (((N : ℝ) - K) * ((N : ℝ) - n) /
          ((N : ℝ) * ((N : ℝ) - 1)))) ≤
      Real.exp (t ^ 2 / 8) := by
  let p : ℝ := ((N - K : ℕ) : ℝ) / N
  let a : ℝ := -(K : ℝ) * ((N : ℝ) - n) /
    ((N : ℝ) * ((N : ℝ) - 1))
  let b : ℝ := ((N : ℝ) - K) * ((N : ℝ) - n) /
    ((N : ℝ) * ((N : ℝ) - 1))
  have hNpos : 0 < N := lt_of_lt_of_le hKpos hKN
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hN_pos_real : 0 < (N : ℝ) := Nat.cast_pos.mpr hNpos
  have hN_gt_one : 1 < N := lt_of_le_of_lt (Nat.succ_le_of_lt hKpos) hK_lt_N
  have hN_gt_one_real : (1 : ℝ) < N := by exact_mod_cast hN_gt_one
  have hNm1_pos : 0 < (N : ℝ) - 1 := sub_pos.mpr hN_gt_one_real
  have hNm1_ne : ((N : ℝ) - 1) ≠ 0 := ne_of_gt hNm1_pos
  have hKN_cast : ((N - K : ℕ) : ℝ) = (N : ℝ) - K := by
    exact Nat.cast_sub hKN
  have hp_nonneg : 0 ≤ p := by
    dsimp [p]
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg N)
  have hp_le_one : p ≤ 1 := by
    dsimp [p]
    rw [hKN_cast]
    exact (div_le_one hN_pos_real).mpr
      (sub_le_self (N : ℝ) (Nat.cast_nonneg K))
  have hdiff : b - a = ((N : ℝ) - n) / ((N : ℝ) - 1) := by
    dsimp [a, b]
    field_simp [hN_ne, hNm1_ne]
    ring
  have hab : a ≤ b := by
    have hn_le_N_real : (n : ℝ) ≤ N := by exact_mod_cast le_of_lt hn_lt_N
    have hdiff_nonneg : 0 ≤ b - a := by
      rw [hdiff]
      exact div_nonneg (sub_nonneg.mpr hn_le_N_real) (le_of_lt hNm1_pos)
    exact sub_nonneg.mp hdiff_nonneg
  have hdiam : b - a ≤ 1 := by
    rw [hdiff]
    have hn_ge_one_real : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt hnpos
    have hnum_le : (N : ℝ) - n ≤ (N : ℝ) - 1 :=
      sub_le_sub_left hn_ge_one_real (N : ℝ)
    exact (div_le_one hNm1_pos).mpr hnum_le
  have hmean : p * a + (1 - p) * b = 0 := by
    dsimp [p, a, b]
    rw [hKN_cast]
    field_simp [hN_ne, hNm1_ne]
    ring
  have hp_compl : 1 - p = (K : ℝ) / N := by
    dsimp [p]
    rw [hKN_cast]
    field_simp [hN_ne]
    ring
  have htwo :=
    twoPoint_centeredMGF_le
      (p := p) (a := a) (b := b) (t := t)
      hp_nonneg hp_le_one hab hdiam hmean ht
  rw [hp_compl] at htwo
  simpa [p, a, b] using htwo

/-- Success-branch choose weights carry the `k / n` factor that appears when an
unordered hypergeometric count is represented by conditioning an ordered sample
on a successful first draw. -/
lemma chooseWeight_success_branch_mul
    {N n K j : ℕ} (hKN : K ≤ N) (hKpos : 0 < K) :
    (K : ℝ) * chooseWeight (N - 1) (n - 1) (K - 1) j =
      ((j + 1 : ℕ) : ℝ) * chooseWeight N n K (j + 1) := by
  have hNK : (N - 1) - (K - 1) = N - K := by omega
  have hnj : (n - 1) - j = n - (j + 1) := by omega
  have hK : K - 1 + 1 = K := Nat.sub_add_cancel (Nat.succ_le_of_lt hKpos)
  have hchoose := Nat.add_one_mul_choose_eq (K - 1) j
  rw [hK] at hchoose
  unfold chooseWeight
  norm_num [hNK, hnj]
  exact_mod_cast
    (calc
      K * ((K - 1).choose j * (N - K).choose (n - (j + 1))) =
          (K * (K - 1).choose j) * (N - K).choose (n - (j + 1)) := by ring
      _ = (K.choose (j + 1) * (j + 1)) * (N - K).choose (n - (j + 1)) := by
          rw [hchoose]
      _ = (j + 1) * (K.choose (j + 1) * (N - K).choose (n - (j + 1))) := by ring)

/-- Failure-branch choose weights carry the complementary `(n-k) / n` factor
from the ordered first-draw decomposition. -/
lemma chooseWeight_failure_branch_mul
    {N n K j : ℕ} (hK_lt_N : K < N) (hj : j < n) :
    ((N - K : ℕ) : ℝ) * chooseWeight (N - 1) (n - 1) K j =
      ((n - j : ℕ) : ℝ) * chooseWeight N n K j := by
  have hNKpos : 0 < N - K := Nat.sub_pos_of_lt hK_lt_N
  have hNK : (N - 1) - K + 1 = N - K := by omega
  have hnj : (n - 1) - j + 1 = n - j := by omega
  have hNsub : (N - 1) - K = (N - K) - 1 := by omega
  have hchoose := Nat.add_one_mul_choose_eq ((N - K) - 1) ((n - 1) - j)
  have hleft :
      ((N - K) - 1 + 1) * ((N - K) - 1).choose ((n - 1) - j) =
        (N - K) * ((N - 1) - K).choose ((n - 1) - j) := by
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hNKpos), hNsub]
  have hright :
      (((N - K) - 1) + 1).choose (((n - 1) - j) + 1) *
          (((n - 1) - j) + 1) =
        (N - K).choose (n - j) * (n - j) := by
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hNKpos), hnj]
  rw [hleft, hright] at hchoose
  rw [hNsub] at hchoose
  unfold chooseWeight
  norm_num [hNsub]
  exact_mod_cast
    (calc
      (N - K) * (K.choose j * ((N - K) - 1).choose ((n - 1) - j)) =
          K.choose j * ((N - K) * ((N - K) - 1).choose ((n - 1) - j)) := by ring
      _ = K.choose j * ((N - K).choose (n - j) * (n - j)) := by rw [hchoose]
      _ = (n - j) * (K.choose j * (N - K).choose (n - j)) := by ring)

/-- The denominator recurrence for conditioning an unordered sample on its
first ordered draw. -/
lemma choose_sample_mul_eq_population_mul_pred_choose
    {N n : ℕ} (hnpos : 0 < n) (hn_le_N : n ≤ N) :
    (n : ℝ) * (N.choose n : ℝ) =
      (N : ℝ) * ((N - 1).choose (n - 1) : ℝ) := by
  have hNpos : 0 < N := lt_of_lt_of_le hnpos hn_le_N
  have hNsub : N - 1 + 1 = N := Nat.sub_add_cancel (Nat.succ_le_of_lt hNpos)
  have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hnpos)
  have hchoose := Nat.add_one_mul_choose_eq (N - 1) (n - 1)
  rw [hNsub, hnsub] at hchoose
  exact_mod_cast
    (calc
      n * N.choose n = N.choose n * n := by rw [Nat.mul_comm]
      _ = N * (N - 1).choose (n - 1) := hchoose.symm)

/-- Split a finite sum according to whether the first element of a uniformly
ordered `n`-sample comes from the `k` marked positions or from its complement. -/
lemma sum_range_first_draw_split (f : ℕ → ℝ) {n : ℕ} (hnpos : 0 < n) :
    ∑ k ∈ Finset.range (n + 1), f k =
      ∑ j ∈ Finset.range n, (((j + 1 : ℕ) : ℝ) / n) * f (j + 1) +
        ∑ j ∈ Finset.range n, (((n - j : ℕ) : ℝ) / n) * f j := by
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hsuccess :
      ∑ j ∈ Finset.range n, (((j + 1 : ℕ) : ℝ) / n) * f (j + 1) =
        ∑ k ∈ Finset.range (n + 1), ((k : ℝ) / n) * f k := by
    rw [Finset.sum_range_succ' (fun k => ((k : ℝ) / n) * f k) n]
    simp
  have hfailure :
      ∑ j ∈ Finset.range n, (((n - j : ℕ) : ℝ) / n) * f j =
        ∑ k ∈ Finset.range (n + 1), (((n - k : ℕ) : ℝ) / n) * f k := by
    rw [Finset.sum_range_succ (fun k => (((n - k : ℕ) : ℝ) / n) * f k) n]
    simp
  rw [hsuccess, hfailure, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hsum : (k : ℝ) + ((n - k : ℕ) : ℝ) = n := by
    norm_num [Nat.cast_sub hk_le]
  calc
    f k = 1 * f k := by ring
    _ = (((k : ℝ) / n) + (((n - k : ℕ) : ℝ) / n)) * f k := by
      congr 1
      field_simp [hn_ne]
      exact hsum.symm
    _ = (k : ℝ) / n * f k + ((n - k : ℕ) : ℝ) / n * f k := by ring

/-- The success branch term is the `k / n` part of the original
hypergeometric term. -/
lemma hypergeometric_success_branch_term
    {N n K j : ℕ} (hKN : K ≤ N) (hKpos : 0 < K)
    (hnpos : 0 < n) (hn_lt_N : n < N) (t : ℝ) :
    (K : ℝ) / n *
        Real.exp (t * (((N : ℝ) - K) * ((N : ℝ) - n) /
          ((N : ℝ) * ((N : ℝ) - 1)))) *
        (chooseWeight (N - 1) (n - 1) (K - 1) j *
          Real.exp (t * centeredSuccessCount (N - 1) (n - 1) (K - 1) j)) =
      (((j + 1 : ℕ) : ℝ) / n) *
        (chooseWeight N n K (j + 1) *
          Real.exp (t * centeredSuccessCount N n K (j + 1))) := by
  let successOffset : ℝ := ((N : ℝ) - K) * ((N : ℝ) - n) /
    ((N : ℝ) * ((N : ℝ) - 1))
  have hNpos : 0 < N := lt_of_lt_of_le hnpos (le_of_lt hn_lt_N)
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hcenter :=
    centeredSuccessCount_success_branch
      (N := N) (n := n) (K := K) (j := j) hNpos hnpos hKpos hn_lt_N
  have hweight :=
    chooseWeight_success_branch_mul
      (N := N) (n := n) (K := K) (j := j) hKN hKpos
  have hexp :
      Real.exp (t * centeredSuccessCount N n K (j + 1)) =
        Real.exp (t * successOffset) *
          Real.exp (t * centeredSuccessCount (N - 1) (n - 1) (K - 1) j) := by
    rw [hcenter]
    rw [show t * (centeredSuccessCount (N - 1) (n - 1) (K - 1) j +
        successOffset) =
        t * successOffset + t * centeredSuccessCount (N - 1) (n - 1) (K - 1) j by ring]
    rw [Real.exp_add]
  have hweight_div :
      (K : ℝ) / n * chooseWeight (N - 1) (n - 1) (K - 1) j =
        (((j + 1 : ℕ) : ℝ) / n) * chooseWeight N n K (j + 1) := by
    field_simp [hn_ne]
    exact hweight
  change
    (K : ℝ) / n * Real.exp (t * successOffset) *
        (chooseWeight (N - 1) (n - 1) (K - 1) j *
          Real.exp (t * centeredSuccessCount (N - 1) (n - 1) (K - 1) j)) =
      (((j + 1 : ℕ) : ℝ) / n) *
        (chooseWeight N n K (j + 1) *
          Real.exp (t * centeredSuccessCount N n K (j + 1)))
  rw [hexp]
  calc
    (K : ℝ) / n * Real.exp (t * successOffset) *
        (chooseWeight (N - 1) (n - 1) (K - 1) j *
          Real.exp (t * centeredSuccessCount (N - 1) (n - 1) (K - 1) j))
        =
        ((K : ℝ) / n * chooseWeight (N - 1) (n - 1) (K - 1) j) *
          (Real.exp (t * successOffset) *
            Real.exp (t * centeredSuccessCount (N - 1) (n - 1) (K - 1) j)) := by ring
    _ =
        ((((j + 1 : ℕ) : ℝ) / n) * chooseWeight N n K (j + 1)) *
          (Real.exp (t * successOffset) *
            Real.exp (t * centeredSuccessCount (N - 1) (n - 1) (K - 1) j)) := by
          rw [hweight_div]
    _ =
        (((j + 1 : ℕ) : ℝ) / n) *
          (chooseWeight N n K (j + 1) *
            (Real.exp (t * successOffset) *
              Real.exp (t * centeredSuccessCount (N - 1) (n - 1) (K - 1) j))) := by ring

/-- The failure branch term is the `(n-k) / n` part of the original
hypergeometric term. -/
lemma hypergeometric_failure_branch_term
    {N n K j : ℕ} (hK_lt_N : K < N) (hnpos : 0 < n) (hn_lt_N : n < N)
    (hj : j < n) (t : ℝ) :
    ((N - K : ℕ) : ℝ) / n *
        Real.exp (t * (-(K : ℝ) * ((N : ℝ) - n) /
          ((N : ℝ) * ((N : ℝ) - 1)))) *
        (chooseWeight (N - 1) (n - 1) K j *
          Real.exp (t * centeredSuccessCount (N - 1) (n - 1) K j)) =
      (((n - j : ℕ) : ℝ) / n) *
        (chooseWeight N n K j *
          Real.exp (t * centeredSuccessCount N n K j)) := by
  let failureOffset : ℝ := -(K : ℝ) * ((N : ℝ) - n) /
    ((N : ℝ) * ((N : ℝ) - 1))
  have hNpos : 0 < N := lt_of_lt_of_le hnpos (le_of_lt hn_lt_N)
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hcenter :=
    centeredSuccessCount_failure_branch
      (N := N) (n := n) (K := K) (j := j) hNpos hnpos hn_lt_N
  have hweight :=
    chooseWeight_failure_branch_mul
      (N := N) (n := n) (K := K) (j := j) hK_lt_N hj
  have hfailure :
      centeredSuccessCount (N - 1) (n - 1) K j -
          (K : ℝ) * ((N : ℝ) - n) / ((N : ℝ) * ((N : ℝ) - 1)) =
        centeredSuccessCount (N - 1) (n - 1) K j + failureOffset := by
    dsimp [failureOffset]
    ring
  have hexp :
      Real.exp (t * centeredSuccessCount N n K j) =
        Real.exp (t * failureOffset) *
          Real.exp (t * centeredSuccessCount (N - 1) (n - 1) K j) := by
    rw [hcenter, hfailure]
    rw [show t * (centeredSuccessCount (N - 1) (n - 1) K j + failureOffset) =
        t * failureOffset + t * centeredSuccessCount (N - 1) (n - 1) K j by ring]
    rw [Real.exp_add]
  have hweight_div :
      ((N - K : ℕ) : ℝ) / n * chooseWeight (N - 1) (n - 1) K j =
        (((n - j : ℕ) : ℝ) / n) * chooseWeight N n K j := by
    field_simp [hn_ne]
    exact hweight
  change
    ((N - K : ℕ) : ℝ) / n * Real.exp (t * failureOffset) *
        (chooseWeight (N - 1) (n - 1) K j *
          Real.exp (t * centeredSuccessCount (N - 1) (n - 1) K j)) =
      (((n - j : ℕ) : ℝ) / n) *
        (chooseWeight N n K j *
          Real.exp (t * centeredSuccessCount N n K j))
  rw [hexp]
  calc
    ((N - K : ℕ) : ℝ) / n * Real.exp (t * failureOffset) *
        (chooseWeight (N - 1) (n - 1) K j *
          Real.exp (t * centeredSuccessCount (N - 1) (n - 1) K j))
        =
        (((N - K : ℕ) : ℝ) / n * chooseWeight (N - 1) (n - 1) K j) *
          (Real.exp (t * failureOffset) *
            Real.exp (t * centeredSuccessCount (N - 1) (n - 1) K j)) := by ring
    _ =
        ((((n - j : ℕ) : ℝ) / n) * chooseWeight N n K j) *
          (Real.exp (t * failureOffset) *
            Real.exp (t * centeredSuccessCount (N - 1) (n - 1) K j)) := by
          rw [hweight_div]
    _ =
        (((n - j : ℕ) : ℝ) / n) *
          (chooseWeight N n K j *
            (Real.exp (t * failureOffset) *
              Real.exp (t * centeredSuccessCount (N - 1) (n - 1) K j))) := by ring

/-- The real-valued hypergeometric choose weights sum to `N.choose n`. -/
lemma chooseWeight_sum_eq_choose
    {N n K : ℕ} (hKN : K ≤ N) :
    ∑ k ∈ Finset.range (n + 1), chooseWeight N n K k = N.choose n := by
  unfold chooseWeight
  rw [← Nat.cast_sum]
  have hV := Nat.add_choose_eq K (N - K) n
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => K.choose i * (N - K).choose j) n] at hV
  have hsum : K + (N - K) = N := Nat.add_sub_of_le hKN
  simpa [chooseWeight, Nat.succ_eq_add_one, hsum] using congrArg (fun m : ℕ => (m : ℝ)) hV.symm

/-- If the sample is the whole population, the centered hypergeometric MGF is
deterministic. -/
lemma hypergeometricCenteredMGF_sum_of_sample_eq_population
    {N K : ℕ} (hKN : K ≤ N) (hN : N ≠ 0) (t : ℝ) :
    ∑ k ∈ Finset.range (N + 1),
        chooseWeight N N K k *
          Real.exp (t * centeredSuccessCount N N K k) =
      1 := by
  classical
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  rw [Finset.sum_eq_single K]
  · have hcenter : centeredSuccessCount N N K K = 0 := by
      unfold centeredSuccessCount
      field_simp [hN_ne]
      ring
    simp [chooseWeight, hcenter]
  · intro k hk hk_ne
    by_cases hk_le : k ≤ K
    · have hk_lt : k < K := lt_of_le_of_ne hk_le hk_ne
      have hchoose_lt : N - K < N - k := by omega
      have hchoose : (N - K).choose (N - k) = 0 :=
        Nat.choose_eq_zero_of_lt hchoose_lt
      simp [chooseWeight, hchoose]
    · have hK_lt : K < k := by omega
      have hchoose : K.choose k = 0 := Nat.choose_eq_zero_of_lt hK_lt
      simp [chooseWeight, hchoose]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hKN))).elim

/-- The centered hypergeometric MGF bound when the sample is the whole
population. -/
lemma hypergeometricChooseCenteredMGF_le_of_sample_eq_population
    {N K : ℕ} (hKN : K ≤ N) (hN : N ≠ 0) (t : ℝ) :
    (∑ k ∈ Finset.range (N + 1),
        chooseWeight N N K k *
          Real.exp (t * centeredSuccessCount N N K k)) /
      N.choose N ≤ Real.exp (t ^ 2 * N / 8) := by
  have hsum := hypergeometricCenteredMGF_sum_of_sample_eq_population (N := N) (K := K) hKN hN t
  have hexp_nonneg : 0 ≤ t ^ 2 * (N : ℝ) / 8 := by positivity
  calc
    (∑ k ∈ Finset.range (N + 1),
        chooseWeight N N K k *
          Real.exp (t * centeredSuccessCount N N K k)) /
      N.choose N
        = 1 := by
          rw [hsum]
          simp
    _ ≤ Real.exp (t ^ 2 * N / 8) := Real.one_le_exp hexp_nonneg

/-- Unnormalized first-draw recurrence for the centered hypergeometric MGF
sum. The coefficients are divided by `n` because an unordered sample with `k`
successes has a successful first ordered draw in `k / n` of its orderings. -/
lemma centeredHypergeometricMGF_sum_first_draw
    {N n K : ℕ} (hKN : K ≤ N) (hKpos : 0 < K) (hK_lt_N : K < N)
    (hnpos : 0 < n) (hn_lt_N : n < N) (t : ℝ) :
    ∑ k ∈ Finset.range (n + 1),
        chooseWeight N n K k *
          Real.exp (t * centeredSuccessCount N n K k) =
      (K : ℝ) / n *
          Real.exp (t * (((N : ℝ) - K) * ((N : ℝ) - n) /
            ((N : ℝ) * ((N : ℝ) - 1)))) *
          ∑ j ∈ Finset.range n,
            chooseWeight (N - 1) (n - 1) (K - 1) j *
              Real.exp (t * centeredSuccessCount (N - 1) (n - 1) (K - 1) j) +
        ((N - K : ℕ) : ℝ) / n *
          Real.exp (t * (-(K : ℝ) * ((N : ℝ) - n) /
            ((N : ℝ) * ((N : ℝ) - 1)))) *
          ∑ j ∈ Finset.range n,
            chooseWeight (N - 1) (n - 1) K j *
              Real.exp (t * centeredSuccessCount (N - 1) (n - 1) K j) := by
  let f : ℕ → ℝ := fun k =>
    chooseWeight N n K k * Real.exp (t * centeredSuccessCount N n K k)
  have hsplit := sum_range_first_draw_split f hnpos
  have hsuccess :
      ∑ j ∈ Finset.range n, (((j : ℝ) + 1) / n) * f (j + 1) =
        (K : ℝ) / n *
          Real.exp (t * (((N : ℝ) - K) * ((N : ℝ) - n) /
            ((N : ℝ) * ((N : ℝ) - 1)))) *
          ∑ j ∈ Finset.range n,
            chooseWeight (N - 1) (n - 1) (K - 1) j *
              Real.exp (t * centeredSuccessCount (N - 1) (n - 1) (K - 1) j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    dsimp [f]
    symm
    simpa using
      (hypergeometric_success_branch_term
        (N := N) (n := n) (K := K) (j := j) hKN hKpos hnpos hn_lt_N t)
  have hfailure :
      ∑ j ∈ Finset.range n, (((n - j : ℕ) : ℝ) / n) * f j =
        ((N - K : ℕ) : ℝ) / n *
          Real.exp (t * (-(K : ℝ) * ((N : ℝ) - n) /
            ((N : ℝ) * ((N : ℝ) - 1)))) *
          ∑ j ∈ Finset.range n,
            chooseWeight (N - 1) (n - 1) K j *
              Real.exp (t * centeredSuccessCount (N - 1) (n - 1) K j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [f]
    symm
    exact hypergeometric_failure_branch_term
      (N := N) (n := n) (K := K) (j := j) hK_lt_N hnpos hn_lt_N
      (Finset.mem_range.mp hj) t
  simpa [f, hsuccess, hfailure] using hsplit

/-- First-draw recurrence for the normalized centered hypergeometric MGF.

The two recursive terms condition on whether the first ordered draw is a
success or a failure; the offsets are exactly the centering corrections proved
in `centeredSuccessCount_success_branch` and
`centeredSuccessCount_failure_branch`. -/
lemma centeredHypergeometricMGF_first_draw
    {N n K : ℕ} (hKN : K ≤ N) (hKpos : 0 < K) (hK_lt_N : K < N)
    (hnpos : 0 < n) (hn_lt_N : n < N) (t : ℝ) :
    centeredHypergeometricMGF N n K t =
      (K : ℝ) / N *
          Real.exp (t * (((N : ℝ) - K) * ((N : ℝ) - n) /
            ((N : ℝ) * ((N : ℝ) - 1)))) *
          centeredHypergeometricMGF (N - 1) (n - 1) (K - 1) t +
        ((N - K : ℕ) : ℝ) / N *
          Real.exp (t * (-(K : ℝ) * ((N : ℝ) - n) /
            ((N : ℝ) * ((N : ℝ) - 1)))) *
          centeredHypergeometricMGF (N - 1) (n - 1) K t := by
  have hn_le_N : n ≤ N := le_of_lt hn_lt_N
  have hNpos : 0 < N := lt_of_lt_of_le hnpos hn_le_N
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hpred_le : n - 1 ≤ N - 1 := Nat.sub_le_sub_right hn_le_N 1
  have hpred_choose_pos : 0 < (N - 1).choose (n - 1) := Nat.choose_pos hpred_le
  have hpred_choose_ne : ((N - 1).choose (n - 1) : ℝ) ≠ 0 := by
    exact_mod_cast hpred_choose_pos.ne'
  have hrange : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hnpos)
  have hden :=
    choose_sample_mul_eq_population_mul_pred_choose
      (N := N) (n := n) hnpos hn_le_N
  have hden' :
      (N.choose n : ℝ) =
        (N : ℝ) * ((N - 1).choose (n - 1) : ℝ) / n := by
    field_simp [hn_ne]
    simpa [mul_comm] using hden
  have hsum :=
    centeredHypergeometricMGF_sum_first_draw
      (N := N) (n := n) (K := K) hKN hKpos hK_lt_N hnpos hn_lt_N t
  unfold centeredHypergeometricMGF
  rw [hsum, hrange, hden']
  field_simp [hN_ne, hn_ne, hpred_choose_ne]

/-- Nondegenerate induction step for the centered hypergeometric MGF bound. -/
lemma centeredHypergeometricMGF_le_exp_of_recursion
    {N n K : ℕ} (hKN : K ≤ N) (hKpos : 0 < K) (hK_lt_N : K < N)
    (hnpos : 0 < n) (hn_lt_N : n < N) (t : ℝ) (ht : 0 ≤ t)
    (hsuccess :
      centeredHypergeometricMGF (N - 1) (n - 1) (K - 1) t ≤
        Real.exp (t ^ 2 * (n - 1 : ℕ) / 8))
    (hfailure :
      centeredHypergeometricMGF (N - 1) (n - 1) K t ≤
        Real.exp (t ^ 2 * (n - 1 : ℕ) / 8)) :
    centeredHypergeometricMGF N n K t ≤ Real.exp (t ^ 2 * n / 8) := by
  let successOffset : ℝ := ((N : ℝ) - K) * ((N : ℝ) - n) /
    ((N : ℝ) * ((N : ℝ) - 1))
  let failureOffset : ℝ := -(K : ℝ) * ((N : ℝ) - n) /
    ((N : ℝ) * ((N : ℝ) - 1))
  let E : ℝ := Real.exp (t ^ 2 * (n - 1 : ℕ) / 8)
  have hsuccess_term :
      (K : ℝ) / N * Real.exp (t * successOffset) *
          centeredHypergeometricMGF (N - 1) (n - 1) (K - 1) t ≤
        (K : ℝ) / N * Real.exp (t * successOffset) * E := by
    have hcoef_nonneg :
        0 ≤ (K : ℝ) / N * Real.exp (t * successOffset) := by
      exact mul_nonneg
        (div_nonneg (Nat.cast_nonneg K) (Nat.cast_nonneg N))
        (le_of_lt (Real.exp_pos _))
    exact mul_le_mul_of_nonneg_left hsuccess hcoef_nonneg
  have hfailure_term :
      ((N - K : ℕ) : ℝ) / N * Real.exp (t * failureOffset) *
          centeredHypergeometricMGF (N - 1) (n - 1) K t ≤
        ((N - K : ℕ) : ℝ) / N * Real.exp (t * failureOffset) * E := by
    have hcoef_nonneg :
        0 ≤ ((N - K : ℕ) : ℝ) / N * Real.exp (t * failureOffset) := by
      exact mul_nonneg
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg N))
        (le_of_lt (Real.exp_pos _))
    exact mul_le_mul_of_nonneg_left hfailure hcoef_nonneg
  have hbranch :
      ((N - K : ℕ) : ℝ) / N * Real.exp (t * failureOffset) +
          (K : ℝ) / N * Real.exp (t * successOffset) ≤
        Real.exp (t ^ 2 / 8) := by
    exact hypergeometric_branch_offsets_mgf_le
      (N := N) (n := n) (K := K) hKN hKpos hK_lt_N hnpos hn_lt_N ht
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact le_of_lt (Real.exp_pos _)
  have hrec :=
    centeredHypergeometricMGF_first_draw
      (N := N) (n := n) (K := K) hKN hKpos hK_lt_N hnpos hn_lt_N t
  calc
    centeredHypergeometricMGF N n K t
        = (K : ℝ) / N * Real.exp (t * successOffset) *
            centeredHypergeometricMGF (N - 1) (n - 1) (K - 1) t +
          ((N - K : ℕ) : ℝ) / N * Real.exp (t * failureOffset) *
            centeredHypergeometricMGF (N - 1) (n - 1) K t := by
            simpa [successOffset, failureOffset] using hrec
    _ ≤ (K : ℝ) / N * Real.exp (t * successOffset) * E +
          ((N - K : ℕ) : ℝ) / N * Real.exp (t * failureOffset) * E :=
        add_le_add hsuccess_term hfailure_term
    _ = E * (((N - K : ℕ) : ℝ) / N * Real.exp (t * failureOffset) +
          (K : ℝ) / N * Real.exp (t * successOffset)) := by ring
    _ ≤ E * Real.exp (t ^ 2 / 8) :=
        mul_le_mul_of_nonneg_left hbranch hE_nonneg
    _ = Real.exp (t ^ 2 * n / 8) := by
        dsimp [E]
        rw [← Real.exp_add]
        congr 1
        have hn_one_le : 1 ≤ n := Nat.succ_le_of_lt hnpos
        norm_num [Nat.cast_sub hn_one_le]
        ring

/-- MGF comparison for hypergeometric choose weights, including the
zero-sample base case needed by the first-draw induction. -/
lemma centeredHypergeometricMGF_le_exp
    {N n K : ℕ} (hKN : K ≤ N) (hN : n ≤ N)
    (t : ℝ) (ht : 0 ≤ t) :
    centeredHypergeometricMGF N n K t ≤ Real.exp (t ^ 2 * n / 8) := by
  classical
  revert N K
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro N K hKN hN
      by_cases hn0 : n = 0
      · subst n
        simpa [centeredHypergeometricMGF]
          using hypergeometricChooseCenteredMGF_le_of_n_eq_zero (N := N) (K := K) t
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      by_cases hK0 : K = 0
      · subst K
        simpa [centeredHypergeometricMGF]
          using hypergeometricChooseCenteredMGF_le_of_zero_success (N := N) (n := n) hN t
      have hKpos : 0 < K := Nat.pos_of_ne_zero hK0
      by_cases hKN_eq : K = N
      · subst K
        simpa [centeredHypergeometricMGF]
          using hypergeometricChooseCenteredMGF_le_of_success_eq_population
            (N := N) (n := n) hN hn0 t
      have hK_lt_N : K < N := lt_of_le_of_ne hKN hKN_eq
      by_cases hnN : n = N
      · subst n
        simpa [centeredHypergeometricMGF]
          using hypergeometricChooseCenteredMGF_le_of_sample_eq_population
            (N := N) (K := K) hKN hn0 t
      have hn_lt_N : n < N := lt_of_le_of_ne hN hnN
      have hn_pred_lt : n - 1 < n := by omega
      have hKN_success : K - 1 ≤ N - 1 := Nat.sub_le_sub_right hKN 1
      have hn_success : n - 1 ≤ N - 1 := Nat.sub_le_sub_right hN 1
      have hKN_failure : K ≤ N - 1 := by omega
      have hsuccess :=
        ih (n - 1) hn_pred_lt (N := N - 1) (K := K - 1) hKN_success hn_success
      have hfailure :=
        ih (n - 1) hn_pred_lt (N := N - 1) (K := K) hKN_failure hn_success
      exact centeredHypergeometricMGF_le_exp_of_recursion
        (N := N) (n := n) (K := K) hKN hKpos hK_lt_N hnpos hn_lt_N t ht
        hsuccess hfailure

/-- MGF comparison for hypergeometric choose weights.

This is the remaining analytic without-replacement concentration core: the
centered hypergeometric MGF is bounded by the Hoeffding sub-Gaussian envelope. -/
lemma hypergeometricChooseCenteredMGF_le
    {N n K : ℕ} (hKN : K ≤ N) (hN : n ≤ N) (_hn : n ≠ 0)
    (t : ℝ) (ht : 0 ≤ t) :
    (∑ k ∈ Finset.range (n + 1),
        chooseWeight N n K k *
          Real.exp (t * centeredSuccessCount N n K k)) /
      N.choose n ≤ Real.exp (t ^ 2 * n / 8) := by
  simpa [centeredHypergeometricMGF]
    using centeredHypergeometricMGF_le_exp
      (N := N) (n := n) (K := K) hKN hN t ht

end Math.Concentration.HypergeometricTail
