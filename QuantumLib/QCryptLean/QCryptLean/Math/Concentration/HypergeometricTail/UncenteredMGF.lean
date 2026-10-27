import Mathlib.Analysis.MeanInequalities
import QCryptLean.Math.Concentration.HypergeometricTail.Basic
import QCryptLean.Math.Concentration.HypergeometricTail.MGF

/-!
# Un-centered WOR→WR moment-generating-function domination

This file proves the **without-replacement (hypergeometric) convex domination** of the
un-centered `c`-power moment-generating function by the with-replacement (binomial) MGF at the
same population rate `p = K/N` (Hoeffding 1963, *Probability inequalities for sums of bounded
random variables*, J. Amer. Statist. Assoc. 58, Theorem 4):

  `(∑_k chooseWeight N m K k · c^k) / C(N,m)  ≤  ((K/N)·c + (N-K)/N)^m`   (**DOM**)

for `0 < c ≤ 1`.  This is the "un-centered, fixed-rate" analogue of the centered
sub-Gaussian recursion `Math.Concentration.HypergeometricTail.centeredHypergeometricMGF_first_draw`
(`MGF.lean`), whose base rate `K/N` drifts along the first-draw recursion.

The whole domination collapses to one elementary power inequality
(`one_add_pow_mul_one_sub_nmul_le_one`, `(1+t)^M(1-M·t) ≤ 1`) applied twice, plus the linear
side condition `M ≤ N-1` ("the sample fits the population").  The per-step comparison is FALSE
off the reachable range `M ≤ N-2`; the load-bearing hypothesis `n < N` is carried into
`weighted_gBase_pow_le` (`n = N` is a separate base case).

References: Hoeffding (1963), Theorem 4; Cover–Thomas §11.1.
-/

open scoped BigOperators

namespace Math.Concentration.HypergeometricTail

/-- Envelope base: the with-replacement per-draw `c`-MGF at population rate `K/N`. -/
noncomputable def gBase (N K : ℕ) (c : ℝ) : ℝ :=
  (K : ℝ) / N * c + ((N - K : ℕ) : ℝ) / N

/-- Normalized un-centered hypergeometric `c`-power MGF  `E_WOR[c^S]`. -/
noncomputable def hypergeometricPowMGF (N n K : ℕ) (c : ℝ) : ℝ :=
  (∑ k ∈ Finset.range (n + 1), chooseWeight N n K k * c ^ k) / (N.choose n : ℝ)

/-- **The elementary two-sided power bound.**  For `0 ≤ 1 + t`,
`(1 + t) ^ M · (1 - M · t) ≤ 1`.  The `0 ≤ 1 + t` hypothesis is load-bearing (fails for `t < -1`
at even `M`).  Applied at `t ≥ 0` for the upper base and at `t ∈ (-1, 0]` for the lower base. -/
lemma one_add_pow_mul_one_sub_nmul_le_one (t : ℝ) (ht : 0 ≤ 1 + t) (M : ℕ) :
    (1 + t) ^ M * (1 - (M : ℝ) * t) ≤ 1 := by
  induction M with
  | zero => simp
  | succ M ih =>
      have hpow_nonneg : 0 ≤ (1 + t) ^ M := pow_nonneg ht M
      have hstep : (1 + t) * (1 - ((M : ℝ) + 1) * t) ≤ 1 - (M : ℝ) * t := by
        nlinarith [sq_nonneg t, hpow_nonneg]
      have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      calc
        (1 + t) ^ (M + 1) * (1 - ((M : ℝ) + 1) * t)
            = (1 + t) ^ M * ((1 + t) * (1 - ((M : ℝ) + 1) * t)) := by
              ring
        _ ≤ (1 + t) ^ M * (1 - (M : ℝ) * t) :=
              mul_le_mul_of_nonneg_left hstep hpow_nonneg
        _ ≤ 1 := ih

/-- **Raw first-draw split of the un-centered `c`-power sum.**  Mirror of
`centeredHypergeometricMGF_sum_first_draw` (`MGF.lean`) with `exp(t·centeredSuccessCount)`
replaced by `c^k`. -/
lemma sum_chooseWeight_mul_pow_eq_recursion
    {N n K : ℕ} (hKN : K ≤ N) (hKpos : 0 < K) (hK_lt_N : K < N)
    (hnpos : 0 < n) (c : ℝ) :
    ∑ k ∈ Finset.range (n + 1), chooseWeight N n K k * c ^ k
      = (K : ℝ) / n * c *
          (∑ j ∈ Finset.range n, chooseWeight (N - 1) (n - 1) (K - 1) j * c ^ j)
        + ((N - K : ℕ) : ℝ) / n *
          (∑ j ∈ Finset.range n, chooseWeight (N - 1) (n - 1) K j * c ^ j) := by
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
  let f : ℕ → ℝ := fun k => chooseWeight N n K k * c ^ k
  have hsplit := sum_range_first_draw_split f hnpos
  have hsuccess :
      ∑ j ∈ Finset.range n, (((j : ℝ) + 1) / n) * f (j + 1) =
        (K : ℝ) / n * c *
          ∑ j ∈ Finset.range n, chooseWeight (N - 1) (n - 1) (K - 1) j * c ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    have hweight :=
      chooseWeight_success_branch_mul (N := N) (n := n) (K := K) (j := j) hKN hKpos
    have hweight_div :
        (K : ℝ) / n * chooseWeight (N - 1) (n - 1) (K - 1) j =
          (((j + 1 : ℕ) : ℝ) / n) * chooseWeight N n K (j + 1) := by
      field_simp [hn_ne]
      exact hweight
    dsimp [f]
    have hcj : c ^ (j + 1) = c * c ^ j := by ring
    push_cast at hweight_div ⊢
    rw [hcj]
    calc
      (((j : ℝ) + 1) / n) * (chooseWeight N n K (j + 1) * (c * c ^ j))
          = ((((j : ℝ) + 1) / n) * chooseWeight N n K (j + 1)) * (c * c ^ j) := by ring
      _ = ((K : ℝ) / n * chooseWeight (N - 1) (n - 1) (K - 1) j) * (c * c ^ j) := by
            rw [hweight_div]
      _ = (K : ℝ) / n * c * (chooseWeight (N - 1) (n - 1) (K - 1) j * c ^ j) := by ring
  have hfailure :
      ∑ j ∈ Finset.range n, (((n - j : ℕ) : ℝ) / n) * f j =
        ((N - K : ℕ) : ℝ) / n *
          ∑ j ∈ Finset.range n, chooseWeight (N - 1) (n - 1) K j * c ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have hweight :=
      chooseWeight_failure_branch_mul (N := N) (n := n) (K := K) (j := j) hK_lt_N hjn
    have hweight_div :
        ((N - K : ℕ) : ℝ) / n * chooseWeight (N - 1) (n - 1) K j =
          (((n - j : ℕ) : ℝ) / n) * chooseWeight N n K j := by
      field_simp [hn_ne]
      exact hweight
    dsimp [f]
    calc
      (((n - j : ℕ) : ℝ) / n) * (chooseWeight N n K j * c ^ j)
          = ((((n - j : ℕ) : ℝ) / n) * chooseWeight N n K j) * c ^ j := by ring
      _ = (((N - K : ℕ) : ℝ) / n * chooseWeight (N - 1) (n - 1) K j) * c ^ j := by
            rw [hweight_div]
      _ = ((N - K : ℕ) : ℝ) / n * (chooseWeight (N - 1) (n - 1) K j * c ^ j) := by ring
  calc
    ∑ k ∈ Finset.range (n + 1), chooseWeight N n K k * c ^ k
        = ∑ j ∈ Finset.range n, (((j : ℝ) + 1) / n) * f (j + 1) +
            ∑ j ∈ Finset.range n, (((n - j : ℕ) : ℝ) / n) * f j := by
          simpa [f] using hsplit
    _ = (K : ℝ) / n * c *
          (∑ j ∈ Finset.range n, chooseWeight (N - 1) (n - 1) (K - 1) j * c ^ j)
        + ((N - K : ℕ) : ℝ) / n *
          (∑ j ∈ Finset.range n, chooseWeight (N - 1) (n - 1) K j * c ^ j) := by
          rw [hsuccess, hfailure]

/-- **First-draw recurrence for the normalized un-centered `c`-power MGF.**  Mirror of
`centeredHypergeometricMGF_first_draw` (`MGF.lean`). -/
lemma hypergeometricPowMGF_eq_recursion
    {N n K : ℕ} (hKN : K ≤ N) (hKpos : 0 < K) (hK_lt_N : K < N)
    (hnpos : 0 < n) (hn_lt_N : n < N) (c : ℝ) :
    hypergeometricPowMGF N n K c
      = (K : ℝ) / N * c * hypergeometricPowMGF (N - 1) (n - 1) (K - 1) c
        + ((N - K : ℕ) : ℝ) / N * hypergeometricPowMGF (N - 1) (n - 1) K c := by
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
    choose_sample_mul_eq_population_mul_pred_choose (N := N) (n := n) hnpos hn_le_N
  have hden' :
      (N.choose n : ℝ) = (N : ℝ) * ((N - 1).choose (n - 1) : ℝ) / n := by
    field_simp [hn_ne]
    simpa [mul_comm] using hden
  have hsum :=
    sum_chooseWeight_mul_pow_eq_recursion (N := N) (n := n) (K := K) hKN hKpos hK_lt_N hnpos c
  unfold hypergeometricPowMGF
  rw [hsum, hrange, hden']
  field_simp [hN_ne, hn_ne, hpred_choose_ne]

/-- **Division-free consequence of the power bound.**  For `0 < G`, `0 ≤ H`, and `H = G + d`,
`H ^ M · (G - M · d) ≤ G ^ (M + 1)`.  Applied at `H = G₁, d = δ₁` (upper child, `d ≥ 0`) and
at `H = G₀, d = -δ₀` (lower child, `d ≤ 0`). -/
lemma pow_mul_sub_mul_le_pow_succ {G H d : ℝ} (hG : 0 < G) (hH : 0 ≤ H) (hHGd : H = G + d)
    (M : ℕ) : H ^ M * (G - (M : ℝ) * d) ≤ G ^ (M + 1) := by
  have hG_ne : G ≠ 0 := hG.ne'
  have h1t : 0 ≤ 1 + d / G := by
    rw [show (1 : ℝ) + d / G = H / G by rw [hHGd]; field_simp]
    exact div_nonneg hH hG.le
  have hpow := one_add_pow_mul_one_sub_nmul_le_one (d / G) h1t M
  have hGM1_nonneg : 0 ≤ G ^ (M + 1) := pow_nonneg hG.le _
  have hmul := mul_le_mul_of_nonneg_right hpow hGM1_nonneg
  have heq :
      (1 + d / G) ^ M * (1 - (M : ℝ) * (d / G)) * G ^ (M + 1)
        = H ^ M * (G - (M : ℝ) * d) := by
    rw [show (1 : ℝ) + d / G = H / G by rw [hHGd]; field_simp]
    rw [div_pow, pow_succ]
    field_simp
  rw [heq, one_mul] at hmul
  exact hmul

/-- **Scalar core of the per-step comparison** (abstract reals).  With `S := δ₁ + c·δ₀`,
`S·Nm1 = (1-c)·G` and `0 ≤ S·(Nm1 - M)` give `c·(G + M·δ₀) ≤ G - M·δ₁`.  Split off so the
`linarith`/Simplex call runs in a minimal context. -/
lemma mul_add_mul_le_sub_mul (G δ0 δ1 c Nm1 M : ℝ)
    (hδsum : (δ1 + c * δ0) * Nm1 = (1 - c) * G)
    (hprod : 0 ≤ (δ1 + c * δ0) * (Nm1 - M)) :
    c * (G + M * δ0) ≤ G - M * δ1 := by
  have hid : (G - M * δ1) - c * (G + M * δ0) = (δ1 + c * δ0) * (Nm1 - M) := by
    linear_combination -hδsum
  linarith [hprod, hid]

/-- **Clearing-and-assembly core of the per-step comparison** (abstract reals).  From the two
one-step power bounds `P1, P2`, the scalar core, and the identity `a·δ₁ = c·b·δ₀`, derive the
geometric-factor inequality `a·G₁^M + b·G₀^M ≤ (a+b)·G^M`.  Split off so the heavy
`ring`/`linarith` clearing runs in a minimal context. -/
lemma add_mul_pow_le_mul_pow_of_weighted_perturbation (a b c G G1 G0 δ0 δ1 : ℝ) (M : ℕ)
    (hAnn : 0 ≤ a) (hBnn : 0 ≤ b) (hGpos : 0 < G) (hδ0nn : 0 ≤ δ0)
    (hAδ : a * δ1 = c * b * δ0)
    (hscalar : c * (G + (M : ℝ) * δ0) ≤ G - (M : ℝ) * δ1)
    (hP1 : G1 ^ M * (G - (M : ℝ) * δ1) ≤ G * G ^ M)
    (hP2 : G0 ^ M * (G + (M : ℝ) * δ0) ≤ G * G ^ M)
    (hD1_pos : 0 < G - (M : ℝ) * δ1)
    (hD0_pos : 0 < G + (M : ℝ) * δ0) :
    a * G1 ^ M + b * G0 ^ M ≤ (a + b) * G ^ M := by
  have hMnn : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  have hD1D0_pos : 0 < (G - (M : ℝ) * δ1) * (G + (M : ℝ) * δ0) := mul_pos hD1_pos hD0_pos
  have hCORE2slack_eq :
      (a + b) * ((G - (M : ℝ) * δ1) * (G + (M : ℝ) * δ0))
          - G * (a * (G + (M : ℝ) * δ0) + b * (G - (M : ℝ) * δ1))
        = (M : ℝ) * b * δ0 * ((G - (M : ℝ) * δ1) - c * (G + (M : ℝ) * δ0)) := by
    linear_combination (-(M : ℝ) * (G + (M : ℝ) * δ0)) * hAδ
  have hCORE2 :
      G * (a * (G + (M : ℝ) * δ0) + b * (G - (M : ℝ) * δ1))
        ≤ (a + b) * ((G - (M : ℝ) * δ1) * (G + (M : ℝ) * δ0)) := by
    have hrhs_nn :
        0 ≤ (M : ℝ) * b * δ0 * ((G - (M : ℝ) * δ1) - c * (G + (M : ℝ) * δ0)) :=
      mul_nonneg (mul_nonneg (mul_nonneg hMnn hBnn) hδ0nn) (by linarith [hscalar])
    linarith [hCORE2slack_eq, hrhs_nn]
  have hCORE2_ge :
      0 ≤ (a + b) * ((G - (M : ℝ) * δ1) * (G + (M : ℝ) * δ0))
          - G * (a * (G + (M : ℝ) * δ0) + b * (G - (M : ℝ) * δ1)) := by
    linarith [hCORE2]
  have t1 : 0 ≤ (a * (G + (M : ℝ) * δ0)) * (G * G ^ M - G1 ^ M * (G - (M : ℝ) * δ1)) :=
    mul_nonneg (mul_nonneg hAnn hD0_pos.le) (by linarith [hP1])
  have t2 : 0 ≤ (b * (G - (M : ℝ) * δ1)) * (G * G ^ M - G0 ^ M * (G + (M : ℝ) * δ0)) :=
    mul_nonneg (mul_nonneg hBnn hD1_pos.le) (by linarith [hP2])
  have t3 : 0 ≤ G ^ M * ((a + b) * ((G - (M : ℝ) * δ1) * (G + (M : ℝ) * δ0))
          - G * (a * (G + (M : ℝ) * δ0) + b * (G - (M : ℝ) * δ1))) :=
    mul_nonneg (pow_nonneg hGpos.le M) hCORE2_ge
  have hcleared :
      (a * G1 ^ M + b * G0 ^ M) * ((G - (M : ℝ) * δ1) * (G + (M : ℝ) * δ0))
        ≤ (a + b) * G ^ M * ((G - (M : ℝ) * δ1) * (G + (M : ℝ) * δ0)) := by
    have hid :
        (a + b) * G ^ M * ((G - (M : ℝ) * δ1) * (G + (M : ℝ) * δ0))
            - (a * G1 ^ M + b * G0 ^ M) * ((G - (M : ℝ) * δ1) * (G + (M : ℝ) * δ0))
          = (a * (G + (M : ℝ) * δ0)) * (G * G ^ M - G1 ^ M * (G - (M : ℝ) * δ1))
            + (b * (G - (M : ℝ) * δ1)) * (G * G ^ M - G0 ^ M * (G + (M : ℝ) * δ0))
            + G ^ M * ((a + b) * ((G - (M : ℝ) * δ1) * (G + (M : ℝ) * δ0))
                - G * (a * (G + (M : ℝ) * δ0) + b * (G - (M : ℝ) * δ1))) := by
      ring
    have hkey :
        0 ≤ (a + b) * G ^ M * ((G - (M : ℝ) * δ1) * (G + (M : ℝ) * δ0))
            - (a * G1 ^ M + b * G0 ^ M) * ((G - (M : ℝ) * δ1) * (G + (M : ℝ) * δ0)) := by
      rw [hid]; exact add_nonneg (add_nonneg t1 t2) t3
    exact sub_nonneg.mp hkey
  exact le_of_mul_le_mul_right hcleared hD1D0_pos

/-- **The per-step comparison (the crux).**  With `M := n - 1`, `G := gBase N K c`,
`G₁ := gBase (N-1) (K-1) c`, `G₀ := gBase (N-1) K c`:
`(K/N)·c·G₁^M + ((N-K)/N)·G₀^M ≤ G^n`.

**The load-bearing hypothesis is `n < N`** (⇔ `M ≤ N-2`).  Off the reachable range the
inequality is FALSE (first failure `M ≈ N+4`); `n = N` is a separate base case. -/
lemma weighted_gBase_pow_le
    {N n K : ℕ} (hKpos : 0 < K) (hK_lt_N : K < N)
    (hnpos : 0 < n) (hn_lt_N : n < N) {c : ℝ} (hc_nn : 0 ≤ c) (hc1 : c ≤ 1) :
    (K : ℝ) / N * c * gBase (N - 1) (K - 1) c ^ (n - 1)
      + ((N - K : ℕ) : ℝ) / N * gBase (N - 1) K c ^ (n - 1)
      ≤ gBase N K c ^ n := by
  -- Natural-number arithmetic facts and casts.
  have h1K : 1 ≤ K := hKpos
  have hKN : K ≤ N := le_of_lt hK_lt_N
  have h1N : 1 ≤ N := le_trans h1K hKN
  have hK_le_N1 : K ≤ N - 1 := by omega
  have hNK_eq : (N - 1) - (K - 1) = N - K := by omega
  have hn_eq : n = (n - 1) + 1 := by omega
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast lt_of_lt_of_le hKpos hKN
  have hN_ne : (N : ℝ) ≠ 0 := hN_pos.ne'
  have hN2 : 2 ≤ N := by omega
  have hN1_pos : 0 < (N : ℝ) - 1 := by
    have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    linarith only [hN2']
  have hN1_ne : (N : ℝ) - 1 ≠ 0 := hN1_pos.ne'
  have hcNK : ((N - K : ℕ) : ℝ) = (N : ℝ) - K := Nat.cast_sub hKN
  have hcN1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub h1N]; norm_num
  have hcK1 : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    rw [Nat.cast_sub h1K]; norm_num
  have hcN1K1 : (((N - 1) - (K - 1) : ℕ) : ℝ) = (N : ℝ) - K := by
    rw [hNK_eq, hcNK]
  have hcN1K : (((N - 1) - K : ℕ) : ℝ) = (N : ℝ) - 1 - K := by
    rw [Nat.cast_sub hK_le_N1, hcN1]
  -- Abbreviations.
  set M := n - 1 with hMdef
  set G := gBase N K c with hGdef
  set G1 := gBase (N - 1) (K - 1) c with hG1def
  set G0 := gBase (N - 1) K c with hG0def
  -- Explicit real forms.
  have hGr : G = ((K : ℝ) * c + ((N : ℝ) - K)) / N := by
    rw [hGdef, gBase, hcNK, div_mul_eq_mul_div, ← add_div]
  have hG1r : G1 = (((K : ℝ) - 1) * c + ((N : ℝ) - K)) / ((N : ℝ) - 1) := by
    rw [hG1def, gBase, hcK1, hcN1, hcN1K1, div_mul_eq_mul_div, ← add_div]
  have hG0r : G0 = ((K : ℝ) * c + ((N : ℝ) - 1 - K)) / ((N : ℝ) - 1) := by
    rw [hG0def, gBase, hcN1, hcN1K, div_mul_eq_mul_div, ← add_div]
  -- Positivity.
  have hGpos : 0 < G := by
    rw [hGr]
    apply div_pos _ hN_pos
    have hNK_pos : 0 < (N : ℝ) - K := by
      have hKN' : (K : ℝ) < N := by exact_mod_cast hK_lt_N
      linarith only [hKN']
    have hKc_nn : 0 ≤ (K : ℝ) * c := mul_nonneg (Nat.cast_nonneg K) hc_nn
    linarith only [hNK_pos, hKc_nn]
  have hG1nn : 0 ≤ G1 := by
    rw [hG1r]
    apply div_nonneg _ (le_of_lt hN1_pos)
    have hK1_nn : 0 ≤ (K : ℝ) - 1 := by
      have h1K' : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast h1K
      linarith only [h1K']
    have hNK_nn : 0 ≤ (N : ℝ) - K := by
      have hKN' : (K : ℝ) ≤ N := by exact_mod_cast hKN
      linarith only [hKN']
    have hK1c_nn : 0 ≤ ((K : ℝ) - 1) * c := mul_nonneg hK1_nn hc_nn
    linarith only [hK1c_nn, hNK_nn]
  have hG0nn : 0 ≤ G0 := by
    rw [hG0r]
    apply div_nonneg _ (le_of_lt hN1_pos)
    have hN1K_nn : 0 ≤ (N : ℝ) - 1 - K := by
      have hKN1 : (K : ℝ) ≤ (N : ℝ) - 1 := by
        have hKN1' := (Nat.cast_le (α := ℝ)).mpr hK_le_N1
        rw [hcN1] at hKN1'
        linarith only [hKN1']
      linarith only [hKN1]
    have hKc_nn' : 0 ≤ (K : ℝ) * c := mul_nonneg (Nat.cast_nonneg K) hc_nn
    linarith only [hN1K_nn, hKc_nn']
  -- The two centering deltas and the certified scalar identities.
  set δ1 := G1 - G with hδ1def
  set δ0 := G - G0 with hδ0def
  have hδ1val : δ1 = ((N : ℝ) - K) * (1 - c) / ((N : ℝ) * ((N : ℝ) - 1)) := by
    rw [hδ1def, hG1r, hGr]; field_simp; ring
  have hδ0val : δ0 = (K : ℝ) * (1 - c) / ((N : ℝ) * ((N : ℝ) - 1)) := by
    rw [hδ0def, hG0r, hGr]; field_simp; ring
  have hδ1nn : 0 ≤ δ1 := by
    rw [hδ1val]
    have hNK_nn : 0 ≤ (N : ℝ) - K := by
      have hKN' : (K : ℝ) ≤ N := by exact_mod_cast hKN
      linarith only [hKN']
    have h1c : 0 ≤ 1 - c := sub_nonneg.mpr hc1
    exact div_nonneg (mul_nonneg hNK_nn h1c) (mul_pos hN_pos hN1_pos).le
  have hδ0nn : 0 ≤ δ0 := by
    rw [hδ0val]
    have h1c : 0 ≤ 1 - c := sub_nonneg.mpr hc1
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg K) h1c) (mul_pos hN_pos hN1_pos).le
  -- Nonnegativity abbreviations.
  have hMnn : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  have hAnn : 0 ≤ (K : ℝ) * c := mul_nonneg (Nat.cast_nonneg K) hc_nn
  have hBnn : 0 ≤ (N : ℝ) - K := by
    have hKN' : (K : ℝ) ≤ N := by exact_mod_cast hKN
    linarith only [hKN']
  -- Certified scalar identities.
  have hAδ : (K : ℝ) * c * δ1 = c * ((N : ℝ) - K) * δ0 := by
    rw [hδ1val, hδ0val]; ring
  have hδsum' : (δ1 + c * δ0) * ((N : ℝ) - 1) = (1 - c) * G := by
    rw [hδ1val, hδ0val, hGr]; field_simp; ring
  have hδ0sum_nn : 0 ≤ δ1 + c * δ0 := add_nonneg hδ1nn (mul_nonneg hc_nn hδ0nn)
  have hMr : (M : ℝ) ≤ (N : ℝ) - 1 := by
    have hMN1 : M ≤ N - 1 := by omega
    calc (M : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hMN1
      _ = (N : ℝ) - 1 := hcN1
  have hGN1δ1 : G - ((N : ℝ) - 1) * δ1 = c := by
    rw [hGr, hδ1val]; field_simp; ring
  have hNG : (N : ℝ) * G = (K : ℝ) * c + ((N : ℝ) - K) := by
    rw [hGr, mul_div_cancel₀ _ hN_ne]
  -- The scalar core (isolated as `mul_add_mul_le_sub_mul`).
  have hprod : 0 ≤ (δ1 + c * δ0) * ((N : ℝ) - 1 - (M : ℝ)) :=
    mul_nonneg hδ0sum_nn (sub_nonneg.mpr hMr)
  have hscalar : c * (G + (M : ℝ) * δ0) ≤ G - (M : ℝ) * δ1 :=
    mul_add_mul_le_sub_mul G δ0 δ1 c ((N : ℝ) - 1) (M : ℝ) hδsum' hprod
  -- Positivity of the denominators.  `G - M·δ₁ = c + (N-1-M)·δ₁ ≥ c ≥ 0`; strict because
  -- when `c = 0` the deficiency `δ₁ > 0` and `N-1-M ≥ 1` (from `n < N ⇒ M ≤ N-2`).
  have hMr2 : (M : ℝ) ≤ (N : ℝ) - 2 := by
    have hMN2 : M ≤ N - 2 := by omega
    have h := (Nat.cast_le (α := ℝ)).mpr hMN2
    rwa [Nat.cast_sub hN2, Nat.cast_ofNat] at h
  have hD1_pos : 0 < G - (M : ℝ) * δ1 := by
    have hid : G - (M : ℝ) * δ1 = c + ((N : ℝ) - 1 - (M : ℝ)) * δ1 := by
      linear_combination hGN1δ1
    rw [hid]
    rcases eq_or_lt_of_le hc_nn with hc0 | hcpos
    · have hNK : 0 < (N : ℝ) - K := by
        have hKN' : (K : ℝ) < N := by exact_mod_cast hK_lt_N
        linarith only [hKN']
      have hδ1pos : 0 < δ1 := by
        rw [hδ1val, ← hc0]
        have hnum : 0 < ((N : ℝ) - K) * (1 - 0) := by rw [sub_zero, mul_one]; exact hNK
        exact div_pos hnum (mul_pos hN_pos hN1_pos)
      have hkey : 0 < ((N : ℝ) - 1 - (M : ℝ)) * δ1 :=
        mul_pos (by linarith only [hMr2]) hδ1pos
      rw [← hc0, zero_add]
      exact hkey
    · exact add_pos_of_pos_of_nonneg hcpos (mul_nonneg (sub_nonneg.mpr hMr) hδ1nn)
  have hD0_pos : 0 < G + (M : ℝ) * δ0 := by positivity
  -- The two power bounds P1, P2.
  have hGpow : G ^ (M + 1) = G * G ^ M := by rw [pow_succ]; ring
  have hP1 : G1 ^ M * (G - (M : ℝ) * δ1) ≤ G * G ^ M := by
    have h := pow_mul_sub_mul_le_pow_succ hGpos hG1nn (show G1 = G + δ1 by rw [hδ1def]; ring) M
    rw [hGpow] at h; exact h
  have hP2 : G0 ^ M * (G + (M : ℝ) * δ0) ≤ G * G ^ M := by
    have h := pow_mul_sub_mul_le_pow_succ hGpos hG0nn (show G0 = G + (-δ0) by rw [hδ0def]; ring) M
    rw [hGpow] at h
    have hcast : G - (M : ℝ) * (-δ0) = G + (M : ℝ) * δ0 := by ring
    rw [hcast] at h; exact h
  -- CORE2 + clearing + assembly (isolated as `add_mul_pow_le_mul_pow_of_weighted_perturbation`).
  have hGF :
      (K : ℝ) * c * G1 ^ M + ((N : ℝ) - K) * G0 ^ M
        ≤ ((K : ℝ) * c + ((N : ℝ) - K)) * G ^ M :=
    add_mul_pow_le_mul_pow_of_weighted_perturbation ((K : ℝ) * c) ((N : ℝ) - K) c G G1 G0 δ0 δ1 M
      hAnn hBnn hGpos hδ0nn hAδ hscalar hP1 hP2 hD1_pos hD0_pos
  -- Assemble the per-step from GF.
  have hnM : n = M + 1 := by omega
  rw [hcNK, hnM]
  rw [show (K : ℝ) / N * c * G1 ^ M + ((N : ℝ) - K) / N * G0 ^ M
        = ((K : ℝ) * c * G1 ^ M + ((N : ℝ) - K) * G0 ^ M) / N by ring]
  rw [div_le_iff₀ hN_pos]
  have hRHS : G ^ (M + 1) * (N : ℝ) = ((K : ℝ) * c + ((N : ℝ) - K)) * G ^ M := by
    rw [pow_succ, ← hNG]; ring
  rw [hRHS]
  exact hGF

/-- **One nondegenerate induction step.**  Mirror of
`centeredHypergeometricMGF_le_exp_of_recursion` (`MGF.lean`). -/
lemma hypergeometricPowMGF_le_gBase_pow_of_recursion
    {N n K : ℕ} (hKpos : 0 < K) (hK_lt_N : K < N)
    (hnpos : 0 < n) (hn_lt_N : n < N) {c : ℝ} (hc_nn : 0 ≤ c) (hc1 : c ≤ 1)
    (hsucc : hypergeometricPowMGF (N - 1) (n - 1) (K - 1) c ≤ gBase (N - 1) (K - 1) c ^ (n - 1))
    (hfail : hypergeometricPowMGF (N - 1) (n - 1) K c ≤ gBase (N - 1) K c ^ (n - 1)) :
    hypergeometricPowMGF N n K c ≤ gBase N K c ^ n := by
  have hKN : K ≤ N := le_of_lt hK_lt_N
  have hcoef1 : 0 ≤ (K : ℝ) / N * c :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg K) (Nat.cast_nonneg N)) hc_nn
  have hcoef0 : 0 ≤ ((N - K : ℕ) : ℝ) / N :=
    div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg N)
  rw [hypergeometricPowMGF_eq_recursion hKN hKpos hK_lt_N hnpos hn_lt_N c]
  calc
    (K : ℝ) / N * c * hypergeometricPowMGF (N - 1) (n - 1) (K - 1) c
        + ((N - K : ℕ) : ℝ) / N * hypergeometricPowMGF (N - 1) (n - 1) K c
      ≤ (K : ℝ) / N * c * gBase (N - 1) (K - 1) c ^ (n - 1)
        + ((N - K : ℕ) : ℝ) / N * gBase (N - 1) K c ^ (n - 1) :=
        add_le_add (mul_le_mul_of_nonneg_left hsucc hcoef1)
          (mul_le_mul_of_nonneg_left hfail hcoef0)
    _ ≤ gBase N K c ^ n :=
        weighted_gBase_pow_le hKpos hK_lt_N hnpos hn_lt_N hc_nn hc1

/-- Degenerate value: no draws. -/
lemma hypergeometricPowMGF_zero_sample (N K : ℕ) (c : ℝ) : hypergeometricPowMGF N 0 K c = 1 := by
  simp [hypergeometricPowMGF, chooseWeight]

/-- Degenerate value: no successes in the population ⇒ `E_WOR[c^S] = 1`. -/
lemma hypergeometricPowMGF_zero_success {N n : ℕ} (hn : n ≤ N) (c : ℝ) : hypergeometricPowMGF N n 0
    c = 1 := by
  have hden_ne : (N.choose n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hn).ne'
  have hsum : ∑ k ∈ Finset.range (n + 1), chooseWeight N n 0 k * c ^ k = (N.choose n : ℝ) := by
    rw [Finset.sum_eq_single 0]
    · simp [chooseWeight]
    · intro k _hk hk_ne
      have hchoose : (0 : ℕ).choose k = 0 := Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hk_ne)
      simp [chooseWeight, hchoose]
    · intro hnot; simp at hnot
  rw [hypergeometricPowMGF, hsum, div_self hden_ne]

/-- Degenerate value: every population element is a success ⇒ `E_WOR[c^S] = c^n`. -/
lemma hypergeometricPowMGF_success_eq_population {N n : ℕ} (hn : n ≤ N) (c : ℝ) :
    hypergeometricPowMGF N n N c = c ^ n := by
  have hden_ne : (N.choose n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hn).ne'
  have hsum :
      ∑ k ∈ Finset.range (n + 1), chooseWeight N n N k * c ^ k = (N.choose n : ℝ) * c ^ n := by
    rw [Finset.sum_eq_single n]
    · simp [chooseWeight]
    · intro k hk hk_ne
      have hk_lt : k < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hk_ne
      have hsub : 0 < n - k := Nat.sub_pos_of_lt hk_lt
      simp [chooseWeight, Nat.choose_eq_zero_of_lt hsub]
    · intro hnot
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self n)) hnot
  rw [hypergeometricPowMGF, hsum, mul_comm, mul_div_assoc, div_self hden_ne, mul_one]

/-- Degenerate value: the sample is the whole population ⇒ `E_WOR[c^S] = c^K`. -/
lemma hypergeometricPowMGF_sample_eq_population {N K : ℕ} (hKN : K ≤ N) (c : ℝ) :
    hypergeometricPowMGF N N K c = c ^ K := by
  have hden_ne : (N.choose N : ℝ) ≠ 0 := by simp [Nat.choose_self]
  have hsum : ∑ k ∈ Finset.range (N + 1), chooseWeight N N K k * c ^ k = c ^ K := by
    rw [Finset.sum_eq_single K]
    · simp [chooseWeight]
    · intro k _hk hk_ne
      by_cases hkK : k ≤ K
      · have hk_lt : k < K := lt_of_le_of_ne hkK hk_ne
        have hchoose : (N - K).choose (N - k) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        simp [chooseWeight, hchoose]
      · have hKk : K < k := by omega
        have hchoose : K.choose k = 0 := Nat.choose_eq_zero_of_lt hKk
        simp [chooseWeight, hchoose]
    · intro hnot
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hKN)) hnot
  rw [hypergeometricPowMGF, hsum, Nat.choose_self]
  simp

/-- `gBase N 0 c = 1` (no successes). -/
lemma gBase_zero {N : ℕ} (hN : N ≠ 0) (c : ℝ) : gBase N 0 c = 1 := by
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  simp only [gBase, Nat.cast_zero, Nat.sub_zero, zero_div, zero_mul, zero_add]
  field_simp

/-- `gBase N N c = c` (all successes). -/
lemma gBase_self {N : ℕ} (hN : N ≠ 0) (c : ℝ) : gBase N N c = c := by
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  simp only [gBase, Nat.sub_self, Nat.cast_zero, zero_div, add_zero]
  field_simp

/-- **The `n = N` base case via weighted AM–GM:** `c^K ≤ (gBase N K c)^N`.
`Real.geom_mean_le_arith_mean2_weighted` with weights `K/N, (N-K)/N` gives
`c^(K/N) ≤ gBase N K c`; raising to `N` and `(c^(K/N))^N = c^K` closes it. -/
lemma pow_le_gBase_pow {N K : ℕ} (hKN : K ≤ N) (hN_pos : 0 < N)
    {c : ℝ} (hc_nn : 0 ≤ c) :
    c ^ K ≤ gBase N K c ^ N := by
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN_pos.ne'
  have hw1nn : 0 ≤ (K : ℝ) / N := div_nonneg (Nat.cast_nonneg K) (Nat.cast_nonneg N)
  have hw2nn : 0 ≤ ((N - K : ℕ) : ℝ) / N := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg N)
  have hw_sum : (K : ℝ) / N + ((N - K : ℕ) : ℝ) / N = 1 := by
    rw [Nat.cast_sub hKN]; field_simp; ring
  have hAMGM :=
    Real.geom_mean_le_arith_mean2_weighted hw1nn hw2nn hc_nn (zero_le_one) hw_sum
  have hbase_le : c ^ ((K : ℝ) / N) ≤ gBase N K c := by
    simpa [gBase, Real.one_rpow] using hAMGM
  have hrpow_nn : 0 ≤ c ^ ((K : ℝ) / N) := Real.rpow_nonneg hc_nn _
  have hraise := pow_le_pow_left₀ hrpow_nn hbase_le N
  have heq : (c ^ ((K : ℝ) / N)) ^ N = c ^ K := by
    rw [← Real.rpow_natCast (c ^ ((K : ℝ) / N)) N, ← Real.rpow_mul hc_nn,
      show (K : ℝ) / N * (N : ℝ) = (K : ℝ) by field_simp, Real.rpow_natCast]
  rwa [heq] at hraise

/-- **WOR→WR moment-generating-function domination (Hoeffding 1963, Theorem 4).**
For `K ≤ N`, `n ≤ N`, `0 ≤ c ≤ 1`, the normalized un-centered hypergeometric `c`-power MGF is
dominated by the fixed-rate binomial envelope at rate `K/N`:
`hypergeometricPowMGF N n K c ≤ (gBase N K c)^n`.  Strong induction on `n` (mirror of
`centeredHypergeometricMGF_le_exp`, `MGF.lean`), with the four degenerate base cases and
the per-step crux `weighted_gBase_pow_le`.  Includes `c = 0` (the zero-success WOR probability). -/
lemma hypergeometricPowMGF_le_gBase_pow {N n K : ℕ} (hKN : K ≤ N) (hN : n ≤ N)
    {c : ℝ} (hc_nn : 0 ≤ c) (hc1 : c ≤ 1) :
    hypergeometricPowMGF N n K c ≤ gBase N K c ^ n := by
  classical
  revert N K
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro N K hKN hN
    by_cases hn0 : n = 0
    · subst hn0
      rw [hypergeometricPowMGF_zero_sample, pow_zero]
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hN_ne0 : N ≠ 0 := by omega
    by_cases hK0 : K = 0
    · subst hK0
      rw [hypergeometricPowMGF_zero_success hN, gBase_zero hN_ne0, one_pow]
    have hKpos : 0 < K := Nat.pos_of_ne_zero hK0
    by_cases hKN_eq : K = N
    · subst hKN_eq
      rw [hypergeometricPowMGF_success_eq_population hN, gBase_self hN_ne0]
    have hK_lt_N : K < N := lt_of_le_of_ne hKN hKN_eq
    by_cases hnN : n = N
    · subst hnN
      rw [hypergeometricPowMGF_sample_eq_population hKN]
      exact pow_le_gBase_pow hKN (Nat.pos_of_ne_zero hN_ne0) hc_nn
    have hn_lt_N : n < N := lt_of_le_of_ne hN hnN
    have hn_pred_lt : n - 1 < n := by omega
    have hKN_success : K - 1 ≤ N - 1 := Nat.sub_le_sub_right hKN 1
    have hn_success : n - 1 ≤ N - 1 := Nat.sub_le_sub_right hN 1
    have hKN_failure : K ≤ N - 1 := by omega
    have hsucc := ih (n - 1) hn_pred_lt (N := N - 1) (K := K - 1) hKN_success hn_success
    have hfail := ih (n - 1) hn_pred_lt (N := N - 1) (K := K) hKN_failure hn_success
    exact hypergeometricPowMGF_le_gBase_pow_of_recursion hKpos hK_lt_N hnpos hn_lt_N hc_nn hc1
      hsucc hfail

end Math.Concentration.HypergeometricTail
