import Mathlib.InformationTheory.Hamming
import Mathlib.Logic.Equiv.Fin.Basic
import QCryptLean.Math.ClassicalEntropy.BinaryEntropy
import QCryptLean.Math.ClassicalEntropy.Entropy

/-!
# Hamming-ball volume and its binary-entropy bound

For a fixed reference string `x : ι → Bool` over a finite index set `ι` of size
`n = |ι|`, this file counts binary strings by Hamming distance to `x`:

- `card_filter_hammingDist_eq_choose`: the Hamming *sphere* of radius `j` has exactly
  `C(n, j)` points (bijection with the `j`-element disagreement subsets of `ι`).
- `card_filter_hammingDist_le_two_pow`: the Hamming *ball* of radius `r` has at most
  `2^{n · h(r/n)}` points when `2·r ≤ n`, obtained by summing the sphere counts and
  applying `sum_choose_le_two_pow_mul_binaryEntropyBits`.
- `sum_choose_le_two_pow_mul_binaryEntropyBits_of_le` and
  `card_filter_hammingDist_le_two_pow_of_le`: the same bounds at an **arbitrary real relative
  radius** `p ∈ [0, 1/2]` with an integer radius `r ≤ p·n` — the shape parameter estimation
  needs, where the tolerated radius `(Q + δ)·n` is a real slack bound rather than the exact
  ratio `r/n`.  Monotonicity of `h` on `[0, 1/2]` turns the exact-ratio bound into the slack
  bound; nothing new has to be proved about binomial sums.
- `two_rpow_mul_binaryEntropyBits_eq` and `rpow_mul_rpow_le_of_le_half_of_le_mul`: the two
real-exponent
  analytic facts underlying every Chernoff-style form of the estimate — the identity
  `2^{m·h(p)} = p^{-mp}(1-p)^{-m(1-p)}` and the typical-term bound
  `p^{pm}(1-p)^{(1-p)m} ≤ p^{k}(1-p)^{m-k}` for `k ≤ p·m`.  They are stated for real exponents,
  so they also apply where no integer radius is available.

This is the classical "typical set" volume estimate of TLGR (arXiv:1103.4130) Lemma 3:
the number of Alice strings within the tolerated Hamming distance of Bob's string is
the fiber size entering the fiber-wise conditional max-entropy bound.

The `Mathlib.InformationTheory.Hamming` import is confined to this file to keep the
central binary-entropy module free of coding-theory machinery.
-/

open Finset

namespace Math.ClassicalEntropy

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Hamming-sphere count.** For a fixed `x : ι → Bool`, the number of binary strings
at Hamming distance exactly `j` from `x` equals `C(|ι|, j)`.

The bijection sends a string `y` to its disagreement set `{i | x i ≠ y i}` (a subset of
size `hammingDist x y`); over the binary alphabet the inverse recovers `y` from a subset
`S` by flipping `x` on exactly the coordinates in `S`. -/
theorem card_filter_hammingDist_eq_choose (x : ι → Bool) (j : ℕ) :
    (Finset.univ.filter (fun y : ι → Bool => hammingDist x y = j)).card
      = (Fintype.card ι).choose j := by
  -- The flip-on-`S` map disagrees with `x` exactly on `S`.
  have setEq : ∀ S : Finset ι,
      Finset.univ.filter (fun i => x i ≠ (if i ∈ S then !(x i) else x i)) = S := by
    intro S
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : i ∈ S
    · rw [ite_eq_left hi]
      simp only [hi, iff_true]
      cases x i <;> simp
    · rw [ite_eq_right hi]
      simp only [hi, iff_false, ne_eq, not_not]
  rw [← Finset.card_univ (α := ι), ← Finset.card_powersetCard j Finset.univ]
  refine Finset.card_bij'
    (fun y _ => Finset.univ.filter (fun i => x i ≠ y i))
    (fun S _ => fun i => if i ∈ S then !(x i) else x i)
    ?_ ?_ ?_ ?_
  · -- forward map lands in the `j`-element subsets
    intro y hy
    rw [Finset.mem_filter] at hy
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.filter_subset _ _, hy.2⟩
  · -- backward map lands in the sphere
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    change (Finset.univ.filter (fun i => x i ≠ (if i ∈ S then !(x i) else x i))).card = j
    rw [setEq S]; exact hS.2
  · -- left inverse: recover `y` from its disagreement set
    intro y _
    funext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hxy : x i ≠ y i
    · rw [ite_eq_left hxy]
      cases hb : x i <;> cases hc : y i <;> simp_all
    · rw [ite_eq_right hxy]
      exact not_not.mp hxy
  · -- right inverse: recover `S` from the flip map's disagreement set
    intro S _
    exact setEq S

/-- **Hamming-ball cardinality as a partial binomial sum.** For a fixed `x : ι → Bool`, the
number of binary strings within Hamming distance `r` of `x` is `∑_{j≤r} C(|ι|, j)`.

This is the exact ball volume (the base of `card_filter_hammingDist_le_two_pow`); in particular it
is *independent of the center* `x`, so all Hamming balls of a given radius have equal
cardinality.  Sum the sphere counts `card_filter_hammingDist_eq_choose` over `j ≤ r`. -/
theorem card_filter_hammingDist_le_eq_sum_choose (x : ι → Bool) (r : ℕ) :
    (Finset.univ.filter (fun y : ι → Bool => hammingDist x y ≤ r)).card
      = ∑ j ∈ Finset.range (r + 1), (Fintype.card ι).choose j := by
  have hmem : Set.MapsTo (fun y : ι → Bool => hammingDist x y)
      ↑(Finset.univ.filter (fun y : ι → Bool => hammingDist x y ≤ r))
      ↑(Finset.range (r + 1)) := by
    intro y hy
    rw [Finset.mem_coe, Finset.mem_filter] at hy
    rw [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le hy.2
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range, Nat.lt_succ_iff] at hj
  rw [← card_filter_hammingDist_eq_choose x j]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨by rw [h]; exact hj, h⟩

/-- **Partial binomial-sum entropy bound.** For `2·r ≤ n`, the cumulative binomial sum is
bounded by the binary-entropy volume factor:

`∑_{j ≤ r} C(n, j) ≤ 2^{n · h(r/n)}`.

Standard Chernoff-style argument: with `p = r/n ∈ (0, 1/2]`, each term `C(n,j)·p^r·(1-p)^{n-r}`
is dominated by `C(n,j)·p^j·(1-p)^{n-j}` for `j ≤ r` (because `p ≤ 1-p`), the full binomial sum
`∑_{j=0}^n C(n,j)·p^j·(1-p)^{n-j} = (p + (1-p))^n = 1`, and dividing by
`p^r·(1-p)^{n-r} = 2^{-n·h(r/n)}` gives the bound. -/
theorem sum_choose_le_two_pow_mul_binaryEntropyBits (n r : ℕ) (hr : 2 * r ≤ n) :
    (∑ j ∈ Finset.range (r + 1), (n.choose j : ℝ))
      ≤ (2 : ℝ) ^ ((n : ℝ) * binaryEntropyBits ((r : ℝ) / (n : ℝ))) := by
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · -- `r = 0`: LHS `= C(n,0) = 1`, RHS `= 2^{n·h(0)} = 2^0 = 1`.
    subst hr0
    simp only [Nat.cast_zero, zero_div]
    rw [show binaryEntropyBits (0 : ℝ) = 0 by
        simp [binaryEntropyBits, binaryEntropy, entropyTerm],
      mul_zero, Real.rpow_zero]
    simp
  · have hnpos : 0 < n := by omega
    have hrn : r ≤ n := by omega
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    set p : ℝ := (r : ℝ) / (n : ℝ) with hp_def
    have hp_pos : 0 < p := by rw [hp_def]; positivity
    have hp_half : p ≤ 1 / 2 := by
      have h2 : (2 : ℝ) * r ≤ (n : ℝ) := by exact_mod_cast hr
      rw [hp_def, div_le_iff₀ hnR]
      linarith
    have hp_lt1 : p < 1 := by linarith
    have hq_pos : 0 < 1 - p := by linarith
    have hpq : p ≤ 1 - p := by linarith
    -- Base-2 power `= exp` of the natural-log entropy.
    have hrhs : (2 : ℝ) ^ ((n : ℝ) * binaryEntropyBits p)
        = Real.exp ((n : ℝ) * binaryEntropy p) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 1
      rw [binaryEntropyBits]
      field_simp
    have hnp : (n : ℝ) * p = (r : ℝ) := by rw [hp_def]; field_simp
    have hnq : (n : ℝ) * (1 - p) = (n : ℝ) - (r : ℝ) := by rw [mul_sub, mul_one, hnp]
    have hcastsub : ((n : ℝ) - (r : ℝ)) = ((n - r : ℕ) : ℝ) := by rw [Nat.cast_sub hrn]
    have hentropy : (n : ℝ) * binaryEntropy p
        = -(r : ℝ) * Real.log p + -((n : ℝ) - (r : ℝ)) * Real.log (1 - p) := by
      rw [binaryEntropy, entropyTerm, entropyTerm, ite_eq_right (ne_of_gt hp_pos),
        ite_eq_right (by linarith : (1 : ℝ) - p ≠ 0)]
      rw [show (n : ℝ) * (-p * Real.log p + -(1 - p) * Real.log (1 - p))
            = -((n : ℝ) * p) * Real.log p + -((n : ℝ) * (1 - p)) * Real.log (1 - p) by ring,
        hnp, hnq]
    -- RHS as the reciprocal of `p^r · (1-p)^{n-r}`.
    have hRHSval : (2 : ℝ) ^ ((n : ℝ) * binaryEntropyBits p)
        = (p ^ r * (1 - p) ^ (n - r))⁻¹ := by
      rw [hrhs, hentropy, Real.exp_add, mul_comm (-(r : ℝ)) (Real.log p),
        mul_comm (-((n : ℝ) - (r : ℝ))) (Real.log (1 - p)),
        ← Real.rpow_def_of_pos hp_pos, ← Real.rpow_def_of_pos hq_pos,
        Real.rpow_neg hp_pos.le, Real.rpow_neg hq_pos.le, Real.rpow_natCast,
        hcastsub, Real.rpow_natCast, mul_inv]
    -- Per-term domination for `j ≤ r`.
    have hdom : ∀ j ∈ Finset.range (r + 1),
        (n.choose j : ℝ) * (p ^ r * (1 - p) ^ (n - r))
          ≤ (n.choose j : ℝ) * (p ^ j * (1 - p) ^ (n - j)) := by
      intro j hj
      rw [Finset.mem_range, Nat.lt_succ_iff] at hj
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have e1 : p ^ r = p ^ j * p ^ (r - j) := by
        rw [← pow_add, Nat.add_sub_cancel' hj]
      have e2 : (1 - p) ^ (n - j) = (1 - p) ^ (n - r) * (1 - p) ^ (r - j) := by
        rw [← pow_add, Nat.sub_add_sub_cancel hrn hj]
      rw [e1, e2]
      have hpow : p ^ (r - j) ≤ (1 - p) ^ (r - j) := pow_le_pow_left₀ hp_pos.le hpq _
      calc p ^ j * p ^ (r - j) * (1 - p) ^ (n - r)
          = (p ^ j * (1 - p) ^ (n - r)) * p ^ (r - j) := by ring
        _ ≤ (p ^ j * (1 - p) ^ (n - r)) * (1 - p) ^ (r - j) :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = p ^ j * ((1 - p) ^ (n - r) * (1 - p) ^ (r - j)) := by ring
    -- Full binomial sum is `1`.
    have hbinom : ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℝ) * (p ^ j * (1 - p) ^ (n - j)) = 1 := by
      have hstep : ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (p ^ j * (1 - p) ^ (n - j))
          = (p + (1 - p)) ^ n := by
        rw [add_pow]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [hstep, show p + (1 - p) = 1 by ring, one_pow]
    have hsub : ∑ j ∈ Finset.range (r + 1), (n.choose j : ℝ) * (p ^ j * (1 - p) ^ (n - j))
        ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (p ^ j * (1 - p) ^ (n - j)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => by positivity)
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      exact lt_of_lt_of_le hx (Nat.succ_le_succ hrn)
    have hcore : (∑ j ∈ Finset.range (r + 1), (n.choose j : ℝ)) * (p ^ r * (1 - p) ^ (n - r))
        ≤ 1 := by
      rw [Finset.sum_mul]
      calc ∑ j ∈ Finset.range (r + 1), (n.choose j : ℝ) * (p ^ r * (1 - p) ^ (n - r))
          ≤ ∑ j ∈ Finset.range (r + 1), (n.choose j : ℝ) * (p ^ j * (1 - p) ^ (n - j)) :=
            Finset.sum_le_sum hdom
        _ ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (p ^ j * (1 - p) ^ (n - j)) := hsub
        _ = 1 := hbinom
    have hposprod : 0 < p ^ r * (1 - p) ^ (n - r) := by positivity
    rw [hRHSval, ← one_div]
    exact (le_div_iff₀ hposprod).mpr hcore

/-- **Hamming-ball volume bound (base 2).** For a fixed `x : ι → Bool` with `|ι| = n`,
the number of binary strings within Hamming distance `r` of `x` is at most
`2^{n · h(r/n)}`, whenever `2·r ≤ n` (equivalently `r/n ≤ 1/2`).

Sum the sphere counts `C(n, j)` over `j ≤ r` and apply the partial-binomial-sum bound
`sum_choose_le_two_pow_mul_binaryEntropyBits`.  This is the typical-fiber size in the
fiber-wise conditional max-entropy estimate of TLGR (arXiv:1103.4130) Lemma 3. -/
theorem card_filter_hammingDist_le_two_pow (x : ι → Bool) {r : ℕ}
    (hr : 2 * r ≤ Fintype.card ι) :
    ((Finset.univ.filter (fun y : ι → Bool => hammingDist x y ≤ r)).card : ℝ)
      ≤ (2 : ℝ) ^ ((Fintype.card ι : ℝ) *
          binaryEntropyBits ((r : ℝ) / (Fintype.card ι : ℝ))) := by
  -- Ball = disjoint union of spheres of radius `j ≤ r`.
  have hmem : Set.MapsTo (fun y : ι → Bool => hammingDist x y)
      ↑(Finset.univ.filter (fun y : ι → Bool => hammingDist x y ≤ r))
      ↑(Finset.range (r + 1)) := by
    intro y hy
    rw [Finset.mem_coe, Finset.mem_filter] at hy
    rw [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le hy.2
  have hsum : (Finset.univ.filter (fun y : ι → Bool => hammingDist x y ≤ r)).card
      = ∑ j ∈ Finset.range (r + 1),
          (Finset.univ.filter (fun y : ι → Bool => hammingDist x y = j)).card := by
    rw [Finset.card_eq_sum_card_fiberwise hmem]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range, Nat.lt_succ_iff] at hj
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨by rw [h]; exact hj, h⟩
  rw [hsum]
  push_cast
  simp_rw [card_filter_hammingDist_eq_choose]
  exact sum_choose_le_two_pow_mul_binaryEntropyBits (Fintype.card ι) r hr

/-! ## Real-exponent analytic ingredients -/

/-- **The binary-entropy power as a product of probability powers.**  For `0 < p < 1` and any
real exponent `m`,

  `2 ^ (m · h(p)) = p ^ (-(m·p)) · (1-p) ^ (-(m·(1-p)))`   (real `rpow`).

This is the identity between the base-two entropy `binaryEntropyBits` and the product of
probability powers produced by the binomial theorem; it is what makes `2^{n h(p)}` the
reciprocal of the "typical" binomial term.  The exponent `m` is real, so the identity is
available at non-integer block lengths. -/
theorem two_rpow_mul_binaryEntropyBits_eq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (m : ℝ) :
    (2 : ℝ) ^ (m * binaryEntropyBits p)
      = p ^ (-(m * p)) * (1 - p) ^ (-(m * (1 - p))) := by
  have hp1' : 0 < 1 - p := by linarith
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hbe : binaryEntropyBits p
      = (-p * Real.log p + -(1 - p) * Real.log (1 - p)) / Real.log 2 := by
    unfold binaryEntropyBits binaryEntropy entropyTerm
    rw [ite_eq_right hp0.ne', ite_eq_right hp1'.ne']
  rw [hbe, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hexp : Real.log 2 * (m * ((-p * Real.log p + -(1 - p) * Real.log (1 - p)) / Real.log 2))
      = -(m * p) * Real.log p + -(m * (1 - p)) * Real.log (1 - p) := by
    field_simp
  rw [hexp, Real.exp_add, Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hp1']
  congr 1 <;> ring_nf

/-- **The typical-term bound (real exponents).**  For `0 < p ≤ 1/2` and a real `k ≤ p·m`,

  `p ^ (p·m) · (1-p) ^ ((1-p)·m) ≤ p ^ k · (1-p) ^ (m-k)`   (real `rpow`).

The ratio of the two sides is `(p/(1-p)) ^ (p·m - k)`, a base at most `1` raised to a
nonnegative exponent.  This is exactly where `p ≤ 1/2` enters the Hamming-ball estimate: it is
what makes the binomial term increase as the weight moves towards `p·m`. -/
theorem rpow_mul_rpow_le_of_le_half_of_le_mul {p : ℝ} (hp0 : 0 < p) (hp_half : p ≤ 1 / 2) {k m : ℝ}
    (hk_le : k ≤ p * m) :
    p ^ (p * m) * (1 - p) ^ ((1 - p) * m) ≤ p ^ k * (1 - p) ^ (m - k) := by
  have hp1' : 0 < 1 - p := by linarith
  have e1 : p ^ (p * m) = p ^ k * p ^ (p * m - k) := by
    rw [← Real.rpow_add hp0]; ring_nf
  have e2 : (1 - p) ^ ((1 - p) * m) = (1 - p) ^ (m - k) * (1 - p) ^ (-(p * m - k)) := by
    rw [← Real.rpow_add hp1']; ring_nf
  rw [e1, e2]
  have hbase_pk : (0 : ℝ) ≤ p ^ k * (1 - p) ^ (m - k) :=
    mul_nonneg (Real.rpow_nonneg hp0.le _) (Real.rpow_nonneg hp1'.le _)
  have hexp_nonneg : 0 ≤ p * m - k := by linarith
  have hratio : p ^ (p * m - k) * (1 - p) ^ (-(p * m - k)) ≤ 1 := by
    have hrw : p ^ (p * m - k) * (1 - p) ^ (-(p * m - k)) = (p / (1 - p)) ^ (p * m - k) := by
      rw [Real.div_rpow hp0.le hp1'.le, Real.rpow_neg hp1'.le, div_eq_mul_inv]
    rw [hrw]
    exact Real.rpow_le_one (div_pos hp0 hp1').le ((div_le_one hp1').mpr (by linarith))
      hexp_nonneg
  calc p ^ k * p ^ (p * m - k) * ((1 - p) ^ (m - k) * (1 - p) ^ (-(p * m - k)))
      = (p ^ k * (1 - p) ^ (m - k)) * (p ^ (p * m - k) * (1 - p) ^ (-(p * m - k))) := by ring
    _ ≤ (p ^ k * (1 - p) ^ (m - k)) * 1 := mul_le_mul_of_nonneg_left hratio hbase_pk
    _ = p ^ k * (1 - p) ^ (m - k) := by ring

/-! ## Arbitrary real relative radius -/

/-- **Partial binomial-sum entropy bound at an arbitrary relative radius.**

For `p ∈ [0, 1/2]` and an integer radius `r` with `r ≤ p·n`,

  `∑_{j ≤ r} C(n, j) ≤ 2 ^ (n · h(p))`.

This is the slack form used in parameter estimation, where the tolerated radius is a real
bound `(Q + δ)·n` and `r` is whatever integer radius the protocol actually accepts.  It follows
from the exact-ratio bound `sum_choose_le_two_pow_mul_binaryEntropyBits` together with
monotonicity of the binary entropy on `[0, 1/2]` (`binaryEntropy_mono_on_half`), since
`r/n ≤ p ≤ 1/2`.  The degenerate case `n = 0` forces `r = 0` and both sides equal `1`. -/
theorem sum_choose_le_two_pow_mul_binaryEntropyBits_of_le {p : ℝ} (hp0 : 0 ≤ p)
    (hp_half : p ≤ 1 / 2) (n r : ℕ) (hr : (r : ℝ) ≤ p * (n : ℝ)) :
    (∑ j ∈ Finset.range (r + 1), (n.choose j : ℝ))
      ≤ (2 : ℝ) ^ ((n : ℝ) * binaryEntropyBits p) := by
  have hnR : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- The integer radius is at most half the block length.
  have hr2 : 2 * r ≤ n := by
    have hhalf : p * (n : ℝ) ≤ (1 / 2) * (n : ℝ) := mul_le_mul_of_nonneg_right hp_half hnR
    have : (2 : ℝ) * (r : ℝ) ≤ (n : ℝ) := by linarith
    exact_mod_cast this
  -- The exact relative radius is at most `p`.
  have hratio_le : (r : ℝ) / (n : ℝ) ≤ p := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simpa using hp0
    · rw [div_le_iff₀ (by exact_mod_cast hn : (0 : ℝ) < (n : ℝ))]; exact hr
  have hratio_nonneg : (0 : ℝ) ≤ (r : ℝ) / (n : ℝ) :=
    div_nonneg (Nat.cast_nonneg r) hnR
  -- Entropy is monotone on `[0, 1/2]`, hence so is the exponent.
  have hent : binaryEntropyBits ((r : ℝ) / (n : ℝ)) ≤ binaryEntropyBits p := by
    unfold binaryEntropyBits
    exact div_le_div_of_nonneg_right
      (binaryEntropy_mono_on_half hratio_nonneg hp_half hratio_le) hlog2.le
  refine le_trans (sum_choose_le_two_pow_mul_binaryEntropyBits n r hr2) ?_
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
    (mul_le_mul_of_nonneg_left hent hnR)

/-- **Hamming-ball volume bound at an arbitrary relative radius.**  For `p ∈ [0, 1/2]` and an
integer radius `r ≤ p·|ι|`, the ball of radius `r` around any `x` has at most `2^{|ι|·h(p)}`
points.  This is the ball-counting form of
`sum_choose_le_two_pow_mul_binaryEntropyBits_of_le`. -/
theorem card_filter_hammingDist_le_two_pow_of_le (x : ι → Bool) {r : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp_half : p ≤ 1 / 2) (hr : (r : ℝ) ≤ p * (Fintype.card ι : ℝ)) :
    ((Finset.univ.filter (fun y : ι → Bool => hammingDist x y ≤ r)).card : ℝ)
      ≤ (2 : ℝ) ^ ((Fintype.card ι : ℝ) * binaryEntropyBits p) := by
  rw [card_filter_hammingDist_le_eq_sum_choose x r]
  push_cast
  exact sum_choose_le_two_pow_mul_binaryEntropyBits_of_le hp0 hp_half (Fintype.card ι) r hr

/-- The Hamming ball over `Fin 2` has the same binomial volume as the Boolean ball. -/
theorem card_filter_hammingDist_le_eq_sum_choose_finTwo (x : ι → Fin 2) (r : ℕ) :
    (Finset.univ.filter (fun y : ι → Fin 2 => hammingDist x y ≤ r)).card =
      ∑ j ∈ Finset.range (r + 1), (Fintype.card ι).choose j := by
  rw [← card_filter_hammingDist_le_eq_sum_choose (fun i => finTwoEquiv (x i)) r]
  refine Finset.card_bij' (fun y _ => fun i => finTwoEquiv (y i))
    (fun y _ => fun i => finTwoEquiv.symm (y i)) ?_ ?_ ?_ ?_
  · intro y hy
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
      hammingDist_comp (fun _ => finTwoEquiv) (fun _ => finTwoEquiv.injective)] using hy
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [← hammingDist_comp (fun _ => finTwoEquiv) (fun _ => finTwoEquiv.injective)]
    simpa using hy
  · intro y _
    funext i
    simp
  · intro y _
    funext i
    simp

/-- Binary-entropy volume bound for a `Fin 2` Hamming ball at a real relative radius. -/
theorem card_filter_hammingDist_le_two_pow_of_le_finTwo (x : ι → Fin 2) {r : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp_half : p ≤ 1 / 2) (hr : (r : ℝ) ≤ p * (Fintype.card ι : ℝ)) :
    ((Finset.univ.filter (fun y : ι → Fin 2 => hammingDist x y ≤ r)).card : ℝ) ≤
      (2 : ℝ) ^ ((Fintype.card ι : ℝ) * binaryEntropyBits p) := by
  rw [card_filter_hammingDist_le_eq_sum_choose_finTwo]
  push_cast
  exact sum_choose_le_two_pow_mul_binaryEntropyBits_of_le hp0 hp_half (Fintype.card ι) r hr

/-- A syndrome alphabet with `s` bits above the ball entropy bounds collisions by `2⁻ˢ`. -/
lemma card_filter_hammingDist_le_div_two_pow_le_of_entropy (t leakEC s : ℕ)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1 / 2)
    (ht : (t : ℝ) ≤ r * Fintype.card ι)
    (hleak : (Fintype.card ι : ℝ) * binaryEntropyBits r + s ≤ leakEC) :
    ((Finset.univ.filter (fun e : ι → Fin 2 => hammingDist e 0 ≤ t)).card : ℝ) /
      (2 : ℝ) ^ leakEC ≤ ((2 : ℝ) ^ s)⁻¹ := by
  have hvol := card_filter_hammingDist_le_two_pow_of_le_finTwo (0 : ι → Fin 2) hr0 hr1 ht
  simp only [hammingDist_comm (0 : ι → Fin 2)] at hvol
  rw [← one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  calc
    _ ≤ (2 : ℝ) ^ ((Fintype.card ι : ℝ) * binaryEntropyBits r) * (2 : ℝ) ^ s :=
      mul_le_mul_of_nonneg_right hvol (by positivity)
    _ = (2 : ℝ) ^ ((Fintype.card ι : ℝ) * binaryEntropyBits r + s) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_natCast]
    _ ≤ (2 : ℝ) ^ (leakEC : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hleak
    _ = _ := Real.rpow_natCast _ _

end Math.ClassicalEntropy
