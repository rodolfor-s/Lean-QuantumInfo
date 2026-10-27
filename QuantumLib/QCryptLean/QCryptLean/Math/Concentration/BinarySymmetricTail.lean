import Mathlib.Algebra.Group.Fin.Basic
import QCryptLean.Math.ClassicalEntropy.HammingBall
import QCryptLean.Math.Concentration.BernoulliKL
import QCryptLean.Math.Concentration.BinomialHoeffding
import QCryptLean.Math.Concentration.BinomialKLTail

/-!
# Binary symmetric product measure and its Hoeffding upper tail

Fix a finite index set `ι` and a crossover probability `Q`.  The **binary symmetric product
measure** centred at a reference string `a : ι → Fin 2` assigns to `b : ι → Fin 2` the weight
`bscWeight Q a b = ∏ i, (1 − Q if a i = b i else Q)`, i.e. the law of `b = a ⊕ e` with `e` an
i.i.d. `Bernoulli(Q)` error pattern.  Two facts are recorded, and neither has quantum content:

- the mass is constant on Hamming spheres and the spheres are binomial, so any *distance-gated*
  mass collapses to a binomial partial sum (`sum_bscWeight_indicator_eq_binomial`);
- hence the mass strictly outside the Hamming ball of radius `(Q + ε)·|ι|` is at most the one-sided
  Hoeffding exponent `exp(−2·|ι|·ε²)` (`bscWeight_upperTail_le`).

The alphabet is `Fin 2` rather than `Bool` because that is the alphabet of
`QKD.BB84.KeyBitString`; the sphere count is transported from the `Bool`
version `Math.ClassicalEntropy.card_filter_hammingDist_eq_choose` along `finTwoEquiv`, and the
binomial tail is `Math.Concentration.BinomialHoeffding.binomial_upper_tail`.

This is the classical typical-set estimate for a memoryless binary symmetric channel
(Cover–Thomas §3), used as the error-correction typicality input by Nahar, Tupkary, Zhao,
Lütkenhaus, Tan 2024 (arXiv:2403.11851) §V.C.

## Main definitions

- `bscWeight`: the binary symmetric product weight of `b` relative to a reference string `a` at
  crossover `Q`.

## Main statements

- `card_filter_disagreeCard_eq_choose`: the Hamming-sphere count over the `Fin 2` alphabet.
- `bscWeight_eq_pow`: the weight is constant on Hamming spheres.
- `bscWeight_nonneg`: the weight is nonnegative for a crossover in `[0, 1]`.
- `sum_bscWeight_indicator_eq_binomial`: any distance-gated mass is a binomial partial sum.
- `bscWeight_upperTail_le`: **the Hoeffding upper tail** of the binary symmetric product measure.
- `bscWeight_ball_compl_le`: the mass outside the Hamming ball of radius `t` is at most the
  Hoeffding tail `exp(−2·|ι|·ε²)` at the strict-shortfall endpoint `(t+1)/|ι|`.
- `bscWeight_ball_compl_le_exp_neg_mul_klBer`: the same bound at the KL rate
  `exp(−|ι|·klBer ((t+1)/|ι|) q)`, no margin.
-/

noncomputable section

namespace Math.Concentration.BinarySymmetricTail

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The binary symmetric product weight** of `b` relative to the reference string `a` at crossover
`Q`: each index contributes `1 − Q` where the two strings agree and `Q` where they disagree. -/
def bscWeight (Q : ℝ) (a b : ι → Fin 2) : ℝ :=
  ∏ i, (if a i = b i then 1 - Q else Q)

/-- **Hamming-sphere count over the `Fin 2` alphabet.** For a fixed reference string `a`, exactly
`C(|ι|, k)` strings disagree with `a` on exactly `k` indices.  Transported from the `Bool` version
`Math.ClassicalEntropy.card_filter_hammingDist_eq_choose` along `finTwoEquiv`. -/
theorem card_filter_disagreeCard_eq_choose (a : ι → Fin 2) (k : ℕ) :
    (Finset.univ.filter (fun b : ι → Fin 2 =>
        hammingDist a b = k)).card
      = (Fintype.card ι).choose k := by
  classical
  rw [← Math.ClassicalEntropy.card_filter_hammingDist_eq_choose
    (fun i => finTwoEquiv (a i)) k]
  refine Finset.card_bij' (fun b _ => fun i => finTwoEquiv (b i))
    (fun y _ => fun i => finTwoEquiv.symm (y i)) ?_ ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rw [hammingDist_comp (fun _ => finTwoEquiv) (fun _ => finTwoEquiv.injective)]
    exact hb
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [← hammingDist_comp (fun _ => finTwoEquiv) (fun _ => finTwoEquiv.injective)]
    simpa using hy
  · intro b _; funext i; simp
  · intro y _; funext i; simp

omit [DecidableEq ι] in
/-- **The weight is constant on Hamming spheres**: it depends on `b` only through the number of
indices at which `b` disagrees with `a`. -/
theorem bscWeight_eq_pow (Q : ℝ) (a b : ι → Fin 2) :
    bscWeight Q a b
      = (1 - Q) ^ (Fintype.card ι - hammingDist a b)
        * Q ^ hammingDist a b := by
  classical
  change bscWeight Q a b =
    (1 - Q) ^ (Fintype.card ι - (Finset.univ.filter (fun i => a i ≠ b i)).card) *
      Q ^ (Finset.univ.filter (fun i => a i ≠ b i)).card
  have hnot : (Finset.univ.filter (fun i => ¬ (a i = b i)))
      = Finset.univ.filter (fun i => a i ≠ b i) := rfl
  have hcard : (Finset.univ.filter (fun i => a i = b i)).card
      = Fintype.card ι - (Finset.univ.filter (fun i => a i ≠ b i)).card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ι)) (p := fun i => a i = b i)
    rw [Finset.card_univ] at h
    rw [hnot] at h
    omega
  rw [bscWeight, Finset.prod_ite (fun _ => (1 - Q)) (fun _ => Q), Finset.prod_const,
    Finset.prod_const, hnot, hcard]

omit [DecidableEq ι] in
/-- The weight is nonnegative for a crossover in `[0, 1]`. -/
theorem bscWeight_nonneg {Q : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) (a b : ι → Fin 2) :
    0 ≤ bscWeight Q a b := by
  rw [bscWeight_eq_pow]
  exact mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg hQ0 _)

/-- **Any distance-gated mass is a binomial partial sum.** Gating the binary symmetric weight by an
arbitrary predicate `P` of the disagreement count collapses the `2^{|ι|}`-term string sum to the
`(|ι|+1)`-term binomial sum, because the weight is sphere-constant (`bscWeight_eq_pow`) and the
spheres are binomial (`card_filter_disagreeCard_eq_choose`). -/
theorem sum_bscWeight_indicator_eq_binomial (Q : ℝ) (a : ι → Fin 2)
    (P : ℕ → Prop) [DecidablePred P] :
    (∑ b : ι → Fin 2,
        if P (hammingDist a b) then bscWeight Q a b else 0)
      = ∑ k ∈ Finset.range (Fintype.card ι + 1),
          if P k then ((Fintype.card ι).choose k : ℝ) * Q ^ k * (1 - Q) ^ (Fintype.card ι - k)
          else 0 := by
  classical
  set F : (ι → Fin 2) → ℝ := fun b =>
    if P (hammingDist a b) then bscWeight Q a b else 0 with hF
  have hmaps : ∀ b ∈ (Finset.univ : Finset (ι → Fin 2)),
      hammingDist a b ∈ Finset.range (Fintype.card ι + 1) := by
    intro b _
    rw [Finset.mem_range, Nat.lt_succ_iff, ← Finset.card_univ]
    exact Finset.card_filter_le _ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps F]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hfiber : ∀ b ∈ (Finset.univ : Finset (ι → Fin 2)).filter
      (fun b => hammingDist a b = k),
      F b = if P k then (1 - Q) ^ (Fintype.card ι - k) * Q ^ k else 0 := by
    intro b hb
    rw [Finset.mem_filter] at hb
    rw [hF]
    simp only [hb.2]
    split_ifs with h
    · rw [bscWeight_eq_pow, hb.2]
    · rfl
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.univ : Finset (ι → Fin 2)).filter
      (fun b => hammingDist a b = k)).card
      = (Fintype.card ι).choose k := card_filter_disagreeCard_eq_choose a k
  rw [hcard]
  split_ifs with h
  · ring
  · ring

/-- **Hoeffding upper tail for the binary symmetric product measure.**

The mass that the binary symmetric channel at crossover `Q ∈ [0, 1]` puts strictly outside the
Hamming ball of radius `(Q + ε)·|ι|` around its centre is at most `exp(−2·|ι|·ε²)`, for every
margin `ε > 0` and every centre `a`.

This is the typical-set input of the error-correction argument: the honest error pattern of an
`|ι|`-round key block is `Bernoulli(Q)`, and the tolerance band the parameter estimate certifies is
`Q + ε`.  The bound is uniform in the centre `a`. -/
theorem bscWeight_upperTail_le {Q ε : ℝ} (hQ0 : 0 ≤ Q) (hQ1 : Q ≤ 1) (hε : 0 < ε)
    (a : ι → Fin 2) :
    (∑ b ∈ Finset.univ.filter (fun b : ι → Fin 2 =>
        (Q + ε) * (Fintype.card ι : ℝ) < (hammingDist a b : ℝ)),
        bscWeight Q a b)
      ≤ Real.exp (-2 * (Fintype.card ι : ℝ) * ε ^ 2) := by
  classical
  set N : ℕ := Fintype.card ι with hN
  rw [Finset.sum_filter,
    sum_bscWeight_indicator_eq_binomial Q a (fun k => (Q + ε) * (N : ℝ) < (k : ℝ))]
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · -- an empty index set carries no string outside the (degenerate) ball
    have hzero : ∑ k ∈ Finset.range (N + 1),
        (if (Q + ε) * (N : ℝ) < (k : ℝ) then
          ((N).choose k : ℝ) * Q ^ k * (1 - Q) ^ (N - k) else 0) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [Finset.mem_range, h0] at hk
      have hk0 : k = 0 := by omega
      rw [ite_eq_right]
      rw [hk0, h0]
      norm_num
    rw [hzero]
    positivity
  · have hNne : N ≠ 0 := hpos.ne'
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hpos
    refine le_trans ?_
      (Math.Concentration.BinomialHoeffding.binomial_upper_tail N hNne Q ε hQ0 hQ1 hε)
    refine Finset.sum_le_sum fun k _ => ?_
    have hnn : (0 : ℝ) ≤ ((N).choose k : ℝ) * Q ^ k * (1 - Q) ^ (N - k) := by
      have h1 : (0 : ℝ) ≤ Q ^ k := pow_nonneg hQ0 _
      have h2 : (0 : ℝ) ≤ (1 - Q) ^ (N - k) := pow_nonneg (by linarith) _
      positivity
    by_cases hgate : (Q + ε) * (N : ℝ) < (k : ℝ)
    · rw [ite_eq_left hgate, ite_eq_left]
      rw [le_div_iff₀ hNpos]
      linarith
    · rw [ite_eq_right hgate]
      split_ifs
      · exact hnn
      · exact le_rfl

/-- The binary-symmetric transition law is normalized. -/
lemma sum_bscWeight (q : ℝ) (a : ι → Fin 2) :
    ∑ b, bscWeight q a b = 1 := by
  unfold bscWeight
  rw [← Fintype.prod_sum (fun i b => if a i = b then 1 - q else q)]
  apply Finset.prod_eq_one
  intro i _
  generalize a i = b
  fin_cases b <;> simp [Fin.sum_univ_two]

omit [DecidableEq ι] in
/-- Subtracting Bob's word from Alice's transports the BSC law to the zero-centered error law. -/
lemma bscWeight_self_sub_right (q : ℝ) (a e : ι → Fin 2) :
    bscWeight q a (a - e) =
      bscWeight q 0 e := by
  unfold bscWeight
  apply Finset.prod_congr rfl
  intro i _
  simp only [Pi.sub_apply, Pi.zero_apply, eq_sub_iff_add_eq, add_eq_left]
  simp only [eq_comm]

/-- The mass outside a Hamming ball is bounded by the one-sided Hoeffding tail. -/
lemma bscWeight_ball_compl_le {q ε : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hε : 0 < ε)
    (a : ι → Fin 2) (t : ℕ)
    (hgate : (q + ε) * (Fintype.card ι : ℝ) < (t + 1 : ℝ)) :
    (∑ b : ι → Fin 2, if hammingDist a b ≤ t then 0 else bscWeight q a b) ≤
      Real.exp (-2 * (Fintype.card ι : ℝ) * ε ^ 2) := by
  have htail := bscWeight_upperTail_le hq0 hq1 hε a
  refine le_trans ?_ htail
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro b _
  by_cases hb : hammingDist a b ≤ t
  · simp only [ite_eq_left hb]
    split_ifs
    · exact bscWeight_nonneg hq0 hq1 a b
    · exact le_refl 0
  · have hdist : (t + 1 : ℝ) ≤ hammingDist a b := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.lt_of_not_ge hb)
    have hlarge := hgate.trans_le hdist
    simp only [ite_eq_right hb, ite_eq_left hlarge, le_refl]

/-- **KL-rate Chernoff upper tail for the binary symmetric product measure.**

The mass that the binary symmetric channel at crossover `q ∈ (0, 1)` puts outside the Hamming
ball of radius `t` around its centre is at most `exp(-|ι| · klBer ((t+1)/|ι|) q)`, for
`q · |ι| < t + 1 ≤ |ι|` (`q < 1` follows from the condition).  No margin is needed: via
`sum_bscWeight_indicator_eq_binomial` the outside mass is the binomial mass of the counts `t < k`,
i.e. of the fractions `(t+1)/|ι| ≤ k/|ι|`, which is the KL-rate upper tail
(`upperTail_le_exp_neg_mul_klBer`) at threshold `(t+1)/|ι|` and reference rate `q`.

Sharper analogue of `bscWeight_ball_compl_le` (which prices the tail at the Hoeffding rate and
needs a margin `ε`); the typical-set input of the error-correction argument at the Chernoff rate
(Cover–Thomas, *Elements of Information Theory*, §11.1). -/
theorem bscWeight_ball_compl_le_exp_neg_mul_klBer {q : ℝ} (hq0 : 0 < q)
    (a : ι → Fin 2) (t : ℕ)
    (hgate : q * (Fintype.card ι : ℝ) < (t + 1 : ℝ))
    (ht : (t + 1 : ℝ) ≤ (Fintype.card ι : ℝ)) :
    (∑ b : ι → Fin 2, if hammingDist a b ≤ t then 0 else bscWeight q a b) ≤
      Real.exp (-((Fintype.card ι : ℝ)) *
        Math.Concentration.BernoulliKL.klBer ((t + 1 : ℝ) / Fintype.card ι) q) := by
  classical
  -- `N = 0` contradicts `t + 1 ≤ N`.
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · rw [h0, Nat.cast_zero] at ht
    have h01 : (0 : ℝ) < (t + 1 : ℝ) := by positivity
    linarith
  have hNpos : (0 : ℝ) < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr hpos
  -- The outside mass is the binomial mass of the counts `t < k`.
  have step1 : (∑ b : ι → Fin 2,
      if hammingDist a b ≤ t then (0 : ℝ) else bscWeight q a b)
      = ∑ k ∈ Finset.range (Fintype.card ι + 1),
          if t < k then
            (((Fintype.card ι).choose k : ℝ) * q ^ k * (1 - q) ^ (Fintype.card ι - k))
          else 0 := by
    have hswap : ∀ b : ι → Fin 2,
        (if hammingDist a b ≤ t then (0 : ℝ) else bscWeight q a b)
          = if t < hammingDist a b then bscWeight q a b else 0 := by
      intro b; by_cases hb : hammingDist a b ≤ t <;> simp [hb]
    rw [Finset.sum_congr rfl (fun b _ => hswap b),
      sum_bscWeight_indicator_eq_binomial q a (fun k => t < k)]
  rw [step1]
  -- the fraction threshold `(t+1)/N ≤ k/N` is the count condition `t < k`
  have hkN : ∀ k : ℕ,
      (((t + 1 : ℝ) / Fintype.card ι) ≤ ((k : ℝ) / Fintype.card ι)) ↔ t < k := by
    intro k
    rw [div_le_div_iff₀ hNpos hNpos]
    constructor
    · intro h
      exact Nat.succ_le_iff.mp (by exact_mod_cast (mul_le_mul_iff_of_pos_right hNpos).mp h)
    · intro h
      refine mul_le_mul_iff_of_pos_right hNpos |>.mpr ?_
      exact_mod_cast Nat.succ_le_iff.mpr h
  have hba : q ≤ (t + 1 : ℝ) / Fintype.card ι := by
    rw [le_div_iff₀ hNpos]
    exact hgate.le
  refine le_trans (Finset.sum_le_sum fun k _ => ?_)
    (Math.Concentration.BinomialKLTail.upperTail_le_exp_neg_mul_klBer
      (Fintype.card ι) q ((t + 1 : ℝ) / Fintype.card ι) q
      hba (le_refl q) hq0.le hq0)
  by_cases hgate2 : t < k
  · rw [ite_eq_left hgate2, ite_eq_left ((hkN k).mpr hgate2)]
  · rw [ite_eq_right hgate2, ite_eq_right (mt (hkN k).mp hgate2)]

end Math.Concentration.BinarySymmetricTail

end
