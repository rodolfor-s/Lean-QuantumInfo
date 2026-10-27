import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Probability.ProbabilityMassFunction.Basic
import QCryptLean.Math.CodingTheory.HashFamily

/-!
# Classical Privacy Amplification — min-entropy, leftover hash lemma, key extraction

Classical leftover hash lemma and privacy amplification for finite distributions.
All results here are purely classical: the source is a probability distribution
p : Fin n → ℝ, distances are classical statistical distance, and no quantum side
information or quantum states are involved.

## Main definitions
- `minEntropy`: H_∞(X) = -ln(max_x p(x))
- `HashFamily`: A family of hash functions parameterized by a seed type
- `statisticalDistance`: L1 distance between probability distributions
- `extractedKeyDistance`: Distance between (h(X), h) and (U_m, h)
- `classicalSmoothMinEntropy`: H_∞^ε(X) maximized over ε-close distributions

## Main statements
- `extractedKeyDistance_le_half_mul_sqrt_of_le_minEntropy`: If H_∞(X) ≥ k, hashing with a
2-universal
  family to output space of size m gives d ≤ (1/2)·√(m·e^{-k})
- `extractedKeyDistance_le_of_le_minEntropy`: Corollary giving ε-closeness to
  uniform when m·e^{-k} ≤ (2ε)²
- `finiteKeyRate_tendsto`: Finite key rate converges to asymptotic rate
-/

open Real BigOperators Finset

noncomputable section

namespace Math.Concentration.PrivacyAmplification

/-! ## Min-Entropy

Min-entropy is the most conservative entropy measure, quantifying the maximum
probability of any single outcome. It's the relevant entropy for security proofs
because it bounds the probability that an adversary can guess the correct value.

H_∞(X) = -ln(max_x p(x))

Uses natural logarithm (nats) throughout, consistent with the definition below.

For a distribution p : Fin n → ℝ≥0 with ∑ p = 1:
- H_∞ = 0 when one outcome has probability 1 (deterministic)
- H_∞ = ln(n) when uniform (maximum entropy)
-/

/-- The maximum probability in a distribution. -/
def maxProb {n : ℕ} [NeZero n] (p : Fin n → ℝ) : ℝ :=
  Finset.sup' Finset.univ ⟨0, Finset.mem_univ 0⟩ p

/-- Min-entropy of a probability distribution: H_∞(p) = -ln(max_x p(x)).

    Uses natural logarithm (nats) for consistency with all other entropy definitions
    in this library. To convert to bits, divide by ln(2). -/
def minEntropy {n : ℕ} [NeZero n] (p : Fin n → ℝ) : ℝ :=
  -Real.log (maxProb p)

/-- Max probability is non-negative for non-negative distributions. -/
lemma maxProb_nonneg {n : ℕ} [NeZero n] (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) :
    0 ≤ maxProb p := by
  unfold maxProb
  have h := Finset.le_sup' p (Finset.mem_univ 0)
  exact le_trans (hp 0) h

/-- Max probability is at most 1 for probability distributions. -/
lemma maxProb_le_one {n : ℕ} [NeZero n] (p : Fin n → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1) :
    maxProb p ≤ 1 := by
  unfold maxProb
  apply Finset.sup'_le
  intro i _
  calc p i ≤ ∑ j, p j := Finset.single_le_sum (fun j _ => hp_nonneg j) (Finset.mem_univ i)
    _ = 1 := hp_sum

/-- Max probability is positive for probability distributions (at least 1/n). -/
lemma maxProb_pos {n : ℕ} [NeZero n] (p : Fin n → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1) :
    0 < maxProb p := by
  unfold maxProb
  -- The sum is 1, so at least one term must be ≥ 1/n > 0
  by_contra h
  have h' : Finset.sup' Finset.univ ⟨0, Finset.mem_univ 0⟩ p ≤ 0 := le_of_not_gt h
  have h_all_le : ∀ i, p i ≤ 0 := fun i => by
    have h_le := Finset.le_sup' p (Finset.mem_univ i)
    exact le_trans h_le h'
  have h_all_eq : ∀ i, p i = 0 := fun i => le_antisymm (h_all_le i) (hp_nonneg i)
  have h_sum_zero : ∑ i, p i = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact h_all_eq i
  rw [hp_sum] at h_sum_zero
  exact one_ne_zero h_sum_zero

/-- By pigeonhole, the max probability of a distribution on Fin n is at least 1/n. -/
lemma one_div_card_le_maxProb {n : ℕ} [NeZero n] (p : Fin n → ℝ)
    (hp_sum : ∑ i, p i = 1) :
    1 / (n : ℝ) ≤ maxProb p := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have h : (1 : ℝ) ≤ n * maxProb p := by
    calc (1 : ℝ) = ∑ i, p i := hp_sum.symm
      _ ≤ ∑ _i : Fin n, maxProb p := by
          apply Finset.sum_le_sum; intro i _
          exact Finset.le_sup' p (Finset.mem_univ i)
      _ = n * maxProb p := by
          simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  rw [div_le_iff₀ hn_pos]; linarith

/-- Min-entropy is non-negative for probability distributions. -/
theorem minEntropy_nonneg {n : ℕ} [NeZero n] (p : Fin n → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1) :
    0 ≤ minEntropy p := by
  unfold minEntropy
  rw [neg_nonneg]
  apply Real.log_nonpos (le_of_lt (maxProb_pos p hp_nonneg hp_sum))
  exact maxProb_le_one p hp_nonneg hp_sum

/-- Min-entropy is at most log(n) (achieved by uniform distribution). -/
theorem minEntropy_le_log {n : ℕ} [NeZero n] (p : Fin n → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1) :
    minEntropy p ≤ Real.log n := by
  unfold minEntropy
  rw [neg_le_iff_add_nonneg, add_comm]
  have h_pos : 0 < maxProb p := maxProb_pos p hp_nonneg hp_sum
  rw [← Real.log_mul (ne_of_gt h_pos) (ne_of_gt (Nat.cast_pos.mpr (NeZero.pos n)))]
  apply Real.log_nonneg
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have h_max_ge := one_div_card_le_maxProb p hp_sum
  calc (1 : ℝ) = 1 / n * n := by field_simp
    _ ≤ maxProb p * n :=
        mul_le_mul_of_nonneg_right h_max_ge (le_of_lt hn_pos)

/-- Min-entropy of the uniform distribution equals log(n). -/
theorem minEntropy_uniform {n : ℕ} [NeZero n] :
    minEntropy (fun _ : Fin n => (1 : ℝ) / n) = Real.log n := by
  unfold minEntropy maxProb
  have h_sup : Finset.sup' Finset.univ ⟨0, Finset.mem_univ 0⟩
      (fun _ : Fin n => (1 : ℝ) / n) = 1 / n := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      rfl
    · have h := Finset.le_sup' (fun _ : Fin n => (1 : ℝ) / n) (Finset.mem_univ 0)
      exact h
  rw [h_sup]
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  rw [Real.log_div one_ne_zero (ne_of_gt hn_pos), Real.log_one, zero_sub, neg_neg]

/-- Min-entropy increases as probabilities become more uniform (decrease max). -/
lemma minEntropy_mono {n : ℕ} [NeZero n] (p q : Fin n → ℝ)
    (hp_pos : 0 < maxProb p)
    (h : maxProb p ≤ maxProb q) :
    minEntropy q ≤ minEntropy p := by
  unfold minEntropy
  rw [neg_le_neg_iff]
  exact Real.log_le_log hp_pos h

/-! ## 2-Universal Hash Families

A family of hash functions H = {h : X → Y} is 2-universal (or pairwise independent)
if for any two distinct inputs x, x' ∈ X:
  Pr_{h ← H}[h(x) = h(x')] ≤ 1/|Y|

This collision bound is the key property used in the leftover hash lemma.

Common examples:
- Linear functions over finite fields: h_{a,b}(x) = ax + b mod p
- Polynomial evaluation: h_r(x) = polynomial(x) mod r
-/

-- `HashFamily`, `HashFamily.IsUniversal`, and `HashFamily.collisionProb` are defined
-- in `Math/HashFamily.lean` (imported above) inside `namespace Math`.
-- They are accessible here as `HashFamily` via parent-namespace resolution.

/-! ## Statistical Distance

The statistical distance (also called total variation distance or L1 distance)
between two probability distributions measures how distinguishable they are.

For distributions p, q over a finite set:
  d(p, q) = (1/2) · ∑_x |p(x) - q(x)|
         = max_{S} |p(S) - q(S)|

A distance of 0 means the distributions are identical.
A distance of 1 means they have disjoint support.
-/

/-- Statistical distance between two probability distributions. -/
def statisticalDistance {n : ℕ} (p q : Fin n → ℝ) : ℝ :=
  (1 / 2) * ∑ i, |p i - q i|

/-- Statistical distance is non-negative. -/
lemma statisticalDistance_nonneg {n : ℕ} (p q : Fin n → ℝ) :
    0 ≤ statisticalDistance p q := by
  unfold statisticalDistance
  apply mul_nonneg
  · norm_num
  · apply Finset.sum_nonneg
    intro i _
    exact abs_nonneg _

/-- Statistical distance is symmetric. -/
lemma statisticalDistance_symm {n : ℕ} (p q : Fin n → ℝ) :
    statisticalDistance p q = statisticalDistance q p := by
  unfold statisticalDistance
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [abs_sub_comm]

/-- Statistical distance is 0 iff distributions are equal. -/
lemma statisticalDistance_eq_zero_iff {n : ℕ} (p q : Fin n → ℝ) :
    statisticalDistance p q = 0 ↔ p = q := by
  unfold statisticalDistance
  constructor
  · intro h
    have h_sum_zero : ∑ i, |p i - q i| = 0 := by
      have h_prod : (1 / 2 : ℝ) * ∑ i, |p i - q i| = 0 := h
      have h_half_ne : (1 / 2 : ℝ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp h_prod).resolve_left h_half_ne
    have h_all_zero : ∀ i, |p i - q i| = 0 := by
      intro i
      have h_nonneg : ∀ j ∈ Finset.univ, 0 ≤ |p j - q j| := fun j _ => abs_nonneg _
      exact Finset.sum_eq_zero_iff_of_nonneg h_nonneg |>.mp h_sum_zero i (Finset.mem_univ i)
    ext i
    have := h_all_zero i
    rw [abs_eq_zero, sub_eq_zero] at this
    exact this
  · intro h
    rw [h]
    simp only [sub_self, abs_zero, Finset.sum_const_zero, mul_zero]

/-- Statistical distance is at most 1 for probability distributions. -/
lemma statisticalDistance_le_one {n : ℕ} (p q : Fin n → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hq_nonneg : ∀ i, 0 ≤ q i)
    (hp_sum : ∑ i, p i = 1) (hq_sum : ∑ i, q i = 1) :
    statisticalDistance p q ≤ 1 := by
  unfold statisticalDistance
  -- We use: ∑ |p - q| ≤ ∑ p + ∑ q = 2
  have h_le : ∑ i, |p i - q i| ≤ ∑ i, (p i + q i) := by
    apply Finset.sum_le_sum
    intro i _
    calc |p i - q i| ≤ |p i| + |q i| := abs_sub (p i) (q i)
      _ = p i + q i := by rw [abs_of_nonneg (hp_nonneg i), abs_of_nonneg (hq_nonneg i)]
  have h_sum : ∑ i, (p i + q i) = 2 := by
    rw [Finset.sum_add_distrib, hp_sum, hq_sum]; ring
  calc (1 / 2) * ∑ i, |p i - q i|
      ≤ (1 / 2) * ∑ i, (p i + q i) := by
        apply mul_le_mul_of_nonneg_left h_le
        norm_num
    _ = (1 / 2) * 2 := by rw [h_sum]
    _ = 1 := by ring

/-! ## Leftover Hash Lemma

The leftover hash lemma is the main theorem for privacy amplification.
It states that hashing a source with high min-entropy using a 2-universal
hash function produces output that is close to uniform.

**Formal Statement**:
Let X be a random variable on Fin n with min-entropy H_∞(X) ≥ k (in nats).
Let H be a 2-universal hash family from Fin n to Fin m (output space of size m).
Let h be chosen uniformly from H.
Then:
  d((h(X), h), (U_m, h)) ≤ (1/2) · √(m · e^{-k})

where U_m is uniform on Fin m and d is statistical distance.

**Corollary**:
For ε-closeness to uniform, need m · e^{-k} ≤ (2ε)², i.e., m ≤ 4ε² · e^k.
-/

/-- The uniform distribution on Fin m. -/
def uniformDist {m : ℕ} : Fin m → ℝ :=
  fun _ => 1 / m

/-- Uniform distribution is a valid probability distribution. -/
lemma uniformDist_nonneg {m : ℕ} (i : Fin m) :
    0 ≤ uniformDist i := by
  unfold uniformDist
  apply div_nonneg one_pos.le
  exact Nat.cast_nonneg m

/-- Uniform distribution sums to 1. -/
lemma uniformDist_sum {m : ℕ} [NeZero m] :
    ∑ i : Fin m, uniformDist i = 1 := by
  unfold uniformDist
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hm_ne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  field_simp

/-- The distance between extracted key and uniform, averaged over hash choice.

    For a source distribution p on Domain and a hash family H:
    This measures how far (h(X), h) is from (U_m, h) in statistical distance,
    averaged over uniform choice of h. -/
def extractedKeyDistance {n m : ℕ}
    {Seed : Type*} [Fintype Seed]
    (p : Fin n → ℝ)
    (H : HashFamily (Fin n) (Fin m) Seed) : ℝ :=
  -- The distance is computed as the average over seeds of the
  -- statistical distance between the hashed distribution and uniform
  let hashDist := fun (s : Seed) (j : Fin m) =>
    ∑ i : Fin n, if H.hash s i = j then p i else 0
  (1 / Fintype.card Seed) * ∑ s : Seed, statisticalDistance (hashDist s) uniformDist

/-! ### Helper lemmas for the leftover hash lemma -/

/-- Max probability is bounded by exp(-minEntropy). -/
lemma maxProb_le_exp_neg_minEntropy {n : ℕ} [NeZero n] (p : Fin n → ℝ)
    (_hp_nonneg : ∀ i, 0 ≤ p i) (_hp_sum : ∑ i, p i = 1) :
    maxProb p ≤ Real.exp (-minEntropy p) := by
  unfold minEntropy
  rw [neg_neg]
  exact Real.le_exp_log (maxProb p)

/-- Individual probabilities are bounded by max probability. -/
lemma prob_le_maxProb {n : ℕ} [NeZero n] (p : Fin n → ℝ) (i : Fin n) :
    p i ≤ maxProb p := by
  unfold maxProb
  exact Finset.le_sup' p (Finset.mem_univ i)

/-- The collision probability ∑ p_i² is bounded by maxProb p for distributions. -/
lemma sum_sq_le_maxProb {n : ℕ} [NeZero n] (p : Fin n → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1) :
    ∑ i, p i ^ 2 ≤ maxProb p := by
  calc ∑ i, p i ^ 2
      = ∑ i, p i * p i := by congr 1; ext i; ring
    _ ≤ ∑ i, p i * maxProb p := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (prob_le_maxProb p i) (hp_nonneg i)
    _ = maxProb p * ∑ i, p i := by rw [← Finset.sum_mul]; ring
    _ = maxProb p := by rw [hp_sum, mul_one]

/-- The collision probability is bounded by exp(-k) when min-entropy ≥ k. -/
lemma sum_sq_le_exp_neg {n : ℕ} [NeZero n] (p : Fin n → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (k : ℝ) (hk : minEntropy p ≥ k) :
    ∑ i, p i ^ 2 ≤ Real.exp (-k) := by
  calc ∑ i, p i ^ 2
      ≤ maxProb p := sum_sq_le_maxProb p hp_nonneg hp_sum
    _ ≤ Real.exp (-minEntropy p) := maxProb_le_exp_neg_minEntropy p hp_nonneg hp_sum
    _ ≤ Real.exp (-k) := by
        apply Real.exp_le_exp_of_le
        linarith

/-- L1-L2 bound via Cauchy-Schwarz: ∑|a_i| ≤ √n · √(∑ a_i²). -/
lemma sum_abs_le_sqrt_card_mul_sqrt_sum_sq {m : ℕ} (a : Fin m → ℝ) :
    ∑ i, |a i| ≤ Real.sqrt m * Real.sqrt (∑ i, a i ^ 2) := by
  -- Apply Cauchy-Schwarz: ∑ f·g ≤ √(∑ f²) · √(∑ g²) with f = |a|, g = 1
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => |a i|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sq_abs] at hCS
  have h_card : ∑ _i : Fin m, (1 : ℝ) = (m : ℝ) := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [h_card] at hCS
  linarith [Real.sqrt_nonneg (∑ i, a i ^ 2)]

/-- Key bound: the average over seeds of the L2² distance between hashed distribution
    and uniform is bounded using universality and collision probability.

    The proof proceeds as follows. For each seed s:
      ∑_j (hashDist_s j - 1/m)² = ∑_j (hashDist_s j)² - 1/m
    Averaging over s and using universality:
      E_s[∑_j (hashDist_s j)²] ≤ ∑_i p_i² + (1/m)(1 - ∑_i p_i²)
    So: E_s[L2²] ≤ ∑_i p_i² · (1 - 1/m) ≤ ∑_i p_i² -/
lemma average_sum_sub_sq_le_sum_sq {n m : ℕ} [NeZero m]
    [DecidableEq (Fin m)]
    {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (p : Fin n → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (H : HashFamily (Fin n) (Fin m) Seed) (hH : H.IsUniversal) :
    let hashDist := fun (s : Seed) (j : Fin m) =>
      ∑ i : Fin n, if H.hash s i = j then p i else 0
    (1 / (Fintype.card Seed : ℝ)) * ∑ s : Seed,
      ∑ j : Fin m, (hashDist s j - uniformDist j) ^ 2 ≤ ∑ i, p i ^ 2 := by
  intro hashDist
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  have hSeed_pos : (0 : ℝ) < Fintype.card Seed := Nat.cast_pos.mpr Fintype.card_pos
  have hSeed_ne : (Fintype.card Seed : ℝ) ≠ 0 := ne_of_gt hSeed_pos
  have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
  -- hashDist sums to 1 for any s
  have h_hashDist_sum : ∀ s, ∑ j, hashDist s j = 1 := fun s => by
    simp only [hashDist]
    rw [Finset.sum_comm]
    have h_each : ∀ i, ∑ j : Fin m, (if H.hash s i = j then p i else 0) = p i := fun i => by
      have : ∀ j, (if H.hash s i = j then p i else 0) = (if j = H.hash s i then p i else 0) :=
        fun j => by
          split_ifs with h1 h2 h2 <;>
            [rfl; exact (h2 h1.symm).elim; exact (h1 h2.symm).elim; rfl]
      simp_rw [this]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    simp_rw [h_each]
    exact hp_sum
  -- Uniform squared sum is 1/m
  have h_unif_sq : ∑ j : Fin m, uniformDist j ^ 2 = 1 / m := by
    unfold uniformDist
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    field_simp
  -- Cross term
  have h_cross : ∀ s, ∑ j, hashDist s j * uniformDist j = 1 / m := fun s => by
    unfold uniformDist
    rw [← Finset.sum_mul, h_hashDist_sum s]
    field_simp
  -- Expand (hashDist - uniform)^2 = hashDist^2 - 2*hashDist*uniform + uniform^2
  have h_simplified : ∀ s, ∑ j, (hashDist s j - uniformDist j) ^ 2 =
      ∑ j, (hashDist s j) ^ 2 - 1 / m := fun s => by
    have h1 : ∑ j, (hashDist s j - uniformDist j) ^ 2 =
        ∑ j, (hashDist s j ^ 2 - 2 * hashDist s j * uniformDist j + uniformDist j ^ 2) := by
      apply Finset.sum_congr rfl; intro j _; ring
    rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have h2 : ∑ j, 2 * hashDist s j * uniformDist j = 2 * (1 / m) := by
      calc ∑ j, 2 * hashDist s j * uniformDist j
          = ∑ j, 2 * (hashDist s j * uniformDist j) := by ring_nf
        _ = 2 * ∑ j, hashDist s j * uniformDist j := by rw [← Finset.mul_sum]
        _ = 2 * (1 / m) := by rw [h_cross s]
    rw [h2, h_unif_sq]; ring
  simp_rw [h_simplified]
  -- Rewrite the average
  have h_avg_eq : (1 / (Fintype.card Seed : ℝ)) * ∑ s : Seed, (∑ j, hashDist s j ^ 2 - 1 / ↑m) =
      (1 / (Fintype.card Seed : ℝ)) * ∑ s : Seed, ∑ j, hashDist s j ^ 2 - 1 / m := by
    rw [Finset.mul_sum, Finset.mul_sum]
    have h_const : ∑ s : Seed, (1 / (Fintype.card Seed : ℝ)) * (1 / ↑m) = 1 / m := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp
    calc ∑ s : Seed, (1 / ↑(Fintype.card Seed)) * (∑ j, hashDist s j ^ 2 - 1 / ↑m)
        = ∑ s : Seed, ((1 / ↑(Fintype.card Seed)) * ∑ j, hashDist s j ^ 2 -
            (1 / ↑(Fintype.card Seed)) * (1 / ↑m)) := by
          apply Finset.sum_congr rfl; intro s _; ring
      _ = ∑ s, (1 / ↑(Fintype.card Seed)) * ∑ j, hashDist s j ^ 2 -
            ∑ _s : Seed, (1 / ↑(Fintype.card Seed)) * (1 / ↑m) := by rw [Finset.sum_sub_distrib]
      _ = ∑ s, (1 / ↑(Fintype.card Seed)) * ∑ j, hashDist s j ^ 2 - 1 / m := by rw [h_const]
  rw [h_avg_eq]
  -- Key: ∑_j hashDist² = ∑_{i,i'} p_i * p_i' * [h(i)=h(i')]
  have h_expand : ∀ s, ∑ j, hashDist s j ^ 2 =
      ∑ i, ∑ i', p i * p i' * (if H.hash s i = H.hash s i' then 1 else 0) := fun s => by
    simp only [hashDist, sq]
    have h_prod : ∀ j, (∑ i, if H.hash s i = j then p i else 0) *
        (∑ i', if H.hash s i' = j then p i' else 0) =
        ∑ i, ∑ i', (if H.hash s i = j then p i else 0) * (if H.hash s i' = j then p i' else 0) := by
      intro j; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
    simp_rw [h_prod]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i' _
    by_cases heq : H.hash s i = H.hash s i'
    · simp only [heq, ↓reduceIte, mul_one]
      have h_prod_ite : ∀ x,
          (if H.hash s i' = x then p i else 0) *
            (if H.hash s i' = x then p i' else 0) =
          if H.hash s i' = x then p i * p i' else 0 :=
        fun x => by split_ifs <;> ring
      simp_rw [h_prod_ite]
      rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
    · simp only [heq, ↓reduceIte, mul_zero]
      apply Finset.sum_eq_zero; intro j _
      by_cases hj1 : H.hash s i = j
      · have hj2 : H.hash s i' ≠ j := fun h => heq (hj1.trans h.symm)
        simp only [hj1, hj2, ↓reduceIte, mul_zero]
      · simp only [hj1, ↓reduceIte, zero_mul]
  simp_rw [h_expand]
  -- Split into diagonal (i = i') and off-diagonal (i ≠ i')
  have h_split : ∀ s, ∑ i, ∑ i', p i * p i' * (if H.hash s i = H.hash s i' then 1 else 0) =
      ∑ i, p i ^ 2 + ∑ i, ∑ i' ∈ (Finset.univ : Finset (Fin n)).erase i,
        p i * p i' * (if H.hash s i = H.hash s i' then 1 else 0) := fun s => by
    have h_decomp : ∀ i, ∑ i', p i * p i' * (if H.hash s i = H.hash s i' then 1 else 0) =
        p i ^ 2 + ∑ i' ∈ (Finset.univ : Finset (Fin n)).erase i,
          p i * p i' * (if H.hash s i = H.hash s i' then 1 else 0) := fun i => by
      rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
      congr 1
      simp only [↓reduceIte, mul_one, sq]
    simp_rw [h_decomp, Finset.sum_add_distrib]
  simp_rw [h_split]
  -- Off-diagonal sum without indicators
  have h_off_diag_total : ∑ i, ∑ i' ∈ (Finset.univ : Finset (Fin n)).erase i, p i * p i' =
      1 - ∑ i, p i ^ 2 := by
    have h1 : ∑ i, ∑ i', p i * p i' = (∑ i, p i) * (∑ i', p i') := by
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
    have h2 : (∑ i, p i) * (∑ i', p i') = 1 := by rw [hp_sum]; ring
    have h3 : ∑ i, p i * p i = ∑ i, p i ^ 2 := by
      apply Finset.sum_congr rfl; intro i _; ring
    have h4 : ∀ i, ∑ i' ∈ (Finset.univ : Finset (Fin n)).erase i, p i * p i' =
        ∑ i', p i * p i' - p i * p i := fun i => by
      rw [← Finset.add_sum_erase Finset.univ (fun i' => p i * p i') (Finset.mem_univ i)]
      ring
    simp_rw [h4]
    rw [Finset.sum_sub_distrib, h1, h2, h3]
  -- Universality bound on off-diagonal collision probability
  have h_avg_offdiag : (1 / (Fintype.card Seed : ℝ)) * ∑ s : Seed,
      ∑ i, ∑ i' ∈ (Finset.univ : Finset (Fin n)).erase i,
        p i * p i' * (if H.hash s i = H.hash s i' then 1 else 0) ≤
      (1 / m) * (1 - ∑ i, p i ^ 2) := by
    have h_swap : ∑ s : Seed, ∑ i, ∑ i' ∈ (Finset.univ : Finset (Fin n)).erase i,
        p i * p i' * (if H.hash s i = H.hash s i' then 1 else 0) =
        ∑ i, ∑ i' ∈ (Finset.univ : Finset (Fin n)).erase i, p i * p i' *
          (∑ s : Seed, if H.hash s i = H.hash s i' then 1 else 0) := by
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i' _
      rw [Finset.mul_sum]
    rw [h_swap, Finset.mul_sum]
    have h_indicator_bound : ∀ i i', i' ≠ i →
        (1 / (Fintype.card Seed : ℝ)) *
          (∑ s : Seed, if H.hash s i = H.hash s i' then 1 else 0) ≤
        1 / m := by
      intro i i' hne
      have hne' : i ≠ i' := fun h => hne h.symm
      have h_univ := hH i i' hne'
      have h_count : (∑ s : Seed, if H.hash s i = H.hash s i' then (1:ℝ) else 0) =
          ((Finset.univ.filter (fun s => H.hash s i = H.hash s i')).card : ℝ) := by
        rw [← Finset.sum_boole]
      rw [h_count]
      have h_card_le : (Finset.univ.filter (fun s => H.hash s i = H.hash s i')).card ≤
          Fintype.card Seed / Fintype.card (Fin m) := by convert h_univ
      simp only [Fintype.card_fin] at h_card_le
      calc (1 / (Fintype.card Seed : ℝ)) *
            ↑(Finset.filter
              (fun s => H.hash s i = H.hash s i') Finset.univ).card
          ≤ (1 / (Fintype.card Seed : ℝ)) *
            ↑(Fintype.card Seed / m) := by
            apply mul_le_mul_of_nonneg_left (Nat.cast_le.mpr h_card_le)
            apply div_nonneg one_pos.le (le_of_lt hSeed_pos)
        _ ≤ (1 / (Fintype.card Seed : ℝ)) * ((Fintype.card Seed : ℝ) / m) := by
            apply mul_le_mul_of_nonneg_left Nat.cast_div_le
            apply div_nonneg one_pos.le (le_of_lt hSeed_pos)
        _ = 1 / m := by field_simp
    calc ∑ i, (1 / (Fintype.card Seed : ℝ)) * ∑ i' ∈ (Finset.univ : Finset (Fin n)).erase i,
          p i * p i' * (∑ s, if H.hash s i = H.hash s i' then 1 else 0)
        = ∑ i, ∑ i' ∈ (Finset.univ : Finset (Fin n)).erase i, p i * p i' *
            ((1 / (Fintype.card Seed : ℝ)) * (∑ s, if H.hash s i = H.hash s i' then 1 else 0)) := by
          apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro i' _; ring
      _ ≤ ∑ i, ∑ i' ∈ (Finset.univ : Finset (Fin n)).erase i, p i * p i' * (1 / m) := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro i' hi'
          have hne : i' ≠ i := Finset.ne_of_mem_erase hi'
          apply mul_le_mul_of_nonneg_left (h_indicator_bound i i' hne)
          exact mul_nonneg (hp_nonneg i) (hp_nonneg i')
      _ = (1 / m) * ∑ i, ∑ i' ∈ (Finset.univ : Finset (Fin n)).erase i, p i * p i' := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i' _; ring
      _ = (1 / m) * (1 - ∑ i, p i ^ 2) := by rw [h_off_diag_total]
  -- Final bound
  have h_diag_const : (1 / (Fintype.card Seed : ℝ)) * ∑ _s : Seed, ∑ i, p i ^ 2 = ∑ i, p i ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp
  have h_coll_nonneg : 0 ≤ ∑ i, p i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (p i))
  have h_coll_le_1 : ∑ i, p i ^ 2 ≤ 1 := by
    calc ∑ i, p i ^ 2 ≤ ∑ i, p i := by
          apply Finset.sum_le_sum; intro i _
          have hp_le_1 : p i ≤ 1 := by
            calc p i ≤ ∑ j, p j := Finset.single_le_sum (fun j _ => hp_nonneg j) (Finset.mem_univ i)
              _ = 1 := hp_sum
          calc p i ^ 2 = p i * p i := sq (p i)
            _ ≤ p i * 1 := mul_le_mul_of_nonneg_left hp_le_1 (hp_nonneg i)
            _ = p i := mul_one (p i)
      _ = 1 := hp_sum
  calc (1 / (Fintype.card Seed : ℝ)) * ∑ s, (∑ i, p i ^ 2 +
          ∑ i, ∑ i' ∈ (Finset.univ : Finset (Fin n)).erase i,
            p i * p i' * (if H.hash s i = H.hash s i' then 1 else 0)) - 1 / ↑m
      = (1 / (Fintype.card Seed : ℝ)) * ∑ _s : Seed, ∑ i, p i ^ 2 +
          (1 / (Fintype.card Seed : ℝ)) * ∑ s, ∑ i, ∑ i' ∈ (Finset.univ : Finset (Fin n)).erase i,
            p i * p i' * (if H.hash s i = H.hash s i' then 1 else 0) - 1 / m := by
        rw [Finset.sum_add_distrib, mul_add]
    _ = ∑ i, p i ^ 2 +
          (1 / (Fintype.card Seed : ℝ)) *
            ∑ s, ∑ i, ∑ i' ∈ (Finset.univ : Finset (Fin n)).erase i,
              p i * p i' *
                (if H.hash s i = H.hash s i' then 1 else 0) -
          1 / m := by rw [h_diag_const]
    _ ≤ ∑ i, p i ^ 2 + (1 / m) * (1 - ∑ i, p i ^ 2) - 1 / m := by linarith [h_avg_offdiag]
    _ = ∑ i, p i ^ 2 + (1 / m) - (1 / m) * (∑ i, p i ^ 2) - 1 / m := by ring
    _ = ∑ i, p i ^ 2 - (1 / m) * (∑ i, p i ^ 2) := by ring
    _ = ∑ i, p i ^ 2 * (1 - 1 / m) := by
        have h_factor : (1 / (m : ℝ)) * (∑ i, p i ^ 2) = ∑ i, (1 / m) * p i ^ 2 :=
          Finset.mul_sum Finset.univ (fun i => p i ^ 2) (1 / m)
        rw [h_factor, ← Finset.sum_sub_distrib]
        congr 1; ext i; ring
    _ ≤ ∑ i, p i ^ 2 := by
        have h_factor_le_1 : 1 - 1 / (m : ℝ) ≤ 1 := by linarith [one_div_pos.mpr hm_pos]
        apply Finset.sum_le_sum; intro i _
        calc p i ^ 2 * (1 - 1 / m)
            ≤ p i ^ 2 * 1 :=
              mul_le_mul_of_nonneg_left h_factor_le_1 (sq_nonneg (p i))
          _ = p i ^ 2 := mul_one _

/-- Core technical bound: extractedKeyDistance is bounded by (1/2) · √(m · ∑ p_i²).

    Combines three ingredients:
    1. Cauchy-Schwarz per seed: ∑_j |a_j| ≤ √m · √(∑_j a_j²)
    2. Average L2² bound from universality:
       (1/|Seed|) · ∑_s ∑_j (hashDist_s j - 1/m)² ≤ ∑_i p_i²
    3. Jensen/concavity to combine averaging with √ -/
lemma extractedKeyDistance_le_sqrt_collision {n m : ℕ} [NeZero m]
    {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (p : Fin n → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (H : HashFamily (Fin n) (Fin m) Seed) (hH : H.IsUniversal) :
    extractedKeyDistance p H ≤
      (1 / 2) * Real.sqrt ((m : ℝ) * ∑ i, p i ^ 2) := by
  unfold extractedKeyDistance statisticalDistance
  let hashDist := fun (s : Seed) (j : Fin m) =>
    ∑ i : Fin n, if H.hash s i = j then p i else 0
  let L2sq := fun (s : Seed) => ∑ j : Fin m, (hashDist s j - uniformDist j) ^ 2
  -- Step 1: Apply Cauchy-Schwarz to each seed's L1 distance
  have h_cs : ∀ s : Seed, ∑ j : Fin m, |hashDist s j - uniformDist j| ≤
      Real.sqrt m * Real.sqrt (L2sq s) := fun s =>
    sum_abs_le_sqrt_card_mul_sqrt_sum_sq (fun j => hashDist s j - uniformDist j)
  -- Step 2: Bound each statistical distance
  have h_stat_bound : ∀ s : Seed, (1 / 2) * ∑ j : Fin m, |hashDist s j - uniformDist j| ≤
      (1 / 2) * Real.sqrt m * Real.sqrt (L2sq s) := fun s => by
    have h1 : (1 / 2 : ℝ) * (Real.sqrt m * Real.sqrt (L2sq s)) =
        (1 / 2) * Real.sqrt m * Real.sqrt (L2sq s) := by ring
    calc (1 / 2 : ℝ) * ∑ j : Fin m, |hashDist s j - uniformDist j|
        ≤ (1 / 2) * (Real.sqrt m * Real.sqrt (L2sq s)) := by
          apply mul_le_mul_of_nonneg_left (h_cs s); norm_num
      _ = (1 / 2) * Real.sqrt m * Real.sqrt (L2sq s) := h1
  -- Step 3: Sum over seeds and factor out constants
  have hSeed_pos : (0 : ℝ) < Fintype.card Seed := by
    have := Fintype.card_pos (α := Seed)
    exact Nat.cast_pos.mpr this
  have hSeed_ne : (Fintype.card Seed : ℝ) ≠ 0 := ne_of_gt hSeed_pos
  have h_sum_bound :
      (1 / Fintype.card Seed : ℝ) *
        ∑ s : Seed, (1 / 2) * ∑ j, |hashDist s j - uniformDist j| ≤
      (1 / Fintype.card Seed) *
        ∑ s : Seed, (1 / 2) * Real.sqrt m * Real.sqrt (L2sq s) := by
    apply mul_le_mul_of_nonneg_left
    · apply Finset.sum_le_sum
      intro s _
      exact h_stat_bound s
    · positivity
  -- Step 4: Rearrange to get (1/2) * √m * (average of √(L2sq s))
  have h_rearrange :
      (1 / Fintype.card Seed : ℝ) *
        ∑ s : Seed, (1 / 2) * Real.sqrt m * Real.sqrt (L2sq s) =
      (1 / 2) * Real.sqrt m *
        ((1 / Fintype.card Seed) * ∑ s : Seed, Real.sqrt (L2sq s)) := by
    have h1 : ∑ s : Seed, (1 / 2 * Real.sqrt m * Real.sqrt (L2sq s)) =
        (1 / 2 * Real.sqrt m) * ∑ s : Seed, Real.sqrt (L2sq s) := by
      rw [← Finset.mul_sum]
    rw [h1]
    ring
  -- Step 5: Use Cauchy-Schwarz for avg(√x) ≤ √(avg x)
  have h_L2sq_nonneg : ∀ s, 0 ≤ L2sq s := fun s =>
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have h_avg_sqrt_le : (1 / Fintype.card Seed : ℝ) * ∑ s : Seed, Real.sqrt (L2sq s) ≤
      Real.sqrt ((1 / Fintype.card Seed) * ∑ s : Seed, L2sq s) := by
    -- Use Cauchy-Schwarz: ∑ √(1) * √(L2sq s) ≤ √(∑ 1) * √(∑ L2sq s)
    have h_cs_sqrt :=
      Real.sum_sqrt_mul_sqrt_le (f := fun _ : Seed => (1 : ℝ))
        (g := fun s => L2sq s) Finset.univ
        (fun _ => zero_le_one) (fun s => h_L2sq_nonneg s)
    simp only [Real.sqrt_one, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one] at h_cs_sqrt
    -- h_cs_sqrt : ∑ s, √(L2sq s) ≤ √|Seed| * √(∑ s, L2sq s)
    have h1 :
        (1 / Fintype.card Seed : ℝ) *
          ∑ s : Seed, Real.sqrt (L2sq s) ≤
        (1 / Fintype.card Seed) *
          (Real.sqrt (Fintype.card Seed) *
            Real.sqrt (∑ s : Seed, L2sq s)) := by
      apply mul_le_mul_of_nonneg_left h_cs_sqrt
      positivity
    -- Now show: (1/c) * √c * √x = √((1/c) * x) where c = |Seed|
    have h_sum_nonneg : 0 ≤ ∑ s : Seed, L2sq s :=
      Finset.sum_nonneg (fun s _ => h_L2sq_nonneg s)
    have h_simp :
        (1 / (Fintype.card Seed : ℝ)) *
          (Real.sqrt (Fintype.card Seed) *
            Real.sqrt (∑ s : Seed, L2sq s)) =
        Real.sqrt ((1 / Fintype.card Seed) *
          ∑ s : Seed, L2sq s) := by
      have h_sqrt_ne : Real.sqrt (Fintype.card Seed : ℝ) ≠ 0 := by
        rw [Real.sqrt_ne_zero']
        exact hSeed_pos
      have h_step1 :
          (1 / (Fintype.card Seed : ℝ)) *
            Real.sqrt (Fintype.card Seed) =
          1 / Real.sqrt (Fintype.card Seed) := by
        field_simp
        exact Real.sq_sqrt hSeed_pos.le
      have h_step2 :
          (1 : ℝ) / Real.sqrt (Fintype.card Seed) =
          Real.sqrt (1 / Fintype.card Seed) := by
        rw [one_div, one_div, Real.sqrt_inv (Fintype.card Seed : ℝ)]
      have h_step3 :
          Real.sqrt (1 / (Fintype.card Seed : ℝ)) *
            Real.sqrt (∑ s : Seed, L2sq s) =
          Real.sqrt ((1 / Fintype.card Seed) *
            ∑ s : Seed, L2sq s) := by
        rw [← Real.sqrt_mul
          (by positivity : 0 ≤ 1 / (Fintype.card Seed : ℝ))]
      calc (1 / (Fintype.card Seed : ℝ)) *
            (Real.sqrt (Fintype.card Seed) *
              Real.sqrt (∑ s : Seed, L2sq s))
          = ((1 / (Fintype.card Seed : ℝ)) *
              Real.sqrt (Fintype.card Seed)) *
              Real.sqrt (∑ s : Seed, L2sq s) := by ring
        _ = (1 / Real.sqrt (Fintype.card Seed)) *
              Real.sqrt (∑ s : Seed, L2sq s) := by
            rw [h_step1]
        _ = Real.sqrt (1 / (Fintype.card Seed : ℝ)) *
              Real.sqrt (∑ s : Seed, L2sq s) := by
            rw [h_step2]
        _ = Real.sqrt ((1 / Fintype.card Seed) *
              ∑ s : Seed, L2sq s) := h_step3
    calc (1 / Fintype.card Seed : ℝ) *
          ∑ s : Seed, Real.sqrt (L2sq s)
        ≤ (1 / Fintype.card Seed) *
            (Real.sqrt (Fintype.card Seed) *
              Real.sqrt (∑ s : Seed, L2sq s)) := h1
      _ = Real.sqrt ((1 / Fintype.card Seed) *
            ∑ s : Seed, L2sq s) := h_simp
  -- Step 6: Use the L2² bound from average_sum_sub_sq_le_sum_sq
  have h_l2_bound : (1 / (Fintype.card Seed : ℝ)) * ∑ s : Seed, L2sq s ≤ ∑ i, p i ^ 2 :=
    average_sum_sub_sq_le_sum_sq p hp_nonneg hp_sum H hH
  -- Step 7: Combine all bounds
  have h_coll_nonneg : 0 ≤ ∑ i, p i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (p i))
  have h_sqrt_mono : Real.sqrt ((1 / Fintype.card Seed : ℝ) * ∑ s : Seed, L2sq s) ≤
      Real.sqrt (∑ i, p i ^ 2) := Real.sqrt_le_sqrt h_l2_bound
  have h_sqrt_mul_eq : Real.sqrt m * Real.sqrt (∑ i, p i ^ 2) =
      Real.sqrt ((m : ℝ) * ∑ i, p i ^ 2) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg m) (∑ i, p i ^ 2)]
  calc (1 / ↑(Fintype.card Seed)) *
        ∑ s : Seed, (1 / 2) *
          ∑ j : Fin m, |hashDist s j - uniformDist j|
      ≤ (1 / ↑(Fintype.card Seed)) *
          ∑ s : Seed, (1 / 2) * Real.sqrt ↑m *
            Real.sqrt (L2sq s) := h_sum_bound
    _ = (1 / 2) * Real.sqrt m *
          ((1 / Fintype.card Seed) *
            ∑ s : Seed, Real.sqrt (L2sq s)) := h_rearrange
    _ ≤ (1 / 2) * Real.sqrt m *
        Real.sqrt ((1 / Fintype.card Seed) * ∑ s : Seed, L2sq s) := by
        apply mul_le_mul_of_nonneg_left h_avg_sqrt_le
        apply mul_nonneg
        · norm_num
        · exact Real.sqrt_nonneg _
    _ ≤ (1 / 2) * Real.sqrt m * Real.sqrt (∑ i, p i ^ 2) := by
        apply mul_le_mul_of_nonneg_left h_sqrt_mono
        apply mul_nonneg
        · norm_num
        · exact Real.sqrt_nonneg _
    _ = (1 / 2) * Real.sqrt ((m : ℝ) * ∑ i, p i ^ 2) := by
        rw [mul_assoc, h_sqrt_mul_eq]

/-- For non-negative k: m · e^(-k) ≤ 2^m · 2^(-k) = 2^(m-k).
    Uses e^(-k) ≤ 2^(-k) for k ≥ 0 and m ≤ 2^m. -/
lemma nat_mul_exp_neg_le_rpow_two_sub (m : ℕ) (k : ℝ) (hk : 0 ≤ k) :
    (m : ℝ) * Real.exp (-k) ≤ Real.rpow 2 ((m : ℝ) - k) := by
  -- Write 2^(m-k) = 2^m / 2^k using Real.rpow_sub
  have h2_pos : (0 : ℝ) < 2 := by norm_num
  have h1 : Real.rpow 2 ((m : ℝ) - k) = Real.rpow 2 (m : ℝ) / Real.rpow 2 k := by
    exact Real.rpow_sub h2_pos (m : ℝ) k
  rw [h1]
  -- Key inequality 1: exp(-k) ≤ 2^(-k) = 1/2^k for k ≥ 0
  have h_rpow_pos : 0 < Real.rpow 2 k := Real.rpow_pos_of_pos h2_pos k
  have h_exp_le : Real.exp (-k) ≤ 1 / Real.rpow 2 k := by
    rw [one_div, Real.exp_neg]
    apply inv_anti₀ h_rpow_pos
    -- Need: rpow 2 k ≤ exp k
    -- rpow 2 k = exp(log 2 * k), and log 2 ≤ 1, so log 2 * k ≤ k for k ≥ 0
    have h_eq : Real.rpow 2 k = Real.exp (Real.log 2 * k) := by
      change (2 : ℝ) ^ k = Real.exp (Real.log 2 * k)
      exact Real.rpow_def_of_pos h2_pos k
    rw [h_eq]
    apply Real.exp_le_exp.mpr
    -- Prove log 2 ≤ 1 using log_le_iff_le_exp and add_one_le_exp
    have hlog : Real.log 2 ≤ 1 := by
      rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)]
      have h_add := Real.add_one_le_exp (1 : ℝ)
      linarith
    calc Real.log 2 * k ≤ 1 * k := mul_le_mul_of_nonneg_right hlog hk
      _ = k := one_mul k
  -- Key inequality 2: m ≤ 2^m for natural numbers
  have h_m_le : (m : ℝ) ≤ Real.rpow 2 (m : ℝ) := by
    have h_nat : m ≤ 2 ^ m := le_of_lt Nat.lt_two_pow_self
    calc (m : ℝ) ≤ ((2^m : ℕ) : ℝ) := Nat.cast_le.mpr h_nat
      _ = (2 : ℝ)^m := by norm_cast
      _ = Real.rpow 2 (m : ℝ) := (Real.rpow_natCast 2 m).symm
  -- Combine: m * exp(-k) ≤ m * (1/2^k) ≤ 2^m * (1/2^k) = 2^m / 2^k
  have h_inv_nonneg : 0 ≤ 1 / Real.rpow 2 k := by positivity
  calc (m : ℝ) * Real.exp (-k)
      ≤ (m : ℝ) * (1 / Real.rpow 2 k) := by
        apply mul_le_mul_of_nonneg_left h_exp_le (Nat.cast_nonneg m)
    _ ≤ Real.rpow 2 (m : ℝ) * (1 / Real.rpow 2 k) := by
        apply mul_le_mul_of_nonneg_right h_m_le h_inv_nonneg
    _ = Real.rpow 2 (m : ℝ) / Real.rpow 2 k := by ring

/-- **Classical Leftover Hash Lemma**

    If a source X has min-entropy at least k (in nats), and we hash it with a
    2-universal hash family to an output space of size m, then the extracted
    key is close to uniform:
      d((h(X), h), (U_m, h)) ≤ (1/2) · √(m · e^{-k})

    **Proof**: Three steps:
    1. Bound collision probability ∑ p_i² ≤ exp(-k) using min-entropy
    2. Apply `extractedKeyDistance_le_sqrt_collision`: d ≤ (1/2) · √(m · ∑ p_i²)
    3. Monotonicity of √ gives the result -/
theorem extractedKeyDistance_le_half_mul_sqrt_of_le_minEntropy {n m : ℕ} [NeZero n] [NeZero m]
    {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (p : Fin n → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hp_sum : ∑ i, p i = 1)
    (H : HashFamily (Fin n) (Fin m) Seed)
    (hH : H.IsUniversal)
    (k : ℝ)
    (hk : minEntropy p ≥ k) :
    extractedKeyDistance p H ≤ (1 / 2) * Real.sqrt ((m : ℝ) * Real.exp (-k)) := by
  calc extractedKeyDistance p H
      ≤ 1 / 2 * Real.sqrt ((m : ℝ) * ∑ i, p i ^ 2) :=
          extractedKeyDistance_le_sqrt_collision p hp_nonneg hp_sum H hH
    _ ≤ 1 / 2 * Real.sqrt ((m : ℝ) * Real.exp (-k)) := by
          apply mul_le_mul_of_nonneg_left
          · apply Real.sqrt_le_sqrt
            apply mul_le_mul_of_nonneg_left
            · exact sum_sq_le_exp_neg p hp_nonneg hp_sum k hk
            · exact Nat.cast_nonneg m
          · linarith

/-- **Classical Privacy Amplification Bound**

    Corollary of the classical leftover hash lemma.

    If a source on n outcomes has min-entropy at least k (in nats),
    and we hash to an output space of size m satisfying
    m · e^{-k} ≤ (2ε)², then the extracted key is ε-close to uniform
    in statistical distance.

    To use: choose m so that m · e^{-k} ≤ 4ε² for desired closeness ε. -/
theorem extractedKeyDistance_le_of_le_minEntropy {n m : ℕ} [NeZero n] [NeZero m]
    {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (p : Fin n → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hp_sum : ∑ i, p i = 1)
    (H : HashFamily (Fin n) (Fin m) Seed)
    (hH : H.IsUniversal)
    (k : ℝ)
    (hk : minEntropy p ≥ k)
    (ε : ℝ)
    (hε_pos : 0 < ε)
    (hm : (m : ℝ) * Real.exp (-k) ≤ (2 * ε) ^ 2) :
    extractedKeyDistance p H ≤ ε := by
  calc extractedKeyDistance p H
      ≤ 1 / 2 * Real.sqrt ((m : ℝ) * Real.exp (-k)) :=
          extractedKeyDistance_le_half_mul_sqrt_of_le_minEntropy p hp_nonneg hp_sum H hH k hk
    _ ≤ 1 / 2 * Real.sqrt ((2 * ε) ^ 2) := by
          apply mul_le_mul_of_nonneg_left
          · exact Real.sqrt_le_sqrt hm
          · linarith
    _ = 1 / 2 * (2 * ε) := by
          rw [Real.sqrt_sq (by linarith : 0 ≤ 2 * ε)]
    _ = ε := by ring

/-! ## Classical Smooth Min-Entropy

Smooth min-entropy for classical distributions: maximize min-entropy over
distributions ε-close in statistical distance.

H_∞^ε(X) = sup { H_∞(X') : d(X, X') ≤ ε }

This is more robust than plain min-entropy and is used in finite-blocklength
analysis. Note: a quantum generalization (conditioning on a quantum register E,
using trace distance) would require cq-states and is not formalized here. -/

/-- Classical smooth min-entropy.

    H_inf^ε(X) = sup { H_inf(X') : statisticalDistance(X, X') ≤ ε }

    Maximizes min-entropy over distributions ε-close in statistical distance.
    Equals regular min-entropy when ε = 0. -/
noncomputable def classicalSmoothMinEntropy {n : ℕ} [NeZero n] (p : Fin n → ℝ) (ε : ℝ) : ℝ :=
  sSup { h : ℝ | ∃ q : Fin n → ℝ, (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 ∧
    statisticalDistance p q ≤ ε ∧ minEntropy q = h }

/-- Smooth min-entropy is at least regular min-entropy (for ε ≥ 0). -/
lemma minEntropy_le_classicalSmoothMinEntropy {n : ℕ} [NeZero n] (p : Fin n → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1) :
    minEntropy p ≤ classicalSmoothMinEntropy p ε := by
  -- p itself is ε-close to p (distance 0 ≤ ε), so minEntropy p is in the set
  unfold classicalSmoothMinEntropy
  apply le_csSup
  · -- BddAbove: min-entropy ≤ log(n) for any prob dist on Fin n
    -- By pigeonhole: maxProb q ≥ 1/n, so -log(maxProb q) ≤ log(n)
    use Real.log n
    rintro _ ⟨q, hq_nonneg, hq_sum, _, rfl⟩
    unfold minEntropy
    have hn_pos : (0 : ℝ) < n :=
      Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
    have h_maxProb_ge := one_div_card_le_maxProb q hq_sum
    have h_maxProb_pos : 0 < maxProb q :=
      lt_of_lt_of_le (by positivity) h_maxProb_ge
    -- -log(maxProb q) ≤ -log(1/n) = log(n)
    -- Since 1/n ≤ maxProb q and log is monotone:
    -- log(1/n) ≤ log(maxProb q), so -log(maxProb q) ≤ -log(1/n) = log(n)
    have h_log := Real.log_le_log (by positivity : 0 < 1 / (n : ℝ)) h_maxProb_ge
    have h_log_inv : Real.log (1 / (n : ℝ)) = -Real.log n := by
      rw [one_div, Real.log_inv]
    linarith
  · -- minEntropy p is in the set (witnessed by q = p)
    refine ⟨p, hp_nonneg, hp_sum, ?_, rfl⟩
    have : statisticalDistance p p = 0 := (statisticalDistance_eq_zero_iff p p).mpr rfl
    linarith

/-! ## Rate of Privacy Amplification

The rate at which we can extract near-uniform bits depends on:
1. The min-entropy rate of the source
2. The desired closeness parameter ε
3. Any information leakage (e.g., error correction in a protocol)

Asymptotically, the extractable rate equals the min-entropy rate. -/

/-- The asymptotic key rate for privacy amplification.

    Given min-entropy rate r_H and security parameter ε,
    the key rate approaches r_H as n → ∞. -/
def asymptoticKeyRate (minEntropyRate : ℝ) : ℝ := minEntropyRate

/-- The finite-key rate for privacy amplification.

    For n input bits with min-entropy rate r_H, extracting m secure bits:
    m/n ≈ r_H - 2·log(1/ε)/(n·log(2))

    The correction term vanishes as n → ∞. -/
def finiteKeyRate (n : ℕ) (minEntropyRate ε : ℝ) : ℝ :=
  minEntropyRate - 2 * Real.log ε⁻¹ / (n * Real.log 2)

/-- Finite key rate approaches asymptotic rate as n → ∞. -/
theorem finiteKeyRate_tendsto (minEntropyRate ε : ℝ) (_hε : 0 < ε) (_hε' : ε < 1) :
    Filter.Tendsto (fun n => finiteKeyRate n minEntropyRate ε)
      Filter.atTop (nhds (asymptoticKeyRate minEntropyRate)) := by
  unfold finiteKeyRate asymptoticKeyRate
  -- Rewrite correction term as C * n⁻¹ where C = 2·log(1/ε)/log(2)
  have h_eq : (fun n : ℕ => minEntropyRate -
      2 * Real.log ε⁻¹ / (↑n * Real.log 2)) =
      (fun n : ℕ => minEntropyRate -
      (2 * Real.log ε⁻¹ / Real.log 2) * (↑n : ℝ)⁻¹) := by
    ext n; ring
  rw [h_eq]
  -- n⁻¹ → 0
  have h_inv : Filter.Tendsto (fun n : ℕ => (↑n : ℝ)⁻¹)
      Filter.atTop (nhds 0) :=
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
  -- C * n⁻¹ → 0
  have h_corr : Filter.Tendsto
      (fun n : ℕ => (2 * Real.log ε⁻¹ / Real.log 2) * (↑n : ℝ)⁻¹)
      Filter.atTop (nhds 0) := by
    have := h_inv.const_mul (2 * Real.log ε⁻¹ / Real.log 2)
    simp only [mul_zero] at this
    exact this
  -- minEntropyRate - (→ 0) → minEntropyRate
  have := h_corr.neg.add_const minEntropyRate
  simp only [neg_add_eq_sub] at this
  simp only [sub_zero] at this
  exact this

end Math.Concentration.PrivacyAmplification

end
