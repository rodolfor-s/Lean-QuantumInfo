import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import QCryptLean.Math.Analysis.LogBounds

/-!
# Shannon Entropy — entropyTerm, Shannon entropy, binary entropy, monotonicity

Core definitions and properties for Shannon entropy and binary entropy.

## Main definitions
- `entropyTerm`: Single term -p log p with convention 0·log(0) = 0
- `shannonEntropy`: H(p) = Σᵢ entropyTerm(pᵢ)
- `binaryEntropy`: H(p) = -p log p - (1-p) log(1-p)
- `binaryEntropyBits`: Binary entropy in bits (base-2)

## Main statements
- `shannonEntropy_nonneg`: H(p) ≥ 0
- `shannonEntropy_le_log`: H(p) ≤ log n
- `binaryEntropy_pos`: H(p) > 0 for p ∈ (0, 1)
- `binaryEntropy_strictMonoOn`: Strict monotonicity on [0, 1/2]
-/

noncomputable section

namespace Math.ClassicalEntropy

/-!
## Entropy Term

The building block for Shannon entropy: -p log p with convention 0·log(0) = 0.
-/

/-- The entropy contribution of a single probability: -p log p with 0·log(0) = 0 -/
def entropyTerm (p : ℝ) : ℝ :=
  if p = 0 then 0 else -p * Real.log p

/-- Entropy term is non-negative for probabilities in [0,1].

    **Proof strategy**: For p ∈ (0,1], log p ≤ 0, so -p log p ≥ 0.
    For p = 0, the term is 0 by definition. -/
theorem entropyTerm_nonneg (p : ℝ) (hp_nonneg : 0 ≤ p) (hp_le : p ≤ 1) :
    0 ≤ entropyTerm p := by
  unfold entropyTerm
  split_ifs with hp
  · -- Case p = 0: entropyTerm 0 = 0 ≥ 0
    rfl
  · -- Case p ≠ 0: need -p * log p ≥ 0
    -- Since 0 < p ≤ 1, we have log p ≤ 0, so -p * log p ≥ 0
    have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg (Ne.symm hp)
    have hlog_nonpos : Real.log p ≤ 0 := Real.log_nonpos (le_of_lt hp_pos) hp_le
    -- -p * log p = p * (-log p) ≥ 0 since p ≥ 0 and -log p ≥ 0
    have h := mul_nonneg (le_of_lt hp_pos) (neg_nonneg.mpr hlog_nonpos)
    linarith

/-- Entropy term at 0 is 0 (by convention 0·log(0) = 0). -/
lemma entropyTerm_zero : entropyTerm 0 = 0 := by
  unfold entropyTerm; simp only [↓reduceIte]

/-- Entropy term at 1 is 0 since log(1) = 0. -/
lemma entropyTerm_one : entropyTerm 1 = 0 := by
  unfold entropyTerm
  simp only [one_ne_zero, ↓reduceIte, Real.log_one, mul_zero]

/-- Entropy term is 0 for p ∈ {0, 1}. -/
lemma entropyTerm_zero_or_one (p : ℝ) (h : p = 0 ∨ p = 1) : entropyTerm p = 0 := by
  rcases h with rfl | rfl
  · exact entropyTerm_zero
  · exact entropyTerm_one

/-- entropyTerm equals Mathlib's negMulLog for non-negative inputs. -/
lemma entropyTerm_eq_negMulLog (p : ℝ) (_hp : 0 ≤ p) : entropyTerm p = Real.negMulLog p := by
  unfold entropyTerm
  rw [Real.negMulLog_eq_neg]
  split_ifs with h
  · simp [h]
  · ring

/-- Helper: -p * log p = -(p * log p) -/
private lemma neg_mul_log_eq (p : ℝ) : -p * Real.log p = -(p * Real.log p) := by ring

/-- entropyTerm equals the standard formula using Mathlib's convention log 0 = 0. -/
lemma entropyTerm_eq_neg_mul_log (p : ℝ) :
    entropyTerm p = -(p * Real.log p) := by
  unfold entropyTerm
  split_ifs with h
  · simp only [h, Real.log_zero, mul_zero, neg_zero]
  · exact neg_mul_log_eq p

/-!
## Shannon Entropy

Shannon entropy of a probability distribution: H(p) = -Σᵢ pᵢ log pᵢ
-/

/-- Shannon entropy of a probability distribution: H(p) = -Σᵢ pᵢ log pᵢ -/
def shannonEntropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, entropyTerm (p i)

/-- Shannon entropy is non-negative.

    **Proof strategy**: Sum of non-negative terms (entropyTerm_nonneg). -/
theorem shannonEntropy_nonneg {n : ℕ} (p : Fin n → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_le : ∀ i, p i ≤ 1) :
    0 ≤ shannonEntropy p := by
  unfold shannonEntropy
  apply Finset.sum_nonneg
  intro i _
  exact entropyTerm_nonneg (p i) (hp_nonneg i) (hp_le i)

/-- Shannon entropy is 0 if all probabilities are 0 or 1. -/
lemma shannonEntropy_zero_of_zero_or_one {n : ℕ} (p : Fin n → ℝ)
    (h : ∀ i, p i = 0 ∨ p i = 1) : shannonEntropy p = 0 := by
  unfold shannonEntropy
  apply Finset.sum_eq_zero
  intro i _
  exact entropyTerm_zero_or_one (p i) (h i)

/-- Shannon entropy in terms of negMulLog. -/
lemma shannonEntropy_eq_sum_negMulLog {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) :
    shannonEntropy p = ∑ i, Real.negMulLog (p i) := by
  unfold shannonEntropy
  congr 1; ext i
  exact entropyTerm_eq_negMulLog (p i) (hp i)

/-- Shannon entropy equals the sum formula -Σᵢ pᵢ log pᵢ. -/
lemma shannonEntropy_eq_neg_sum_mul_log {n : ℕ} (p : Fin n → ℝ) :
    shannonEntropy p = -∑ i, p i * Real.log (p i) := by
  unfold shannonEntropy
  have h : ∀ i ∈ Finset.univ, entropyTerm (p i) = -(p i * Real.log (p i)) := by
    intro i _; exact entropyTerm_eq_neg_mul_log (p i)
  rw [Finset.sum_congr rfl h, Finset.sum_neg_distrib]

/-- Shannon entropy is preserved when all values are equal. -/
lemma shannonEntropy_congr {n : ℕ} (p q : Fin n → ℝ)
    (h : ∀ i, p i = q i) : shannonEntropy p = shannonEntropy q := by
  unfold shannonEntropy
  congr 1; ext i; rw [h i]

/-- Shannon entropy is invariant under permutation of values.
    This follows from the fact that sums over Fin n are permutation-invariant. -/
lemma shannonEntropy_perm {n : ℕ} (p q : Fin n → ℝ) (σ : Equiv.Perm (Fin n))
    (hpq : ∀ i, p i = q (σ i)) :
    shannonEntropy p = shannonEntropy q := by
  unfold shannonEntropy
  conv_lhs => arg 2; ext i; rw [hpq]
  -- Goal: ∑ i, entropyTerm (q (σ i)) = ∑ i, entropyTerm (q i)
  have h : (Set.ofPred fun a => σ a ≠ a) ⊆ (Finset.univ : Finset (Fin n)) := by
    intro x _; exact Finset.mem_univ x
  exact Equiv.Perm.sum_comp σ Finset.univ (entropyTerm ∘ q) h

/-- negMulLog(1/n) = (1/n) * log(n). -/
lemma negMulLog_inv_nat (n : ℕ) [NeZero n] :
    Real.negMulLog ((1 : ℝ) / n) = (1 / n) * Real.log n := by
  have h : Real.log ((1 : ℝ) / n) = -Real.log n := by
    rw [Real.log_div one_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne n)), Real.log_one, zero_sub]
  simp only [Real.negMulLog, h]
  ring

/-- Shannon entropy is bounded by log(n) (maximum for uniform distribution).

    **Proof strategy**: Jensen's inequality. For concave f(x) = -x log x:
    Σᵢ f(pᵢ) ≤ n · f(Σᵢ pᵢ/n) = n · f(1/n) = log n
    Equality holds iff pᵢ = 1/n for all i. -/
theorem shannonEntropy_le_log {n : ℕ} [NeZero n] (p : Fin n → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1) :
    shannonEntropy p ≤ Real.log n := by
  -- Convert to negMulLog
  rw [shannonEntropy_eq_sum_negMulLog p hp_nonneg]
  -- Set uniform weights w i = 1/n
  let w : Fin n → ℝ := fun _ => (1 : ℝ) / n
  have hw_nonneg : ∀ i, 0 ≤ w i := fun _ => by
    apply div_nonneg one_pos.le; exact Nat.cast_nonneg n
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hw_sum : ∑ i : Fin n, w i = 1 := by
    simp only [w, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    field_simp
  have hp_in_Ici : ∀ i, p i ∈ Set.Ici (0 : ℝ) := fun i => hp_nonneg i
  -- Jensen: ∑ (1/n) • negMulLog(p i) ≤ negMulLog(∑ (1/n) • p i)
  have jensen := Real.concaveOn_negMulLog.le_map_sum
    (fun i _ => hw_nonneg i) hw_sum (fun i _ => hp_in_Ici i)
  -- Simplify LHS: ∑ (1/n) • negMulLog(p i) = (1/n) * ∑ negMulLog(p i)
  have h_lhs : ∑ i : Fin n, w i • Real.negMulLog (p i) =
               (1 / n) * ∑ i, Real.negMulLog (p i) := by
    simp only [w, smul_eq_mul]
    rw [← Finset.mul_sum]
  -- Simplify RHS argument: ∑ (1/n) • p i = 1/n
  have h_rhs_arg : ∑ i : Fin n, w i • p i = (1 : ℝ) / n := by
    simp only [w, smul_eq_mul]
    rw [← Finset.mul_sum, hp_sum, mul_one]
  rw [h_lhs, h_rhs_arg] at jensen
  -- Jensen now says: (1/n) * H(p) ≤ negMulLog(1/n) = (1/n) * log(n)
  rw [negMulLog_inv_nat n] at jensen
  -- Multiply both sides by n
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  calc ∑ i, Real.negMulLog (p i)
      = n * ((1 / n) * ∑ i, Real.negMulLog (p i)) := by field_simp
    _ ≤ n * ((1 / n) * Real.log n) := by
        apply mul_le_mul_of_nonneg_left jensen (le_of_lt hn_pos)
    _ = Real.log n := by field_simp

/-- Shannon entropy of the uniform distribution is log n. -/
lemma shannonEntropy_uniform {n : ℕ} [NeZero n] :
    shannonEntropy (fun _ : Fin n => (1 : ℝ) / n) = Real.log n := by
  unfold shannonEntropy entropyTerm
  have hn_ne : (1 : ℝ) / n ≠ 0 := by
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
    exact ne_of_gt (div_pos one_pos hn_pos)
  simp only [hn_ne, ↓reduceIte]
  have h_log : Real.log ((1 : ℝ) / n) = -Real.log n := by
    have hn_ne' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    rw [Real.log_div one_ne_zero hn_ne', Real.log_one, zero_sub]
  simp only [h_log, neg_mul]
  rw [Finset.sum_const, Finset.card_fin]
  simp only [nsmul_eq_mul]
  have hn_ne' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  field_simp [hn_ne']

/-!
## Binary Entropy

Binary entropy function: H(p) = -p log p - (1-p) log(1-p)
-/

/-- Binary entropy function: H(p) = -p log p - (1-p) log(1-p) -/
def binaryEntropy (p : ℝ) : ℝ :=
  entropyTerm p + entropyTerm (1 - p)

/-- A normalized two-point Shannon entropy is the binary entropy of outcome `1`. -/
lemma shannonEntropy_fin_two_eq_binaryEntropy_of_sum_eq_one
    (p : Fin 2 → ℝ) (hp_sum : ∑ i : Fin 2, p i = 1) :
    shannonEntropy p = binaryEntropy (p 1) := by
  have hp0 : p 0 = 1 - p 1 := by
    rw [Fin.sum_univ_two] at hp_sum
    linarith
  unfold shannonEntropy binaryEntropy
  rw [Fin.sum_univ_two, hp0]
  ac_rfl

/-- Binary entropy is symmetric: H(p) = H(1-p) -/
theorem binaryEntropy_symm (p : ℝ) : binaryEntropy p = binaryEntropy (1 - p) := by
  unfold binaryEntropy
  ring_nf

/-- Binary entropy is 0 at p = 0. -/
theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  unfold binaryEntropy entropyTerm
  simp

/-- Binary entropy is 0 at p = 1. -/
theorem binaryEntropy_one : binaryEntropy 1 = 0 := by
  unfold binaryEntropy entropyTerm
  simp

/-- Binary entropy at p = 1/2 equals log 2. -/
theorem binaryEntropy_half : binaryEntropy (1/2) = Real.log 2 := by
  unfold binaryEntropy entropyTerm
  -- H(1/2) = -1/2 * log(1/2) + -1/2 * log(1/2)
  --        = -1/2 * (-log 2) * 2 = log 2
  have hne : (1 : ℝ) / 2 ≠ 0 := by norm_num
  have h1 : (1 : ℝ) - 1/2 = 1/2 := by norm_num
  simp only [hne, h1, ↓reduceIte]
  have hlog : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
    rw [Real.log_div one_ne_zero two_ne_zero, Real.log_one, zero_sub]
  rw [hlog]
  ring

/-- Binary entropy is non-negative for probabilities.

    For p ∈ [0,1], H(p) = -p log p - (1-p) log(1-p) ≥ 0. -/
lemma binaryEntropy_nonneg (p : ℝ) (hp_nonneg : 0 ≤ p) (hp_le : p ≤ 1) :
    0 ≤ binaryEntropy p := by
  unfold binaryEntropy
  apply add_nonneg
  · exact entropyTerm_nonneg p hp_nonneg hp_le
  · have h : 0 ≤ 1 - p := by linarith
    have h' : 1 - p ≤ 1 := by linarith
    exact entropyTerm_nonneg (1 - p) h h'

/-- Binary entropy is strictly positive for probabilities in the open interval (0, 1). -/
lemma binaryEntropy_pos {p : ℝ} (hp_pos : 0 < p) (hp_lt : p < 1) :
    0 < binaryEntropy p := by
  unfold binaryEntropy
  apply add_pos_of_pos_of_nonneg
  · unfold entropyTerm; simp only [ne_of_gt hp_pos, ↓reduceIte, neg_mul]
    exact neg_pos.mpr (mul_neg_of_pos_of_neg hp_pos (Real.log_neg hp_pos hp_lt))
  · exact entropyTerm_nonneg (1 - p) (by linarith) (by linarith)

/-- Binary entropy is bounded above by log 2.

    For p ∈ [0,1], H(p) ≤ log 2, with equality at p = 1/2.

    By Jensen's inequality applied to the concave function -x log x,
    Shannon entropy is maximized when the distribution is uniform.
    For a 2-element distribution, this occurs at p = 1/2, giving H(1/2) = log 2. -/
lemma binaryEntropy_le_log_two (p : ℝ) (hp_nonneg : 0 ≤ p) (hp_le : p ≤ 1) :
    binaryEntropy p ≤ Real.log 2 := by
  -- Define the 2-element distribution
  let q : Fin 2 → ℝ := fun i => if i = 0 then p else 1 - p
  -- Show binaryEntropy p = shannonEntropy q
  have h_eq : binaryEntropy p = shannonEntropy q := by
    unfold binaryEntropy shannonEntropy q
    rw [Finset.sum_fin_eq_sum_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num
  -- Show q is a probability distribution
  have hq_nonneg : ∀ i, 0 ≤ q i := by
    intro i
    simp only [q]
    split_ifs with hi
    · exact hp_nonneg
    · linarith
  have hq_sum : ∑ i, q i = 1 := by
    rw [Finset.sum_fin_eq_sum_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, q]
    norm_num
  -- Apply shannonEntropy_le_log: Shannon entropy ≤ log n for any distribution
  rw [h_eq]
  exact shannonEntropy_le_log q hq_nonneg hq_sum

/-- Binary entropy in bits: H_bits(p) = H_nats(p) / ln(2)

    This is the standard information-theoretic entropy in bits.
    H_bits(1/2) = 1 (one bit of uncertainty). -/
def binaryEntropyBits (p : ℝ) : ℝ := binaryEntropy p / Real.log 2

/-- Binary entropy in bits at p = 1/2 equals 1 bit. -/
theorem binaryEntropyBits_half : binaryEntropyBits (1/2) = 1 := by
  unfold binaryEntropyBits
  rw [binaryEntropy_half]
  exact div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'

/-- Binary entropy in bits at p = 0 equals 0. -/
theorem binaryEntropyBits_zero : binaryEntropyBits 0 = 0 := by
  unfold binaryEntropyBits
  rw [binaryEntropy_zero]
  simp

/-- Binary entropy in bits at p = 1 equals 0. -/
theorem binaryEntropyBits_one : binaryEntropyBits 1 = 0 := by
  unfold binaryEntropyBits
  rw [binaryEntropy_one]
  simp

/-- Binary entropy in bits is non-negative. -/
theorem binaryEntropyBits_nonneg (p : ℝ) (hp_nonneg : 0 ≤ p) (hp_le : p ≤ 1) :
    0 ≤ binaryEntropyBits p := by
  unfold binaryEntropyBits
  apply div_nonneg (binaryEntropy_nonneg p hp_nonneg hp_le)
  exact le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2))

/-- Binary entropy in bits is bounded by 1.

    For p ∈ [0,1], H_bits(p) ≤ 1, with equality at p = 1/2. -/
theorem binaryEntropyBits_le_one (p : ℝ) (hp_nonneg : 0 ≤ p) (hp_le : p ≤ 1) :
    binaryEntropyBits p ≤ 1 := by
  unfold binaryEntropyBits
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h := binaryEntropy_le_log_two p hp_nonneg hp_le
  rw [div_le_one hlog2_pos]
  exact h

/-- **A single binomial term is bounded by 1.**

    For `0 ≤ p ≤ 1` and `k ≤ n`, the binomial term `C(n,k)·p^k·(1−p)^{n−k}` is at most
    `(p + (1−p))^n = 1`, because it is one of the nonnegative summands of the binomial
    expansion `add_pow`. This is the elementary fact underlying the Hartley bound
    `choose_le_two_pow_mul_binaryEntropyBits`. -/
theorem choose_mul_pow_mul_pow_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {n k : ℕ} (hk : k ≤ n) :
    (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) ≤ 1 := by
  have hq0 : (0 : ℝ) ≤ 1 - p := by linarith
  -- The full binomial expansion equals `(p + (1-p))^n = 1`.
  have hexp : (1 : ℝ) = ∑ m ∈ Finset.range (n + 1),
      p ^ m * (1 - p) ^ (n - m) * (n.choose m : ℝ) := by
    have := add_pow p (1 - p) n
    simp only [add_sub_cancel] at this
    rw [one_pow] at this
    exact this
  -- Our term is the `m = k` summand; all summands are nonnegative.
  have hmem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
  have hnonneg : ∀ m ∈ Finset.range (n + 1),
      0 ≤ p ^ m * (1 - p) ^ (n - m) * (n.choose m : ℝ) := by
    intro m _
    positivity
  have hle := Finset.single_le_sum hnonneg hmem
  rw [← hexp] at hle
  calc (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)
      = p ^ k * (1 - p) ^ (n - k) * (n.choose k : ℝ) := by ring
    _ ≤ 1 := hle

/-- **Hartley / binomial-coefficient entropy bound (base 2).**

    The number of `k`-subsets of `[n]` is at most `2^{n·h(k/n)}`, where `h` is the
    base-2 binary entropy. Concretely, for `k ≤ n`,
    `C(n, k) ≤ 2^{n · binaryEntropyBits(k/n)}`.

    This is the standard Stirling/Hartley bound (Renner thesis `lem:binsize`,
    arXiv:quant-ph/0512258 `main.tex:5306-5347`), not present in Mathlib. The proof is
    the elementary one: with `p := k/n ∈ [0,1]`, the single binomial term
    `C(n,k)·p^k·(1−p)^{n−k} ≤ 1` (`choose_mul_pow_mul_pow_le_one`), and taking base-2
    logarithms turns `p^k·(1−p)^{n−k}` into `−n·h(p)`.

    It is the discharge of the `RestrictedSymSpaceWitness.card_S` cardinality bound at
    the genuine combinatorial count `S.card = C(n, n−r) = C(n, r)` (`lem:symspacebin`). -/
theorem choose_le_two_pow_mul_binaryEntropyBits (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) * binaryEntropyBits ((k : ℝ) / (n : ℝ))) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  -- Reduce the base-2 power on the right to a natural exponential: with
  -- `binaryEntropyBits p = binaryEntropy p / log 2`, the exponent `n · h_bits(p) · log 2`
  -- collapses to `n · binaryEntropy(p)`, so the RHS is `exp (n · binaryEntropy(p))`.
  set p : ℝ := (k : ℝ) / (n : ℝ) with hp_def
  have hrhs : (2 : ℝ) ^ ((n : ℝ) * binaryEntropyBits p)
      = Real.exp ((n : ℝ) * binaryEntropy p) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), binaryEntropyBits, mul_div_assoc',
      mul_div_assoc', mul_div_cancel_left₀ _ hlog2_pos.ne']
  rw [hrhs]
  -- It suffices to bound `log (choose) ≤ n · binaryEntropy p`, then exponentiate.
  have hchoose_pos : (0 : ℝ) < (n.choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos hk
  rw [← Real.exp_log hchoose_pos]
  apply Real.exp_le_exp.mpr
  -- Edge cases where the binomial term has a factor `0^0` need separate handling.
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · -- n = 0 ⟹ k = 0, choose = 1, log 1 = 0; RHS exponent has factor n = 0.
    have hk0 : k = 0 := Nat.le_zero.mp (hn0 ▸ hk)
    subst hk0; subst hn0
    simp
  · have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have hp0 : 0 ≤ p := div_nonneg (Nat.cast_nonneg _) hnR.le
    have hp1 : p ≤ 1 := by
      rw [hp_def, div_le_one hnR]; exact_mod_cast hk
    -- The base inequality: `choose · p^k · (1-p)^{n-k} ≤ 1`.
    have hterm := choose_mul_pow_mul_pow_le_one hp0 hp1 hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · -- k = 0: p = 0, binaryEntropy 0 = 0, choose n 0 = 1, log 1 = 0 ≤ 0.
      subst hk0
      have hp_eq : p = 0 := by rw [hp_def, Nat.cast_zero, zero_div]
      simp only [Nat.choose_zero_right, Nat.cast_one, Real.log_one]
      rw [hp_eq]
      simp [binaryEntropy, entropyTerm]
    · rcases eq_or_lt_of_le hk with hkn | hklt
      · -- k = n: p = 1, binaryEntropy 1 = 0, choose n n = 1, log 1 = 0 ≤ 0.
        subst hkn
        have hp_eq : p = 1 := by rw [hp_def, div_self hnR.ne']
        simp only [Nat.choose_self, Nat.cast_one, Real.log_one]
        rw [hp_eq]
        simp [binaryEntropy, entropyTerm]
      · -- 0 < k < n: all factors strictly positive, take logs of `hterm`.
        have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
        have hnkR : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by
          have : 0 < n - k := Nat.sub_pos_of_lt hklt
          exact_mod_cast this
        have hp_pos : 0 < p := div_pos hkR hnR
        have hp_lt1 : p < 1 := by
          rw [hp_def, div_lt_one hnR]; exact_mod_cast hklt
        have hq_pos : 0 < 1 - p := sub_pos.mpr hp_lt1
        -- `entropyTerm p = -p log p`, `entropyTerm (1-p) = -(1-p) log (1-p)`.
        have hep : entropyTerm p = -p * Real.log p := by
          rw [entropyTerm]; rw [ite_eq_right (ne_of_gt hp_pos)]
        have heq : entropyTerm (1 - p) = -(1 - p) * Real.log (1 - p) := by
          rw [entropyTerm]; rw [ite_eq_right (ne_of_gt hq_pos)]
        -- `n · p = k`, `n · (1-p) = n - k` as reals.
        have hnp : (n : ℝ) * p = (k : ℝ) := by
          rw [hp_def, mul_div_cancel₀ _ hnR.ne']
        have hnq : (n : ℝ) * (1 - p) = ((n - k : ℕ) : ℝ) := by
          rw [mul_sub, mul_one, hnp, Nat.cast_sub hk]
        -- Expand `n · binaryEntropy p`.
        have hexpand : (n : ℝ) * binaryEntropy p
            = -(k : ℝ) * Real.log p - ((n - k : ℕ) : ℝ) * Real.log (1 - p) := by
          rw [binaryEntropy, hep, heq]
          linear_combination (-Real.log p) * hnp + (-Real.log (1 - p)) * hnq
        rw [hexpand]
        -- Take `log` of `choose · p^k · (1-p)^{n-k} ≤ 1`.
        have hpk_pos : (0 : ℝ) < p ^ k := pow_pos hp_pos k
        have hqk_pos : (0 : ℝ) < (1 - p) ^ (n - k) := pow_pos hq_pos (n - k)
        have hprod_pos : (0 : ℝ) < (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) :=
          mul_pos (mul_pos hchoose_pos hpk_pos) hqk_pos
        have hlog_le : Real.log ((n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k))
            ≤ Real.log 1 := Real.log_le_log hprod_pos hterm
        rw [Real.log_one] at hlog_le
        rw [Real.log_mul (mul_pos hchoose_pos hpk_pos).ne' (ne_of_gt hqk_pos),
          Real.log_mul (ne_of_gt hchoose_pos) (ne_of_gt hpk_pos),
          Real.log_pow, Real.log_pow] at hlog_le
        -- `log choose + k log p + (n-k) log(1-p) ≤ 0`.
        linarith only [hlog_le]

/-- Our binaryEntropy equals Mathlib's Real.binEntropy.

    Both are defined as -p log p - (1-p) log(1-p), but with slightly different formulations.
    Mathlib: binEntropy p = p * log(p⁻¹) + (1 - p) * log((1 - p)⁻¹)
    Ours: binaryEntropy p = entropyTerm p + entropyTerm (1 - p) where entropyTerm p = -p * log p

    Since p * log(p⁻¹) = p * (-log p) = -p * log p, these are equal. -/
lemma binaryEntropy_eq_binEntropy (p : ℝ) : binaryEntropy p = Real.binEntropy p := by
  unfold binaryEntropy
  -- entropyTerm p = -(p * log p) = negMulLog p
  have h1 : entropyTerm p = Real.negMulLog p := by
    rw [entropyTerm_eq_neg_mul_log, Real.negMulLog_eq_neg]
  have h2 : entropyTerm (1 - p) = Real.negMulLog (1 - p) := by
    rw [entropyTerm_eq_neg_mul_log, Real.negMulLog_eq_neg]
  rw [h1, h2, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

/-- Binary entropy is strictly increasing on [0, 1/2].

    Combined with symmetry, this shows H achieves its unique maximum at p = 1/2.

    **Proof**: Uses Mathlib's Real.binEntropy_strictMonoOn after showing
    binaryEntropy = binEntropy. -/
theorem binaryEntropy_strictMonoOn :
    StrictMonoOn binaryEntropy (Set.Icc 0 (1/2)) := by
  -- Show 1/2 = 2⁻¹ (Mathlib uses 2⁻¹)
  have h_half : (1 : ℝ) / 2 = 2⁻¹ := one_div 2
  rw [h_half]
  -- Use binaryEntropy = binEntropy and apply Mathlib's theorem
  intro x hx y hy hxy
  rw [binaryEntropy_eq_binEntropy, binaryEntropy_eq_binEntropy]
  exact Real.binEntropy_strictMonoOn hx hy hxy

/-- Binary entropy in bits is strictly increasing on [0, 1/2]. -/
theorem binaryEntropyBits_strictMonoOn :
    StrictMonoOn binaryEntropyBits (Set.Icc 0 (1/2)) := by
  unfold binaryEntropyBits
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  intro x hx y hy hxy
  apply div_lt_div_of_pos_right _ hlog2_pos
  exact binaryEntropy_strictMonoOn hx hy hxy

/-- Binary entropy is monotone on [0, 1/2]: for `0 ≤ p ≤ q ≤ 1/2`, `h(p) ≤ h(q)`.

    Equivalently, `log 2 − 2·h(q) ≤ log 2 − 2·h(p)` for `p ≤ q` in `[0, 1/2]`.
    This is the non-strict form of `binaryEntropy_strictMonoOn`, used to convert
    an upper bound on the true error rate into a lower bound on the Shor–Preskill
    per-round key rate. -/
theorem binaryEntropy_le_of_le_of_le_half {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1 / 2) :
    binaryEntropy p ≤ binaryEntropy q := by
  rcases eq_or_lt_of_le hpq with rfl | hlt
  · exact le_refl _
  · exact le_of_lt (binaryEntropy_strictMonoOn
      ⟨hp, le_trans hpq hq⟩ ⟨le_trans hp (le_of_lt hlt), hq⟩ hlt)

/-- `−(1−p)·log(1−p) ≤ p` for `p < 1`: `log(1/(1−p)) ≤ 1/(1−p) − 1 = p/(1−p)`. -/
lemma entropyTerm_one_sub_le {p : ℝ} (hp1 : p < 1) : entropyTerm (1 - p) ≤ p := by
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have hkey : Real.log (1 / (1 - p)) ≤ 1 / (1 - p) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [one_div, Real.log_inv] at hkey
  rw [entropyTerm_eq_neg_mul_log]
  calc -((1 - p) * Real.log (1 - p))
      = (1 - p) * -Real.log (1 - p) := by ring
    _ ≤ (1 - p) * ((1 - p)⁻¹ - 1) := mul_le_mul_of_nonneg_left hkey h1p.le
    _ = p := by field_simp; ring

/-- **The binary-entropy bound at a free anchor**: `h₂(p) ≤ a − p·log a` for every `a > 0` and
every `p ∈ [0, 1)`.

Proved from `log x ≤ x − 1` at `x = a/p`, which gives `−p·log p ≤ a − p − p·log a`, combined with
`entropyTerm_one_sub_le`'s bound `−(1−p)·log(1−p) ≤ p`; the two `p`'s cancel. At `p = 0` the
first term is `0` and the bound reads `0 ≤ a`. The bound is tightest at `a = p`, where it
becomes `p·(1 − log p)`. -/
lemma binaryEntropy_le_sub_mul_log {a p : ℝ} (ha : 0 < a) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    binaryEntropy p ≤ a - p * Real.log a := by
  have hterm1 : entropyTerm p ≤ a - p - p * Real.log a := by
    rcases eq_or_lt_of_le hp0 with rfl | hppos
    · simp only [entropyTerm_eq_neg_mul_log, zero_mul, neg_zero, sub_zero, sub_zero]
      linarith only [ha]
    · have hpne : p ≠ 0 := ne_of_gt hppos
      have hkey : Real.log (a / p) ≤ a / p - 1 :=
        Real.log_le_sub_one_of_pos (div_pos ha hppos)
      rw [Real.log_div (ne_of_gt ha) hpne] at hkey
      have hmul : p * Real.log a - p * Real.log p ≤ a - p := by
        calc p * Real.log a - p * Real.log p
            = p * (Real.log a - Real.log p) := by ring
          _ ≤ p * (a / p - 1) := mul_le_mul_of_nonneg_left hkey hppos.le
          _ = a - p := by field_simp
      rw [entropyTerm_eq_neg_mul_log]
      linarith only [hmul]
  have hterm2 : entropyTerm (1 - p) ≤ p := entropyTerm_one_sub_le hp1
  have hsplit : binaryEntropy p = entropyTerm p + entropyTerm (1 - p) := rfl
  linarith only [hterm1, hterm2, hsplit]

end Math.ClassicalEntropy
