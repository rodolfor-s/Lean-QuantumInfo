import Mathlib.Analysis.Complex.ExponentialBounds
import QCryptLean.Math.Analysis.LogBounds
import QCryptLean.Math.ClassicalEntropy.Entropy

/-!
# Binary Entropy Thresholds — BB84 threshold, numerical bounds on h(p)

Numerical bounds on binary entropy needed for BB84 security analysis, including
the unique threshold e ∈ (0, 1/2) where H_bits(e) = 1/2.

## Main definitions
- `binaryEntropyBitsHalfRoot`: The unique e ∈ (0, 1/2) with H_bits(e) = 1/2

## Main statements
- `binaryEntropyBits_011_lt_half`: H_bits(0.11) < 1/2
- `binaryEntropyBitsHalfRoot_approx`: binaryEntropyBitsHalfRoot ∈ (0.109, 0.112)
- `binaryEntropyBits_lt_half_of_lt_011`: H_bits(e) < 1/2 for e < 0.11
-/

noncomputable section

namespace Math.ClassicalEntropy

/-!
## Exponential and Logarithm Bounds

These technical lemmas establish bounds on exp and log needed for entropy calculations.
They use Taylor series bounds from Mathlib's ExponentialBounds.
-/

/-- exp(0.19) < 1.211, derived from Taylor series with error bound. -/
private lemma exp_0_19_lt : Real.exp 0.19 < 1.211 := by
  have h := Real.exp_bound (x := 0.19) (by norm_num : |(0.19 : ℝ)| ≤ 1)
                          (n := 3) (by norm_num : 0 < 3)
  have hsum : (∑ m ∈ Finset.range 3, (0.19 : ℝ)^m / m.factorial) = 1.20805 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
    norm_num
  have herr : |(0.19 : ℝ)|^3 * (↑(Nat.succ 3) / (↑(Nat.factorial 3) * 3)) < 0.002 := by
    simp [Nat.factorial]; norm_num
  have h3 : |Real.exp 0.19 - 1.20805| < 0.002 := by
    calc |Real.exp 0.19 - 1.20805|
        = |Real.exp 0.19 - ∑ m ∈ Finset.range 3, (0.19 : ℝ)^m / m.factorial| := by rw [hsum]
      _ ≤ |(0.19 : ℝ)|^3 * (↑(Nat.succ 3) / (↑(Nat.factorial 3) * 3)) := h
      _ < 0.002 := herr
  have := abs_sub_lt_iff.mp h3
  linarith

/-- exp(2.19) < 9, using exp(2.19) = exp(1)² * exp(0.19). -/
private lemma exp_2_19_lt : Real.exp 2.19 < 9 := by
  have h1 : Real.exp 2.19 = Real.exp 1 * Real.exp 1 * Real.exp 0.19 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  rw [h1]
  have he1 := Real.exp_one_lt_d9
  have he019 := exp_0_19_lt
  calc Real.exp 1 * Real.exp 1 * Real.exp 0.19
      < 2.7182818286 * 2.7182818286 * 1.211 := by
        have hp1 := Real.exp_pos 1
        have hp019 := Real.exp_pos 0.19
        nlinarith
    _ < 9 := by norm_num

/-- log(9) > 2.19, derived from exp(2.19) < 9. -/
private lemma log_9_gt_2_19 : Real.log 9 > 2.19 := by
  have h := exp_2_19_lt
  rw [show (2.19 : ℝ) = Real.log (Real.exp 2.19) from (Real.log_exp 2.19).symm]
  exact Real.log_lt_log (Real.exp_pos 2.19) h

/-- exp(0.31) > 1.36, derived from Taylor series with error bound. -/
private lemma exp_0_31_gt : Real.exp 0.31 > 1.36 := by
  have h := Real.exp_bound (x := 0.31) (by norm_num : |(0.31 : ℝ)| ≤ 1)
                          (n := 4) (by norm_num : 0 < 4)
  have hsum : (∑ m ∈ Finset.range 4, (0.31 : ℝ)^m / m.factorial) = 8178091/6000000 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial]
    norm_num
  have herr : |(0.31 : ℝ)|^4 * (↑(Nat.succ 4) / (↑(Nat.factorial 4) * 4)) < 0.0025 := by
    simp [Nat.factorial]; norm_num
  have h3 : |Real.exp 0.31 - 8178091/6000000| < 0.0025 := by
    calc |Real.exp 0.31 - 8178091/6000000|
        = |Real.exp 0.31 - ∑ m ∈ Finset.range 4, (0.31 : ℝ)^m / m.factorial| := by rw [hsum]
      _ ≤ |(0.31 : ℝ)|^4 * (↑(Nat.succ 4) / (↑(Nat.factorial 4) * 4)) := h
      _ < 0.0025 := herr
  have := abs_sub_lt_iff.mp h3
  have hval : (8178091 : ℝ)/6000000 > 1.3625 := by norm_num
  linarith

/-- exp(2.31) > 10, using exp(2.31) = exp(1)² * exp(0.31). -/
private lemma exp_2_31_gt : Real.exp 2.31 > 10 := by
  have h1 : Real.exp 2.31 = Real.exp 1 * Real.exp 1 * Real.exp 0.31 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  rw [h1]
  have he1 := Real.exp_one_gt_d9
  have he031 := exp_0_31_gt
  calc (10 : ℝ) < 2.7182818283 * 2.7182818283 * 1.36 := by norm_num
    _ < Real.exp 1 * Real.exp 1 * Real.exp 0.31 := by
        have hp1 := Real.exp_pos 1
        have hp031 := Real.exp_pos 0.31
        nlinarith

/-- log(10) < 2.31, derived from exp(2.31) > 10. -/
private lemma log_10_lt_2_31 : Real.log 10 < 2.31 := by
  have h := exp_2_31_gt
  rw [show (2.31 : ℝ) = Real.log (Real.exp 2.31) from (Real.log_exp 2.31).symm]
  exact Real.log_lt_log (by norm_num : (0 : ℝ) < 10) h

/-!
### Auxiliary bounds for H(0.11)

The algebraic identity for binary entropy at 0.11 is established below. The numerical bound
H_bits(0.11) < 1/2 has margin about `6·10⁻⁵` in natural-log units; it follows linearly from
`log 2 > 0.6931471803` and the series bounds on `log 1.25`, `log 1.1` and `log (100/89)` in
`QCryptLean.Math.Analysis.LogBounds`.
-/

/-- Binary entropy at 0.11 equals 2*log(10) - 0.11*log(11) - 0.89*log(89).

    H(0.11) = -0.11 * log(0.11) - 0.89 * log(0.89)
            = 0.11 * (2*log(10) - log(11)) + 0.89 * (2*log(10) - log(89))
            = 2*log(10) - 0.11*log(11) - 0.89*log(89) -/
private lemma binaryEntropy_011_eq : binaryEntropy (0.11 : ℝ) =
    2 * Real.log 10 - 0.11 * Real.log 11 - 0.89 * Real.log 89 := by
  unfold binaryEntropy entropyTerm
  have h1 : (0.11 : ℝ) ≠ 0 := by norm_num
  have h2 : (0.89 : ℝ) ≠ 0 := by norm_num
  have h3 : (1 : ℝ) - 0.11 = 0.89 := by norm_num
  simp only [h1, ↓reduceIte, h3, h2]
  have h_log_011 : Real.log (0.11 : ℝ) = Real.log 11 - 2 * Real.log 10 := by
    have : (0.11 : ℝ) = 11/100 := by norm_num
    rw [this, Real.log_div (by norm_num : (11:ℝ) ≠ 0) (by norm_num : (100:ℝ) ≠ 0)]
    have h100 : Real.log (100 : ℝ) = 2 * Real.log 10 := by
      have : (100 : ℝ) = 10^2 := by norm_num
      rw [this, Real.log_pow]; ring
    linarith
  have h_log_089 : Real.log (0.89 : ℝ) = Real.log 89 - 2 * Real.log 10 := by
    have : (0.89 : ℝ) = 89/100 := by norm_num
    rw [this, Real.log_div (by norm_num : (89:ℝ) ≠ 0) (by norm_num : (100:ℝ) ≠ 0)]
    have h100 : Real.log (100 : ℝ) = 2 * Real.log 10 := by
      have : (100 : ℝ) = 10^2 := by norm_num
      rw [this, Real.log_pow]; ring
    linarith
  rw [h_log_011, h_log_089]
  ring

/-- Binary entropy at 0.10 equals log(10) - 0.9 * log(9) in natural log units.

    H(0.1) = -0.1 * log(0.1) - 0.9 * log(0.9)
           = 0.1 * log(10) + 0.9 * (log(10) - log(9))
           = log(10) - 0.9 * log(9) -/
private lemma binaryEntropy_010_eq : binaryEntropy (0.10 : ℝ) =
    Real.log 10 - 0.9 * Real.log 9 := by
  unfold binaryEntropy entropyTerm
  have h1 : (0.10 : ℝ) ≠ 0 := by norm_num
  have h2 : (0.90 : ℝ) ≠ 0 := by norm_num
  have h3 : (1 : ℝ) - 0.10 = 0.90 := by norm_num
  simp only [h1, ↓reduceIte, h3, h2]
  have h_log_01 : Real.log (0.10 : ℝ) = -Real.log 10 := by
    have : (0.10 : ℝ) = 1/10 := by norm_num
    rw [this, Real.log_div one_ne_zero (by norm_num : (10:ℝ) ≠ 0), Real.log_one]
    ring
  have h_log_09 : Real.log (0.90 : ℝ) = Real.log 9 - Real.log 10 := by
    have : (0.90 : ℝ) = 9/10 := by norm_num
    rw [this, Real.log_div (by norm_num : (9:ℝ) ≠ 0) (by norm_num : (10:ℝ) ≠ 0)]
  rw [h_log_01, h_log_09]
  ring

/-- H_bits(0.10) < 1/2 (provable bound with margin ~0.03).

    **Numerical fact**: H_bits(0.10) ≈ 0.469 < 0.5

    **Proof strategy**: Use Taylor series bounds to establish:
    - log(9) > 2.19 (from exp(2.19) < 9)
    - log(10) < 2.31 (from exp(2.31) > 10)

    Then H(0.1) = log(10) - 0.9 * log(9) < 2.31 - 0.9 * 2.19 = 0.339 < log(2)/2 ≈ 0.347. -/
theorem binaryEntropyBits_010_lt_half : binaryEntropyBits 0.10 < 1/2 := by
  unfold binaryEntropyBits
  rw [binaryEntropy_010_eq]
  have h_log9 := log_9_gt_2_19
  have h_log10 := log_10_lt_2_31
  have h_log2 := Real.log_two_gt_d9
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1:ℝ) < 2)
  rw [div_lt_iff₀ hlog2_pos]
  -- Need: log(10) - 0.9*log(9) < (1/2) * log(2)
  have h_bound : Real.log 10 - 0.9 * Real.log 9 < 0.339 := by
    calc Real.log 10 - 0.9 * Real.log 9
        < 2.31 - 0.9 * Real.log 9 := by linarith
      _ < 2.31 - 0.9 * 2.19 := by nlinarith
      _ = 0.339 := by norm_num
  calc Real.log 10 - 0.9 * Real.log 9
      < 0.339 := h_bound
    _ < 0.3465 := by norm_num
    _ < 0.6931471803 / 2 := by norm_num
    _ < Real.log 2 / 2 := by linarith
    _ = (1 / 2) * Real.log 2 := by ring

/-- For e ≤ 0.10, we have H_bits(e) < 0.5.

    This is a weaker but provable version of binaryEntropyBits_lt_half_of_lt_011. -/
theorem binaryEntropyBits_lt_half_of_le_010 {e : ℝ} (he_nonneg : 0 ≤ e) (he_le : e ≤ 0.10) :
    binaryEntropyBits e < 1/2 := by
  by_cases he_zero : e = 0
  · rw [he_zero, binaryEntropyBits_zero]; norm_num
  · by_cases he_eq : e = 0.10
    · rw [he_eq]; exact binaryEntropyBits_010_lt_half
    · -- e ∈ (0, 0.10) ⊂ (0, 1/2), and H_bits is strictly increasing
      have he_lt : e < 0.10 := lt_of_le_of_ne he_le he_eq
      have he_pos : 0 < e := lt_of_le_of_ne he_nonneg (Ne.symm he_zero)
      have he_lt_half : e < 1/2 := by linarith
      have h010_lt_half : (0.10 : ℝ) < 1/2 := by norm_num
      have he_mem : e ∈ Set.Icc 0 (1/2) := ⟨he_nonneg, le_of_lt he_lt_half⟩
      have h010_mem : (0.10 : ℝ) ∈ Set.Icc 0 (1/2) := ⟨by norm_num, le_of_lt h010_lt_half⟩
      calc binaryEntropyBits e
          < binaryEntropyBits 0.10 := binaryEntropyBits_strictMonoOn he_mem h010_mem he_lt
        _ < 1/2 := binaryEntropyBits_010_lt_half

/-!
## BB84 Security Threshold Derivation

The BB84 security threshold is where H_bits(e) = 1/2, i.e., one can extract
1 - 2 * (1/2) = 0 bits of key per raw bit. We prove this occurs at e ≈ 0.11.
-/

/-- The BB84 threshold is the unique e ∈ (0, 1/2) where H_bits(e) = 1/2.

    Since H_bits is strictly increasing on [0, 1/2] with H_bits(0) = 0 and H_bits(1/2) = 1,
    there is a unique point where H_bits(e) = 1/2. -/
theorem exists_unique_threshold :
    ∃! e : ℝ, e ∈ Set.Ioo 0 (1/2) ∧ binaryEntropyBits e = 1/2 := by
  -- Step 1: Show continuity of binaryEntropyBits
  have entropyTerm_eq_negMulLog' : ∀ p, entropyTerm p = Real.negMulLog p := by
    intro p; unfold entropyTerm; simp only [Real.negMulLog]
    split_ifs with hp
    · simp [hp, Real.log_zero]
    · ring
  have binaryEntropy_eq : ∀ p, binaryEntropy p = Real.binEntropy p := by
    intro p; unfold binaryEntropy
    rw [entropyTerm_eq_negMulLog', entropyTerm_eq_negMulLog']
    exact (Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub p).symm
  have hcont : Continuous binaryEntropyBits := by
    unfold binaryEntropyBits
    have : (fun p => binaryEntropy p / Real.log 2) = (fun p => Real.binEntropy p / Real.log 2) := by
      ext p; rw [binaryEntropy_eq]
    rw [this]
    exact Real.binEntropy_continuous.div_const _
  -- Step 2: Use IVT on [0, 1/2]
  have hIVT := intermediate_value_Icc (le_of_lt (by norm_num : (0 : ℝ) < 1/2))
                 hcont.continuousOn
  rw [binaryEntropyBits_zero, binaryEntropyBits_half] at hIVT
  -- Since 1/2 ∈ [0, 1], there exists e ∈ [0, 1/2] with binaryEntropyBits e = 1/2
  have h_half_in : (1/2 : ℝ) ∈ Set.Icc 0 1 := by constructor <;> norm_num
  obtain ⟨e, he_mem, he_eq⟩ := hIVT h_half_in
  -- Step 3: Show e ∈ (0, 1/2) (open interval)
  have he_ne_zero : e ≠ 0 := by
    intro h; rw [h, binaryEntropyBits_zero] at he_eq; norm_num at he_eq
  have he_ne_half : e ≠ 1/2 := by
    intro h; rw [h, binaryEntropyBits_half] at he_eq; norm_num at he_eq
  have he_Ioo : e ∈ Set.Ioo 0 (1/2) := by
    constructor
    · exact lt_of_le_of_ne he_mem.1 he_ne_zero.symm
    · exact lt_of_le_of_ne he_mem.2 he_ne_half
  -- Step 4: Existence
  use e
  constructor
  · exact ⟨he_Ioo, he_eq⟩
  -- Step 5: Uniqueness from strict monotonicity
  · intro e' ⟨he'_Ioo, he'_eq⟩
    rcases lt_trichotomy e e' with h_lt | h_eq | h_gt
    · have := binaryEntropyBits_strictMonoOn
                 (Set.Ioo_subset_Icc_self he_Ioo)
                 (Set.Ioo_subset_Icc_self he'_Ioo)
                 h_lt
      rw [he_eq, he'_eq] at this
      exact absurd this (lt_irrefl _)
    · exact h_eq.symm
    · have := binaryEntropyBits_strictMonoOn
                 (Set.Ioo_subset_Icc_self he'_Ioo)
                 (Set.Ioo_subset_Icc_self he_Ioo)
                 h_gt
      rw [he_eq, he'_eq] at this
      exact absurd this (lt_irrefl _)

/-- The threshold value (defined as the unique solution to H_bits(e) = 1/2). -/
noncomputable def binaryEntropyBitsHalfRoot : ℝ :=
  Classical.choose exists_unique_threshold

/-- The threshold is in (0, 1/2). -/
theorem binaryEntropyBitsHalfRoot_mem_Ioo : binaryEntropyBitsHalfRoot ∈ Set.Ioo 0 (1/2) :=
  (Classical.choose_spec exists_unique_threshold).1.1

/-- At the threshold, H_bits = 1/2. -/
theorem binaryEntropyBitsHalfRoot_entropy : binaryEntropyBits binaryEntropyBitsHalfRoot = 1/2 :=
  (Classical.choose_spec exists_unique_threshold).1.2

/-- `H₂(0.11) < 1/2`: the binary entropy in bits at `0.11` is below one half
(numerically `H₂(0.11) ≈ 0.49992`, margin about `8·10⁻⁵`).

The proof writes every logarithm through `log 2` and logarithms of numbers close to one and
closes a single linear inequality against series bounds on those. -/
theorem binaryEntropyBits_011_lt_half : binaryEntropyBits 0.11 < 1/2 := by
  -- With `H(0.11) = 2·log 10 - 0.11·log 11 - 0.89·log 89`, rewrite every logarithm in terms of
  -- `log 2` and logarithms of numbers near one:
  -- `log 10 = 3·log 2 + log 1.25`, `log 11 = log 10 + log 1.1`, `log 89 = 2·log 10 - log (100/89)`.
  -- Then `H(0.11) = 0.33·log 2 + 0.11·log 1.25 - 0.11·log 1.1 + 0.89·log (100/89)`, and the claim
  -- `H(0.11) < log 2 / 2` is linear in these four logarithms, with margin about `5·10⁻⁵`.
  unfold binaryEntropyBits
  rw [binaryEntropy_011_eq, div_lt_iff₀ (Real.log_pos one_lt_two)]
  have h10 : Real.log 10 = 3 * Real.log 2 + Real.log 1.25 := by
    rw [show (10 : ℝ) = 2 ^ 3 * 1.25 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Nat.cast_ofNat]
  have h11 : Real.log 11 = Real.log 10 + Real.log 1.1 := by
    rw [show (11 : ℝ) = 10 * 1.1 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  have h89 : Real.log 89 = 2 * Real.log 10 - Real.log (100/89) := by
    rw [Real.log_div (by norm_num) (by norm_num), show (100 : ℝ) = 10 ^ 2 by norm_num,
      Real.log_pow, Nat.cast_ofNat]
    ring
  linarith only [h10, h11, h89, Real.log_two_gt_d9, Real.log_one_point_two_five_lt_d5,
    Real.log_one_point_one_gt_d4, Real.log_hundred_div_eighty_nine_lt_d5]

/-- Binary entropy at 0.112 in terms of log 10, log 1.12, log 8.88.

    Since 0.112 = 1.12/10 and 0.888 = 8.88/10:
    H(0.112) = log(10) - 0.112·log(1.12) - 0.888·log(8.88) -/
private lemma binaryEntropy_0112_eq : binaryEntropy (0.112 : ℝ) =
    Real.log 10 - 0.112 * Real.log 1.12 - 0.888 * Real.log 8.88 := by
  unfold binaryEntropy entropyTerm
  have h1 : (0.112 : ℝ) ≠ 0 := by norm_num
  have h2 : (0.888 : ℝ) ≠ 0 := by norm_num
  have h3 : (1 : ℝ) - 0.112 = 0.888 := by norm_num
  simp only [h1, ↓reduceIte, h3, h2]
  have h_log_0112 : Real.log (0.112 : ℝ) = Real.log 1.12 - Real.log 10 := by
    have : (0.112 : ℝ) = 1.12/10 := by norm_num
    rw [this, Real.log_div (by norm_num : (1.12:ℝ) ≠ 0) (by norm_num : (10:ℝ) ≠ 0)]
  have h_log_0888 : Real.log (0.888 : ℝ) = Real.log 8.88 - Real.log 10 := by
    have : (0.888 : ℝ) = 8.88/10 := by norm_num
    rw [this, Real.log_div (by norm_num : (8.88:ℝ) ≠ 0) (by norm_num : (10:ℝ) ≠ 0)]
  rw [h_log_0112, h_log_0888]
  ring

/-- H_bits(0.112) > 1/2 (0.112 is above the BB84 threshold).

    **Numerical fact**: H_bits(0.112) ≈ 0.5054... > 0.5
    Margin ~0.005, requiring moderate-precision bounds.

    **Strategy**: Show log(10) - 0.112·log(1.12) - 0.888·log(8.88) > log(2)/2,
    using log(10) > 2.3025, log(1.12) < 0.114, log(8.88) < 2.185.
    log(8.88) = 3·log(2) + log(1.11) since 8.88 = 8 × 1.11. -/
theorem binaryEntropyBits_0112_gt_half : binaryEntropyBits 0.112 > 1/2 := by
  -- With `H(0.112) = log 10 - 0.112·log 1.12 - 0.888·log 8.88` and `log 8.88 = 3·log 2 + log 1.11`,
  -- the claim `log 2 / 2 < H(0.112)` is linear in `log 2`, `log 10`, `log 1.12` and `log 1.11`,
  -- with margin about `3·10⁻³`.
  unfold binaryEntropyBits
  rw [binaryEntropy_0112_eq, gt_iff_lt, lt_div_iff₀ (Real.log_pos one_lt_two)]
  have h888 : Real.log 8.88 = 3 * Real.log 2 + Real.log 1.11 := by
    rw [show (8.88 : ℝ) = 2 ^ 3 * 1.11 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow, Nat.cast_ofNat]
  linarith only [h888, Real.log_two_lt_d9, Real.log_ten_gt_d5, Real.log_one_point_one_two_lt_d3,
    Real.log_one_point_one_one_lt_d3]

/-- The BB84 threshold is approximately 0.11: it lies in the interval (0.109, 0.112).

    Proved by combining the lower bound `binaryEntropyBits_011_lt_half`
    (H_bits(0.11) < 1/2) with the upper bound `binaryEntropyBits_0112_gt_half`
    (H_bits(0.112) > 1/2) and strict monotonicity. -/
theorem binaryEntropyBitsHalfRoot_approx : binaryEntropyBitsHalfRoot ∈ Set.Ioo 0.109 0.112 := by
  have ht_mem := binaryEntropyBitsHalfRoot_mem_Ioo
  have ht_ent := binaryEntropyBitsHalfRoot_entropy
  constructor
  · -- Lower bound: binaryEntropyBitsHalfRoot > 0.109
    suffices h : binaryEntropyBitsHalfRoot > 0.11 by linarith
    by_contra h
    push Not at h
    rcases eq_or_lt_of_le h with heq | hlt
    · rw [heq] at ht_ent
      exact absurd ht_ent (by linarith [binaryEntropyBits_011_lt_half])
    · have := binaryEntropyBits_strictMonoOn
                (Set.Ioo_subset_Icc_self ht_mem)
                (⟨by norm_num, by norm_num⟩ : (0.11 : ℝ) ∈ Set.Icc 0 (1/2))
                hlt
      linarith [binaryEntropyBits_011_lt_half]
  · -- Upper bound: binaryEntropyBitsHalfRoot < 0.112
    by_contra h
    push Not at h
    rcases eq_or_lt_of_le h with heq | hlt
    · rw [← heq] at ht_ent
      exact absurd ht_ent (by linarith [binaryEntropyBits_0112_gt_half])
    · have := binaryEntropyBits_strictMonoOn
                (⟨by norm_num, by norm_num⟩ : (0.112 : ℝ) ∈ Set.Icc 0 (1/2))
                (Set.Ioo_subset_Icc_self ht_mem)
                hlt
      linarith [binaryEntropyBits_0112_gt_half]

/-- For e < 0.11, we have H_bits(e) < 0.5.

    This is the key lemma for BB84 security: error rate below threshold
    implies entropy in bits is less than 1/2, so key rate is positive. -/
theorem binaryEntropyBits_lt_half_of_lt_011 {e : ℝ} (he_nonneg : 0 ≤ e) (he_lt : e < 0.11) :
    binaryEntropyBits e < 1/2 := by
  by_cases he_zero : e = 0
  · rw [he_zero, binaryEntropyBits_zero]; norm_num
  · -- e ∈ (0, 0.11) ⊂ (0, 1/2), and H_bits is strictly increasing
    -- H_bits(e) < H_bits(0.11) < 1/2
    have he_pos : 0 < e := lt_of_le_of_ne he_nonneg (Ne.symm he_zero)
    have he_lt_half : e < 1/2 := by linarith
    have h011_lt_half : (0.11 : ℝ) < 1/2 := by norm_num
    have he_mem : e ∈ Set.Icc 0 (1/2) := ⟨he_nonneg, le_of_lt he_lt_half⟩
    have h011_mem : (0.11 : ℝ) ∈ Set.Icc 0 (1/2) := ⟨by norm_num, le_of_lt h011_lt_half⟩
    calc binaryEntropyBits e
        < binaryEntropyBits 0.11 := binaryEntropyBits_strictMonoOn he_mem h011_mem he_lt
      _ < 1/2 := binaryEntropyBits_011_lt_half

/-- Binary entropy is monotone on [0, 1/2]. -/
theorem binaryEntropy_mono_on_half {x y : ℝ}
    (hx : 0 ≤ x) (hy : y ≤ 1 / 2) (hxy : x ≤ y) :
    binaryEntropy x ≤ binaryEntropy y := by
  by_cases hx_eq_y : x = y
  · rw [hx_eq_y]
  · have hxy_lt : x < y := lt_of_le_of_ne hxy hx_eq_y
    have hx_mem : x ∈ Set.Icc 0 (1 / 2) := ⟨hx, le_trans hxy hy⟩
    have hy_mem : y ∈ Set.Icc 0 (1 / 2) := ⟨le_trans hx hxy, hy⟩
    exact le_of_lt (binaryEntropy_strictMonoOn hx_mem hy_mem hxy_lt)

end Math.ClassicalEntropy
