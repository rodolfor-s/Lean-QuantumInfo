import Mathlib.Analysis.Complex.ExponentialBounds
import QCryptLean.Math.Analysis.LogBounds
import QCryptLean.Math.Concentration.BernoulliKL
import QCryptLean.Math.Concentration.StirlingUpper

/-!
# A sharpened Stirling upper bound: antitonicity anchored at `n = 10`

`Math.Concentration.StirlingUpper.log_factorial_le` bounds `log n !` by anchoring the antitone
sequence `Stirling.stirlingSeq` at `n = 1`, where `stirlingSeq 1 = e/√2` and
`log (stirlingSeq 1) = 1 − (log 2)/2`.  Anchoring the *same* antitonicity
(`Stirling.stirlingSeq'_antitone`) at `n = 10` instead gives a strictly smaller additive
constant on every `n ≥ 10`:

* `Math.Concentration.LogFactorial.stirlingConst = 5807/10000`, a rational upper bound for
  `log (stirlingSeq 10) = −3 log 2 + 4 log 3 − (17/2) log 5 + log 7 + 10 = 0.58069550635806…`;
* `Math.Concentration.LogFactorial.stirlingUpper n = n log n − n + (log (2n))/2 +
Math.Concentration.LogFactorial.stirlingConst`;
* `Math.Concentration.LogFactorial.log_factorial_le_stirlingUpper : 10 ≤ n → log n ! ≤
Math.Concentration.LogFactorial.stirlingUpper n`.

`n = 10` is the largest anchor whose factorial is supported on the primes `{2,3,5,7}`
(`10! = 2^8·3^4·5^2·7`, while `11 ∣ 11!`), so the constant still decomposes over a four-prime
log basis.

**Per-slot gain.**  `Math.Concentration.LogFactorial.stirlingUpper` beats the `n = 1` anchor by
exactly `1 − (log 2)/2 − 5807/10000`
per Stirling slot, which `Math.Concentration.LogFactorial.stirlingConst_offset_mem_Ioo` pins between
`0.0727264` and `0.0727265`.

**Precision note (why this file does not reuse the project's existing prime-log bank).**  The
enclosures of `QKD.BB84.FiniteKey.LaggFiniteLow.log{3,5,7}_bound` are too wide on the
sides this constant needs: they give only `log (stirlingSeq 10) ≤ 0.5812575`, which does not reach
`5807/10000`.  The three private enclosures below are re-derived here at the required precision
(and this file, living under `Math/`, must not depend on `Protocols/` anyway).  Each uses only the
Padé `[2,1]` upper bound `Math.Concentration.BernoulliKL.log_one_add_le_mul_add_div` together with
Mathlib's `Real.log_two_{gt,lt}_d9`, on a power identity chosen so that the Padé argument is small:

| bound | identity | Padé argument |
|---|---|---|
| `log 3 < 1.09861233` | `3^12 = 2^19 · (531441/524288)` | `7153/524288 ≈ 0.01364` |
| `1.60943782 < log 5` | `2^7 = 5^3 · (128/125)`, then | |
| | `128/125 = (126/125)(127/126)(128/127)` | `1/125`, `1/126`, `1/127` |
| `log 7 < 1.94591071` | `7^5 = 2^14 · (16807/16384)` | `423/16384 ≈ 0.02582` |

The resulting bound on the constant is `0.5806970191`, i.e. `5807/10000` with `2.98·10⁻⁶` to
spare (reference value `0.58069550635806`).

## References

* Mathlib `Mathlib/Analysis/SpecialFunctions/Stirling.lean`: `Stirling.stirlingSeq`,
  `Stirling.stirlingSeq'_antitone`, `Stirling.log_stirlingSeq_formula`.
* Robbins, *A remark on Stirling's formula*, Amer. Math. Monthly 62 (1955) 26–29: the
  `1/(12n)` correction, of which `log (stirlingSeq 10) − (1/2) log π = 0.00833…` is the `n = 10`
  instance (a sanity check on the constant, not used in any proof below).
-/

namespace Math.Concentration.LogFactorial

open Real Nat

/-! ### The three prime-log enclosures at the precision this constant needs -/

/-- `1.60943782 < log 5` (true value `1.6094379124341…`).  From `2^7 = 5^3·(128/125)`,
`3 log 5 = 7 log 2 − log (128/125)`, with `0.6931471803 < log 2` (`Real.log_two_gt_d9`) and the
Padé `[2,1]` upper bound applied to the telescoping factorisation
`128/125 = (126/125)·(127/126)·(128/127)` (three arguments `≈ 0.0079`, which is `9×` more accurate
than a single Padé at `3/125`). -/
private lemma _root_.Real.log_five_gt_d8 : 1.60943782 < Real.log 5 := by
  have hpa := Math.Concentration.BernoulliKL.log_one_add_le_mul_add_div (1 / 125 : ℝ) (by norm_num)
  have hpb := Math.Concentration.BernoulliKL.log_one_add_le_mul_add_div (1 / 126 : ℝ) (by norm_num)
  have hpc := Math.Concentration.BernoulliKL.log_one_add_le_mul_add_div (1 / 127 : ℝ) (by norm_num)
  rw [show (1 : ℝ) + 1 / 125 = 126 / 125 by norm_num,
    show (1 : ℝ) / 125 * (1 / 125 + 2) / (2 * (1 / 125 + 1)) = 251 / 31500 by norm_num] at hpa
  rw [show (1 : ℝ) + 1 / 126 = 127 / 126 by norm_num,
    show (1 : ℝ) / 126 * (1 / 126 + 2) / (2 * (1 / 126 + 1)) = 253 / 32004 by norm_num] at hpb
  rw [show (1 : ℝ) + 1 / 127 = 128 / 127 by norm_num,
    show (1 : ℝ) / 127 * (1 / 127 + 2) / (2 * (1 / 127 + 1)) = 255 / 32512 by norm_num] at hpc
  have hsplit : Real.log (126 / 125 : ℝ) + Real.log (127 / 126 : ℝ) + Real.log (128 / 127 : ℝ)
      = Real.log (128 / 125 : ℝ) := by
    rw [← Real.log_mul (by norm_num) (by norm_num), ← Real.log_mul (by norm_num) (by norm_num),
      show (126 : ℝ) / 125 * (127 / 126) * (128 / 127) = 128 / 125 by norm_num]
  have hid : 3 * Real.log 5 = 7 * Real.log 2 - Real.log (128 / 125 : ℝ) := by
    have h1 : Real.log ((2 : ℝ) ^ (7 : ℕ)) = 7 * Real.log 2 := by
      rw [Real.log_pow]; push_cast; ring
    rw [show ((2 : ℝ) ^ (7 : ℕ)) = 5 ^ (3 : ℕ) * (128 / 125) by norm_num,
      Real.log_mul (by positivity) (by norm_num), Real.log_pow] at h1
    push_cast at h1 ⊢
    linarith [h1]
  have h2 := Real.log_two_gt_d9
  linarith [hpa, hpb, hpc, hsplit, hid, h2]

/-- `log 7 < 1.94591071` (true value `1.9459101090932…`).  From `7^5 = 2^14·(16807/16384)`,
`5 log 7 = 14 log 2 + log (16807/16384)`, with `log 2 < 0.6931471808` (`Real.log_two_lt_d9`) and
the Padé `[2,1]` upper bound at `t = 423/16384`. -/
private lemma _root_.Real.log_seven_lt_d8 : Real.log 7 < 1.94591071 := by
  have hp := Math.Concentration.BernoulliKL.log_one_add_le_mul_add_div (423 / 16384 : ℝ) (by
    norm_num)
  rw [show (1 : ℝ) + 423 / 16384 = 16807 / 16384 by norm_num,
    show (423 : ℝ) / 16384 * (423 / 16384 + 2) / (2 * (423 / 16384 + 1))
      = 14039793 / 550731776 by norm_num] at hp
  have hid : 5 * Real.log 7 = 14 * Real.log 2 + Real.log (16807 / 16384 : ℝ) := by
    have h1 : Real.log ((7 : ℝ) ^ (5 : ℕ)) = 5 * Real.log 7 := by
      rw [Real.log_pow]; push_cast; ring
    rw [show ((7 : ℝ) ^ (5 : ℕ)) = 2 ^ (14 : ℕ) * (16807 / 16384) by norm_num,
      Real.log_mul (by positivity) (by norm_num), Real.log_pow] at h1
    push_cast at h1 ⊢
    linarith [h1]
  have h2 := Real.log_two_lt_d9
  linarith [hp, hid, h2]

/-! ### The constant and the sharpened bound -/

/-- **The `n = 10` Stirling anchor constant (rational upper bound).**
`log (Stirling.stirlingSeq 10) = log 10! − (1/2) log 20 − 10 log 10 + 10
= −3 log 2 + 4 log 3 − (17/2) log 5 + log 7 + 10 = 0.58069550635806…`, and
`Math.Concentration.LogFactorial.stirlingConst = 5807/10000` is a rational upper bound for it
(`Math.Concentration.LogFactorial.log_stirlingSeq_ten_le`).  Compare the `n = 1` anchor of
`Math.Concentration.StirlingUpper.log_factorial_le`, whose constant is `1`. -/
noncomputable def stirlingConst : ℝ := 5807 / 10000

/-- **The sharpened Stirling upper envelope**, `Math.Concentration.LogFactorial.stirlingUpper n = n
log n − n + (log (2n))/2 +
Math.Concentration.LogFactorial.stirlingConst`.  The `n = 1`-anchored envelope of
`Math.Concentration.StirlingUpper.log_factorial_le` is `n log n − n + (log n)/2 + 1`; the two
differ by the constant `1 − (log 2)/2 − Math.Concentration.LogFactorial.stirlingConst`
(`Math.Concentration.LogFactorial.sub_stirlingUpper_eq`). -/
noncomputable def stirlingUpper (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log n - n + Real.log (2 * n) / 2 + Math.Concentration.LogFactorial.stirlingConst

/-- **The anchor bound** `log (stirlingSeq 10) ≤ 5807/10000`.  `10! = 2^8·3^4·5^2·7`,
`20 = 2^2·5`, `10 = 2·5`, so
`log (stirlingSeq 10) = −3 log 2 + 4 log 3 − (17/2) log 5 + log 7 + 10`, and the four enclosures
above give `≤ 0.5806970191`. -/
theorem log_stirlingSeq_ten_le : Real.log (Stirling.stirlingSeq 10) ≤
    Math.Concentration.LogFactorial.stirlingConst := by
  have hfact : ((10 : ℕ)! : ℝ) = 3628800 := by norm_num [Nat.factorial]
  have hcast : ((10 : ℕ) : ℝ) = 10 := by norm_num
  have hform := Stirling.log_stirlingSeq_formula 10
  rw [hfact, hcast, show (2 : ℝ) * 10 = 20 by norm_num] at hform
  have hdiv : Real.log ((10 : ℝ) / Real.exp 1) = Real.log 10 - 1 := by
    rw [Real.log_div (by norm_num) (Real.exp_ne_zero 1), Real.log_exp]
  have h3628800 : Real.log (3628800 : ℝ)
      = 8 * Real.log 2 + 4 * Real.log 3 + 2 * Real.log 5 + Real.log 7 := by
    rw [show (3628800 : ℝ) = 2 ^ (8 : ℕ) * (3 ^ (4 : ℕ) * (5 ^ (2 : ℕ) * 7)) by norm_num,
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by norm_num),
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast; ring
  have h20 : Real.log (20 : ℝ) = 2 * Real.log 2 + Real.log 5 := by
    rw [show (20 : ℝ) = 2 ^ (2 : ℕ) * 5 by norm_num,
      Real.log_mul (by positivity) (by norm_num), Real.log_pow]
    push_cast; ring
  have h10 : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  rw [hdiv, h3628800, h20, h10] at hform
  have hb2 := Real.log_two_gt_d9
  have hb3 := Real.log_three_lt_d8
  have hb5 := Real.log_five_gt_d8
  have hb7 := Real.log_seven_lt_d8
  rw [Math.Concentration.LogFactorial.stirlingConst]
  norm_num at hform ⊢
  linarith [hform, hb2, hb3, hb5, hb7]

/-- **Sharpened logarithmic Stirling upper bound.**  For `10 ≤ n`,
`log n ! ≤ n log n − n + (log (2n))/2 + 5807/10000`.

Proof: `Stirling.stirlingSeq` is antitone from `n = 1` on
(`Stirling.stirlingSeq'_antitone`), so `stirlingSeq n ≤ stirlingSeq 10` for `n ≥ 10`; take
`Real.log` and use `Stirling.log_stirlingSeq_formula` on both sides, then
`Math.Concentration.LogFactorial.log_stirlingSeq_ten_le`.
This is `Math.Concentration.StirlingUpper.log_factorial_le` with the antitonicity anchored at
`10` instead of `1`. -/
theorem log_factorial_le_stirlingUpper (n : ℕ) (hn : 10 ≤ n) : Real.log (n !) ≤
    Math.Concentration.LogFactorial.stirlingUpper n := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hfacpos : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hdenpos : (0 : ℝ) < Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n := by
    have h1 : (0 : ℝ) < Real.sqrt (2 * (n : ℝ)) := Real.sqrt_pos.mpr (by linarith)
    have h2 : (0 : ℝ) < ((n : ℝ) / Real.exp 1) ^ n := by positivity
    exact mul_pos h1 h2
  have hpos : 0 < Stirling.stirlingSeq n := by
    rw [Stirling.stirlingSeq]; exact div_pos hfacpos hdenpos
  -- antitonicity of `stirlingSeq ∘ succ`, anchored at `9 ↦ stirlingSeq 10`
  have hle : Stirling.stirlingSeq n ≤ Stirling.stirlingSeq 10 := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hk : 9 ≤ k := by omega
    have hanti := Stirling.stirlingSeq'_antitone hk
    simpa using hanti
  have hlog := Real.log_le_log hpos hle
  rw [Stirling.log_stirlingSeq_formula n] at hlog
  have hten := Math.Concentration.LogFactorial.log_stirlingSeq_ten_le
  have hdiv : Real.log ((n : ℝ) / Real.exp 1) = Real.log n - 1 := by
    rw [Real.log_div (ne_of_gt hnR) (Real.exp_ne_zero 1), Real.log_exp]
  rw [hdiv] at hlog
  rw [Math.Concentration.LogFactorial.stirlingUpper]
  linarith [hlog, hten]

/-- **The per-slot gain over the `n = 1` anchor.**  The library envelope
`Math.Concentration.StirlingUpper.log_factorial_le` has the shape
`n log n − n + (log n)/2 + 1`; since `log (2n) = log 2 + log n` for `n ≠ 0`, the two envelopes
differ by the constant `1 − (log 2)/2 − Math.Concentration.LogFactorial.stirlingConst`,
independently of `n`. -/
theorem sub_stirlingUpper_eq (n : ℕ) (hn : n ≠ 0) :
    ((n : ℝ) * Real.log n - n + Real.log n / 2 + 1) - Math.Concentration.LogFactorial.stirlingUpper
      n
      = 1 - Real.log 2 / 2 - Math.Concentration.LogFactorial.stirlingConst := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have h2n : Real.log (2 * (n : ℝ)) = Real.log 2 + Real.log n :=
    Real.log_mul (by norm_num) (ne_of_gt hnR)
  rw [Math.Concentration.LogFactorial.stirlingUpper, h2n]; ring

/-- **The gain, numerically.**  `0.0727264 < 1 − (log 2)/2 − 5807/10000 < 0.0727265`
(`log 2 ∈ (0.6931471803, 0.6931471808)` by `Real.log_two_{gt,lt}_d9`); the exact value is
`0.072726409723…`.  Each Stirling slot switched from `log_factorial_le` to
`Math.Concentration.LogFactorial.log_factorial_le_stirlingUpper` buys this many nats. -/
theorem stirlingConst_offset_mem_Ioo :
    0.0727264 < 1 - Real.log 2 / 2 - Math.Concentration.LogFactorial.stirlingConst
      ∧ 1 - Real.log 2 / 2 - Math.Concentration.LogFactorial.stirlingConst < 0.0727265 := by
  have hlo := Real.log_two_gt_d9
  have hhi := Real.log_two_lt_d9
  rw [Math.Concentration.LogFactorial.stirlingConst]
  constructor <;> [linarith; linarith]

end Math.Concentration.LogFactorial
