import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Stirling upper bounds

Mathlib provides the Stirling *lower* bounds (`Stirling.le_factorial_stirling`,
`Stirling.le_log_factorial_stirling`) but not the matching upper bounds.  This file supplies:

* `factorial_le_stirling_upper` : `n ! ≤ e · √n · (n / e) ^ n`;
* `log_factorial_le`           : the logarithmic form of the above;
* `le_log_factorial`           : a thin wrapper around Mathlib's logarithmic lower bound,
  packaged with the `log (2 π n)` term for a uniform interface;
* `ascFactorial_cast_eq`       : the ascending-factorial ↔ factorial identity, cast to `ℝ`.

The upper bound is obtained from the fact that Mathlib's `Stirling.stirlingSeq` is antitone from
`n = 1` on, so `stirlingSeq n ≤ stirlingSeq 1 = e / √2` for all `n ≥ 1`.
-/

namespace Math.Concentration.StirlingUpper

open Real Nat

/-- **Ascending-factorial ↔ factorial identity (cast to `ℝ`).**
With the convention `Nat.ascFactorial a k = a·(a+1)·…·(a+k−1)`,
`a.ascFactorial k = (a + k − 1)! / (a − 1)!` for `a ≥ 1`. -/
theorem ascFactorial_cast_eq (a k : ℕ) (ha : 1 ≤ a) :
    ((a.ascFactorial k : ℕ) : ℝ) = ((a + k - 1)! : ℝ) / ((a - 1)! : ℝ) := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  have hkey : (a' ! : ℕ) * (a' + 1).ascFactorial k = (a' + k)! :=
    Nat.factorial_mul_ascFactorial a' k
  have hsub1 : a' + 1 + k - 1 = a' + k := by omega
  have hsub2 : a' + 1 - 1 = a' := by omega
  rw [hsub1, hsub2]
  rw [eq_div_iff (by positivity)]
  have := congrArg (fun m : ℕ => (m : ℝ)) hkey
  push_cast at this ⊢
  linarith [this]

/-- **Logarithmic Stirling lower bound.**  For `n ≠ 0`,
`n·log n − n + log(2 π n)/2 ≤ log n !`.  Thin wrapper around
`Stirling.le_log_factorial_stirling`, repackaged with the combined `log (2 π n)` term. -/
theorem le_log_factorial (n : ℕ) (hn : n ≠ 0) :
    n * Real.log n - n + Real.log (2 * Real.pi * n) / 2 ≤ Real.log (n !) := by
  have hn' : (0 : ℝ) < n := by positivity
  have hsplit : Real.log (2 * Real.pi * n) = Real.log (2 * Real.pi) + Real.log n := by
    rw [Real.log_mul (by positivity) (by positivity)]
  have hmathlib := Stirling.le_log_factorial_stirling hn
  rw [hsplit]
  linarith [hmathlib]

/-- **Stirling upper bound on the factorial.**  For `n ≠ 0`,
`n ! ≤ e · √n · (n / e) ^ n`.  Obtained from the antitonicity of `Stirling.stirlingSeq`
(from `n = 1` on): `stirlingSeq n ≤ stirlingSeq 1 = e / √2`. -/
theorem factorial_le_stirling_upper (n : ℕ) (hn : n ≠ 0) :
    (n ! : ℝ) ≤ Real.exp 1 * Real.sqrt n * (n / Real.exp 1) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- Antitonicity gives `stirlingSeq (m+1) ≤ stirlingSeq 1 = e / √2`.
  have hanti := Stirling.stirlingSeq'_antitone (Nat.zero_le m)
  simp only [Function.comp_apply] at hanti
  rw [Stirling.stirlingSeq_one] at hanti
  -- Denominator is positive.
  have hden_pos : 0 < Real.sqrt (2 * (m + 1 : ℕ)) * ((m + 1 : ℕ) / Real.exp 1) ^ (m + 1) := by
    have : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    positivity
  -- Unfold the definition of stirlingSeq at `m+1`.
  rw [Stirling.stirlingSeq] at hanti
  rw [div_le_iff₀ hden_pos] at hanti
  -- `hanti : (m+1)! ≤ (e/√2) · (√(2(m+1)) · ((m+1)/e)^(m+1))`.
  -- Now show the RHS equals `e · √(m+1) · ((m+1)/e)^(m+1)`.
  have hsqrt : Real.exp 1 / Real.sqrt 2 * Real.sqrt (2 * (m + 1 : ℕ))
      = Real.exp 1 * Real.sqrt (m + 1 : ℕ) := by
    rw [Real.sqrt_mul (by norm_num) (m + 1 : ℕ)]
    field_simp
  calc ((m + 1)! : ℝ)
      ≤ Real.exp 1 / Real.sqrt 2
          * (Real.sqrt (2 * (m + 1 : ℕ)) * ((m + 1 : ℕ) / Real.exp 1) ^ (m + 1)) := hanti
    _ = (Real.exp 1 / Real.sqrt 2 * Real.sqrt (2 * (m + 1 : ℕ)))
          * ((m + 1 : ℕ) / Real.exp 1) ^ (m + 1) := by ring
    _ = Real.exp 1 * Real.sqrt (m + 1 : ℕ) * ((m + 1 : ℕ) / Real.exp 1) ^ (m + 1) := by
          rw [hsqrt]

/-- **Logarithmic Stirling upper bound.**  For `n ≠ 0`,
`log n ! ≤ n·log n − n + log n / 2 + 1`.  Logarithm of `factorial_le_stirling_upper`. -/
theorem log_factorial_le (n : ℕ) (hn : n ≠ 0) :
    Real.log (n !) ≤ n * Real.log n - n + Real.log n / 2 + 1 := by
  have hn' : (0 : ℝ) < n := by positivity
  have hupper := factorial_le_stirling_upper n hn
  have hfac_pos : (0 : ℝ) < (n ! : ℝ) := by positivity
  have hrhs_pos : (0 : ℝ) < Real.exp 1 * Real.sqrt n * (n / Real.exp 1) ^ n := by positivity
  have hlog_le := Real.log_le_log hfac_pos hupper
  -- Expand `log (e · √n · (n/e)^n)`.
  have hexp_ne : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
  have hexpand : Real.log (Real.exp 1 * Real.sqrt n * (n / Real.exp 1) ^ n)
      = 1 + Real.log n / 2 + n * (Real.log n - 1) := by
    rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (Real.exp_pos 1).ne' (by positivity),
        Real.log_exp, Real.log_sqrt hn'.le, Real.log_pow,
        Real.log_div (by positivity) hexp_ne, Real.log_exp]
  rw [hexpand] at hlog_le
  linarith [hlog_le]

end Math.Concentration.StirlingUpper
