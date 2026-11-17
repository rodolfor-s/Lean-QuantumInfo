import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Discretely log-convex sequences and geometric lower bounds

A sequence `φ : ℕ → ℝ` is *discretely log-convex* when `φ k ^ 2 ≤ φ (k - 1) * φ (k + 1)`
for every `k ≥ 1`, i.e. when the consecutive ratios `φ (k + 1) / φ k` are non-decreasing.
Such a sequence normalised by `φ 0 = 1` is bounded below by the geometric sequence built
from any lower bound `λ ≤ φ 1`.

This is the discrete form of the statement that a log-convex function through `(0, 1)`
dominates the exponential through `(1, φ 1)`, and it is the shape in which the estimate
appears in matrix-analysis arguments: a sequence of the form `φ k = ‖A ^ k B ^ k‖` or
`φ k = Tr (A ^ k B ^ k)` is log-convex in `k`, so a bound at `k = 1` propagates to every
`k` (Bhatia, *Matrix Analysis*, IX.2 uses this step for the Araki–Lieb–Thirring family).

Only real analysis appears here; no matrix statement is assumed or proved.

## Main statements

- `Math.LogConvexSequence.pos_and_mul_le_succ` : positivity and the one-step ratio bound
  `λ * φ k ≤ φ (k + 1)`.
- `Math.LogConvexSequence.geom_lower_bound` : `λ ^ n ≤ φ n`.
-/

noncomputable section

namespace Math.LogConvexSequence

/-- **One-step ratio bound for a discretely log-convex sequence.** If `φ 0 = 1`,
`0 < λ ≤ φ 1` and `φ k ^ 2 ≤ φ (k - 1) * φ (k + 1)` for `k ≥ 1`, then every term is
positive and `λ * φ k ≤ φ (k + 1)`.

Induction on `k`: the base case is the hypothesis `λ ≤ φ 1`, and the step divides the
log-convexity inequality at `k + 1` by the (positive) term `φ k`. -/
theorem pos_and_mul_le_succ (φ : ℕ → ℝ) (lam : ℝ) (hlam : 0 < lam) (hφ₀ : φ 0 = 1)
    (hφ₁ : lam ≤ φ 1) (hconv : ∀ k, 0 < k → (φ k) ^ 2 ≤ φ (k - 1) * φ (k + 1)) (k : ℕ) :
    0 < φ k ∧ lam * φ k ≤ φ (k + 1) := by
  induction k with
  | zero => exact ⟨by rw [hφ₀]; exact one_pos, by rwa [hφ₀, mul_one]⟩
  | succ k ih =>
    have hpos : 0 < φ k := ih.1
    have hpos' : 0 < φ (k + 1) := lt_of_lt_of_le (mul_pos hlam ih.1) ih.2
    refine ⟨hpos', ?_⟩
    have hlc := hconv (k + 1) (Nat.succ_pos k)
    simp only [Nat.add_sub_cancel] at hlc
    rw [sq] at hlc
    have hstep : lam * φ (k + 1) * φ k ≤ φ k * φ (k + 1 + 1) :=
      calc lam * φ (k + 1) * φ k
          = (lam * φ k) * φ (k + 1) := by ring
        _ ≤ φ (k + 1) * φ (k + 1) := mul_le_mul_of_nonneg_right ih.2 hpos'.le
        _ ≤ φ k * φ (k + 1 + 1) := hlc
    exact le_of_mul_le_mul_left (by linarith) hpos

/-- **Geometric lower bound for a discretely log-convex sequence.** With `φ 0 = 1` and
`0 < λ ≤ φ 1`, discrete log-convexity gives `λ ^ n ≤ φ n` for every `n`. -/
theorem geom_lower_bound (φ : ℕ → ℝ) (lam : ℝ) (hlam : 0 < lam) (hφ₀ : φ 0 = 1)
    (hφ₁ : lam ≤ φ 1) (hconv : ∀ k, 0 < k → (φ k) ^ 2 ≤ φ (k - 1) * φ (k + 1)) (n : ℕ) :
    lam ^ n ≤ φ n := by
  have h := pos_and_mul_le_succ φ lam hlam hφ₀ hφ₁ hconv
  induction n with
  | zero => simp [hφ₀]
  | succ n ih =>
    calc lam ^ (n + 1) = lam ^ n * lam := pow_succ lam n
      _ ≤ φ n * lam := mul_le_mul_of_nonneg_right ih hlam.le
      _ = lam * φ n := by ring
      _ ≤ φ (n + 1) := (h n).2

end Math.LogConvexSequence

end
