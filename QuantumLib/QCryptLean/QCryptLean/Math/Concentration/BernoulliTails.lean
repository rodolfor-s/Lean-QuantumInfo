import QCryptLean.Math.Concentration.BernoulliKL

/-!
# Scalar Bernoulli tail bounds

Chernoff and Hoeffding expressions for one-sided and two-sided sampling deviations.
-/

noncomputable section

namespace Math.Concentration

/-- Bernoulli Chernoff tail for `n` samples, threshold `a` and mean `p`. -/
def bernoulliChernoffTail (n : ℕ) (a p : ℝ) : ℝ :=
  Real.exp (-(n : ℝ) * BernoulliKL.klBer a p)

/-- Sum of the Chernoff tails outside the interval `[Q - δ, Q + δ]`. -/
def bernoulliWindowTail (n : ℕ) (Q δ p : ℝ) : ℝ :=
  bernoulliChernoffTail n (Q + δ) p + bernoulliChernoffTail n (Q - δ) p

/-- Two-sided Hoeffding bound for a deviation of `δ` in `n` Bernoulli samples. -/
def hoeffdingTwoSidedTail (n : ℕ) (δ : ℝ) : ℝ :=
  2 * Real.exp (-2 * (n : ℝ) * δ ^ 2)

end Math.Concentration
