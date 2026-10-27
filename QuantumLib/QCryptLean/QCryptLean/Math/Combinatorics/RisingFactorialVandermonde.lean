import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Chu–Vandermonde convolution for rising factorials

The rising-factorial (ascending-factorial / Pochhammer) analogue of the Chu–Vandermonde identity
```
∑_{k ≤ m} C(m,k) · x^{(k)} · y^{(m−k)} = (x+y)^{(m)}
```
where `x^{(k)} = x(x+1)⋯(x+k−1) = Nat.ascFactorial x k`.  This is not packaged in Mathlib (Mathlib
carries the ordinary binomial Vandermonde `Nat.add_choose_le`/`Nat.choose_add_eq` but not the rising
one), so it is proved here from the elementary `Nat.ascFactorial` recurrences by induction on `m`.

## Main statement

- `Nat.ascFactorial_add_eq_sum_choose_mul` : the ℕ identity above.
- `Nat.ascFactorial_add_eq_sum_choose_mul_cast` : the same identity cast to any commutative
  semiring (the form consumed by the real-valued beta-binomial `betaBinomialPmf` normalisation).

## Downstream client

The KEY-phase Dirichlet–Multinomial marginal `betaBinomialPmf` is a
probability mass function: with `x = S+2`, `y = P−S+2`, `m = n_K`, the numerators sum to the
normalising denominator `(P+4)^{(n_K)}`.
-/

open scoped BigOperators

namespace Nat

/-- **Rising-factorial Chu–Vandermonde identity.**  The ascending-factorial convolution
`∑_{k ≤ m} C(m,k)·x^{(k)}·y^{(m−k)}` telescopes to `(x+y)^{(m)}`, where `n^{(j)} = n.ascFactorial j`
is the rising factorial `n(n+1)⋯(n+j−1)`.

Proved by induction on `m` from the two one-step recurrences `Nat.ascFactorial_succ`
(`n^{(j+1)} = (n+j)·n^{(j)}`) and Pascal's rule `Nat.choose_succ_succ`; the inductive step splits
the `(m+1)`-sum into the two convolution halves `A` (peeling a `y`-factor) and `B` (peeling an
`x`-factor) whose common `C(m,k)·x^{(k)}·y^{(m−k)}` core carries the linear factor
`(y+(m−k)) + (x+k) = x+y+m`. -/
theorem ascFactorial_add_eq_sum_choose_mul (x y m : ℕ) :
    (x + y).ascFactorial m
      = ∑ k ∈ Finset.range (m + 1), m.choose k * x.ascFactorial k * y.ascFactorial (m - k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    -- `A` (the `y`-peel half) and `B` (the `x`-peel half).
    set B : ℕ := ∑ k ∈ Finset.range (m + 1),
        m.choose k * x.ascFactorial (k + 1) * y.ascFactorial (m - k) with hB
    set A : ℕ := ∑ k ∈ Finset.range (m + 1),
        m.choose k * x.ascFactorial k * y.ascFactorial (m + 1 - k) with hA
    -- `A` reassembled: the leading `k = 0` term of `A` is `y^{(m+1)}`, the rest shifts.
    have hAeq : A = (∑ k ∈ Finset.range m,
          m.choose (k + 1) * x.ascFactorial (k + 1) * y.ascFactorial (m - k))
        + y.ascFactorial (m + 1) := by
      rw [hA, Finset.sum_range_succ'
        (fun k => m.choose k * x.ascFactorial k * y.ascFactorial (m + 1 - k)) m]
      congr 1
      · exact Finset.sum_congr rfl (fun k _ => by rw [Nat.succ_sub_succ])
      · simp
    -- (1) The `(m+1)`-sum splits into `A + B` via Pascal's rule.
    have hsplit : (∑ k ∈ Finset.range (m + 1 + 1),
          (m + 1).choose k * x.ascFactorial k * y.ascFactorial (m + 1 - k)) = A + B := by
      rw [Finset.sum_range_succ'
        (fun k => (m + 1).choose k * x.ascFactorial k * y.ascFactorial (m + 1 - k)) (m + 1)]
      -- peel index 0 (`= y^{(m+1)}`)
      have hpeel : (m + 1).choose 0 * x.ascFactorial 0 * y.ascFactorial (m + 1 - 0)
          = y.ascFactorial (m + 1) := by simp
      rw [hpeel]
      -- Pascal-expand the shifted `C(m+1,k+1)` sum into `B` + the leftover `C(m,k+1)` sum
      have hpascal : (∑ k ∈ Finset.range (m + 1),
            (m + 1).choose (k + 1) * x.ascFactorial (k + 1) * y.ascFactorial (m + 1 - (k + 1)))
          = B + (∑ k ∈ Finset.range m,
              m.choose (k + 1) * x.ascFactorial (k + 1) * y.ascFactorial (m - k)) := by
        have step1 : (∑ k ∈ Finset.range (m + 1),
              (m + 1).choose (k + 1) * x.ascFactorial (k + 1) * y.ascFactorial (m + 1 - (k + 1)))
            = ∑ k ∈ Finset.range (m + 1),
              (m.choose k * x.ascFactorial (k + 1) * y.ascFactorial (m - k)
                + m.choose (k + 1) * x.ascFactorial (k + 1) * y.ascFactorial (m - k)) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Nat.succ_sub_succ, Nat.choose_succ_succ, Nat.add_mul, Nat.add_mul]
        rw [step1, Finset.sum_add_distrib, ← hB]
        congr 1
        rw [Finset.sum_range_succ]
        simp [Nat.choose_succ_self]
      rw [hpascal, hAeq]
      ring
    -- (2) `A + B = (x+y+m) · Sₘ`, and `Sₘ = (x+y)^{(m)}` by the induction hypothesis.
    have hcombine : A + B = (x + y + m) *
        ∑ k ∈ Finset.range (m + 1), m.choose k * x.ascFactorial k * y.ascFactorial (m - k) := by
      rw [hA, hB, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      -- peel a `y`-factor on the `A` term and an `x`-factor on the `B` term
      have hy : y.ascFactorial (m + 1 - k) = (y + (m - k)) * y.ascFactorial (m - k) := by
        rw [show m + 1 - k = (m - k) + 1 from by omega, Nat.ascFactorial_succ]
      have hx : x.ascFactorial (k + 1) = (x + k) * x.ascFactorial k := by
        rw [Nat.ascFactorial_succ]
      rw [hy, hx]
      have hlin : y + (m - k) + (x + k) = x + y + m := by omega
      calc m.choose k * x.ascFactorial k * ((y + (m - k)) * y.ascFactorial (m - k))
            + m.choose k * ((x + k) * x.ascFactorial k) * y.ascFactorial (m - k)
          = (m.choose k * x.ascFactorial k * y.ascFactorial (m - k))
              * (y + (m - k) + (x + k)) := by ring
        _ = (x + y + m) * (m.choose k * x.ascFactorial k * y.ascFactorial (m - k)) := by
              rw [hlin]; ring
    rw [Nat.ascFactorial_succ, ih, ← hcombine]
    exact hsplit.symm

/-- Rising-factorial Chu–Vandermonde over an arbitrary commutative semiring (the real-valued form
used to normalise the beta-binomial `betaBinomialPmf`).  Cast of
`ascFactorial_add_eq_sum_choose_mul`. -/
theorem ascFactorial_add_eq_sum_choose_mul_cast {R : Type*} [CommSemiring R] (x y m : ℕ) :
    ((x + y).ascFactorial m : R)
      = ∑ k ∈ Finset.range (m + 1),
          (m.choose k : R) * (x.ascFactorial k : R) * (y.ascFactorial (m - k) : R) := by
  have h := ascFactorial_add_eq_sum_choose_mul x y m
  have := congrArg (Nat.cast : ℕ → R) h
  push_cast at this
  simpa using this

end Nat

-- Numerical probe (non-vacuity / orientation): the L-AGG `betaBinomialPmf` normalisation
-- `x = S+2 = 4`, `y = P−S+2 = 5`, `m = n_K = 4`  ⇒  denominator `(P+4)^{(n_K)} = 9^{(4)} = 11880`

example :
    (∑ k ∈ Finset.range 5, (4).choose k * (4).ascFactorial k * (5).ascFactorial (4 - k))
      = (9).ascFactorial 4 :=
  (Nat.ascFactorial_add_eq_sum_choose_mul 4 5 4).symm

example : (9).ascFactorial 4 = 11880 := by decide

/-! ## Rising-factorial monotonicity and log-supermodularity helpers

The log-supermodular cross inequality for `Nat.ascFactorial`, using base monotonicity
`Nat.ascFactorial_le`. This supplies the rising-factorial bound for the beta-binomial
likelihood ratio `Math.Probability.betaBinomialPmf_mlr`. -/

namespace Math.Combinatorics

/-- The rising-factorial cross inequality: for `j ≤ k`,
`(a+1)^{(j)}·a^{(k)} ≤ (a+1)^{(k)}·a^{(j)}` — the log-supermodularity of `x^{(v)}` in `(x, v)`. -/
lemma ascFactorial_cross (a j k : ℕ) (hjk : j ≤ k) :
    (a + 1).ascFactorial j * a.ascFactorial k ≤ (a + 1).ascFactorial k * a.ascFactorial j := by
  obtain ⟨t, rfl⟩ := Nat.le.dest hjk
  rw [← Nat.ascFactorial_mul_ascFactorial a j t, ← Nat.ascFactorial_mul_ascFactorial (a + 1) j t]
  have hbase : (a + j).ascFactorial t ≤ (a + 1 + j).ascFactorial t :=
    Nat.ascFactorial_le t (by omega)
  calc (a + 1).ascFactorial j * (a.ascFactorial j * (a + j).ascFactorial t)
      = ((a + 1).ascFactorial j * a.ascFactorial j) * (a + j).ascFactorial t := by ring
    _ ≤ ((a + 1).ascFactorial j * a.ascFactorial j) * (a + 1 + j).ascFactorial t :=
        Nat.mul_le_mul (le_refl _) hbase
    _ = ((a + 1).ascFactorial j * (a + 1 + j).ascFactorial t) * a.ascFactorial j := by ring

end Math.Combinatorics
