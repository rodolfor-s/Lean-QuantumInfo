import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import QCryptLean.Math.Combinatorics.RisingFactorialVandermonde

/-!
# The beta-binomial / Dirichlet–Multinomial phase-count pmf `betaBinomialPmf`

General (protocol-free) probability of the rising-factorial beta-binomial law
```
betaBinomialPmf m P S v  =  C(m,v) · (S+2)^{(v)} · (P−S+2)^{(m−v)} / (P+4)^{(m)}
```
the `BetaBin(m; S+2, P−S+2)` pmf on `v ∈ {0,…,m}`, where `x^{(k)} = Nat.ascFactorial x k` is the
rising factorial.  This is the phase-count marginal of the de Finetti (Dirichlet–Multinomial) law;
the
file collects the elementary pmf facts and the likelihood-ratio (MLR / single-crossing /
MGF-monotone)
family, all pure real/combinatorial analysis with no dependence on any protocol object.

## Main statements

- `betaBinomialPmf` — the pmf (explicit; no `Classical.choose`).
- `betaBinomialPmf_denom_pos`, `betaBinomialPmf_nonneg`, `betaBinomialPmf_pos` — positivity of the
denominator, nonnegativity,
  and strict positivity on the support `v ≤ m`.
- `betaBinomialPmf_sum_eq_one` — `∑_{v≤m} betaBinomialPmf = 1` (via the rising-factorial
Chu–Vandermonde identity
  `Nat.ascFactorial_add_eq_sum_choose_mul_cast`).
- `betaBinomialPmf_mlr` — the monotone-likelihood-ratio / log-supermodularity cross inequality in
`(S, v)`.
- `betaBinomialPmf_single_crossing` — the signed difference `betaBinomialPmf(·,S+1,·) −
betaBinomialPmf(·,S,·)` changes sign
  once.
- `mgf_mono_of_single_crossing` — the MGF-weighted difference is nonnegative for increasing weights.

## Combinatorial core

`card_boolCount_eq_choose` and `boolSum_ascFactorial` are the two binary rising-factorial
multinomial
helpers (block boolean-filling counts) feeding the marginal identifications of the callers.
-/

open scoped BigOperators
open Math.Combinatorics

namespace Math.Probability

/-! ## Combinatorial core: the binary rising-factorial multinomial identity

Two block-count helpers.  `card_boolCount_eq_choose` counts the boolean fillings of a block with a
prescribed number of `true`s (`= C(#block, k)`, via the `(α → Bool) ≃ Finset α` true-set bijection
and `Fintype.card_finset_len`).  `boolSum_ascFactorial` sums the block DM-weight
`a^{(#true)}·b^{(#false)}` over all boolean fillings and evaluates it to `(a+b)^{(#block)}` by
grouping
the fillings by their `true`-count into the rising-factorial Chu–Vandermonde identity
`Nat.ascFactorial_add_eq_sum_choose_mul`. -/

/-- The number of boolean functions on `α` with exactly `k` `true` values is `C(card α, k)`. -/
lemma card_boolCount_eq_choose {α : Type*} [Fintype α] [DecidableEq α] (k : ℕ) :
    (Finset.univ.filter (fun g : α → Bool =>
        (Finset.univ.filter (fun i => g i = true)).card = k)).card = (Fintype.card α).choose k := by
  have e : {g : α → Bool // (Finset.univ.filter (fun i => g i = true)).card = k}
      ≃ {s : Finset α // s.card = k} :=
    Equiv.subtypeEquiv
      { toFun := fun g => Finset.univ.filter (fun i => g i = true),
        invFun := fun s => fun i => decide (i ∈ s),
        left_inv := by intro g; ext i; simp,
        right_inv := by intro s; ext i; simp } (fun g => Iff.rfl)
  rw [← Fintype.card_subtype, Fintype.card_congr e]
  exact Fintype.card_finset_len k

/-- The block rising-factorial DM-weight `a^{(#true)}·b^{(#false)}` summed over every boolean
filling
of a block `α` evaluates to `(a+b)^{(card α)}` (binary rising-factorial multinomial). -/
lemma boolSum_ascFactorial {α : Type*} [Fintype α] [DecidableEq α] (a b : ℕ) :
    ∑ g : α → Bool,
        (a.ascFactorial (Finset.univ.filter (fun i => g i = true)).card)
          * (b.ascFactorial (Finset.univ.filter (fun i => g i = false)).card)
      = (a + b).ascFactorial (Fintype.card α) := by
  -- `#false = card α − #true`.
  have hpart : ∀ g : α → Bool,
      (Finset.univ.filter (fun i => g i = false)).card
        = Fintype.card α - (Finset.univ.filter (fun i => g i = true)).card := by
    intro g
    have hfeq : (Finset.univ.filter (fun i => g i = false))
        = (Finset.univ.filter (fun i => ¬ (g i = true))) := by
      apply Finset.filter_congr; intro i _; cases g i <;> simp
    have h1 : (Finset.univ.filter (fun i => g i = true)).card
        + (Finset.univ.filter (fun i => g i = false)).card = Fintype.card α := by
      rw [hfeq, ← Finset.card_univ]
      exact Finset.card_filter_add_card_filter_not _
    omega
  simp_rw [hpart]
  rw [Nat.ascFactorial_add_eq_sum_choose_mul a b (Fintype.card α)]
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (α → Bool))) (t := Finset.range (Fintype.card α + 1))
    (g := fun g => (Finset.univ.filter (fun i => g i = true)).card)
    (f := fun g => a.ascFactorial (Finset.univ.filter (fun i => g i = true)).card
      * b.ascFactorial (Fintype.card α - (Finset.univ.filter (fun i => g i = true)).card))
    (fun g _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_filter_le _ _)))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_congr rfl (g := fun _ => a.ascFactorial k * b.ascFactorial (Fintype.card α - k))
    (fun g hg => by rw [(Finset.mem_filter.mp hg).2])]
  rw [Finset.sum_const, card_boolCount_eq_choose k, nsmul_eq_mul, Nat.cast_id, ← mul_assoc]

/-! ## The phase-count marginal `betaBinomialPmf` -/

/-- **The rising-factorial beta-binomial pmf**:
```
betaBinomialPmf m P S v  =  C(m,v) · (S+2)^{(v)} · (P−S+2)^{(m−v)} / (P+4)^{(m)}
```
the `BetaBin(m; S+2, P−S+2)` pmf on `v ∈ {0,…,m}`, where `x^{(k)} = Nat.ascFactorial x k` is the
rising factorial.  Explicit; no `Classical.choose`. -/
noncomputable def betaBinomialPmf (m P S v : ℕ) : ℝ :=
  (m.choose v : ℝ) * ((S + 2).ascFactorial v : ℝ) * ((P - S + 2).ascFactorial (m - v) : ℝ)
    / ((P + 4).ascFactorial m : ℝ)

/-- The normalising denominator `(P+4)^{(m)}` is strictly positive. -/
theorem betaBinomialPmf_denom_pos (m P : ℕ) : (0 : ℝ) < ((P + 4).ascFactorial m : ℝ) := by
  have : 0 < (P + 4).ascFactorial m := by
    rw [show P + 4 = (P + 3) + 1 from rfl]
    exact Nat.ascFactorial_pos _ _
  exact_mod_cast this

/-- Every `betaBinomialPmf` value is nonnegative. -/
theorem betaBinomialPmf_nonneg (m P S v : ℕ) : 0 ≤ betaBinomialPmf m P S v := by
  unfold betaBinomialPmf
  apply div_nonneg
  · positivity
  · exact (betaBinomialPmf_denom_pos m P).le

/-- **`betaBinomialPmf` is a probability mass function**: for `S ≤ P` the `m+1` values sum to `1`.
Proved by
the rising-factorial Chu–Vandermonde primitive `Nat.ascFactorial_add_eq_sum_choose_mul_cast` applied
at
`x = S+2`, `y = P−S+2`, so the numerators sum to `((S+2)+(P−S+2))^{(m)} = (P+4)^{(m)}`, the
denominator. -/
theorem betaBinomialPmf_sum_eq_one (m P S : ℕ) (hSP : S ≤ P) :
    ∑ v ∈ Finset.range (m + 1), betaBinomialPmf m P S v = 1 := by
  have hden : ((P + 4).ascFactorial m : ℝ) ≠ 0 := (betaBinomialPmf_denom_pos m P).ne'
  have hPS : (S + 2) + (P - S + 2) = P + 4 := by omega
  -- Chu–Vandermonde the numerators to the denominator `(P+4)^{(m)}`
  have hnum : (∑ v ∈ Finset.range (m + 1),
        (m.choose v : ℝ) * ((S + 2).ascFactorial v : ℝ) * ((P - S + 2).ascFactorial (m - v) : ℝ))
      = ((P + 4).ascFactorial m : ℝ) := by
    rw [← Nat.ascFactorial_add_eq_sum_choose_mul_cast (S + 2) (P - S + 2) m, hPS]
  calc ∑ v ∈ Finset.range (m + 1), betaBinomialPmf m P S v
      = ∑ v ∈ Finset.range (m + 1),
          ((m.choose v : ℝ) * ((S + 2).ascFactorial v : ℝ) * ((P - S + 2).ascFactorial (m - v) : ℝ))
            * ((P + 4).ascFactorial m : ℝ)⁻¹ :=
        Finset.sum_congr rfl (fun v _ => by rw [betaBinomialPmf, div_eq_mul_inv])
    _ = (∑ v ∈ Finset.range (m + 1),
          (m.choose v : ℝ) * ((S + 2).ascFactorial v : ℝ) * ((P - S + 2).ascFactorial (m - v) : ℝ))
            * ((P + 4).ascFactorial m : ℝ)⁻¹ := by rw [Finset.sum_mul]
    _ = 1 := by rw [hnum, mul_inv_cancel₀ hden]

-- Numerical probes (non-vacuity / orientation): `m = 4`, `P = 5`, `S = 2`.
example : (4 : ℕ).choose 1 * (4 : ℕ).ascFactorial 1 * (5 : ℕ).ascFactorial 3 = 3360 := by decide
example : (9 : ℕ).ascFactorial 4 = 11880 := by decide
example : betaBinomialPmf 4 5 2 1 = (3360 : ℝ) / 11880 := by
  norm_num [betaBinomialPmf, Nat.ascFactorial, Nat.choose]

/-- **`betaBinomialPmf` is strictly positive on the support**: for `v ≤ m` the choose and both
rising
factorials are positive. -/
lemma betaBinomialPmf_pos (m P S v : ℕ) (hv : v ≤ m) : 0 < betaBinomialPmf m P S v := by
  unfold betaBinomialPmf
  apply div_pos _ (betaBinomialPmf_denom_pos m P)
  have h1 : 0 < m.choose v := Nat.choose_pos hv
  have h2 : 0 < (S + 2).ascFactorial v := Nat.ascFactorial_pos _ _
  have h3 : 0 < (P - S + 2).ascFactorial (m - v) := Nat.ascFactorial_pos _ _
  exact mul_pos (mul_pos (by exact_mod_cast h1) (by exact_mod_cast h2)) (by exact_mod_cast h3)

/-! ## The likelihood-ratio family (MLR / single-crossing / MGF-monotone) -/

/-- **`betaBinomialPmf_mlr`**.  The likelihood ratio
`betaBinomialPmf(m,P,S+1,·)/betaBinomialPmf(m,P,S,·)` is monotone in `v`
(log-supermodularity), in cross-product form: for `S+1 ≤ P` and `v₁ ≤ v₂ ≤ m`,
`betaBinomialPmf m P (S+1) v₁ · betaBinomialPmf m P S v₂ ≤ betaBinomialPmf m P (S+1) v₂ ·
betaBinomialPmf m P S v₁`.  Both ratios
`(S+3)^{(v)}/(S+2)^{(v)}` and `(P−S)^{(m−v)}/(P−S+1)^{(m−v)}` rise in `v`. -/
theorem betaBinomialPmf_mlr (m P S v₁ v₂ : ℕ) (hSP : S + 1 ≤ P) (h12 : v₁ ≤ v₂) (h2m : v₂ ≤ m) :
    betaBinomialPmf m P (S + 1) v₁ * betaBinomialPmf m P S v₂ ≤ betaBinomialPmf m P (S + 1) v₂ *
        betaBinomialPmf m P S v₁ := by
  -- ℕ numerator inequality (the core MLR / log-supermodularity).  The common denominator
  -- `D = (P+4)^{(m)}` cancels; write `a = S+2` (so `(S+1)+2 = a+1`) and `b = P−S+1`
  -- (so `P−(S+1)+2 = b` and `P−S+2 = b+1`), then use `ascFactorial_cross` on each of the two
  -- rising-factorial pairs and multiply.
  have key :
      (m.choose v₁ * (S + 1 + 2).ascFactorial v₁ * (P - (S + 1) + 2).ascFactorial (m - v₁))
        * (m.choose v₂ * (S + 2).ascFactorial v₂ * (P - S + 2).ascFactorial (m - v₂))
      ≤ (m.choose v₂ * (S + 1 + 2).ascFactorial v₂ * (P - (S + 1) + 2).ascFactorial (m - v₂))
        * (m.choose v₁ * (S + 2).ascFactorial v₁ * (P - S + 2).ascFactorial (m - v₁)) := by
    have e1 : S + 1 + 2 = S + 2 + 1 := by omega
    have e2 : P - (S + 1) + 2 = P - S + 1 := by omega
    have e3 : P - S + 2 = P - S + 1 + 1 := by omega
    rw [e1, e2, e3]
    have hi : (S + 2 + 1).ascFactorial v₁ * (S + 2).ascFactorial v₂
            ≤ (S + 2 + 1).ascFactorial v₂ * (S + 2).ascFactorial v₁ :=
      ascFactorial_cross (S + 2) v₁ v₂ h12
    have hii : (P - S + 1).ascFactorial (m - v₁) * (P - S + 1 + 1).ascFactorial (m - v₂)
             ≤ (P - S + 1).ascFactorial (m - v₂) * (P - S + 1 + 1).ascFactorial (m - v₁) := by
      have h := ascFactorial_cross (P - S + 1) (m - v₂) (m - v₁) (by omega)
      calc (P - S + 1).ascFactorial (m - v₁) * (P - S + 1 + 1).ascFactorial (m - v₂)
          = (P - S + 1 + 1).ascFactorial (m - v₂) * (P - S + 1).ascFactorial (m - v₁) := by ring
        _ ≤ (P - S + 1 + 1).ascFactorial (m - v₁) * (P - S + 1).ascFactorial (m - v₂) := h
        _ = (P - S + 1).ascFactorial (m - v₂) * (P - S + 1 + 1).ascFactorial (m - v₁) := by ring
    calc (m.choose v₁ * (S + 2 + 1).ascFactorial v₁ * (P - S + 1).ascFactorial (m - v₁))
          * (m.choose v₂ * (S + 2).ascFactorial v₂ * (P - S + 1 + 1).ascFactorial (m - v₂))
        = (m.choose v₁ * m.choose v₂)
            * (((S + 2 + 1).ascFactorial v₁ * (S + 2).ascFactorial v₂)
               * ((P - S + 1).ascFactorial (m - v₁) * (P - S + 1 + 1).ascFactorial (m - v₂))) := by
          ring
      _ ≤ (m.choose v₁ * m.choose v₂)
            * (((S + 2 + 1).ascFactorial v₂ * (S + 2).ascFactorial v₁)
               * ((P - S + 1).ascFactorial (m - v₂) * (P - S + 1 + 1).ascFactorial (m - v₁))) :=
          Nat.mul_le_mul (le_refl _) (Nat.mul_le_mul hi hii)
      _ = (m.choose v₂ * (S + 2 + 1).ascFactorial v₂ * (P - S + 1).ascFactorial (m - v₂))
            * (m.choose v₁ * (S + 2).ascFactorial v₁ * (P - S + 1 + 1).ascFactorial (m - v₁)) := by
          ring
  -- Transport the ℕ inequality to the real `betaBinomialPmf` inequality (divide by `D²`).
  have hD : (0 : ℝ) < ((P + 4).ascFactorial m : ℝ) := betaBinomialPmf_denom_pos m P
  have hDD : (0 : ℝ) < ((P + 4).ascFactorial m : ℝ) * ((P + 4).ascFactorial m : ℝ) := mul_pos hD hD
  rw [betaBinomialPmf, betaBinomialPmf, betaBinomialPmf, betaBinomialPmf, div_mul_div_comm,
      div_mul_div_comm,
    div_le_div_iff_of_pos_right hDD]
  exact_mod_cast key

/-- **`betaBinomialPmf_single_crossing`**.  The signed difference `betaBinomialPmf(m,P,S+1,·) −
betaBinomialPmf(m,P,S,·)`
changes sign exactly once (from `betaBinomialPmf_mlr` and both being pmfs): there is a threshold
`v*` below
which `S+1` under-weights and at/above which it over-weights. -/
theorem betaBinomialPmf_single_crossing (m P S : ℕ) (hSP : S + 1 ≤ P) :
    ∃ vc : ℕ, (∀ v, v ≤ m → v < vc → betaBinomialPmf m P (S + 1) v ≤ betaBinomialPmf m P S v)
      ∧ (∀ v, v ≤ m → vc ≤ v → betaBinomialPmf m P S v ≤ betaBinomialPmf m P (S + 1) v) := by
  classical
  -- `vc` = least `v ≤ m` where `S+1` over-weights, or `m+1` if none.  MLR (`betaBinomialPmf_mlr`)
  -- makes the
  -- over-weight set upward-closed, so this threshold splits `≤`/`≥`.
  have hex : ∃ v : ℕ, (v ≤ m ∧ betaBinomialPmf m P S v ≤ betaBinomialPmf m P (S + 1) v) ∨ v = m + 1
      :=
    ⟨m + 1, Or.inr rfl⟩
  refine ⟨Nat.find hex, ?_, ?_⟩
  · intro v hvm hvlt
    have hnot := Nat.find_min hex hvlt
    have hnotQ : ¬ (betaBinomialPmf m P S v ≤ betaBinomialPmf m P (S + 1) v) := fun hQ => hnot
        (Or.inl ⟨hvm, hQ⟩)
    exact le_of_lt (not_le.mp hnotQ)
  · intro v hvm hge
    rcases Nat.find_spec hex with ⟨hvcm, hQvc⟩ | hvc1
    · set vc := Nat.find hex with hvcdef
      have hmlr := betaBinomialPmf_mlr m P S vc v hSP hge hvm
      have hpos_vc1 : 0 < betaBinomialPmf m P (S + 1) vc := betaBinomialPmf_pos m P (S + 1) vc hvcm
      have hpos_v1 : 0 < betaBinomialPmf m P (S + 1) v := betaBinomialPmf_pos m P (S + 1) v hvm
      have step : betaBinomialPmf m P (S + 1) vc * betaBinomialPmf m P S v
                ≤ betaBinomialPmf m P (S + 1) vc * betaBinomialPmf m P (S + 1) v := by
        calc betaBinomialPmf m P (S + 1) vc * betaBinomialPmf m P S v
            ≤ betaBinomialPmf m P (S + 1) v * betaBinomialPmf m P S vc := hmlr
          _ ≤ betaBinomialPmf m P (S + 1) v * betaBinomialPmf m P (S + 1) vc :=
              mul_le_mul_of_nonneg_left hQvc hpos_v1.le
          _ = betaBinomialPmf m P (S + 1) vc * betaBinomialPmf m P (S + 1) v := by ring
      exact le_of_mul_le_mul_left step hpos_vc1
    · exfalso; omega

/-- **`mgf_mono_of_single_crossing`**.  With increasing weights `(1/c)^v` (`0 < c ≤ 1`) and the
single-crossing signed difference of two pmfs of equal mass, the MGF-weighted difference is
nonnegative: `0 ≤ ∑_{v=0}^m (betaBinomialPmf(m,P,S+1,v) − betaBinomialPmf(m,P,S,v))·(1/c)^v`
(Abel/Chebyshev sum). -/
theorem mgf_mono_of_single_crossing (m P S : ℕ) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hSP : S + 1 ≤ P) :
    0 ≤ ∑ v ∈ Finset.range (m + 1),
        (betaBinomialPmf m P (S + 1) v - betaBinomialPmf m P S v) * (1 / c) ^ v := by
  obtain ⟨vc, hlow, hhigh⟩ := betaBinomialPmf_single_crossing m P S hSP
  -- weights `w v = (1/c)^v` are `≥ 1` (so nondecreasing in `v`); the signed difference has total
  -- mass `0`; subtract `w(vc)·0` and split at `vc`, each term nonnegative (Chebyshev/Abel).
  have hw1 : (1 : ℝ) ≤ 1 / c := by rw [le_div_iff₀ hc, one_mul]; exact hc1
  have hSP' : S ≤ P := by omega
  have hmass : ∑ v ∈ Finset.range (m + 1), (betaBinomialPmf m P (S + 1) v - betaBinomialPmf m P S v)
      = 0 := by
    rw [Finset.sum_sub_distrib, betaBinomialPmf_sum_eq_one m P (S + 1) hSP,
        betaBinomialPmf_sum_eq_one m P S hSP',
      sub_self]
  have hrw : ∑ v ∈ Finset.range (m + 1), (betaBinomialPmf m P (S + 1) v - betaBinomialPmf m P S v) *
      (1 / c) ^ v
      = ∑ v ∈ Finset.range (m + 1),
          (betaBinomialPmf m P (S + 1) v - betaBinomialPmf m P S v) * ((1 / c) ^ v - (1 / c) ^ vc)
              := by
    have hexpand : ∑ v ∈ Finset.range (m + 1),
            (betaBinomialPmf m P (S + 1) v - betaBinomialPmf m P S v) * ((1 / c) ^ v - (1 / c) ^ vc)
        = (∑ v ∈ Finset.range (m + 1), (betaBinomialPmf m P (S + 1) v - betaBinomialPmf m P S v) *
            (1 / c) ^ v)
          - (∑ v ∈ Finset.range (m + 1), (betaBinomialPmf m P (S + 1) v - betaBinomialPmf m P S v))
              * (1 / c) ^ vc := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun v _ => by ring)
    rw [hexpand, hmass, zero_mul, sub_zero]
  rw [hrw]
  apply Finset.sum_nonneg
  intro v hv
  rw [Finset.mem_range, Nat.lt_succ_iff] at hv
  rcases Nat.lt_or_ge v vc with hvlt | hvge
  · have hd : betaBinomialPmf m P (S + 1) v - betaBinomialPmf m P S v ≤ 0 := by
      have := hlow v hv hvlt; linarith
    have hwle : (1 / c) ^ v - (1 / c) ^ vc ≤ 0 := by
      have : (1 / c) ^ v ≤ (1 / c) ^ vc := pow_le_pow_right₀ hw1 (le_of_lt hvlt)
      linarith
    exact mul_nonneg_of_nonpos_of_nonpos hd hwle
  · have hd : 0 ≤ betaBinomialPmf m P (S + 1) v - betaBinomialPmf m P S v := by
      have := hhigh v hv hvge; linarith
    have hwge : 0 ≤ (1 / c) ^ v - (1 / c) ^ vc := by
      have : (1 / c) ^ vc ≤ (1 / c) ^ v := pow_le_pow_right₀ hw1 hvge
      linarith
    exact mul_nonneg hd hwge

end Math.Probability
