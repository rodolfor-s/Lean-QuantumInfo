import QCryptLean.Math.Concentration.BinomialHoeffding

/-!
# Binomial PE-pass sum and its Hoeffding lower-tail bound

This file isolates, as a reusable classical object, the **parameter-estimation
pass mass** of a binomial distribution: the sum of binomial terms over the counts
`k` whose empirical fraction `k/n` lies within a tolerance `δ` of a target `Q`.

This is the basis-agnostic core of a parameter-estimation soundness argument
(Renner 2005, §6.5): the classical content factors out so it can be reused unchanged
across bases and for any other binomial PE classifier.

## Main definitions
- `Math.Concentration.BinomialPassSum.binomialPassSum`: the PE-pass binomial mass, an
  explicit finite sum (no `Classical.choose`).

## Main statements
- `Math.Concentration.BinomialPassSum.binomialPassSum_le_hoeffding`: if the true rate
  `p` exceeds the PE-pass band `Q + δ` by a margin `η > 0`, the pass mass is at most the
  one-sided Hoeffding exponent `exp(-2 n η²)`.
- `Math.Concentration.BinomialPassSum.binomialPassSum_eq_zero_of_rate_one`: at the certain-failure
  rate `p = 1` the pass mass is exactly `0` whenever the band excludes `1` (`Q + δ < 1`).
- `Math.Concentration.BinomialPassSum.binomialPassSum_eq_one_of_rate_zero`: at the certain-success
  rate `p = 0` the pass mass is exactly `1` whenever the band contains `0` (`0 ≤ Q ≤ δ`).

## Source
Renner 2005, §6.5 (parameter-estimation lower tail).  The classical Hoeffding lower
tail is `Math.Concentration.BinomialHoeffding.binomial_lower_tail`; this file packages
the indicator-domination `|k/n - Q| ≤ δ ⟹ k/n ≤ p - η` on top of it.
-/

namespace Math.Concentration.BinomialPassSum

open scoped BigOperators

/-- **Binomial PE-pass mass.**

For `n : ℕ` trials with per-trial success probability `p` and a parameter-estimation
band `|k/n - Q| ≤ δ`, this is the total binomial mass on the counts `k` that pass the
band (outside-band counts contribute `0`):
`∑_{k=0}^{n} [ |k/n - Q| ≤ δ ] · C(n,k) p^k (1-p)^{n-k}`. -/
noncomputable def binomialPassSum (n : ℕ) (Q δ p : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    if |(k : ℝ) / n - Q| ≤ δ then
      (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)
    else 0

/-- **Hoeffding lower-tail bound on the PE-pass mass.**

If the true per-trial rate `p ∈ [0, 1]` exceeds the upper edge of the PE-pass band by a
margin `η > 0` (`Q + δ + η < p`), then the PE-pass mass is at most the one-sided
Hoeffding exponent `exp(-2 n η²)`.

The PE-band sum is termwise dominated by the lower-tail sum at threshold `p - η`, because
`|k/n - Q| ≤ δ ⟹ k/n ≤ Q + δ < p - η`; the conclusion is then
`Math.Concentration.BinomialHoeffding.binomial_lower_tail` (Renner 2005, §6.5). -/
theorem binomialPassSum_le_hoeffding (n : ℕ) (hn : n ≠ 0) (Q δ η p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hη : 0 < η) (hbad : Q + δ + η < p) :
    binomialPassSum n Q δ p ≤ Real.exp (-2 * (n : ℝ) * η ^ 2) := by
  classical
  unfold binomialPassSum
  -- The PE-band sum is termwise dominated by the lower-tail sum at threshold `p - η`,
  -- because `|k/n - Q| ≤ δ ⟹ k/n ≤ Q + δ < p - η`.
  have hdom :
      (∑ k ∈ Finset.range (n + 1),
          if |(k : ℝ) / n - Q| ≤ δ then
            (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)
          else 0) ≤
        ∑ k ∈ Finset.range (n + 1),
          if ((k : ℝ) / n ≤ p - η) then
            (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)
          else 0 := by
    refine Finset.sum_le_sum ?_
    intro k _hk
    have hw_nonneg : 0 ≤ (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) := by
      have hpk : 0 ≤ p ^ k := pow_nonneg hp0 _
      have h1pk : 0 ≤ (1 - p) ^ (n - k) := pow_nonneg (by linarith) _
      positivity
    by_cases hband : |(k : ℝ) / n - Q| ≤ δ
    · rw [ite_eq_left hband]
      have hle : (k : ℝ) / n ≤ p - η := by
        have h1 : (k : ℝ) / n - Q ≤ δ := (abs_le.mp hband).2
        linarith
      rw [ite_eq_left hle]
    · rw [ite_eq_right hband]
      by_cases hlt : (k : ℝ) / n ≤ p - η
      · rw [ite_eq_left hlt]; exact hw_nonneg
      · rw [ite_eq_right hlt]
  refine le_trans hdom ?_
  exact Math.Concentration.BinomialHoeffding.binomial_lower_tail n hn p η hp0 hp1 hη

/-- **The PE-pass mass at the certain-failure rate `p = 1` is exactly `0`.**

At rate `p = 1` the binomial mass sits entirely on the full count `k = n`: every `k < n` carries the
factor `(1 - p)^(n - k) = 0^(n-k) = 0`.  The single surviving term `k = n` has empirical fraction
`n/n = 1`, which the PE band `|k/n - Q| ≤ δ` rejects as soon as it excludes `1`, i.e. under
`Q + δ < 1`.  So the whole sum vanishes — no rounding, no tail estimate.

`hn : n ≠ 0` is load-bearing twice: it is what makes `n/n = 1`, and at `n = 0` the sum is the single
term `k = 0` whose band test is `|0 - Q| ≤ δ`, which `Q + δ < 1` does not exclude (e.g. `Q = δ = 0`
gives mass `1`).

This is the exact (epsilon-free) companion of `binomialPassSum_le_hoeffding`: a component whose
measured disagreement rate is *certain* contributes nothing at all to a PE-pass mass. -/
theorem binomialPassSum_eq_zero_of_rate_one (n : ℕ) (hn : n ≠ 0) (Q δ : ℝ) (h : Q + δ < 1) :
    binomialPassSum n Q δ 1 = 0 := by
  unfold binomialPassSum
  refine Finset.sum_eq_zero (fun k hk => ?_)
  by_cases hkn : k = n
  · subst hkn
    rw [ite_eq_right]
    intro hband
    rw [div_self (Nat.cast_ne_zero.mpr hn), abs_le] at hband
    exact absurd h (not_lt.mpr (sub_le_iff_le_add'.mp hband.2))
  · have hlt : k < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) hkn
    have hne : n - k ≠ 0 := Nat.sub_ne_zero_of_lt hlt
    split_ifs
    · simp [zero_pow hne]
    · rfl

/-- **The PE-pass mass at the certain-success rate `p = 0` is exactly `1`.**

Mirror image of `binomialPassSum_eq_zero_of_rate_one`.  At rate `p = 0` the binomial mass sits
entirely on the empty count `k = 0`: every `k > 0` carries the factor `p ^ k = 0 ^ k = 0`.  The
single surviving term `k = 0` has empirical fraction `0/n = 0`, which the PE band `|k/n - Q| ≤ δ`
accepts exactly when the band reaches down to `0`, i.e. under `0 ≤ Q ≤ δ`.  So the whole sum is the
one term `C(n,0) · 0^0 · 1^n = 1` — no rounding, no tail estimate.

No `n ≠ 0` hypothesis is needed: at `n = 0` the sum is the single term `k = 0`, whose band test is
`|0 - Q| ≤ δ` and whose weight is `1`, which is the same computation.  (The `p = 1` companion does
need `hn`, because there the surviving count is `k = n` and `n/n = 1` requires `n ≠ 0`.)

This is what makes a component whose measured disagreement rate is *certainly zero* pass the PE
test with certainty; paired with `binomialPassSum_eq_zero_of_rate_one` it turns a rate-preserving
question into an exact two-point calculation.

Source: Renner 2005, §6.5 (parameter-estimation band); the statement is the `p = 0` endpoint of the
same band sum `binomialPassSum`. -/
theorem binomialPassSum_eq_one_of_rate_zero (n : ℕ) (Q δ : ℝ) (hQ0 : 0 ≤ Q) (hQδ : Q ≤ δ) :
    binomialPassSum n Q δ 0 = 1 := by
  unfold binomialPassSum
  have hband : |((0 : ℕ) : ℝ) / n - Q| ≤ δ := by
    rw [Nat.cast_zero, zero_div, zero_sub, abs_neg, abs_of_nonneg hQ0]
    exact hQδ
  rw [Finset.sum_eq_single 0]
  · rw [ite_eq_left hband]
    simp
  · intro k _ hk0
    have hkpos : k ≠ 0 := hk0
    split_ifs
    · rw [zero_pow hkpos]
      ring
    · rfl
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos n)) h

/-!
## Generic flag-count binomial pass-sum

This is the classical content of a combinatorial fact about per-outcome product weights over
`Fin n → Fin 4` filtered by a two-bin mismatch flag `{1, 2}` vs `{0, 3}`, stated here parametric
in an arbitrary per-outcome flag `flag : Fin d → Prop` and per-outcome weight `g : Fin d → ℝ`.
These are the basis-agnostic core needed by any single-POVM, multi-statistic
parameter-estimation classifier (Renner 2005, §6.5, `pr:PE`).
-/

open scoped BigOperators in
/-- **Generic fiber product-sum is binomial.**

For weights `g : Fin d → ℝ` and a per-outcome flag `flag`, the sum of the `n`-fold product
`∏ i, g (ω i)` over outcome strings `ω : Fin n → Fin d` whose number of flagged positions is
exactly `k` factorises as `(n choose k) · (∑_{flag} g)^k · (∑_{¬flag} g)^{n−k}`.

This is the parametric generalisation of the two-bin mismatch-flag instance
(flag = `(· = 1 ∨ · = 2)`, `d = 4`).  Purely combinatorial; no quantum content. -/
theorem fiberProdSum_eq_binomial {n d : ℕ}
    (flag : Fin d → Prop) [DecidablePred flag] (g : Fin d → ℝ) (k : ℕ) :
    ∑ ω ∈ (Finset.univ : Finset (Fin n → Fin d)).filter
            (fun ω => (Finset.univ.filter (fun i => flag (ω i))).card = k),
        ∏ i : Fin n, g (ω i) =
      (n.choose k : ℝ)
        * (∑ j ∈ Finset.univ.filter (fun j => flag j), g j) ^ k
        * (∑ j ∈ Finset.univ.filter (fun j => ¬ flag j), g j) ^ (n - k) := by
  classical
  -- Partition the outcome sum by the flag-support set, via `Finset.sum_fiberwise_of_maps_to`.
  have h_mapsTo : ∀ ω ∈ (Finset.univ : Finset (Fin n → Fin d)).filter
                    (fun ω => (Finset.univ.filter (fun i => flag (ω i))).card = k),
      (Finset.univ.filter (fun i => flag (ω i)))
        ∈ (Finset.univ : Finset (Fin n)).powersetCard k := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hω.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to h_mapsTo (f := fun ω => ∏ i : Fin n, g (ω i))]
  -- On each fiber the cardinality side-condition is automatic, so drop it.
  have h_inner_filter : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      ((Finset.univ : Finset (Fin n → Fin d)).filter
        (fun ω => (Finset.univ.filter (fun i => flag (ω i))).card = k)).filter
          (fun ω => (Finset.univ.filter (fun i => flag (ω i))) = S) =
      (Finset.univ : Finset (Fin n → Fin d)).filter
        (fun ω => (Finset.univ.filter (fun i => flag (ω i))) = S) := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨by rw [h]; exact hS.2, h⟩
  rw [Finset.sum_congr rfl (fun S hS => by rw [h_inner_filter S hS])]
  -- For each support set `S` of size `k`, the fiber bijects with `Fintype.piFinset t`.
  have h_inner_eq : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      (∑ ω ∈ (Finset.univ : Finset (Fin n → Fin d)).filter
              (fun ω => (Finset.univ.filter (fun i => flag (ω i))) = S),
        ∏ i : Fin n, g (ω i)) =
        (∑ j ∈ Finset.univ.filter (fun j => flag j), g j) ^ k *
          (∑ j ∈ Finset.univ.filter (fun j => ¬ flag j), g j) ^ (n - k) := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    obtain ⟨_, hS_card⟩ := hS
    -- per-position 2-element bin: flagged values on `S`, unflagged off `S`.
    let t : Fin n → Finset (Fin d) :=
      fun i => if i ∈ S then Finset.univ.filter (fun j => flag j)
               else Finset.univ.filter (fun j => ¬ flag j)
    have h_eq_pi : (Finset.univ : Finset (Fin n → Fin d)).filter
                    (fun ω => (Finset.univ.filter (fun i => flag (ω i))) = S) =
        Fintype.piFinset t := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
      constructor
      · intro h_eq i
        by_cases hi : i ∈ S
        · simp only [t, ite_eq_left hi]
          have hmem : i ∈ (Finset.univ.filter (fun i => flag (ω i))) := by rw [h_eq]; exact hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
          exact hmem
        · simp only [t, ite_eq_right hi]
          have hmem : i ∉ (Finset.univ.filter (fun i => flag (ω i))) := by rw [h_eq]; exact hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
          exact hmem
      · intro h_pi
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h_flag
          by_contra hi
          specialize h_pi i
          simp only [t, ite_eq_right hi, Finset.mem_filter, Finset.mem_univ, true_and] at h_pi
          exact h_pi h_flag
        · intro hi
          specialize h_pi i
          simp only [t, ite_eq_left hi, Finset.mem_filter, Finset.mem_univ, true_and] at h_pi
          exact h_pi
    rw [h_eq_pi, ← Finset.prod_univ_sum t (fun _ j => g j)]
    have h_t_sum : ∀ i : Fin n,
        (∑ j ∈ t i, g j) =
          if i ∈ S then (∑ j ∈ Finset.univ.filter (fun j => flag j), g j)
          else (∑ j ∈ Finset.univ.filter (fun j => ¬ flag j), g j) := by
      intro i
      by_cases hi : i ∈ S
      · simp only [t, ite_eq_left hi]
      · simp only [t, ite_eq_right hi]
    rw [Finset.prod_congr rfl (fun i _ => h_t_sum i),
        Finset.prod_ite (f := fun _ => (∑ j ∈ Finset.univ.filter (fun j => flag j), g j))
          (g := fun _ => (∑ j ∈ Finset.univ.filter (fun j => ¬ flag j), g j)),
        Finset.prod_const, Finset.prod_const]
    have h_S_eq : (Finset.univ.filter (fun i : Fin n => i ∈ S)).card = k := by
      rw [show Finset.univ.filter (fun i : Fin n => i ∈ S) = S from by ext i; simp]
      exact hS_card
    have h_Sc_eq : (Finset.univ.filter (fun i : Fin n => i ∉ S)).card = n - k := by
      rw [show Finset.univ.filter (fun i : Fin n => i ∉ S) = Sᶜ from by ext i; simp]
      rw [Finset.card_compl, Fintype.card_fin, hS_card]
    rw [h_S_eq, h_Sc_eq]
  rw [Finset.sum_congr rfl h_inner_eq, Finset.sum_const, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin]
  rw [nsmul_eq_mul]
  ring

open scoped BigOperators in
/-- **Generic flag-outcome pass-sum equals the binomial pass-sum.**

If the per-outcome weights `g : Fin d → ℝ` sum to one, then the band-filtered outcome sum
`∑_ω [|flagFraction(ω) − Q| ≤ δ] · ∏ i, g (ω i)` equals `binomialPassSum n Q δ p` at the
marginal flag-success rate `p = ∑_{flag} g`.

This is the parametric generalisation of the two-bin mismatch-flag instance
(flag = `(· = 1 ∨ · = 2)`, `d = 4`, `g j = (σ.toOp j j).re`).  Proof: regroup by flag count
over `range (n+1)`, pull the band-indicator out of each fiber, evaluate fibers via
`fiberProdSum_eq_binomial`, and use `∑_{¬flag} g = 1 − ∑_{flag} g`.  (Holds for all `n`,
including `n = 0`, where both sides reduce to the empty-string indicator.) -/
theorem flagOutcomePassSum_eq_binomialPassSum {n d : ℕ}
    (flag : Fin d → Prop) [DecidablePred flag] (g : Fin d → ℝ)
    (hg : (∑ j, g j) = 1) (Q δ : ℝ) :
    (∑ ω : Fin n → Fin d,
      if |((Finset.univ.filter (fun i => flag (ω i))).card : ℝ) / n - Q| ≤ δ then
        ∏ i : Fin n, g (ω i) else 0) =
      binomialPassSum n Q δ (∑ j ∈ Finset.univ.filter (fun j => flag j), g j) := by
  classical
  -- The per-outcome summand, gated by the band indicator on the flag fraction.
  set F : (Fin n → Fin d) → ℝ :=
    fun ω => if |((Finset.univ.filter (fun i => flag (ω i))).card : ℝ) / n - Q| ≤ δ then
        ∏ i : Fin n, g (ω i) else 0 with hF
  -- Step 1: regroup by flag count over `range (n + 1)`.
  have hmaps : ∀ ω ∈ (Finset.univ : Finset (Fin n → Fin d)),
      (Finset.univ.filter (fun i => flag (ω i))).card ∈ Finset.range (n + 1) := by
    intro ω _
    rw [Finset.mem_range, Nat.lt_succ_iff]
    calc (Finset.univ.filter (fun i => flag (ω i))).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
      _ = n := by rw [Finset.card_univ, Fintype.card_fin]
  rw [(Finset.sum_fiberwise_of_maps_to hmaps F).symm]
  -- Step 2: evaluate each fiber.
  unfold binomialPassSum
  refine Finset.sum_congr rfl ?_
  intro k _hk
  -- On the fiber, pull the band indicator (constant `= decide |k/n − Q| ≤ δ`) out.
  have hfiber :
      (∑ ω ∈ (Finset.univ : Finset (Fin n → Fin d)).filter
              (fun ω => (Finset.univ.filter (fun i => flag (ω i))).card = k), F ω) =
        if |(k : ℝ) / n - Q| ≤ δ then
          ∑ ω ∈ (Finset.univ : Finset (Fin n → Fin d)).filter
                  (fun ω => (Finset.univ.filter (fun i => flag (ω i))).card = k),
            ∏ i : Fin n, g (ω i)
        else 0 := by
    by_cases hpe : |(k : ℝ) / n - Q| ≤ δ
    · rw [ite_eq_left hpe]
      refine Finset.sum_congr rfl ?_
      intro ω hω
      rw [Finset.mem_filter] at hω
      have hck : (Finset.univ.filter (fun i => flag (ω i))).card = k := hω.2
      simp only [hF, hck]
      rw [ite_eq_left hpe]
    · rw [ite_eq_right hpe]
      refine Finset.sum_eq_zero ?_
      intro ω hω
      rw [Finset.mem_filter] at hω
      have hck : (Finset.univ.filter (fun i => flag (ω i))).card = k := hω.2
      simp only [hF, hck]
      rw [ite_eq_right hpe]
  rw [hfiber, fiberProdSum_eq_binomial flag g k]
  -- complement rate: `∑_{¬flag} g = 1 − ∑_{flag} g`.
  have hcomp : (∑ j ∈ Finset.univ.filter (fun j => ¬ flag j), g j) =
      1 - (∑ j ∈ Finset.univ.filter (fun j => flag j), g j) := by
    have hsum := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin d))
      (fun j => flag j) g
    rw [hg] at hsum
    linarith
  rw [hcomp]

end Math.Concentration.BinomialPassSum
