import QCryptLean.Math.Concentration.BinomialPassSum

/-!
# Selected (sub-sample) flag-outcome pass-sum equals the binomial pass-sum

This file extends `Math.Concentration.BinomialPassSum.flagOutcomePassSum_eq_binomialPassSum`
from "all rounds count" to "only a **selected** sub-sample of rounds counts", as required by
the sifted two-basis BB84 parameter-estimation test (the PE test reads only the PE rounds in
the Bell basis; the key rounds carry the `Z` key and never enter the PE statistic).

The model: a per-round outcome string `ω : Fin n → Ω`, a PE selector `sel : Fin n → Bool`,
PE-round weight `g : Ω → ℝ` (same on every PE round, summing to one), unselected-round weights
`h : Fin n → Ω → ℝ` (one weight vector per unselected round, each summing to one), and a
per-outcome flag.  The PE statistic counts flagged positions **among the selected (PE) rounds
only**, normalised by the PE sample size `m = #{i : sel i}`.

Letting the unselected weight vary per round is what the faithful two-basis parameter-estimation
test needs: selecting the `Z`-designated PE rounds leaves unselected rounds of two different kinds —
the `X`-designated PE rounds (whose Born vector is the `H ⊗ H`-rotated one) and the key rounds
(unrotated) — so a single unselected weight vector cannot express them.

## Main statements

- `selectedFlagOutcomePassSum_eq_binomialPassSum_perRound`: the selected-band-filtered outcome sum
  equals `binomialPassSum m Q δ (∑_{flag} g)` at the PE sample size `m` and PE-round flag rate
  `∑_{flag} g`, with the unselected rounds carrying per-round weight vectors.
- `selectedFlagOutcomePassSum_eq_binomialPassSum`: the constant-unselected-weight instantiation, for
  a single key-round weight vector `h : Ω → ℝ`.

The proof splits the product over the selected / unselected subtypes (`Equiv.piEquivPiSubtypeProd`),
factors the free unselected-round sum (`∏ i, (∑ j, h i j) = 1`), and evaluates the PE sub-sample sum
by a `Fintype`-general fiber-count argument (the index-general analogue of
`Math.Concentration.BinomialPassSum.fiberProdSum_eq_binomial`).

References: Renner (2005), `arXiv:quant-ph/0512258v2`, §6.5 (two-statistic parameter estimation
restricted to the PE sub-sample); the underlying binomial combinatorics is basis-agnostic.
-/

namespace Math.Concentration.SelectedBinomialPassSum

open scoped BigOperators

/-- **Fiber product-sum over a general index Fintype is binomial.**

`Fintype`-general analogue of `Math.Concentration.BinomialPassSum.fiberProdSum_eq_binomial`:
for an arbitrary index Fintype `ι`, weights `g : Ω → ℝ`, and a per-outcome flag, the sum of
`∏ i, g (ω i)` over outcome strings `ω : ι → Ω` whose number of flagged positions is exactly
`k` factorises as `(card ι choose k) · (∑_{flag} g)^k · (∑_{¬flag} g)^(card ι − k)`. -/
theorem fiberProdSum_eq_binomial_index {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : Type*} [Fintype Ω]
    (flag : Ω → Prop) [DecidablePred flag] (g : Ω → ℝ) (k : ℕ) :
    ∑ ω ∈ (Finset.univ : Finset (ι → Ω)).filter
            (fun ω => (Finset.univ.filter (fun i => flag (ω i))).card = k),
        ∏ i : ι, g (ω i) =
      (Fintype.card ι).choose k
        * (∑ j ∈ Finset.univ.filter (fun j => flag j), g j) ^ k
        * (∑ j ∈ Finset.univ.filter (fun j => ¬ flag j), g j) ^ (Fintype.card ι - k) := by
  classical
  have h_mapsTo : ∀ ω ∈ (Finset.univ : Finset (ι → Ω)).filter
                    (fun ω => (Finset.univ.filter (fun i => flag (ω i))).card = k),
      (Finset.univ.filter (fun i => flag (ω i)))
        ∈ (Finset.univ : Finset ι).powersetCard k := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hω.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to h_mapsTo (f := fun ω => ∏ i : ι, g (ω i))]
  have h_inner_filter : ∀ S ∈ (Finset.univ : Finset ι).powersetCard k,
      ((Finset.univ : Finset (ι → Ω)).filter
        (fun ω => (Finset.univ.filter (fun i => flag (ω i))).card = k)).filter
          (fun ω => (Finset.univ.filter (fun i => flag (ω i))) = S) =
      (Finset.univ : Finset (ι → Ω)).filter
        (fun ω => (Finset.univ.filter (fun i => flag (ω i))) = S) := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨by rw [h]; exact hS.2, h⟩
  rw [Finset.sum_congr rfl (fun S hS => by rw [h_inner_filter S hS])]
  have h_inner_eq : ∀ S ∈ (Finset.univ : Finset ι).powersetCard k,
      (∑ ω ∈ (Finset.univ : Finset (ι → Ω)).filter
              (fun ω => (Finset.univ.filter (fun i => flag (ω i))) = S),
        ∏ i : ι, g (ω i)) =
        (∑ j ∈ Finset.univ.filter (fun j => flag j), g j) ^ k *
          (∑ j ∈ Finset.univ.filter (fun j => ¬ flag j), g j) ^ (Fintype.card ι - k) := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    obtain ⟨_, hS_card⟩ := hS
    let t : ι → Finset (Ω) :=
      fun i => if i ∈ S then Finset.univ.filter (fun j => flag j)
               else Finset.univ.filter (fun j => ¬ flag j)
    have h_eq_pi : (Finset.univ : Finset (ι → Ω)).filter
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
    have h_t_sum : ∀ i : ι,
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
    have h_S_eq : (Finset.univ.filter (fun i : ι => i ∈ S)).card = k := by
      rw [show Finset.univ.filter (fun i : ι => i ∈ S) = S from by ext i; simp]
      exact hS_card
    have h_Sc_eq : (Finset.univ.filter (fun i : ι => i ∉ S)).card = Fintype.card ι - k := by
      rw [show Finset.univ.filter (fun i : ι => i ∉ S) = Sᶜ from by ext i; simp]
      rw [Finset.card_compl, hS_card]
    rw [h_S_eq, h_Sc_eq]
  rw [Finset.sum_congr rfl h_inner_eq, Finset.sum_const, Finset.card_powersetCard,
      Finset.card_univ]
  rw [nsmul_eq_mul]
  ring

open scoped BigOperators in
/-- **Index-general flag-outcome pass-sum equals the binomial pass-sum.**

`Fintype`-general analogue of
`Math.Concentration.BinomialPassSum.flagOutcomePassSum_eq_binomialPassSum`: if the per-outcome
weights `g : Ω → ℝ` sum to one, then the band-filtered outcome sum over `ω : ι → Ω`
equals `binomialPassSum (card ι) Q δ p` at the marginal flag rate `p = ∑_{flag} g`. -/
theorem flagOutcomePassSum_eq_binomialPassSum_index {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : Type*} [Fintype Ω]
    (flag : Ω → Prop) [DecidablePred flag] (g : Ω → ℝ)
    (hg : (∑ j, g j) = 1) (Q δ : ℝ) :
    (∑ ω : ι → Ω,
      if |((Finset.univ.filter (fun i => flag (ω i))).card : ℝ) / Fintype.card ι - Q| ≤ δ then
        ∏ i : ι, g (ω i) else 0) =
      Math.Concentration.BinomialPassSum.binomialPassSum (Fintype.card ι) Q δ
        (∑ j ∈ Finset.univ.filter (fun j => flag j), g j) := by
  classical
  set N : ℕ := Fintype.card ι with hN
  set F : (ι → Ω) → ℝ :=
    fun ω => if |((Finset.univ.filter (fun i => flag (ω i))).card : ℝ) / N - Q| ≤ δ then
        ∏ i : ι, g (ω i) else 0 with hF
  have hmaps : ∀ ω ∈ (Finset.univ : Finset (ι → Ω)),
      (Finset.univ.filter (fun i => flag (ω i))).card ∈ Finset.range (N + 1) := by
    intro ω _
    rw [Finset.mem_range, Nat.lt_succ_iff, hN]
    calc (Finset.univ.filter (fun i => flag (ω i))).card
        ≤ (Finset.univ : Finset ι).card := Finset.card_filter_le _ _
      _ = Fintype.card ι := Finset.card_univ
  rw [(Finset.sum_fiberwise_of_maps_to hmaps F).symm]
  unfold Math.Concentration.BinomialPassSum.binomialPassSum
  refine Finset.sum_congr rfl ?_
  intro k _hk
  have hfiber :
      (∑ ω ∈ (Finset.univ : Finset (ι → Ω)).filter
              (fun ω => (Finset.univ.filter (fun i => flag (ω i))).card = k), F ω) =
        if |(k : ℝ) / N - Q| ≤ δ then
          ∑ ω ∈ (Finset.univ : Finset (ι → Ω)).filter
                  (fun ω => (Finset.univ.filter (fun i => flag (ω i))).card = k),
            ∏ i : ι, g (ω i)
        else 0 := by
    by_cases hpe : |(k : ℝ) / N - Q| ≤ δ
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
  rw [hfiber, fiberProdSum_eq_binomial_index flag g k, ← hN]
  have hcomp : (∑ j ∈ Finset.univ.filter (fun j => ¬ flag j), g j) =
      1 - (∑ j ∈ Finset.univ.filter (fun j => flag j), g j) := by
    have hsum := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Ω))
      (fun j => flag j) g
    rw [hg] at hsum
    linarith
  rw [hcomp]

open scoped BigOperators in
/-- **Selected sub-sample split, per-round unselected weights.**

For a PE selector `sel : Fin n → Bool`, PE-round weight `g`, and per-round unselected weights
`h i : Ω → ℝ` with `∑ j, h i j = 1` for every round `i`, the full band-filtered outcome sum over
`ω : Fin n → Ω` — where the PE statistic counts flagged positions among the **selected** rounds
only (normalised by the PE sample size `m = card {i // sel i = true}`) — equals the index-restricted
band-filtered sum over the PE subtype, with all unselected rounds summed out (contributing the free
factor `∏ i, (∑ j, h i j) = 1`).

The per-round unselected weight is what the faithful two-basis PE test needs: selecting the
`Z`-designated PE rounds leaves unselected rounds of two different kinds — the `X`-designated PE
rounds (whose Born vector is the `H ⊗ H`-rotated one) and the key rounds (unrotated).
`selected_split` is the constant-family instantiation. -/
theorem selected_split_perRound {n : ℕ} {Ω : Type*} [Fintype Ω]
    (sel : Fin n → Bool) (flag : Ω → Prop) [DecidablePred flag]
    (g : Ω → ℝ) (h : Fin n → Ω → ℝ) (hh : ∀ i, (∑ j, h i j) = 1) (Q δ : ℝ) :
    (∑ ω : Fin n → Ω,
      if |((Finset.univ.filter (fun i => sel i = true ∧ flag (ω i))).card : ℝ) /
            Fintype.card {i // sel i = true} - Q| ≤ δ then
        ∏ i : Fin n, (if sel i then g (ω i) else h i (ω i)) else 0) =
      (∑ ωPE : {i // sel i = true} → Ω,
        if |((Finset.univ.filter (fun j => flag (ωPE j))).card : ℝ) /
              Fintype.card {i // sel i = true} - Q| ≤ δ then
          ∏ j : {i // sel i = true}, g (ωPE j) else 0) := by
  classical
  -- Reindex `ω : Fin n → Ω` as `(ωPE, ωkey)` via the selected / unselected subtype split.
  set p : Fin n → Prop := fun i => sel i = true with hp
  rw [← Equiv.sum_comp (Equiv.piEquivPiSubtypeProd p (fun _ => Ω)).symm]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro ωPE _
  -- Inner sum over the unselected part `ωkey =: y`.
  set E := (Equiv.piEquivPiSubtypeProd p (fun _ => Ω)).symm with hE
  -- On a selected index the reconstructed string reads `ωPE`; on an unselected index it reads `y`.
  -- The flag count over selected positions is independent of `y` and equals `#{j | flag (ωPE j)}`.
  have hcount : ∀ y : {i // ¬ p i} → Ω,
      (Finset.univ.filter (fun i => sel i = true ∧ flag (E (ωPE, y) i))).card =
        (Finset.univ.filter (fun j : {i // sel i = true} => flag (ωPE j))).card := by
    intro y
    refine Finset.card_bij'
      (fun i hi => (⟨i, (Finset.mem_filter.mp hi).2.1⟩ : {i // sel i = true}))
      (fun j _ => (j : Fin n)) ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hpi : p i := hi.2.1
      have heq : E (ωPE, y) i = ωPE ⟨i, hpi⟩ := by
        simp only [hE, Equiv.piEquivPiSubtypeProd_symm_apply, dite_eq_left hpi]
      rw [heq] at hi
      exact hi.2.2
    · intro j hj
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_filter]
      have hpj : p (j : Fin n) := j.2
      refine ⟨Finset.mem_univ _, j.2, ?_⟩
      have heq : E (ωPE, y) (j : Fin n) = ωPE ⟨(j : Fin n), hpj⟩ := by
        simp only [hE, Equiv.piEquivPiSubtypeProd_symm_apply, dite_eq_left hpj]
      rw [heq]
      convert hj.2 using 2
    · intro i hi; rfl
    · intro j hj; rfl
  -- The product factors as (selected product in `ωPE`) · (unselected product in `y`).
  have hprod : ∀ y : {i // ¬ p i} → Ω,
      (∏ i : Fin n, (if sel i = true then g (E (ωPE, y) i) else h i (E (ωPE, y) i))) =
        (∏ j : {i // sel i = true}, g (ωPE j)) *
          (∏ j : {i // ¬ p i}, h (j : Fin n) (y j)) := by
    intro y
    rw [← Fintype.prod_subtype_mul_prod_subtype p
          (fun i => if sel i = true then g (E (ωPE, y) i) else h i (E (ωPE, y) i))]
    congr 1
    · apply Finset.prod_congr rfl
      intro j _
      have hpj : p (j : Fin n) := j.2
      rw [ite_eq_left hpj]
      congr 1
      simp only [hE, Equiv.piEquivPiSubtypeProd_symm_apply, dite_eq_left hpj]
    · apply Finset.prod_congr rfl
      intro j _
      have hnpj : ¬ p (j : Fin n) := j.2
      rw [ite_eq_right hnpj]
      congr 1
      simp only [hE, Equiv.piEquivPiSubtypeProd_symm_apply, dite_eq_right hnpj]
  -- Rewrite the inner sum using the count and product facts.
  simp_rw [hcount, hprod]
  -- The indicator no longer depends on `y`; factor it and sum the free unselected product to one.
  by_cases hpe : |((Finset.univ.filter (fun j : {i // sel i = true} => flag (ωPE j))).card : ℝ) /
      Fintype.card {i // sel i = true} - Q| ≤ δ
  · simp_rw [ite_eq_left hpe]
    rw [← Finset.mul_sum]
    have hkey : (∑ y : {i // ¬ p i} → Ω, ∏ j : {i // ¬ p i}, h (j : Fin n) (y j)) = 1 := by
      rw [← Fintype.prod_sum (f := fun (j : {i // ¬ p i}) (k : Ω) => h (j : Fin n) k)]
      exact Finset.prod_eq_one fun j _ => hh (j : Fin n)
    rw [hkey, mul_one]
  · simp_rw [ite_eq_right hpe]
    simp

open scoped BigOperators in
/-- **Selected sub-sample split.**

For a PE selector `sel : Fin n → Bool`, PE-round weight `g`, key-round weight `h` with
`∑ h = 1`, the full band-filtered outcome sum over `ω : Fin n → Ω` — where the PE statistic
counts flagged positions among the **selected** rounds only (normalised by the PE sample size
`m = card {i // sel i = true}`) — equals the index-restricted band-filtered sum over the PE
subtype, with all key rounds summed out (contributing the free factor `(∑ h)^(n-m) = 1`).

The constant-key-weight instantiation of `selected_split_perRound`. -/
theorem selected_split {n : ℕ} {Ω : Type*} [Fintype Ω]
    (sel : Fin n → Bool) (flag : Ω → Prop) [DecidablePred flag]
    (g h : Ω → ℝ) (hh : (∑ j, h j) = 1) (Q δ : ℝ) :
    (∑ ω : Fin n → Ω,
      if |((Finset.univ.filter (fun i => sel i = true ∧ flag (ω i))).card : ℝ) /
            Fintype.card {i // sel i = true} - Q| ≤ δ then
        ∏ i : Fin n, (if sel i then g (ω i) else h (ω i)) else 0) =
      (∑ ωPE : {i // sel i = true} → Ω,
        if |((Finset.univ.filter (fun j => flag (ωPE j))).card : ℝ) /
              Fintype.card {i // sel i = true} - Q| ≤ δ then
          ∏ j : {i // sel i = true}, g (ωPE j) else 0) :=
  selected_split_perRound sel flag g (fun _ => h) (fun _ => hh) Q δ

open scoped BigOperators in
/-- **Selected flag-outcome pass-sum equals the binomial pass-sum, per-round unselected weights.**

The full sifted parameter-estimation reduction with per-round unselected weights: for a PE selector
`sel`, PE-round weight `g` summing to one, and per-round unselected weights `h i` each summing to
one, the band-filtered outcome sum over `ω : Fin n → Ω` — where the PE statistic counts flagged
positions among the **selected** rounds only, normalised by the PE sample size
`m = card {i // sel i = true}` — equals `binomialPassSum m Q δ (∑_{flag} g)`, the binomial pass-sum
over the `m` PE rounds at the PE-round flag rate `∑_{flag} g`.

This is the form the faithful two-basis PE test needs: applied with `sel` the `Z`-designated PE
rounds, the per-round `h` carries the `H ⊗ H`-rotated Born vector on the `X`-designated PE rounds
and the unrotated one on the key rounds.

Combines `selected_split_perRound` (free unselected-round factorisation) with the index-general
flag-outcome identity `flagOutcomePassSum_eq_binomialPassSum_index` on the PE subtype. -/
theorem selectedFlagOutcomePassSum_eq_binomialPassSum_perRound {n : ℕ} {Ω : Type*} [Fintype Ω]
    (sel : Fin n → Bool) (flag : Ω → Prop) [DecidablePred flag]
    (g : Ω → ℝ) (h : Fin n → Ω → ℝ) (hg : (∑ j, g j) = 1)
    (hh : ∀ i, (∑ j, h i j) = 1) (Q δ : ℝ) :
    (∑ ω : Fin n → Ω,
      if |((Finset.univ.filter (fun i => sel i = true ∧ flag (ω i))).card : ℝ) /
            Fintype.card {i // sel i = true} - Q| ≤ δ then
        ∏ i : Fin n, (if sel i then g (ω i) else h i (ω i)) else 0) =
      Math.Concentration.BinomialPassSum.binomialPassSum
        (Fintype.card {i // sel i = true}) Q δ
        (∑ j ∈ Finset.univ.filter (fun j => flag j), g j) := by
  classical
  rw [selected_split_perRound sel flag g h hh Q δ]
  exact flagOutcomePassSum_eq_binomialPassSum_index (ι := {i // sel i = true}) flag g hg Q δ

open scoped BigOperators in
/-- **Selected flag-outcome pass-sum equals the binomial pass-sum.**

The full sifted parameter-estimation reduction: for a PE selector `sel`, PE-round weight `g`,
key-round weight `h` (each summing to one), the band-filtered outcome sum over `ω : Fin n → Ω`
— where the PE statistic counts flagged positions among the **selected** rounds only, normalised
by the PE sample size `m = card {i // sel i = true}` — equals `binomialPassSum m Q δ (∑_{flag} g)`,
the binomial pass-sum over the `m` PE rounds at the PE-round flag rate `∑_{flag} g`.

The constant-key-weight instantiation of
`selectedFlagOutcomePassSum_eq_binomialPassSum_perRound`. -/
theorem selectedFlagOutcomePassSum_eq_binomialPassSum {n : ℕ} {Ω : Type*} [Fintype Ω]
    (sel : Fin n → Bool) (flag : Ω → Prop) [DecidablePred flag]
    (g h : Ω → ℝ) (hg : (∑ j, g j) = 1) (hh : (∑ j, h j) = 1) (Q δ : ℝ) :
    (∑ ω : Fin n → Ω,
      if |((Finset.univ.filter (fun i => sel i = true ∧ flag (ω i))).card : ℝ) /
            Fintype.card {i // sel i = true} - Q| ≤ δ then
        ∏ i : Fin n, (if sel i then g (ω i) else h (ω i)) else 0) =
      Math.Concentration.BinomialPassSum.binomialPassSum
        (Fintype.card {i // sel i = true}) Q δ
        (∑ j ∈ Finset.univ.filter (fun j => flag j), g j) :=
  selectedFlagOutcomePassSum_eq_binomialPassSum_perRound sel flag g (fun _ => h) hg
    (fun _ => hh) Q δ

open scoped BigOperators in
/-- **A pass-sum is monotone under weakening the pass predicate.**

For nonnegative weights `w`, if passing `P` forces passing `R`, then the `P`-indicator weighted sum
is at most the `R`-indicator weighted sum.  Used to bound a two-statistic (conjunctive) acceptance
event by either of its single-statistic relaxations. -/
theorem passSum_mono_of_imp {ι : Type*} [Fintype ι]
    (P R : ι → Prop) [DecidablePred P] [DecidablePred R]
    (w : ι → ℝ) (hw : ∀ x, 0 ≤ w x) (himp : ∀ x, P x → R x) :
    (∑ x, if P x then w x else 0) ≤ (∑ x, if R x then w x else 0) := by
  refine Finset.sum_le_sum ?_
  intro x _
  by_cases hP : P x
  · rw [ite_eq_left hP, ite_eq_left (himp x hP)]
  · rw [ite_eq_right hP]
    split_ifs with hR
    · exact hw x
    · exact le_refl 0

end Math.Concentration.SelectedBinomialPassSum
