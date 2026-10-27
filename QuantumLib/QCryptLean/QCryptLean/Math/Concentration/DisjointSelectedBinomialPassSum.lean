import QCryptLean.Math.Concentration.BinomialPassSum
import QCryptLean.Math.Concentration.SelectedBinomialPassSum

/-!
# Two disjoint sub-samples: the pass-sum of a conjunctive test is a PRODUCT

`selectedFlagOutcomePassSum_eq_binomialPassSum` reduces a **single**-statistic band test read off
one selected sub-sample to `binomialPassSum`, marginalising every unselected round away.  A
two-basis
parameter-estimation test is *conjunctive*: it reads one band statistic off one sub-sample and a
second band statistic off a **disjoint** second sub-sample, and accepts only if both bands hold.
Relaxing such a test to either conjunct alone (`passSum_mono_of_imp`) gives one-sided **upper**
bounds on the accept mass; it cannot give a lower bound, because dropping a conjunct only enlarges
the accept set.

This file supplies the exact evaluation instead of a relaxation: because the two sub-samples are
disjoint, the two band indicators depend on disjoint blocks of the outcome string, so the accept
mass **factorises** into the product of the two binomial pass masses.  Equality gives the lower
bound and the upper bounds at once.

## Main statements

- `blockSplit`: the general two-block factorisation.  For any per-round weights and any pair of
  predicates `A`, `B` reading only the `p`-block and only the `¬p`-block, the `A ∧ B`-filtered
  outcome sum is the product of the `A`-filtered block sum and the `B`-filtered block sum.  Pure
  reindexing (`Equiv.piEquivPiSubtypeProd`); no normalisation hypothesis.
- `blockSplit_of_rest_sum_one`: the one-block corollary — with `B` trivial and the complement
  weights summing to one, the complement block integrates out to `1`.  The index-general form of
  `selected_split_perRound`.
- `subtype_filter_card`: counting a predicate inside a subtype is counting the conjunction.
- `disjointSelectedFlagOutcomePassSum_eq_binomialPassSum_mul` : the factorization identity. For two
  **disjoint**
  selectors `sel₁`, `sel₂` carrying per-round weight vectors `g₁`, `g₂`, the two-band conjunctive
  pass-sum equals `binomialPassSum m₁ Q δ (∑_{flag} g₁) · binomialPassSum m₂ Q δ (∑_{flag} g₂)`.

References: Renner (2005), `arXiv:quant-ph/0512258v2`, §6.5 (two-statistic parameter estimation on
disjoint sub-samples); the combinatorics is basis-agnostic.
-/

namespace Math.Concentration.SelectedBinomialPassSum

open scoped BigOperators

/-- **Counting inside a subtype is counting the conjunction.**

`#{j : {i // p i} | r j} = #{i | p i ∧ r i}`, by the subtype-of-subtype equivalence
`Equiv.subtypeSubtypeEquivSubtypeInter`.  The bookkeeping lemma that converts a band statistic
stated on a selected sub-population into one stated on the ambient index type. -/
theorem subtype_filter_card {ι : Type*} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    (r : ι → Prop) [DecidablePred r] :
    (Finset.univ.filter (fun j : {i // p i} => r (j : ι))).card =
      (Finset.univ.filter (fun i : ι => p i ∧ r i)).card := by
  classical
  rw [← Fintype.card_subtype (fun j : {i // p i} => r (j : ι)),
    ← Fintype.card_subtype (fun i : ι => p i ∧ r i)]
  exact Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter p r)

open scoped BigOperators in
/-- **Two-block factorisation of a conjunctive pass-sum.**

Split the round index `ι` into the `p`-block and its complement.  If the accept predicate is a
conjunction `A ∧ B` where `A` reads only the `p`-block of the outcome string and `B` reads only the
complement block, then the accept-filtered weighted sum factorises:

`∑_ω [A(ω|_p) ∧ B(ω|_¬p)] ∏_i w i (ω i) = (∑_u [A u] ∏_{p} w) · (∑_v [B v] ∏_{¬p} w)`.

Pure reindexing along `Equiv.piEquivPiSubtypeProd` plus `Fintype.prod_subtype_mul_prod_subtype`; no
hypothesis on the weights at all (they need not be nonnegative or normalised).

This is what a *conjunctive* two-sub-sample test needs and what `passSum_mono_of_imp` cannot give:
the latter drops a conjunct and so only bounds the accept mass from above. -/
theorem blockSplit {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : Type*} [Fintype Ω]
    (p : ι → Prop) [DecidablePred p] (w : ι → Ω → ℝ)
    (A : ({i // p i} → Ω) → Prop) [DecidablePred A]
    (B : ({i // ¬ p i} → Ω) → Prop) [DecidablePred B] :
    (∑ ω : ι → Ω,
        if A (fun j : {i // p i} => ω (j : ι)) ∧ B (fun j : {i // ¬ p i} => ω (j : ι)) then
          ∏ i : ι, w i (ω i) else 0) =
      (∑ u : {i // p i} → Ω, if A u then ∏ j : {i // p i}, w (j : ι) (u j) else 0) *
        (∑ v : {i // ¬ p i} → Ω, if B v then ∏ j : {i // ¬ p i}, w (j : ι) (v j) else 0) := by
  classical
  rw [← Equiv.sum_comp (Equiv.piEquivPiSubtypeProd p (fun _ => Ω)).symm]
  rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  set E := (Equiv.piEquivPiSubtypeProd p (fun _ => Ω)).symm with hE
  have hu : (fun j : {i // p i} => E (u, v) (j : ι)) = u := by
    funext j
    simp only [hE, Equiv.piEquivPiSubtypeProd_symm_apply, dite_eq_left j.2]
  have hv : (fun j : {i // ¬ p i} => E (u, v) (j : ι)) = v := by
    funext j
    simp only [hE, Equiv.piEquivPiSubtypeProd_symm_apply, dite_eq_right j.2]
  have hprod : (∏ i : ι, w i (E (u, v) i)) =
      (∏ j : {i // p i}, w (j : ι) (u j)) * (∏ j : {i // ¬ p i}, w (j : ι) (v j)) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype p (fun i => w i (E (u, v) i))]
    congr 1
    · refine Finset.prod_congr rfl fun j _ => ?_
      congr 1
      simp only [hE, Equiv.piEquivPiSubtypeProd_symm_apply, dite_eq_left j.2]
    · refine Finset.prod_congr rfl fun j _ => ?_
      congr 1
      simp only [hE, Equiv.piEquivPiSubtypeProd_symm_apply, dite_eq_right j.2]
  rw [hu, hv, hprod]
  by_cases hA : A u <;> by_cases hB : B v <;> simp [hA, hB]

open scoped BigOperators in
/-- **One-block corollary: the complement block integrates out.**

The `B := True` case of `blockSplit`, with the complement-round weights summing to one: the whole
complement block contributes the free factor `∏_{¬p} (∑_j w i j) = 1`.

This is the index-general form of `selected_split_perRound`, and additionally allows an arbitrary
predicate `A` on the selected block rather than only a band on a flag count. -/
theorem blockSplit_of_rest_sum_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : Type*} [Fintype Ω]
    (p : ι → Prop) [DecidablePred p] (w : ι → Ω → ℝ)
    (hw : ∀ i, ¬ p i → (∑ j, w i j) = 1)
    (A : ({i // p i} → Ω) → Prop) [DecidablePred A] :
    (∑ ω : ι → Ω,
        if A (fun j : {i // p i} => ω (j : ι)) then ∏ i : ι, w i (ω i) else 0) =
      ∑ u : {i // p i} → Ω, if A u then ∏ j : {i // p i}, w (j : ι) (u j) else 0 := by
  classical
  have h := blockSplit p w A (fun _ => True)
  simp only [and_true, ite_true] at h
  rw [h]
  have hrest : (∑ v : {i // ¬ p i} → Ω, ∏ j : {i // ¬ p i}, w (j : ι) (v j)) = 1 := by
    rw [← Fintype.prod_sum (f := fun (j : {i // ¬ p i}) (k : Ω) => w (j : ι) k)]
    exact Finset.prod_eq_one fun j _ => hw (j : ι) j.2
  rw [hrest, mul_one]

open scoped BigOperators in
/-- **Disjoint two-sub-sample conjunctive pass-sum is a PRODUCT of binomial pass-sums.**

Let `sel₁`, `sel₂` be **disjoint** selectors on the round index `ι` (`hdisj`), let the rounds they
select carry the per-round weight vectors `g₁` and `g₂` respectively (`hw₁`, `hw₂`), and let every
round's weight vector be normalised (`hw`).  Then the mass of the outcome strings passing BOTH
bands — the `sel₁`-flag fraction within `δ` of `Q` **and** the `sel₂`-flag fraction within `δ` of
`Q` — is exactly

`binomialPassSum m₁ Q δ (∑_{flag} g₁) · binomialPassSum m₂ Q δ (∑_{flag} g₂)`,

at the sub-sample sizes `m₁ = card {i // sel₁ i}`, `m₂ = card {i // sel₂ i}`.

Disjointness is what makes this an equality rather than an inequality: the two band statistics then
read disjoint blocks of `ω`, so `blockSplit` applies with `A` the `sel₁`-band and `B` the
`sel₂`-band, after which each block is evaluated by
`flagOutcomePassSum_eq_binomialPassSum_index` and the rounds neither selector reads integrate out
by `blockSplit_of_rest_sum_one`.

The product form both dominates and is dominated by each single-band relaxation, so it strictly
strengthens the pair of one-sided bounds obtained from `passSum_mono_of_imp`. -/
theorem disjointSelectedFlagOutcomePassSum_eq_binomialPassSum_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : Type*} [Fintype Ω]
    (sel₁ sel₂ : ι → Bool) (hdisj : ∀ i, sel₂ i = true → sel₁ i = false)
    (flag : Ω → Prop) [DecidablePred flag]
    (g₁ g₂ : Ω → ℝ) (w : ι → Ω → ℝ)
    (hg₁ : (∑ j, g₁ j) = 1) (hg₂ : (∑ j, g₂ j) = 1) (hw : ∀ i, (∑ j, w i j) = 1)
    (hw₁ : ∀ i, sel₁ i = true → w i = g₁) (hw₂ : ∀ i, sel₂ i = true → w i = g₂)
    (Q δ : ℝ) :
    (∑ ω : ι → Ω,
        if |((Finset.univ.filter (fun i => sel₁ i = true ∧ flag (ω i))).card : ℝ) /
              Fintype.card {i // sel₁ i = true} - Q| ≤ δ ∧
            |((Finset.univ.filter (fun i => sel₂ i = true ∧ flag (ω i))).card : ℝ) /
              Fintype.card {i // sel₂ i = true} - Q| ≤ δ then
          ∏ i : ι, w i (ω i) else 0) =
      Math.Concentration.BinomialPassSum.binomialPassSum
          (Fintype.card {i // sel₁ i = true}) Q δ
          (∑ j ∈ Finset.univ.filter (fun j => flag j), g₁ j) *
        Math.Concentration.BinomialPassSum.binomialPassSum
          (Fintype.card {i // sel₂ i = true}) Q δ
          (∑ j ∈ Finset.univ.filter (fun j => flag j), g₂ j) := by
  classical
  -- Rewrite both flag counts as counts inside the two blocks the `blockSplit` produces.
  have hc₁ : ∀ ω : ι → Ω,
      (Finset.univ.filter (fun i => sel₁ i = true ∧ flag (ω i))).card =
        (Finset.univ.filter (fun j : {i // sel₁ i = true} => flag (ω (j : ι)))).card :=
    fun ω => (subtype_filter_card (fun i => sel₁ i = true) (fun i => flag (ω i))).symm
  have hc₂ : ∀ ω : ι → Ω,
      (Finset.univ.filter (fun i => sel₂ i = true ∧ flag (ω i))).card =
        (Finset.univ.filter
          (fun j : {i // ¬ (sel₁ i = true)} => sel₂ (j : ι) = true ∧ flag (ω (j : ι)))).card := by
    intro ω
    rw [subtype_filter_card (fun i => ¬ (sel₁ i = true)) (fun i => sel₂ i = true ∧ flag (ω i))]
    congr 1
    refine Finset.filter_congr fun i _ => ?_
    constructor
    · rintro ⟨h₂, hf⟩; exact ⟨by simp [hdisj i h₂], h₂, hf⟩
    · rintro ⟨-, h₂, hf⟩; exact ⟨h₂, hf⟩
  simp_rw [hc₁, hc₂]
  -- Split off the `sel₁` block.
  rw [blockSplit (fun i => sel₁ i = true) w
    (fun u => |((Finset.univ.filter (fun j : {i // sel₁ i = true} => flag (u j))).card : ℝ) /
      Fintype.card {i // sel₁ i = true} - Q| ≤ δ)
    (fun v => |((Finset.univ.filter (fun j : {i // ¬ (sel₁ i = true)} =>
        sel₂ (j : ι) = true ∧ flag (v j))).card : ℝ) /
      Fintype.card {i // sel₂ i = true} - Q| ≤ δ)]
  congr 1
  · -- The `sel₁` block: its rounds all carry the weight vector `g₁`.
    rw [show (fun (u : {i // sel₁ i = true} → Ω) =>
          if |((Finset.univ.filter (fun j : {i // sel₁ i = true} => flag (u j))).card : ℝ) /
              Fintype.card {i // sel₁ i = true} - Q| ≤ δ then
            ∏ j : {i // sel₁ i = true}, w (j : ι) (u j) else 0) =
        (fun (u : {i // sel₁ i = true} → Ω) =>
          if |((Finset.univ.filter (fun j : {i // sel₁ i = true} => flag (u j))).card : ℝ) /
              Fintype.card {i // sel₁ i = true} - Q| ≤ δ then
            ∏ j : {i // sel₁ i = true}, g₁ (u j) else 0) from by
      funext u
      congr 1
      exact Finset.prod_congr rfl fun j _ => by rw [hw₁ (j : ι) j.2]]
    exact flagOutcomePassSum_eq_binomialPassSum_index (ι := {i // sel₁ i = true}) flag g₁ hg₁ Q δ
  · -- The complement block: split off `sel₂` inside it; the remaining rounds integrate out.
    have hcard : Fintype.card {j : {i // ¬ (sel₁ i = true)} // sel₂ (j : ι) = true} =
        Fintype.card {i // sel₂ i = true} := by
      rw [Fintype.card_subtype (fun j : {i // ¬ (sel₁ i = true)} => sel₂ (j : ι) = true),
        subtype_filter_card (fun i => ¬ (sel₁ i = true)) (fun i => sel₂ i = true),
        Fintype.card_subtype (fun i => sel₂ i = true)]
      congr 1
      refine Finset.filter_congr fun i _ => ?_
      constructor
      · rintro ⟨-, h₂⟩; exact h₂
      · intro h₂; exact ⟨by simp [hdisj i h₂], h₂⟩
    have hc₃ : ∀ v : {i // ¬ (sel₁ i = true)} → Ω,
        (Finset.univ.filter
            (fun j : {i // ¬ (sel₁ i = true)} => sel₂ (j : ι) = true ∧ flag (v j))).card =
          (Finset.univ.filter
            (fun j' : {j : {i // ¬ (sel₁ i = true)} // sel₂ (j : ι) = true} =>
              flag (v (j' : {i // ¬ (sel₁ i = true)})))).card :=
      fun v => (subtype_filter_card (fun j : {i // ¬ (sel₁ i = true)} => sel₂ (j : ι) = true)
        (fun j => flag (v j))).symm
    simp_rw [hc₃, ← hcard]
    rw [blockSplit_of_rest_sum_one (fun j : {i // ¬ (sel₁ i = true)} => sel₂ (j : ι) = true)
      (fun j => w (j : ι)) (fun j _ => hw (j : ι))
      (fun u => |((Finset.univ.filter
          (fun j' : {j : {i // ¬ (sel₁ i = true)} // sel₂ (j : ι) = true} => flag (u j'))).card : ℝ)
              /
        Fintype.card {j : {i // ¬ (sel₁ i = true)} // sel₂ (j : ι) = true} - Q| ≤ δ)]
    rw [show (fun (u : {j : {i // ¬ (sel₁ i = true)} // sel₂ (j : ι) = true} → Ω) =>
          if |((Finset.univ.filter
              (fun j' : {j : {i // ¬ (sel₁ i = true)} // sel₂ (j : ι) = true} =>
                flag (u j'))).card : ℝ) /
              Fintype.card {j : {i // ¬ (sel₁ i = true)} // sel₂ (j : ι) = true} - Q| ≤ δ then
            ∏ j' : {j : {i // ¬ (sel₁ i = true)} // sel₂ (j : ι) = true},
              w ((j' : {i // ¬ (sel₁ i = true)}) : ι) (u j') else 0) =
        (fun (u : {j : {i // ¬ (sel₁ i = true)} // sel₂ (j : ι) = true} → Ω) =>
          if |((Finset.univ.filter
              (fun j' : {j : {i // ¬ (sel₁ i = true)} // sel₂ (j : ι) = true} =>
                flag (u j'))).card : ℝ) /
              Fintype.card {j : {i // ¬ (sel₁ i = true)} // sel₂ (j : ι) = true} - Q| ≤ δ then
            ∏ j' : {j : {i // ¬ (sel₁ i = true)} // sel₂ (j : ι) = true}, g₂ (u j') else 0) from by
      funext u
      congr 1
      exact Finset.prod_congr rfl fun j' _ => by rw [hw₂ _ j'.2]]
    exact flagOutcomePassSum_eq_binomialPassSum_index
      (ι := {j : {i // ¬ (sel₁ i = true)} // sel₂ (j : ι) = true}) flag g₂ hg₂ Q δ

end Math.Concentration.SelectedBinomialPassSum
