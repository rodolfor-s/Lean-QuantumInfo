import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-! # Coordinate Counts -/


open Finset

namespace Fintype

variable {ι α R : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [CommSemiring R]

/-- Strings whose `p`-coordinates are exactly `t` and whose `q`-coordinates are exactly `s`, for
mutually exclusive `p`, `q` and disjoint `t`, `s`, form a product of coordinatewise alphabets, so
their total product weight factors coordinatewise. -/
theorem sum_prod_filter_eq_and_filter_eq (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hpq : ∀ a, p a → ¬q a) (w : α → R) {t s : Finset ι} (hts : Disjoint t s) :
    ∑ ω : ι → α with ({i | p (ω i)} : Finset ι) = t ∧ ({i | q (ω i)} : Finset ι) = s,
        ∏ i, w (ω i) =
      (∑ a with p a, w a) ^ #t * (∑ a with q a, w a) ^ #s *
        (∑ a with ¬p a ∧ ¬q a, w a) ^ #(t ∪ s)ᶜ := by
  classical
  let T : ι → Finset α := fun i =>
    if i ∈ t then ({a | p a} : Finset α) else if i ∈ s then ({a | q a} : Finset α)
    else ({a | ¬p a ∧ ¬q a} : Finset α)
  have hfilter :
      ({ω : ι → α | ({i | p (ω i)} : Finset ι) = t ∧ ({i | q (ω i)} : Finset ι) = s} :
        Finset (ι → α)) = piFinset T := by
    ext ω
    simp only [mem_filter, mem_univ, true_and, mem_piFinset, T]
    constructor
    · rintro ⟨hp, hq⟩ i
      have hpi : p (ω i) ↔ i ∈ t := by rw [← hp]; simp
      have hqi : q (ω i) ↔ i ∈ s := by rw [← hq]; simp
      split_ifs with hit his
      · simpa using hpi.mpr hit
      · simpa using hqi.mpr his
      · simpa using ⟨mt hpi.mp hit, mt hqi.mp his⟩
    · intro h
      have hmem : ∀ i, (p (ω i) ↔ i ∈ t) ∧ (q (ω i) ↔ i ∈ s) := by
        intro i
        have hi := h i
        split_ifs at hi with hit his
        · have hp : p (ω i) := by simpa using hi
          exact ⟨iff_of_true hp hit,
            iff_of_false (hpq _ hp) fun his => disjoint_left.mp hts hit his⟩
        · have hq : q (ω i) := by simpa using hi
          exact ⟨iff_of_false (fun hp => hpq _ hp hq) hit, iff_of_true hq his⟩
        · have hr : ¬p (ω i) ∧ ¬q (ω i) := by simpa using hi
          exact ⟨iff_of_false hr.1 hit, iff_of_false hr.2 his⟩
      exact ⟨by ext i; simpa using (hmem i).1, by ext i; simpa using (hmem i).2⟩
  rw [hfilter, ← Finset.prod_univ_sum]
  have hT : ∀ i, ∑ a ∈ T i, w a =
      if i ∈ t then ∑ a with p a, w a
      else if i ∈ s then ∑ a with q a, w a else ∑ a with ¬p a ∧ ¬q a, w a := by
    intro i
    simp only [T]
    split_ifs <;> rfl
  simp_rw [hT]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have ht : ({i ∈ univ | i ∈ t} : Finset ι) = t := by ext i; simp
  have hs : ({i ∈ {i ∈ univ | i ∉ t} | i ∈ s} : Finset ι) = s := by
    ext i
    simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
    exact fun his hit => disjoint_left.mp hts hit his
  have hr : ({i ∈ {i ∈ univ | i ∉ t} | i ∉ s} : Finset ι) = (t ∪ s)ᶜ := by
    ext i
    simp
  rw [ht, hs, hr, mul_assoc]

/-- **Trinomial law of two coordinate counts.**  For mutually exclusive predicates `p` and `q`,
the strings with exactly `k` coordinates in `p` and exactly `l` coordinates in `q` have total
product weight
`C(|ι|, k) * C(|ι| - k, l) * (∑_p w) ^ k * (∑_q w) ^ l * (∑_{¬p ∧ ¬q} w) ^ (|ι| - k - l)`.

This holds for all `k` and `l`; the coefficient vanishes unless `k + l ≤ |ι|`. -/
theorem sum_prod_filter_card_eq_and_card_eq (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hpq : ∀ a, p a → ¬q a) (w : α → R) (k l : ℕ) :
    ∑ ω : ι → α with #{i | p (ω i)} = k ∧ #{i | q (ω i)} = l, ∏ i, w (ω i) =
      (card ι).choose k * (card ι - k).choose l * (∑ a with p a, w a) ^ k *
        (∑ a with q a, w a) ^ l * (∑ a with ¬p a ∧ ¬q a, w a) ^ (card ι - k - l) := by
  classical
  set Wp := ∑ a with p a, w a
  set Wq := ∑ a with q a, w a
  set Wr := ∑ a with ¬p a ∧ ¬q a, w a
  let P : (ι → α) → Finset ι := fun ω => {i | p (ω i)}
  let Q : (ι → α) → Finset ι := fun ω => {i | q (ω i)}
  -- Stage 1: fibre over the exact set of `p`-coordinates.
  have hmaps₁ : ∀ ω ∈ ({ω : ι → α | #(P ω) = k ∧ #(Q ω) = l} : Finset (ι → α)),
      P ω ∈ powersetCard k (univ : Finset ι) := by
    intro ω hω
    exact mem_powersetCard.mpr ⟨subset_univ _, (mem_filter.mp hω).2.1⟩
  change ∑ ω ∈ ({ω : ι → α | #(P ω) = k ∧ #(Q ω) = l} : Finset (ι → α)), ∏ i, w (ω i) = _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps₁]
  have hfibre : ∀ t ∈ powersetCard k (univ : Finset ι),
      ∑ ω ∈ ({ω : ι → α | #(P ω) = k ∧ #(Q ω) = l} : Finset (ι → α)) with P ω = t,
          ∏ i, w (ω i) =
        (card ι - k).choose l * (Wp ^ k * Wq ^ l * Wr ^ (card ι - k - l)) := by
    intro t ht
    have htk : #t = k := (mem_powersetCard.mp ht).2
    have hfilter :
        ({ω ∈ ({ω : ι → α | #(P ω) = k ∧ #(Q ω) = l} : Finset (ι → α)) | P ω = t}) =
          ({ω : ι → α | P ω = t ∧ #(Q ω) = l} : Finset (ι → α)) := by
      ext ω
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨⟨-, hl⟩, hP⟩
        exact ⟨hP, hl⟩
      · rintro ⟨hP, hl⟩
        exact ⟨⟨hP ▸ htk, hl⟩, hP⟩
    rw [hfilter]
    -- Stage 2: fibre over the exact set of `q`-coordinates, which avoids `t`.
    have hmaps₂ : ∀ ω ∈ ({ω : ι → α | P ω = t ∧ #(Q ω) = l} : Finset (ι → α)),
        Q ω ∈ powersetCard l tᶜ := by
      intro ω hω
      obtain ⟨hP, hl⟩ := (mem_filter.mp hω).2
      refine mem_powersetCard.mpr ⟨?_, hl⟩
      intro i hi
      rw [mem_compl, ← hP]
      simp only [P, Q, mem_filter, mem_univ, true_and] at hi ⊢
      exact fun hp => hpq _ hp hi
    rw [← Finset.sum_fiberwise_of_maps_to hmaps₂]
    have hinner : ∀ s ∈ powersetCard l tᶜ,
        ∑ ω ∈ ({ω : ι → α | P ω = t ∧ #(Q ω) = l} : Finset (ι → α)) with Q ω = s,
            ∏ i, w (ω i) =
          Wp ^ k * Wq ^ l * Wr ^ (card ι - k - l) := by
      intro s hs
      obtain ⟨hst, hsl⟩ := mem_powersetCard.mp hs
      have hdisj : Disjoint t s := disjoint_left.mpr fun i hit his => mem_compl.mp (hst his) hit
      have hfilter₂ :
          ({ω ∈ ({ω : ι → α | P ω = t ∧ #(Q ω) = l} : Finset (ι → α)) | Q ω = s}) =
            ({ω : ι → α | P ω = t ∧ Q ω = s} : Finset (ι → α)) := by
        ext ω
        simp only [mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨⟨hP, -⟩, hQ⟩
          exact ⟨hP, hQ⟩
        · rintro ⟨hP, hQ⟩
          exact ⟨⟨hP, hQ ▸ hsl⟩, hQ⟩
      rw [hfilter₂]
      have hcard : #(t ∪ s)ᶜ = card ι - k - l := by
        rw [Finset.card_compl, Finset.card_union_of_disjoint hdisj, htk, hsl, Nat.sub_sub]
      simpa only [htk, hsl, hcard] using
        sum_prod_filter_eq_and_filter_eq (ι := ι) p q hpq w hdisj
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_powersetCard,
      Finset.card_compl, htk, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hfibre, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    nsmul_eq_mul]
  ring

/-- **Binomial law of a coordinate count.**  The strings with exactly `k` coordinates in `p` have
total product weight `C(|ι|, k) * (∑_p w) ^ k * (∑_{¬p} w) ^ (|ι| - k)`.

This holds for all `k`; the coefficient vanishes when `|ι| < k`. -/
theorem sum_prod_filter_card_eq (p : α → Prop) [DecidablePred p] (w : α → R) (k : ℕ) :
    ∑ ω : ι → α with #{i | p (ω i)} = k, ∏ i, w (ω i) =
      (card ι).choose k * (∑ a with p a, w a) ^ k * (∑ a with ¬p a, w a) ^ (card ι - k) := by
  classical
  have h := sum_prod_filter_card_eq_and_card_eq (ι := ι) p (fun _ => False)
    (fun _ _ h => h) w k 0
  simpa using h

/-- A coordinatewise event in a finite product law has the product of its coordinate masses. -/
lemma sum_ite_forall_prod {I O R : Type*} [CommSemiring R] [Fintype I] [DecidableEq I] [Fintype O]
    (w : I → O → R) (P : I → O → Prop) [∀ i, DecidablePred (P i)] :
    (∑ x : I → O, if ∀ i, P i (x i) then ∏ i, w i (x i) else 0) =
      ∏ i, ∑ k, if P i k then w i k else 0 := by
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact Fintype.prod_ite_zero.symm

/-- Restricting coordinates of a normalized product law leaves the other coordinates normalized. -/
lemma sum_ite_forall_subtype_prod {I O R : Type*} [CommSemiring R]
    [Fintype I] [DecidableEq I] [Fintype O]
    (s : I → Prop) [DecidablePred s] (w : I → O → R) (hw : ∀ i, ∑ k, w i k = 1)
    (P : {i // s i} → O → Prop) [∀ i, DecidablePred (P i)] :
    (∑ x : I → O, if ∀ i : {i // s i}, P i (x i) then ∏ i, w i (x i) else 0) =
      ∏ i : {i // s i}, ∑ k, if P i k then w i k else 0 := by
  classical
  have hgate (x : I → O) : (∀ i : {i // s i}, P i (x i)) ↔
      ∀ i, ∀ h : s i, P ⟨i, h⟩ (x i) := by simp
  simp_rw [hgate]
  rw [sum_ite_forall_prod w (fun i k => ∀ h : s i, P ⟨i, h⟩ k)]
  rw [← Fintype.prod_subtype_mul_prod_subtype s]
  have hyes (i : {i // s i}) (k : O) : (∀ h : s i, P ⟨i, h⟩ k) ↔ P i k := by
    simp [i.property]
  have hno (i : {i // ¬s i}) (k : O) : (∀ h : s i, P ⟨i, h⟩ k) := by
    intro h
    exact (i.property h).elim
  simp only [hyes, hno, implies_true, ite_true, hw, Finset.prod_const_one, mul_one]

end Fintype
