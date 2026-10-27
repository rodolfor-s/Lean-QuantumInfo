import Mathlib.Data.Set.PowersetCard
import QCryptLean.Math.Concentration.HypergeometricTail.UpperTail
import QCryptLean.Math.Probability.SamplingConcentration

/-!
# Finite Serfling Counting Core — image subsets, hypergeometric counts, injection tail

Counting identity for Serfling's sampling-without-replacement inequality over
the uniform type of injections `Fin n ↪ Fin N`. The file reduces injections to
unordered image subsets, classifies fixed-size subsets by success count, and
then applies the hypergeometric tail bound from `UpperTail.lean`.

## Main definitions
- `populationSuccessCount`: number of successful population entries.
- `sampleSuccessCount`: number of sampled successes through an injection.
- `BadImageSubset`: bad unordered image subset predicate.

## Main statements
- `finite_powersetCard_serfling_upper_tail`: upper-tail bound for unordered
  fixed-size subsets.
- `finite_injection_serfling_upper_tail`: upper-tail bound for uniformly sampled
  injections.
-/

open scoped BigOperators
open Math.Probability.SamplingConcentration

namespace Math.Concentration.Serfling

/-- Number of `true` entries in a finite binary population. -/
def populationSuccessCount {N : ℕ} (seq : Fin N → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin N => seq i)).card

/-- Number of `true` entries seen by an injection sample. -/
def sampleSuccessCount {N n : ℕ} (seq : Fin N → Bool) (f : Fin n ↪ Fin N) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => seq (f i))).card

/-- The image subset of an injection sample. -/
def sampleImage {N n : ℕ} (f : Fin n ↪ Fin N) : Finset (Fin N) :=
  Finset.univ.map f

/-- Number of successful population positions in an injection sample image. -/
def sampleImageSuccessCount {N n : ℕ} (seq : Fin N → Bool) (f : Fin n ↪ Fin N) :
    ℕ :=
  ((sampleImage f).filter (fun i : Fin N => seq i)).card

/-- The population frequency is the success count divided by the population size. -/
lemma populationFreq_eq_successCount {N : ℕ} (seq : Fin N → Bool) :
    populationFreq seq = (populationSuccessCount seq : ℝ) / N := by
  unfold populationFreq populationSuccessCount
  simp [Finset.sum_boole]

/-- The empirical frequency is the sample success count divided by the sample size. -/
lemma empiricalFreqOf_eq_sampleSuccessCount {N n : ℕ} (seq : Fin N → Bool)
    (f : Fin n ↪ Fin N) :
    empiricalFreqOf seq f = (sampleSuccessCount seq f : ℝ) / n := by
  unfold empiricalFreqOf sampleSuccessCount
  simp [Finset.sum_boole]

/-- The sample image has exactly the requested sample size. -/
@[simp]
lemma sampleImage_card {N n : ℕ} (f : Fin n ↪ Fin N) :
    (sampleImage f).card = n := by
  unfold sampleImage
  simp

/-- Membership in the sample image is the same as being hit by the injection. -/
lemma mem_sampleImage_iff {N n : ℕ} (f : Fin n ↪ Fin N) (j : Fin N) :
    j ∈ sampleImage f ↔ ∃ i : Fin n, f i = j := by
  unfold sampleImage
  simp

/-- Counting successes through the domain agrees with counting them in the image subset. -/
lemma sampleSuccessCount_eq_imageSuccessCount {N n : ℕ} (seq : Fin N → Bool)
    (f : Fin n ↪ Fin N) :
    sampleSuccessCount seq f = sampleImageSuccessCount seq f := by
  unfold sampleSuccessCount sampleImageSuccessCount sampleImage
  rw [← Finset.card_map f]
  congr 1
  ext j
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, hseq, hfj⟩
    exact ⟨⟨a, hfj⟩, by simpa [← hfj] using hseq⟩
  · rintro ⟨⟨a, hfj⟩, hseq⟩
    exact ⟨a, by simpa [hfj] using hseq, hfj⟩

/-- The denominator over injections factors into image subsets and their orderings. -/
lemma card_fin_embedding_eq_factorial_mul_powersetCard (N n : ℕ) :
    Fintype.card (Fin n ↪ Fin N) =
      n.factorial * Nat.card (Set.powersetCard (Fin N) n) := by
  rw [Fintype.card_embedding_eq, Set.powersetCard.card]
  simp [Nat.descFactorial_eq_factorial_mul_choose]

/-- There are `n!` ways to order a fixed `n`-element image subset. -/
lemma card_equiv_fin_powersetCard {N n : ℕ} (s : Set.powersetCard (Fin N) n) :
    Fintype.card (Fin n ≃ s) = n.factorial := by
  have hs : Fintype.card s = n := by
    simp [Set.powersetCard.card_eq s]
  let es : Fin n ≃ s := (Fintype.equivFinOfCardEq hs).symm
  simpa [Fintype.card_fin] using (Fintype.card_equiv es)

/-- The fiber of `Set.powersetCard.ofFinEmb` over a fixed image subset has size `n!`. -/
lemma card_ofFinEmb_fiber (N n : ℕ) (s : Set.powersetCard (Fin N) n) :
    Fintype.card
        {f : Fin n ↪ Fin N // Set.powersetCard.ofFinEmb n (Fin N) f = s} =
      n.factorial := by
  let e :
      {f : Fin n ↪ Fin N // Set.powersetCard.ofFinEmb n (Fin N) f = s} ≃
        (Fin n ≃ s) :=
    { toFun := fun hf =>
        Equiv.ofBijective
          (fun i : Fin n =>
            (⟨hf.1 i, by
              have hmem :
                  hf.1 i ∈
                    (Set.powersetCard.ofFinEmb n (Fin N) hf.1 : Finset (Fin N)) := by
                rw [Set.powersetCard.val_ofFinEmb]
                exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
              rwa [hf.2] at hmem⟩ : s))
          ⟨by
            intro a b hab
            apply hf.1.injective
            exact congrArg Subtype.val hab,
          by
            intro x
            have hx :
                (x : Fin N) ∈ Set.powersetCard.ofFinEmb n (Fin N) hf.1 := by
              rw [hf.2]
              exact x.2
            rw [Set.powersetCard.mem_ofFinEmb_iff_mem_range] at hx
            rcases hx with ⟨i, hi⟩
            exact ⟨i, Subtype.ext hi⟩⟩
      invFun := fun e =>
        ⟨{ toFun := fun i => (e i : Fin N)
           inj' := by
             intro a b hab
             apply e.injective
             exact Subtype.ext hab }, by
          apply Subtype.ext
          ext x
          simp only [Set.powersetCard.val_ofFinEmb, Finset.mem_map, Finset.mem_univ,
            true_and]
          constructor
          · rintro ⟨i, rfl⟩
            exact (e i).2
          · intro hx
            refine ⟨e.symm ⟨x, hx⟩, ?_⟩
            exact congrArg Subtype.val (Equiv.apply_symm_apply e ⟨x, hx⟩)⟩
      left_inv := by
        intro hf
        ext i
        rfl
      right_inv := by
        intro e
        ext i
        rfl }
  calc
    Fintype.card
        {f : Fin n ↪ Fin N // Set.powersetCard.ofFinEmb n (Fin N) f = s} =
        Fintype.card (Fin n ≃ s) := Fintype.card_congr e
    _ = n.factorial := card_equiv_fin_powersetCard s

/-- Pulling a predicate on image subsets back to injections multiplies its count by `n!`. -/
lemma card_filter_preimage_ofFinEmb_eq_factorial_mul (N n : ℕ)
    (p : Set.powersetCard (Fin N) n → Prop) [DecidablePred p] :
    (Finset.univ.filter
      (fun f : Fin n ↪ Fin N => p (Set.powersetCard.ofFinEmb n (Fin N) f))).card =
      n.factorial * (Finset.univ.filter p).card := by
  classical
  let e :
      {f : Fin n ↪ Fin N // p (Set.powersetCard.ofFinEmb n (Fin N) f)} ≃
        Sigma (fun s : {s : Set.powersetCard (Fin N) n // p s} =>
          {f : Fin n ↪ Fin N // Set.powersetCard.ofFinEmb n (Fin N) f = s.1}) :=
    (Equiv.sigmaSubtypeFiberEquivSubtype
      (Set.powersetCard.ofFinEmb n (Fin N))
      (p := fun f : Fin n ↪ Fin N => p (Set.powersetCard.ofFinEmb n (Fin N) f))
      (q := p)
      (by intro f; rfl)).symm
  calc
    (Finset.univ.filter
      (fun f : Fin n ↪ Fin N => p (Set.powersetCard.ofFinEmb n (Fin N) f))).card =
        Fintype.card
          {f : Fin n ↪ Fin N // p (Set.powersetCard.ofFinEmb n (Fin N) f)} := by
          rw [Fintype.card_subtype]
    _ = Fintype.card
        (Sigma (fun s : {s : Set.powersetCard (Fin N) n // p s} =>
          {f : Fin n ↪ Fin N // Set.powersetCard.ofFinEmb n (Fin N) f = s.1})) :=
          Fintype.card_congr e
    _ = ∑ s : {s : Set.powersetCard (Fin N) n // p s},
        Fintype.card
          {f : Fin n ↪ Fin N // Set.powersetCard.ofFinEmb n (Fin N) f = s.1} := by
          rw [Fintype.card_sigma]
    _ = ∑ _s : {s : Set.powersetCard (Fin N) n // p s}, n.factorial := by
          apply Finset.sum_congr rfl
          intro s _hs
          exact card_ofFinEmb_fiber N n s.1
    _ = Fintype.card {s : Set.powersetCard (Fin N) n // p s} * n.factorial := by
          simp
    _ = (Finset.univ.filter p).card * n.factorial := by
          rw [Fintype.card_subtype]
    _ = n.factorial * (Finset.univ.filter p).card := Nat.mul_comm _ _

/-- A population has at most `N` successful positions. -/
lemma populationSuccessCount_le {N : ℕ} (seq : Fin N → Bool) :
    populationSuccessCount seq ≤ N := by
  unfold populationSuccessCount
  simpa using Finset.card_filter_le (Finset.univ : Finset (Fin N)) (fun i => seq i)

/-- Union is injective on pairs consisting of a subset of `A` and a subset of `U \ A`. -/
lemma injOn_union_powersetCard_product_sdiff
    {α : Type*} [DecidableEq α] (U A : Finset α) {k l : ℕ} :
    Set.InjOn (fun p : Finset α × Finset α => p.1 ∪ p.2)
      ((A.powersetCard k).product ((U \ A).powersetCard l)) := by
  intro p hp q hq h
  rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
  rcases Finset.mem_product.mp hq with ⟨hq1, hq2⟩
  rcases Finset.mem_powersetCard.mp hp1 with ⟨hp1sub, _hp1card⟩
  rcases Finset.mem_powersetCard.mp hp2 with ⟨hp2sub, _hp2card⟩
  rcases Finset.mem_powersetCard.mp hq1 with ⟨hq1sub, _hq1card⟩
  rcases Finset.mem_powersetCard.mp hq2 with ⟨hq2sub, _hq2card⟩
  change p.1 ∪ p.2 = q.1 ∪ q.2 at h
  apply Prod.ext
  · ext x
    constructor
    · intro hx
      have hxq : x ∈ q.1 ∪ q.2 := by
        rw [← h]
        exact Finset.mem_union.mpr (Or.inl hx)
      rcases Finset.mem_union.mp hxq with hxq1 | hxq2
      · exact hxq1
      · exact False.elim ((Finset.mem_sdiff.mp (hq2sub hxq2)).2 (hp1sub hx))
    · intro hx
      have hxp : x ∈ p.1 ∪ p.2 := by
        rw [h]
        exact Finset.mem_union.mpr (Or.inl hx)
      rcases Finset.mem_union.mp hxp with hxp1 | hxp2
      · exact hxp1
      · exact False.elim ((Finset.mem_sdiff.mp (hp2sub hxp2)).2 (hq1sub hx))
  · ext x
    constructor
    · intro hx
      have hxq : x ∈ q.1 ∪ q.2 := by
        rw [← h]
        exact Finset.mem_union.mpr (Or.inr hx)
      rcases Finset.mem_union.mp hxq with hxq1 | hxq2
      · exact False.elim ((Finset.mem_sdiff.mp (hp2sub hx)).2 (hq1sub hxq1))
      · exact hxq2
    · intro hx
      have hxp : x ∈ p.1 ∪ p.2 := by
        rw [h]
        exact Finset.mem_union.mpr (Or.inr hx)
      rcases Finset.mem_union.mp hxp with hxp1 | hxp2
      · exact False.elim ((Finset.mem_sdiff.mp (hq2sub hx)).2 (hp1sub hxp1))
      · exact hxp2

/-- `n`-subsets of `U` with `k` points in `A` split into `k`-subsets of `A`
and `(n-k)`-subsets of `U \ A`. -/
lemma powersetCard_filter_inter_card_eq_image_product
    {α : Type*} [DecidableEq α] (U A : Finset α) (hA : A ⊆ U)
    {n k : ℕ} (hk : k ≤ n) :
    (U.powersetCard n).filter (fun s : Finset α => (s ∩ A).card = k) =
      ((A.powersetCard k).product ((U \ A).powersetCard (n - k))).image
        (fun p : Finset α × Finset α => p.1 ∪ p.2) := by
  ext s
  constructor
  · intro hs
    rcases Finset.mem_filter.mp hs with ⟨hsP, hsk⟩
    rcases Finset.mem_powersetCard.mp hsP with ⟨hsU, hsn⟩
    refine Finset.mem_image.mpr ⟨(s ∩ A, s \ A), ?_, ?_⟩
    · refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · exact Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hsk⟩
      · refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
        · intro x hx
          exact Finset.mem_sdiff.mpr ⟨hsU (Finset.mem_sdiff.mp hx).1,
            (Finset.mem_sdiff.mp hx).2⟩
        · have hsplit := Finset.card_sdiff_add_card_inter s A
          have hsplit' : (s \ A).card + k = n := by
            simpa [hsk, hsn] using hsplit
          exact Nat.eq_sub_of_add_eq hsplit'
    · rw [Finset.union_comm, Finset.sdiff_union_inter]
  · intro hs
    rcases Finset.mem_image.mp hs with ⟨p, hp, rfl⟩
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    rcases Finset.mem_powersetCard.mp hp1 with ⟨hp1sub, hp1card⟩
    rcases Finset.mem_powersetCard.mp hp2 with ⟨hp2sub, hp2card⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
      · intro x hx
        rcases Finset.mem_union.mp hx with hx1 | hx2
        · exact hA (hp1sub hx1)
        · exact (Finset.mem_sdiff.mp (hp2sub hx2)).1
      · have hdisj : Disjoint p.1 p.2 := by
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          exact (Finset.mem_sdiff.mp (hp2sub hx2)).2 (hp1sub hx1)
        rw [Finset.card_union_of_disjoint hdisj, hp1card, hp2card]
        omega
    · have hinter : (p.1 ∪ p.2) ∩ A = p.1 := by
        ext x
        constructor
        · intro hx
          rcases Finset.mem_inter.mp hx with ⟨hxu, hxA⟩
          rcases Finset.mem_union.mp hxu with hx1 | hx2
          · exact hx1
          · exact False.elim ((Finset.mem_sdiff.mp (hp2sub hx2)).2 hxA)
        · intro hx
          exact Finset.mem_inter.mpr ⟨Finset.mem_union.mpr (Or.inl hx), hp1sub hx⟩
      rw [hinter, hp1card]

/-- The number of `n`-element subsets of `U` whose intersection with `A` has size `k`. -/
lemma card_powersetCard_filter_inter_card_eq_choose_mul
    {α : Type*} [DecidableEq α] (U A : Finset α) (hA : A ⊆ U)
    {n k : ℕ} (hk : k ≤ n) :
    ((U.powersetCard n).filter (fun s : Finset α => (s ∩ A).card = k)).card =
      A.card.choose k * (U.card - A.card).choose (n - k) := by
  classical
  calc
    ((U.powersetCard n).filter (fun s : Finset α => (s ∩ A).card = k)).card =
        (((A.powersetCard k).product ((U \ A).powersetCard (n - k))).image
          (fun p : Finset α × Finset α => p.1 ∪ p.2)).card := by
        rw [powersetCard_filter_inter_card_eq_image_product U A hA hk]
    _ = ((A.powersetCard k).product ((U \ A).powersetCard (n - k))).card :=
        Finset.card_image_of_injOn (injOn_union_powersetCard_product_sdiff U A)
    _ = A.card.choose k * (U.card - A.card).choose (n - k) := by
        simp [Finset.card_powersetCard, Finset.card_sdiff_of_subset hA]

/-- The number of fixed-size population subsets with exactly `k` successes. -/
lemma card_powersetCard_successCount_eq_choose_mul
    {N n : ℕ} (seq : Fin N → Bool) {k : ℕ} (hk : k ≤ n) :
    (Finset.univ.filter (fun s : Set.powersetCard (Fin N) n =>
      (((s : Finset (Fin N)).filter (fun i : Fin N => seq i)).card = k))).card =
      (populationSuccessCount seq).choose k *
        (N - populationSuccessCount seq).choose (n - k) := by
  classical
  let A : Finset (Fin N) := Finset.univ.filter (fun i : Fin N => seq i)
  let pFin : Finset (Fin N) → Prop :=
    fun s => (s.filter (fun i : Fin N => seq i)).card = k
  have hA : A ⊆ (Finset.univ : Finset (Fin N)) := by intro i hi; simp
  have hcard :=
    card_powersetCard_filter_inter_card_eq_choose_mul
      (U := (Finset.univ : Finset (Fin N))) (A := A) hA hk
  let e :
      {s : Set.powersetCard (Fin N) n // pFin (s : Finset (Fin N))} ≃
        {s : Finset (Fin N) //
          s ∈ (Finset.univ : Finset (Fin N)).powersetCard n ∧ pFin s} :=
    { toFun := fun s =>
        ⟨s.1.1, by
          constructor
          · simp [Finset.mem_powersetCard]
          · exact s.2⟩
      invFun := fun s =>
        ⟨⟨s.1, (Finset.mem_powersetCard.mp s.2.1).2⟩, s.2.2⟩
      left_inv := by intro s; rfl
      right_inv := by intro s; rfl }
  calc
    (Finset.univ.filter (fun s : Set.powersetCard (Fin N) n =>
      (((s : Finset (Fin N)).filter (fun i : Fin N => seq i)).card = k))).card =
        Fintype.card {s : Set.powersetCard (Fin N) n // pFin (s : Finset (Fin N))} := by
        rw [Fintype.card_subtype]
    _ = Fintype.card
        {s : Finset (Fin N) //
          s ∈ (Finset.univ : Finset (Fin N)).powersetCard n ∧ pFin s} :=
        Fintype.card_congr e
    _ = (((Finset.univ : Finset (Fin N)).powersetCard n).filter pFin).card := by
        exact Fintype.card_of_subtype
          (((Finset.univ : Finset (Fin N)).powersetCard n).filter pFin)
          (by intro s; simp [pFin])
    _ = (populationSuccessCount seq).choose k *
        (N - populationSuccessCount seq).choose (n - k) := by
        simpa [A, pFin, populationSuccessCount, Finset.filter_filter, Finset.inter_filter,
          and_left_comm, and_assoc, and_comm] using hcard

/-- Partition the bad fixed-size subsets by their number of successful positions. -/
lemma card_powersetCard_bad_eq_hypergeom_sum
    {N n : ℕ} (seq : Fin N → Bool) (δ : ℝ) :
    (Finset.univ.filter (fun s : Set.powersetCard (Fin N) n =>
      (populationSuccessCount seq : ℝ) / N + δ <
        (((s : Finset (Fin N)).filter (fun i : Fin N => seq i)).card : ℝ) /
          n)).card =
      ∑ k ∈ Finset.range (n + 1),
        if (populationSuccessCount seq : ℝ) / N + δ < (k : ℝ) / n then
          (populationSuccessCount seq).choose k *
            (N - populationSuccessCount seq).choose (n - k)
        else 0 := by
  classical
  let successCount : Set.powersetCard (Fin N) n → ℕ := fun s =>
    (((s : Finset (Fin N)).filter (fun i : Fin N => seq i)).card)
  let bad : Set.powersetCard (Fin N) n → Prop := fun s =>
    (populationSuccessCount seq : ℝ) / N + δ < (successCount s : ℝ) / n
  have hmapsto :
      Set.MapsTo successCount ↑(Finset.univ.filter bad) ↑(Finset.range (n + 1)) := by
    intro s _hs
    have hle :
        successCount s ≤ n := by
      have hle' := Finset.card_filter_le (s : Finset (Fin N)) (fun i : Fin N => seq i)
      simpa [successCount, Set.powersetCard.card_eq s] using hle'
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hle)
  have hpartition :
      (Finset.univ.filter bad).card =
        ∑ k ∈ Finset.range (n + 1),
          ((Finset.univ.filter bad).filter (fun s => successCount s = k)).card :=
    Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter bad)
      (t := Finset.range (n + 1)) (f := successCount) hmapsto
  calc
    (Finset.univ.filter (fun s : Set.powersetCard (Fin N) n =>
      (populationSuccessCount seq : ℝ) / N + δ <
        (((s : Finset (Fin N)).filter (fun i : Fin N => seq i)).card : ℝ) /
          n)).card =
        (Finset.univ.filter bad).card := by
        rfl
    _ = ∑ k ∈ Finset.range (n + 1),
        ((Finset.univ.filter bad).filter (fun s => successCount s = k)).card := hpartition
    _ = ∑ k ∈ Finset.range (n + 1),
        if (populationSuccessCount seq : ℝ) / N + δ < (k : ℝ) / n then
          (populationSuccessCount seq).choose k *
            (N - populationSuccessCount seq).choose (n - k)
        else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        by_cases hbadk : (populationSuccessCount seq : ℝ) / N + δ < (k : ℝ) / n
        · have hfiber :
            ((Finset.univ.filter bad).filter (fun s => successCount s = k)).card =
              (Finset.univ.filter (fun s : Set.powersetCard (Fin N) n =>
                successCount s = k)).card := by
              apply congrArg Finset.card
              ext s
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · intro h
                exact h.2
              · intro hs
                exact ⟨by simpa [bad, hs] using hbadk, hs⟩
          rw [hfiber]
          simp [hbadk, successCount,
            card_powersetCard_successCount_eq_choose_mul seq hk_le]
        · have hfiber :
            ((Finset.univ.filter bad).filter (fun s => successCount s = k)).card = 0 := by
              rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
              intro s hsbad hscount
              exact hbadk (by simpa [bad, hscount] using hsbad)
          rw [hfiber]
          simp [hbadk]

/-- An unordered sample image is bad when its success frequency exceeds the
population success frequency by `δ`. -/
def BadImageSubset {N n : ℕ} (seq : Fin N → Bool) (δ : ℝ)
    (s : Set.powersetCard (Fin N) n) : Prop :=
  (populationSuccessCount seq : ℝ) / N + δ <
    (((s : Finset (Fin N)).filter (fun i : Fin N => seq i)).card : ℝ) / n

/-- Serfling's upper tail after reducing injections to unordered image subsets.

This is the remaining hypergeometric-count tail inequality: among `n`-element
subsets of `Fin N`, the fraction whose success count exceeds the population
success rate by `δ` is bounded by `exp (-2 n δ^2)`. -/
lemma finite_powersetCard_serfling_upper_tail
    {N n : ℕ} (hN : n ≤ N) (hn : n ≠ 0)
    (seq : Fin N → Bool) (δ : ℝ) (hδ : 0 < δ) :
    ((Finset.univ.filter (fun s : Set.powersetCard (Fin N) n =>
      (populationSuccessCount seq : ℝ) / N + δ <
        (((s : Finset (Fin N)).filter (fun i : Fin N => seq i)).card : ℝ) /
          n)).card : ℝ) /
      Nat.card (Set.powersetCard (Fin N) n) ≤ Real.exp (-2 * n * δ ^ 2) := by
  rw [card_powersetCard_bad_eq_hypergeom_sum]
  rw [Set.powersetCard.card]
  simp only [Nat.card_fin]
  exact Math.Concentration.HypergeometricTail.hypergeometric_choose_upper_tail
    (populationSuccessCount_le seq) hN hn δ hδ

/-- Pulling the bad image-subset predicate back along an injection gives the
usual empirical-frequency bad event. -/
lemma badImageSubset_ofFinEmb_iff {N n : ℕ} (seq : Fin N → Bool)
    (δ : ℝ) (f : Fin n ↪ Fin N) :
    BadImageSubset seq δ (Set.powersetCard.ofFinEmb n (Fin N) f) ↔
      populationFreq seq + δ < empiricalFreqOf seq f := by
  simp [BadImageSubset, populationFreq_eq_successCount,
    empiricalFreqOf_eq_sampleSuccessCount, sampleSuccessCount_eq_imageSuccessCount,
    sampleImageSuccessCount, sampleImage, Set.powersetCard.val_ofFinEmb]

/-- The finite combinatorial core of Serfling's upper-tail inequality for the
uniform type of injections `Fin n ↪ Fin N`. -/
theorem finite_injection_serfling_upper_tail
    {N n : ℕ} (hN : n ≤ N) (hn : n ≠ 0)
    (seq : Fin N → Bool) (δ : ℝ) (hδ : 0 < δ) :
    ((Finset.univ.filter (fun f : Fin n ↪ Fin N =>
      populationFreq seq + δ < empiricalFreqOf seq f)).card : ℝ) /
      Fintype.card (Fin n ↪ Fin N) ≤ Real.exp (-2 * n * δ ^ 2) := by
  -- An injection is bad exactly when its unordered image subset is bad.
  have hfilter :
      Finset.univ.filter (fun f : Fin n ↪ Fin N =>
        populationFreq seq + δ < empiricalFreqOf seq f) =
      Finset.univ.filter (fun f : Fin n ↪ Fin N =>
        (populationSuccessCount seq : ℝ) / N + δ <
          ((((Set.powersetCard.ofFinEmb n (Fin N) f : Set.powersetCard (Fin N) n) :
            Finset (Fin N)).filter (fun i : Fin N => seq i)).card : ℝ) / n) :=
    Finset.filter_congr fun f _ => (badImageSubset_ofFinEmb_iff seq δ f).symm
  -- Each image subset is the image of exactly `n!` injections, so `n!` cancels.
  have hfac : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [hfilter, card_filter_preimage_ofFinEmb_eq_factorial_mul N n
      (fun s => (populationSuccessCount seq : ℝ) / N + δ <
        (((s : Finset (Fin N)).filter (fun i : Fin N => seq i)).card : ℝ) / n),
    card_fin_embedding_eq_factorial_mul_powersetCard, Nat.cast_mul, Nat.cast_mul,
    mul_div_mul_left _ _ hfac]
  exact finite_powersetCard_serfling_upper_tail hN hn seq δ hδ

end Math.Concentration.Serfling
