import Lean.Elab.Tactic.Omega
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Logic.Equiv.Fin.Basic
import QCryptLean.QKD.BB84.Constants

/-!
# BB84 round selection

Key-round counts, the permutation placing key rounds before test rounds, and the sizes of the
two test subsamples. The general split accepts an arbitrary test count `m`; the canonical split
(`m = (n + 1) / 2`) is its special case. Neither split adds a correctness assumption on a
selector.
-/

noncomputable section

namespace QKD.BB84.FiniteKey

/-- Number of key rounds after reserving `m` test rounds, using truncated natural subtraction. -/
def keyRounds (n m : ℕ) : ℕ := n - m

/-- The key-round count never exceeds the block length. -/
lemma keyRounds_le (n m : ℕ) : keyRounds n m ≤ n :=
  Nat.sub_le _ _

/-- **The number of reserved test rounds is `min n m`.**

The split reserves `min n m` rounds for parameter estimation. Because the key
count is the truncated difference `n - m`, that number is `min n m`: it is `m` exactly when
`m ≤ n`, and it saturates at `n` when `m > n`. Every general-`m` construction that loops over the
reserved rounds runs this many times, and no construction is entitled to rewrite the length to
`m` without the hypothesis `m ≤ n`. -/
lemma sub_keyRounds_eq_min (n m : ℕ) :
    n - keyRounds n m = min n m := by
  simp only [keyRounds]
  omega

/-- `m + n_K = n` for `m ≤ n` (the PE/key split is well-formed). -/
lemma add_keyRounds (n m : ℕ) (hm : m ≤ n) :
    m + keyRounds n m = n :=
  Nat.add_sub_cancel' hm

/-- At least one key round remains when fewer than `n` rounds are tested. -/
lemma keyRounds_pos {n m : ℕ} (hmn : m < n) : 0 < keyRounds n m := by
  simp only [keyRounds]
  omega

/-- Nonzero key-round count when fewer than `n` rounds are tested. -/
lemma neZero_keyRounds {n m : ℕ} (hmn : m < n) :
    NeZero (keyRounds n m) :=
  ⟨by have := keyRounds_pos hmn; omega⟩

/-- The typeclass form of `neZero_keyRounds`. -/
instance neZero_keyRounds_of_fact (n m : ℕ) [h : Fact (m < n)] :
    NeZero (keyRounds n m) :=
  neZero_keyRounds h.out

/-- Number of key rounds in the canonical split, which tests `(n + 1) / 2` rounds — the
`keyRounds` special case at `m = (n + 1) / 2`. -/
def canonicalKeyRounds (n : ℕ) : ℕ := keyRounds n ((n + 1) / 2)

/-- The key-round count never exceeds the block length. -/
lemma canonicalKeyRounds_le (n : ℕ) : canonicalKeyRounds n ≤ n :=
  Nat.sub_le _ _

/-- `n_K = ⌊n/2⌋`. -/
lemma canonicalKeyRounds_eq_div_two (n : ℕ) : canonicalKeyRounds n = n / 2 := by
  rw [canonicalKeyRounds, keyRounds]; omega

/-! ## Key-first ordering -/

/-- The permutation placing key rounds (`peSel = false`) before test rounds. -/
def peSelSort {n : ℕ} (peSel : Fin n → Bool) : Equiv.Perm (Fin n) := Tuple.sort peSel

/-- After sorting, `peSel ∘ peSelSort peSel` is monotone (key rounds first). -/
lemma peSel_comp_peSelSort_monotone {n : ℕ} (peSel : Fin n → Bool) :
    Monotone (peSel ∘ ⇑(peSelSort peSel)) :=
  Tuple.monotone_sort peSel

/-- The number of key rounds (`peSel = false`) is preserved by the sort. -/
lemma peSelSort_keyCount {n : ℕ} (peSel : Fin n → Bool) :
    Fintype.card { i // (peSel ∘ ⇑(peSelSort peSel)) i = false } =
      Fintype.card { i // peSel i = false } :=
  Fintype.card_congr (Equiv.subtypeEquiv (Tuple.sort peSel) (fun i => by simp [peSelSort]))

/-- **Threshold characterization of the sort.**  After sorting, round `j` is a key round
(`peSel = false`) exactly when `j` lies in the prefix `[0, #key)`. -/
lemma peSel_peSelSort_eq_false_iff {n : ℕ} (peSel : Fin n → Bool) (j : Fin n) :
    peSel (peSelSort peSel j) = false ↔
      (j : ℕ) < Fintype.card { i // peSel i = false } := by
  have hbf : ∀ b : Bool, (b ≤ false) ↔ (b = false) := fun b => by cases b <;> simp
  have h := Tuple.lt_card_le_iff_apply_le_of_monotone (f := peSel ∘ ⇑(peSelSort peSel))
    (a := false) (j := j) (peSel_comp_peSelSort_monotone peSel)
  rw [← Fintype.card_subtype] at h
  have hcard : Fintype.card { i // (peSel ∘ ⇑(peSelSort peSel)) i ≤ false } =
      Fintype.card { i // peSel i = false } := by
    rw [← peSelSort_keyCount peSel]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun i => hbf _))
  rw [hcard, hbf] at h
  exact h.symm

/-! ## Sorted test-round indices, at a general test-set size `m` -/

/-- `n_K + (n − n_K) = n` at a general test-set size `m` (the key-rounds-first split is
well-formed). -/
lemma keyRounds_add_min (n m : ℕ) :
    keyRounds n m + min n m = n := by
  simp only [keyRounds]
  omega

/-- Find the original round at test position `j` after sorting key rounds before
test rounds; the split reserves `keyRounds n m` positions for the key. -/
def peRoundIdx {n m : ℕ} (peSel : Fin n → Bool)
    (j : Fin (min n m)) : Fin n :=
  peSelSort peSel
    (Fin.cast (keyRounds_add_min n m) (Fin.natAdd (keyRounds n m) j))

/-- For a selector already in key-first order, test indices are offsets from the key prefix. -/
lemma peRoundIdx_of_monotone {n m : ℕ} (peSel : Fin n → Bool) (h : Monotone peSel)
    (j : Fin (min n m)) :
    peRoundIdx peSel j = ⟨keyRounds n m + j, by
      have := j.isLt
      have := keyRounds_add_min n m
      omega⟩ := by
  rw [peRoundIdx, peSelSort, Tuple.sort_eq_refl_iff_monotone.mpr h]
  rfl

/-! ## Sorted test-round indices, at the canonical test-set size -/

/-- `n_K + (n − n_K) = n` at the canonical test-set size (the key-rounds-first split is
well-formed) — the `keyRounds_add_min` special case at `m = (n + 1) / 2`. -/
lemma canonicalKeyRounds_add_sub (n : ℕ) :
    canonicalKeyRounds n + min n ((n + 1) / 2) = n :=
  keyRounds_add_min n ((n + 1) / 2)

/-- The `j`-th **sorted PE round** index at the canonical test-set size — the `peRoundIdx`
special case at `m = (n + 1) / 2`. -/
def peRoundIdxCanonical {n : ℕ} (peSel : Fin n → Bool)
    (j : Fin (min n ((n + 1) / 2))) : Fin n :=
  peRoundIdx (m := (n + 1) / 2) peSel j

/-! ## Test subsample sizes -/

/-- Z-test subsample size. -/
def siftedZTestSampleSize {n : ℕ} (peSel xSel : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => peSel i = true ∧ xSel i = false)).card

/-- X-test subsample size. -/
def siftedXTestSampleSize {n : ℕ} (peSel xSel : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => peSel i = true ∧ xSel i = true)).card

/-! ## The round-outcome partition equivalence, at a general test-set size `m`

This round-selection combinatorics is built on `keyRounds` and `peRoundIdx`. Both the Model
and FiniteKey developments use the resulting partition equivalence. -/

/-- The `i`-th **sorted key round** index at a general test-set size `m` (mirror of
`peRoundIdx`). -/
def keyRoundIdx {n m : ℕ} (peSel : Fin n → Bool)
    (i : Fin (keyRounds n m)) : Fin n :=
  peSelSort peSel
    (Fin.cast (keyRounds_add_min n m) (Fin.castAdd (min n m) i))

/-- The count hypothesis at a general test-set size `m`: there are exactly
`n_K = keyRounds n m = n − m` key rounds. -/
abbrev KeyCount (n m : ℕ) (peSel : Fin n → Bool) : Prop :=
  Fintype.card { i // peSel i = false } = keyRounds n m

/-- A sorted key round is a key round (`peSel = false`). -/
lemma peSel_keyRoundIdx {n m : ℕ} (peSel : Fin n → Bool) (hcount : KeyCount n m peSel)
    (i : Fin (keyRounds n m)) :
    peSel (keyRoundIdx peSel i) = false := by
  rw [keyRoundIdx, peSel_peSelSort_eq_false_iff, hcount]
  exact i.isLt

/-- A sorted PE round is a PE round (`peSel = true`). -/
lemma peSel_peRoundIdx {n m : ℕ} (peSel : Fin n → Bool) (hcount : KeyCount n m peSel)
    (j : Fin (min n m)) :
    peSel (peRoundIdx peSel j) = true := by
  have h : ¬ (peSel (peRoundIdx peSel j) = false) := by
    rw [peRoundIdx, peSel_peSelSort_eq_false_iff, hcount, not_lt]
    exact Nat.le_add_right _ _
  simpa using h

/-- The combined sorted-round bijection at a general test-set size `m`:
`Fin n_K ⊕ Fin (n − n_K) ≃ Fin n`. -/
def roundEquiv {n m : ℕ} (peSel : Fin n → Bool) :
    Fin (keyRounds n m) ⊕ Fin (min n m) ≃ Fin n :=
  finSumFinEquiv.trans ((finCongr (keyRounds_add_min n m)).trans (peSelSort peSel))

@[simp] lemma roundEquiv_inl {n m : ℕ} (peSel : Fin n → Bool)
    (i : Fin (keyRounds n m)) :
    roundEquiv (m := m) peSel (Sum.inl i) = keyRoundIdx peSel i := by
  simp only [roundEquiv, Equiv.trans_apply, finSumFinEquiv_apply_left, finCongr_apply]
  rfl

@[simp] lemma roundEquiv_inr {n m : ℕ} (peSel : Fin n → Bool)
    (j : Fin (min n m)) :
    roundEquiv (m := m) peSel (Sum.inr j) = peRoundIdx peSel j := by
  simp only [roundEquiv, Equiv.trans_apply, finSumFinEquiv_apply_right, finCongr_apply]
  rfl

/-- The **partition equivalence** of the round-outcome register at a general test-set size `m`. -/
def partEquiv {X : Type*} {n m : ℕ} (peSel : Fin n → Bool) :
    (Fin n → X) ≃
      (Fin (keyRounds n m) → X) ×
        (Fin (min n m) → X) :=
  (Equiv.arrowCongr (roundEquiv (m := m) peSel) (Equiv.refl (X))).symm.trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

@[simp] lemma partEquiv_apply_fst {X : Type*} {n m : ℕ} (peSel : Fin n → Bool)
    (ω : Fin n → X) (i : Fin (keyRounds n m)) :
    (partEquiv (m := m) peSel ω).1 i = ω (keyRoundIdx peSel i) := by
  simp only [partEquiv, Equiv.trans_apply, Equiv.sumArrowEquivProdArrow_apply_fst,
    Equiv.arrowCongr_symm, Equiv.refl_symm, Equiv.arrowCongr_apply, Equiv.coe_refl,
    Function.comp_apply, id_eq, Equiv.symm_symm, roundEquiv_inl]

@[simp] lemma partEquiv_apply_snd {X : Type*} {n m : ℕ} (peSel : Fin n → Bool)
    (ω : Fin n → X) (j : Fin (min n m)) :
    (partEquiv (m := m) peSel ω).2 j = ω (peRoundIdx peSel j) := by
  simp only [partEquiv, Equiv.trans_apply, Equiv.sumArrowEquivProdArrow_apply_snd,
    Equiv.arrowCongr_symm, Equiv.refl_symm, Equiv.arrowCongr_apply, Equiv.coe_refl,
    Function.comp_apply, id_eq, Equiv.symm_symm, roundEquiv_inr]

@[simp] lemma partEquiv_symm_apply_keyIdx {X : Type*} {n m : ℕ} (peSel : Fin n → Bool)
    (k : Fin (keyRounds n m) → X)
    (q : Fin (min n m) → X)
    (i : Fin (keyRounds n m)) :
    (partEquiv (m := m) peSel).symm (k, q) (keyRoundIdx peSel i) = k i := by
  simp only [partEquiv, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.arrowCongr_apply,
    Equiv.coe_refl, Function.comp_apply, id_eq]
  rw [show keyRoundIdx peSel i = roundEquiv (m := m) peSel (Sum.inl i) from
        (roundEquiv_inl peSel i).symm, Equiv.symm_apply_apply,
    Equiv.sumArrowEquivProdArrow_symm_apply_inl]

@[simp] lemma partEquiv_symm_apply_peIdx {X : Type*} {n m : ℕ} (peSel : Fin n → Bool)
    (k : Fin (keyRounds n m) → X)
    (q : Fin (min n m) → X)
    (j : Fin (min n m)) :
    (partEquiv (m := m) peSel).symm (k, q) (peRoundIdx peSel j) = q j := by
  simp only [partEquiv, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.arrowCongr_apply,
    Equiv.coe_refl, Function.comp_apply, id_eq]
  rw [show peRoundIdx peSel j = roundEquiv (m := m) peSel (Sum.inr j) from
        (roundEquiv_inr peSel j).symm, Equiv.symm_apply_apply,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr]

/-- Every PE round (`peSel a = true`) is a sorted PE round. -/
lemma exists_eq_peRoundIdx {n m : ℕ} (peSel : Fin n → Bool) (hcount : KeyCount n m peSel)
    (a : Fin n) (ha : peSel a = true) :
    ∃ j, a = peRoundIdx (m := m) peSel j := by
  rcases hsum : (roundEquiv (m := m) peSel).symm a with i | j
  · exfalso
    have : a = keyRoundIdx peSel i := by
      rw [← roundEquiv_inl peSel i, ← hsum, Equiv.apply_symm_apply]
    rw [this, peSel_keyRoundIdx peSel hcount i] at ha
    exact Bool.noConfusion ha
  · exact ⟨j, by rw [← roundEquiv_inr peSel j, ← hsum, Equiv.apply_symm_apply]⟩

end QKD.BB84.FiniteKey
