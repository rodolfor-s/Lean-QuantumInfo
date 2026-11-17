import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fintype

/-!
# Explicit permutations transporting finite embeddings

This module constructs a permutation of `Fin N` carrying one embedding `Fin n ↪ Fin N` to
another. The construction enumerates the complement of each finite range, so the resulting
transport is explicit.
-/

namespace Math.FiniteEmbedding

/-- The finite range of an embedding, represented as a `Finset`. -/
def embeddingRange {n N : ℕ} (f : Fin n ↪ Fin N) : Finset (Fin N) :=
  Finset.univ.map f

/-- The finite range representation has exactly the same underlying set as `Set.range f`. -/
theorem coe_embeddingRange {n N : ℕ} (f : Fin n ↪ Fin N) :
    (embeddingRange f : Set (Fin N)) = Set.range f := by
  ext i
  simp [embeddingRange]

/-- The range of `f : Fin n ↪ Fin N` has cardinality `n`. -/
theorem card_embeddingRange {n N : ℕ} (f : Fin n ↪ Fin N) :
    (embeddingRange f).card = n := by
  simp [embeddingRange]

/-- The complement of the finite range has cardinality `N - n`. -/
theorem card_embeddingRange_compl {n N : ℕ} (f : Fin n ↪ Fin N) :
    (embeddingRange f)ᶜ.card = N - n := by
  rw [Finset.card_compl, card_embeddingRange, Fintype.card_fin]

/-- Increasing enumeration of the complement of an embedding's range, transported to the
set-theoretic complement expected by `Equiv.Set.sumCompl`. -/
def embeddingComplementEquiv {n N : ℕ} (f : Fin n ↪ Fin N) :
    Fin (N - n) ≃ {i : Fin N // i ∈ (Set.range f)ᶜ} :=
  (((embeddingRange f)ᶜ).orderIsoOfFin (card_embeddingRange_compl f)).toEquiv.trans
    (Set.equivOfEq (by rw [Finset.coe_compl, coe_embeddingRange]))

/-- Split `Fin N` into the actual range of `f` and its increasingly enumerated complement. -/
def embeddingSplitEquiv {n N : ℕ} (f : Fin n ↪ Fin N) :
    Fin n ⊕ Fin (N - n) ≃ Fin N :=
  (Equiv.sumCongr f.toEquivRange (embeddingComplementEquiv f)).trans
    (Equiv.Set.sumCompl (Set.range f))

/-- The explicit permutation transporting the split induced by `f` to the split induced by `g`. -/
def embeddingTransportPerm {n N : ℕ} (f g : Fin n ↪ Fin N) : Fin N ≃ Fin N :=
  (embeddingSplitEquiv f).symm.trans (embeddingSplitEquiv g)

/-- The explicit transport permutation sends every value of `f` to the corresponding value of `g`.

The complement action is fixed by increasing enumerations. -/
theorem embeddingTransportPerm_apply {n N : ℕ} (f g : Fin n ↪ Fin N) (k : Fin n) :
    embeddingTransportPerm f g (f k) = g k := by
  change embeddingSplitEquiv g ((embeddingSplitEquiv f).symm (f k)) = g k
  have hf : embeddingSplitEquiv f (Sum.inl k) = f k := by
    simp [embeddingSplitEquiv]
  rw [← hf, Equiv.symm_apply_apply]
  simp [embeddingSplitEquiv]

/-! ## Explicit transport formulas -/

/-- Membership in the explicit finite range is actual membership in the embedding's image. -/
theorem mem_embeddingRange_iff {n N : ℕ} (f : Fin n ↪ Fin N) (i : Fin N) :
    i ∈ embeddingRange f ↔ ∃ k : Fin n, f k = i := by
  simp [embeddingRange]

/-- The range half of the split evaluates to the original embedding. -/
theorem embeddingSplitEquiv_apply_range {n N : ℕ} (f : Fin n ↪ Fin N) (k : Fin n) :
    embeddingSplitEquiv f (Sum.inl k) = f k := by
  simp [embeddingSplitEquiv]

/-- The complement half of the split evaluates to the increasing complement enumeration. -/
theorem embeddingSplitEquiv_apply_complement {n N : ℕ} (f : Fin n ↪ Fin N)
    (k : Fin (N - n)) :
    embeddingSplitEquiv f (Sum.inr k) = embeddingComplementEquiv f k := by
  simp [embeddingSplitEquiv]

end Math.FiniteEmbedding
