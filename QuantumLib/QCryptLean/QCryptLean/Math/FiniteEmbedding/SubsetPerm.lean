import Mathlib.Data.Set.PowersetCard
import QCryptLean.Math.FiniteEmbedding

/-! # Subset Perm -/


namespace Math.FiniteEmbedding

/-- Increasing enumeration of an `n`-element subset of `Fin N`. -/
def increasingSubsetEquiv {n N : ℕ} (S : Set.powersetCard (Fin N) n) : Fin n ≃ S :=
  (S.1.orderIsoOfFin S.2).toEquiv

/-- The image of an embedding, as the existing Mathlib fixed-cardinality subset type. -/
def imageSubset {n N : ℕ} (f : Fin n ↪ Fin N) : Set.powersetCard (Fin N) n :=
  Set.powersetCard.ofFinEmb n (Fin N) f

/-- The embedding viewed as an equivalence from its domain to its image subset. -/
def embeddingImageEquiv {n N : ℕ} (f : Fin n ↪ Fin N) : Fin n ≃ imageSubset f :=
  f.toEquivRange.trans
    (Set.equivOfEq (Set.powersetCard.coe_ofFinEmb n (Fin N) f).symm)

/-- The inverse-rank permutation comparing the embedding's order with increasing subset order. -/
def embeddingPermutation {n N : ℕ} (f : Fin n ↪ Fin N) : Equiv.Perm (Fin n) :=
  ((embeddingImageEquiv f).trans (increasingSubsetEquiv (imageSubset f)).symm).symm

/-- Join an image subset and inner permutation using `π⁻¹` before increasing enumeration. -/
def joinSubsetPerm {n N : ℕ} (S : Set.powersetCard (Fin N) n)
    (π : Equiv.Perm (Fin n)) : Fin n ↪ Fin N where
  toFun k := (increasingSubsetEquiv S (π.symm k)).1
  inj' := by
    intro k l h
    apply π.symm.injective
    apply (increasingSubsetEquiv S).injective
    exact Subtype.ext h

/-- Forward map from an embedding to its image subset and inverse-rank permutation. -/
def embeddingSubsetPermForward {n N : ℕ} (f : Fin n ↪ Fin N) :
    Set.powersetCard (Fin N) n × Equiv.Perm (Fin n) :=
  (imageSubset f, embeddingPermutation f)

/-- Joining an embedding's actual image and inverse-rank permutation recovers the embedding. -/
theorem join_imageSubset_embeddingPermutation {n N : ℕ} (f : Fin n ↪ Fin N) :
    joinSubsetPerm (imageSubset f) (embeddingPermutation f) = f := by
  ext k
  simp [joinSubsetPerm, embeddingPermutation, embeddingImageEquiv]
  rfl

/-- Taking the image and inverse-rank permutation of a joined pair recovers that exact pair. -/
theorem embeddingSubsetPermForward_join {n N : ℕ} (S : Set.powersetCard (Fin N) n)
    (π : Equiv.Perm (Fin n)) :
    embeddingSubsetPermForward (joinSubsetPerm S π) = (S, π) := by
  have hS : imageSubset (joinSubsetPerm S π) = S := by
    apply Subtype.ext
    ext i
    simp only [imageSubset, Set.powersetCard.mem_ofFinEmb_iff_mem_range,
      Set.powersetCard.mem_coe_iff]
    constructor
    · rintro ⟨k, rfl⟩
      exact (increasingSubsetEquiv S (π.symm k)).2
    · intro hi
      let s : S := ⟨i, hi⟩
      let k : Fin n := (increasingSubsetEquiv S).symm s
      refine ⟨π k, ?_⟩
      change ((increasingSubsetEquiv S) (π.symm (π k))).val = i
      simp [k, s]
  apply Prod.ext
  · exact hS
  · apply Equiv.ext
    intro k
    have henum :
        (increasingSubsetEquiv (imageSubset (joinSubsetPerm S π)) k).1 =
          (increasingSubsetEquiv S k).1 := by
      rw [hS]
    have hleft :
        embeddingImageEquiv (joinSubsetPerm S π)
            (embeddingPermutation (joinSubsetPerm S π) k) =
          increasingSubsetEquiv (imageSubset (joinSubsetPerm S π)) k := by
      simp [embeddingPermutation]
    apply (embeddingImageEquiv (joinSubsetPerm S π)).injective
    change
      embeddingImageEquiv (joinSubsetPerm S π)
          (embeddingPermutation (joinSubsetPerm S π) k) =
        embeddingImageEquiv (joinSubsetPerm S π) (π k)
    rw [hleft]
    apply Subtype.ext
    change
      (increasingSubsetEquiv (imageSubset (joinSubsetPerm S π)) k).1 =
        joinSubsetPerm S π (π k)
    change (increasingSubsetEquiv (imageSubset (joinSubsetPerm S π)) k).val =
      (increasingSubsetEquiv S (π.symm (π k))).val
    simpa only [Equiv.symm_apply_apply] using henum

/-- Explicit equivalence between finite embeddings and image-subset/inner-permutation pairs. -/
def embeddingSubsetPermEquiv (n N : ℕ) :
    (Fin n ↪ Fin N) ≃ Set.powersetCard (Fin N) n × Equiv.Perm (Fin n) where
  toFun := embeddingSubsetPermForward
  invFun pair := joinSubsetPerm pair.1 pair.2
  left_inv := join_imageSubset_embeddingPermutation
  right_inv pair := by
    rcases pair with ⟨S, π⟩
    exact embeddingSubsetPermForward_join S π


/-- The increasing enumeration lands in the supplied subset. -/
theorem increasingSubsetEquiv_mem {n N : ℕ} (S : Set.powersetCard (Fin N) n) (k : Fin n) :
    (increasingSubsetEquiv S k).1 ∈ S :=
  (increasingSubsetEquiv S k).2

/-- Joining evaluates by `π⁻¹` followed by the actual increasing enumeration. -/
theorem joinSubsetPerm_apply {n N : ℕ} (S : Set.powersetCard (Fin N) n)
    (π : Equiv.Perm (Fin n)) (k : Fin n) :
    joinSubsetPerm S π k = (increasingSubsetEquiv S (π.symm k)).1 := by
  rfl

end Math.FiniteEmbedding
