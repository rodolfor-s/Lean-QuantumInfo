import Mathlib.Logic.Equiv.Fin.Basic
import QCryptLean.Math.FiniteEmbedding
import QCryptLean.Math.FiniteEmbedding.FixedLeft

/-! # Prefix Order -/


namespace Math.FiniteEmbedding

/-- Enumerations of `T` whose literal value-list starts with the embedded sequence `u`. -/
def PrefixSequenceFiber {N r : ℕ} (T : Finset (Fin N)) (u : Fin r ↪ T) :=
  {q : Fin T.card ≃ T //
    (List.ofFn fun k : Fin T.card => q k).take r = List.ofFn fun k : Fin r => u k}

/-- The embedded prefix length cannot exceed the cardinality of the target finset. -/
theorem prefixLength_le {N r : ℕ} (T : Finset (Fin N)) (u : Fin r ↪ T) :
    r ≤ T.card := by
  simpa using Fintype.card_le_of_injective (u : Fin r → T) u.injective

/-- Increasing enumeration of the target finset. -/
def increasingTargetEquiv {N : ℕ} (T : Finset (Fin N)) : Fin T.card ≃ T :=
  (T.orderIsoOfFin rfl).toEquiv

/-- Rank embedding of the supplied prefix inside the increasing enumeration of `T`. -/
def prefixRankEmbedding {N r : ℕ} (T : Finset (Fin N)) (u : Fin r ↪ T) :
    Fin r ↪ Fin T.card :=
  u.trans (increasingTargetEquiv T).symm.toEmbedding

/-- Split prefix and residual positions into the flat domain of an enumeration. -/
def prefixDomainEquiv {N r : ℕ} (T : Finset (Fin N)) (u : Fin r ↪ T) :
    Fin r ⊕ Fin (T.card - r) ≃ Fin T.card :=
  (finSumFinEquiv : Fin r ⊕ Fin (T.card - r) ≃ Fin (r + (T.card - r))).trans
    (finCongr (Nat.add_sub_of_le (prefixLength_le T u)))

/-- Split the literal prefix and its increasing complement into the target finset. -/
def prefixTargetEquiv {N r : ℕ} (T : Finset (Fin N)) (u : Fin r ↪ T) :
    Fin r ⊕ Fin (T.card - r) ≃ T :=
  (embeddingSplitEquiv (prefixRankEmbedding T u)).trans (increasingTargetEquiv T)

/-- Compare a prefix-constrained enumeration with the canonical prefix/complement splitting. -/
def prefixComparison {N r : ℕ} (T : Finset (Fin N)) (u : Fin r ↪ T)
    (q : PrefixSequenceFiber T u) :
    Fin r ⊕ Fin (T.card - r) ≃ Fin r ⊕ Fin (T.card - r) :=
  (prefixDomainEquiv T u).trans (q.1.trans (prefixTargetEquiv T u).symm)

/-- The prefix comparison fixes every coordinate of its left block. -/
theorem prefixComparison_apply_left {N r : ℕ} (T : Finset (Fin N))
    (u : Fin r ↪ T) (q : PrefixSequenceFiber T u) (k : Fin r) :
    prefixComparison T u q (Sum.inl k) = Sum.inl k := by
  apply (prefixTargetEquiv T u).injective
  simp only [prefixComparison, Equiv.trans_apply, Equiv.apply_symm_apply]
  have hk := congrArg (fun xs : List T => xs[k.val]?) q.2
  simp only [k.isLt, List.getElem?_take_of_lt, List.getElem?_ofFn, List.length_ofFn,
    getElem?_pos, List.getElem_ofFn, Fin.eta, Option.dite_none_right_eq_some,
    Option.some.injEq] at hk
  rcases hk with ⟨hkT, hk⟩
  have hidx :
      prefixDomainEquiv T u (Sum.inl k) = ⟨k.val, hkT⟩ := by
    apply Fin.ext
    simp [prefixDomainEquiv]
  rw [hidx, hk]
  simp [prefixTargetEquiv, prefixRankEmbedding, increasingTargetEquiv,
    embeddingSplitEquiv_apply_range]

/-- Forward residual permutation extracted from a prefix-constrained enumeration. -/
def prefixSequenceForward {N r : ℕ} (T : Finset (Fin N)) (u : Fin r ↪ T)
    (q : PrefixSequenceFiber T u) : Equiv.Perm (Fin (T.card - r)) :=
  rightPermOfFixesLeft (prefixComparison T u q) (prefixComparison_apply_left T u q)

/-- Rebuild an enumeration from a residual permutation.  Residual output position `k` uses the
`ρ k`-th element of the increasing complement. -/
def rebuildPrefixSequence {N r : ℕ} (T : Finset (Fin N)) (u : Fin r ↪ T)
    (ρ : Equiv.Perm (Fin (T.card - r))) : Fin T.card ≃ T :=
  (prefixDomainEquiv T u).symm.trans
    ((Equiv.sumCongr (Equiv.refl (Fin r)) ρ).trans (prefixTargetEquiv T u))

/-- Rebuilding from a residual permutation produces the literal requested prefix. -/
theorem rebuildPrefixSequence_prefix {N r : ℕ} (T : Finset (Fin N))
    (u : Fin r ↪ T) (ρ : Equiv.Perm (Fin (T.card - r))) :
    (List.ofFn fun k : Fin T.card => rebuildPrefixSequence T u ρ k).take r =
      List.ofFn fun k : Fin r => u k := by
  apply List.ext_getElem
  · simp [prefixLength_le T u]
  · intro i hi₁ hi₂
    simp only [List.getElem_take, List.getElem_ofFn]
    have hir : i < r := by simpa using hi₂
    have hiT : i < T.card := lt_of_lt_of_le hir (prefixLength_le T u)
    have hidx :
        (⟨i, hiT⟩ : Fin T.card) =
          prefixDomainEquiv T u (Sum.inl ⟨i, hir⟩) := by
      apply Fin.ext
      simp [prefixDomainEquiv]
    rw [hidx]
    simp [rebuildPrefixSequence, prefixTargetEquiv, prefixRankEmbedding,
      increasingTargetEquiv, embeddingSplitEquiv_apply_range]

/-- Rebuilt enumeration bundled with its literal prefix proof. -/
def prefixSequenceBackward {N r : ℕ} (T : Finset (Fin N)) (u : Fin r ↪ T)
    (ρ : Equiv.Perm (Fin (T.card - r))) : PrefixSequenceFiber T u :=
  ⟨rebuildPrefixSequence T u ρ, rebuildPrefixSequence_prefix T u ρ⟩

/-- Rebuilding after extracting the residual permutation recovers the constrained enumeration. -/
theorem prefixSequenceBackward_forward {N r : ℕ} (T : Finset (Fin N))
    (u : Fin r ↪ T) (q : PrefixSequenceFiber T u) :
    prefixSequenceBackward T u (prefixSequenceForward T u q) = q := by
  apply Subtype.ext
  apply Equiv.ext
  intro k
  simp only [prefixSequenceBackward, rebuildPrefixSequence, prefixSequenceForward,
    Equiv.trans_apply]
  have h := congrArg (fun e : Equiv.Perm (Fin r ⊕ Fin (T.card - r)) =>
    prefixTargetEquiv T u (e ((prefixDomainEquiv T u).symm k)))
      (sumEquiv_eq_sumCongr_rightPerm (prefixComparison T u q)
        (prefixComparison_apply_left T u q))
  refine h.symm.trans ?_
  simp [prefixComparison]

/-- Extracting after rebuilding recovers the supplied residual permutation. -/
theorem prefixSequenceForward_backward {N r : ℕ} (T : Finset (Fin N))
    (u : Fin r ↪ T) (ρ : Equiv.Perm (Fin (T.card - r))) :
    prefixSequenceForward T u (prefixSequenceBackward T u ρ) = ρ := by
  apply Equiv.ext
  intro j
  change
    rightMapOfFixesLeft
        (prefixComparison T u (prefixSequenceBackward T u ρ))
        (prefixComparison_apply_left T u (prefixSequenceBackward T u ρ)) j =
      ρ j
  have hright :
      prefixComparison T u (prefixSequenceBackward T u ρ) (Sum.inr j) =
        Sum.inr (ρ j) := by
    simp [prefixComparison, prefixSequenceBackward, rebuildPrefixSequence]
  unfold rightMapOfFixesLeft
  split
  · rename_i i hq
    exfalso
    exact Sum.inl_ne_inr (hq.symm.trans hright)
  · rename_i j' hq
    exact Sum.inr.inj (hq.symm.trans hright)

/-- Prefix-constrained enumerations are equivalent to forward permutations of the increasingly
enumerated complement. -/
def prefixSequenceEquiv {N r : ℕ} (T : Finset (Fin N)) (u : Fin r ↪ T) :
    PrefixSequenceFiber T u ≃ Equiv.Perm (Fin (T.card - r)) where
  toFun := prefixSequenceForward T u
  invFun := prefixSequenceBackward T u
  left_inv := prefixSequenceBackward_forward T u
  right_inv := prefixSequenceForward_backward T u


/-- The canonical target split sends a prefix coordinate to the supplied embedded value. -/
theorem prefixTargetEquiv_apply_left {N r : ℕ} (T : Finset (Fin N))
    (u : Fin r ↪ T) (k : Fin r) :
    prefixTargetEquiv T u (Sum.inl k) = u k := by
  simp [prefixTargetEquiv, prefixRankEmbedding, increasingTargetEquiv,
    embeddingSplitEquiv_apply_range]

/-- The residual coordinate is forward: output position `k` uses complement rank `ρ k`. -/
theorem rebuildPrefixSequence_apply_residual {N r : ℕ} (T : Finset (Fin N))
    (u : Fin r ↪ T) (ρ : Equiv.Perm (Fin (T.card - r))) (k : Fin (T.card - r)) :
    rebuildPrefixSequence T u ρ (prefixDomainEquiv T u (Sum.inr k)) =
      prefixTargetEquiv T u (Sum.inr (ρ k)) := by
  simp [rebuildPrefixSequence]

/-- The packaged equivalence forwards by the explicit residual restriction. -/
theorem prefixSequenceEquiv_apply {N r : ℕ} (T : Finset (Fin N))
    (u : Fin r ↪ T) (q : PrefixSequenceFiber T u) :
    prefixSequenceEquiv T u q = prefixSequenceForward T u q := by
  rfl

end Math.FiniteEmbedding
