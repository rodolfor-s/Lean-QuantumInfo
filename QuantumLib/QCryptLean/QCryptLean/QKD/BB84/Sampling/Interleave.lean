import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Set.PowersetCard
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Basic
import QCryptLean.QKD.BB84.Sampling.BasisPartition
import QCryptLean.QKD.BB84.Sampling.Selection

/-!
# Interleaving matched Z and X orderings

An actual `Shuffle a b` decomposes into the slots occupied by Z positions and two basis-specific
ordered enumerations. The ordered-list identity identifies these enumerations with `zOrder` and
`xOrder`. Renner, arXiv:quant-ph/0512258v2, lines 673--736, and Pfister et al.,
arXiv:1506.07502v3, Sections IV--V, motivate the sampling schedule; the decomposition is an explicit
finite construction.
-/

namespace QKD.BB84.Sampling

open QKD.BB84.Measurement

/-- View a shuffle on the cardinality of the Z/X partition. -/
def shufflePartitionOrder {N : ℕ} (a b : Fin N → Basis) (o : Shuffle a b) :
    Fin ((MatchedZ a b).card + (MatchedX a b).card) ≃ Matched a b :=
  (finCongr (matchedBasis_partition_card a b).symm).trans o

/-- Raw set of domain slots whose shuffled values lie in the matched-Z subtype. -/
def shuffleZSlotFinset {N : ℕ} (a b : Fin N → Basis) (o : Shuffle a b) :
    Finset (Fin ((MatchedZ a b).card + (MatchedX a b).card)) :=
  Finset.univ.filter fun k =>
    (shufflePartitionOrder a b o k).1 ∈ MatchedZ a b

/-- Exactly `MatchedZ.card` shuffled slots contain matched-Z positions. -/
theorem shuffleZSlot_card {N : ℕ} (a b : Fin N → Basis) (o : Shuffle a b) :
    (shuffleZSlotFinset a b o).card = (MatchedZ a b).card := by
  let q := shufflePartitionOrder a b o
  refine Finset.card_bij
    (fun k _ => (q k).1) (fun _ hk => (Finset.mem_filter.mp hk).2)
    ?_ ?_
  · intro k₁ hk₁ k₂ hk₂ h
    apply q.injective
    apply Subtype.ext
    exact h
  · intro i hi
    let i' : Matched a b := ⟨i, (mem_matchedZ_iff a b i).mp hi |>.1⟩
    let k := q.symm i'
    have hk : k ∈ shuffleZSlotFinset a b o := by
      rw [shuffleZSlotFinset, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      change (q k).1 ∈ MatchedZ a b
      rw [show q k = i' by simp [k]]
      exact hi
    refine ⟨k, hk, ?_⟩
    simp [k, q, i']

/-- The shuffled Z slots as a fixed-cardinality subset. -/
def shuffleZSlots {N : ℕ} (a b : Fin N → Basis) (o : Shuffle a b) :
    Set.powersetCard
      (Fin ((MatchedZ a b).card + (MatchedX a b).card)) (MatchedZ a b).card :=
  ⟨shuffleZSlotFinset a b o, shuffleZSlot_card a b o⟩

/-- The complement of any correctly-sized Z slot set has the matched-X cardinality. -/
theorem interleaveSubset_compl_card {N : ℕ} (a b : Fin N → Basis)
    (S : Set.powersetCard
      (Fin ((MatchedZ a b).card + (MatchedX a b).card)) (MatchedZ a b).card) :
    (S.1ᶜ : Finset (Fin ((MatchedZ a b).card + (MatchedX a b).card))).card =
      (MatchedX a b).card := by
  rw [Finset.card_compl, Fintype.card_fin, S.2]
  omega

/-- Increasing enumeration of the actual shuffled Z slots. -/
def shuffleZSlotOrderEquiv {N : ℕ} (a b : Fin N → Basis) (o : Shuffle a b) :
    Fin (MatchedZ a b).card ≃ shuffleZSlotFinset a b o :=
  ((shuffleZSlotFinset a b o).orderIsoOfFin (shuffleZSlot_card a b o)).toEquiv

/-- Increasing enumeration of the complementary shuffled X slots. -/
def shuffleXSlotOrderEquiv {N : ℕ} (a b : Fin N → Basis) (o : Shuffle a b) :
    Fin (MatchedX a b).card ≃
      {k // k ∈ (shuffleZSlotFinset a b o)ᶜ} :=
  (((shuffleZSlotFinset a b o)ᶜ).orderIsoOfFin
    (interleaveSubset_compl_card a b (shuffleZSlots a b o))).toEquiv

/-- Reading a shuffled value at an enumerated Z slot is well-defined in `MatchedZ`. -/
theorem shuffleZSequenceForward_mem {N : ℕ} (a b : Fin N → Basis)
    (o : Shuffle a b) (k : Fin (MatchedZ a b).card) :
    (shufflePartitionOrder a b o (shuffleZSlotOrderEquiv a b o k).1).1 ∈
      MatchedZ a b := by
  exact (Finset.mem_filter.mp (shuffleZSlotOrderEquiv a b o k).2).2

/-- The inverse shuffled slot of a matched-Z value lies in the Z slot finset. -/
theorem shuffleZSequenceInverse_mem {N : ℕ} (a b : Fin N → Basis)
    (o : Shuffle a b) (i : MatchedZ a b) :
    (shufflePartitionOrder a b o).symm (matchedZInclusion a b i) ∈
      shuffleZSlotFinset a b o := by
  rw [shuffleZSlotFinset, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [Equiv.apply_symm_apply]
  exact i.2

/-- Forward read of the matched-Z sequence. -/
def shuffleZSequenceForward {N : ℕ} (a b : Fin N → Basis) (o : Shuffle a b) :
    Fin (MatchedZ a b).card → MatchedZ a b := fun k =>
  ⟨(shufflePartitionOrder a b o (shuffleZSlotOrderEquiv a b o k).1).1,
    shuffleZSequenceForward_mem a b o k⟩

/-- Explicit inverse rank of a matched-Z value among the shuffled Z slots. -/
def shuffleZSequenceInverse {N : ℕ} (a b : Fin N → Basis) (o : Shuffle a b) :
    MatchedZ a b → Fin (MatchedZ a b).card := fun i =>
  (shuffleZSlotOrderEquiv a b o).symm
    ⟨(shufflePartitionOrder a b o).symm (matchedZInclusion a b i),
      shuffleZSequenceInverse_mem a b o i⟩

/-- Inverse Z ranking after forward reading is the identity. -/
theorem shuffleZSequenceInverse_forward {N : ℕ} (a b : Fin N → Basis)
    (o : Shuffle a b) (k : Fin (MatchedZ a b).card) :
    shuffleZSequenceInverse a b o (shuffleZSequenceForward a b o k) = k := by
  unfold shuffleZSequenceInverse shuffleZSequenceForward
  apply (shuffleZSlotOrderEquiv a b o).injective
  apply Subtype.ext
  simp only [Equiv.apply_symm_apply]
  change (shufflePartitionOrder a b o).symm
    (shufflePartitionOrder a b o (shuffleZSlotOrderEquiv a b o k).1) = _
  exact Equiv.symm_apply_apply _ _

/-- Forward Z-sequence reading after inverse ranking is the identity. -/
theorem shuffleZSequenceForward_inverse {N : ℕ} (a b : Fin N → Basis)
    (o : Shuffle a b) (i : MatchedZ a b) :
    shuffleZSequenceForward a b o (shuffleZSequenceInverse a b o i) = i := by
  unfold shuffleZSequenceInverse shuffleZSequenceForward
  apply Subtype.ext
  simp only [Equiv.apply_symm_apply]
  rfl

/-- Ordered enumeration of matched-Z values read from their increasing shuffled slots. -/
def shuffleZSequenceEquiv {N : ℕ} (a b : Fin N → Basis) (o : Shuffle a b) :
    Fin (MatchedZ a b).card ≃ MatchedZ a b where
  toFun := shuffleZSequenceForward a b o
  invFun := shuffleZSequenceInverse a b o
  left_inv := shuffleZSequenceInverse_forward a b o
  right_inv := shuffleZSequenceForward_inverse a b o

/-- Reading a shuffled value at an enumerated X slot is well-defined in `MatchedX`. -/
theorem shuffleXSequenceForward_mem {N : ℕ} (a b : Fin N → Basis)
    (o : Shuffle a b) (k : Fin (MatchedX a b).card) :
    (shufflePartitionOrder a b o (shuffleXSlotOrderEquiv a b o k).1).1 ∈
      MatchedX a b := by
  have hnotZ :
      (shuffleXSlotOrderEquiv a b o k).1 ∉ shuffleZSlotFinset a b o := by
    exact Finset.mem_compl.mp (shuffleXSlotOrderEquiv a b o k).2
  have hnotZ' :
      (shufflePartitionOrder a b o (shuffleXSlotOrderEquiv a b o k).1).1 ∉
        MatchedZ a b := by
    simpa [shuffleZSlotFinset] using hnotZ
  have hall :
      (shufflePartitionOrder a b o (shuffleXSlotOrderEquiv a b o k).1).1 ∈
        MatchedZ a b ∪ MatchedX a b := by
    rw [matchedBasis_union]
    exact (shufflePartitionOrder a b o (shuffleXSlotOrderEquiv a b o k).1).2
  rcases Finset.mem_union.mp hall with hZ | hX
  · exact (hnotZ' hZ).elim
  · exact hX

/-- The inverse shuffled slot of a matched-X value lies in the complementary X slot finset. -/
theorem shuffleXSequenceInverse_mem {N : ℕ} (a b : Fin N → Basis)
    (o : Shuffle a b) (i : MatchedX a b) :
    (shufflePartitionOrder a b o).symm (matchedXInclusion a b i) ∈
      (shuffleZSlotFinset a b o)ᶜ := by
  rw [Finset.mem_compl]
  intro hZSlot
  have hZ : i.1 ∈ MatchedZ a b := by
    have := (Finset.mem_filter.mp hZSlot).2
    rw [Equiv.apply_symm_apply] at this
    exact this
  exact (Finset.disjoint_left.mp (matchedBasis_disjoint a b) hZ i.2)

/-- Forward read of the matched-X sequence. -/
def shuffleXSequenceForward {N : ℕ} (a b : Fin N → Basis) (o : Shuffle a b) :
    Fin (MatchedX a b).card → MatchedX a b := fun k =>
  ⟨(shufflePartitionOrder a b o (shuffleXSlotOrderEquiv a b o k).1).1,
    shuffleXSequenceForward_mem a b o k⟩

/-- Explicit inverse rank of a matched-X value among the shuffled X slots. -/
def shuffleXSequenceInverse {N : ℕ} (a b : Fin N → Basis) (o : Shuffle a b) :
    MatchedX a b → Fin (MatchedX a b).card := fun i =>
  (shuffleXSlotOrderEquiv a b o).symm
    ⟨(shufflePartitionOrder a b o).symm (matchedXInclusion a b i),
      shuffleXSequenceInverse_mem a b o i⟩

/-- Inverse X ranking after forward reading is the identity. -/
theorem shuffleXSequenceInverse_forward {N : ℕ} (a b : Fin N → Basis)
    (o : Shuffle a b) (k : Fin (MatchedX a b).card) :
    shuffleXSequenceInverse a b o (shuffleXSequenceForward a b o k) = k := by
  unfold shuffleXSequenceInverse shuffleXSequenceForward
  apply (shuffleXSlotOrderEquiv a b o).injective
  apply Subtype.ext
  simp only [Equiv.apply_symm_apply]
  change (shufflePartitionOrder a b o).symm
    (shufflePartitionOrder a b o (shuffleXSlotOrderEquiv a b o k).1) = _
  exact Equiv.symm_apply_apply _ _

/-- Forward X-sequence reading after inverse ranking is the identity. -/
theorem shuffleXSequenceForward_inverse {N : ℕ} (a b : Fin N → Basis)
    (o : Shuffle a b) (i : MatchedX a b) :
    shuffleXSequenceForward a b o (shuffleXSequenceInverse a b o i) = i := by
  unfold shuffleXSequenceInverse shuffleXSequenceForward
  apply Subtype.ext
  simp only [Equiv.apply_symm_apply]
  rfl

/-- Ordered enumeration of matched-X values read from their increasing shuffled slots. -/
def shuffleXSequenceEquiv {N : ℕ} (a b : Fin N → Basis) (o : Shuffle a b) :
    Fin (MatchedX a b).card ≃ MatchedX a b where
  toFun := shuffleXSequenceForward a b o
  invFun := shuffleXSequenceInverse a b o
  left_inv := shuffleXSequenceInverse_forward a b o
  right_inv := shuffleXSequenceForward_inverse a b o

/-- Interleaving coordinates: Z slots together with ordered Z and X enumerations. -/
abbrev ShuffleInterleaveData {N : ℕ} (a b : Fin N → Basis) :=
  Set.powersetCard
      (Fin ((MatchedZ a b).card + (MatchedX a b).card)) (MatchedZ a b).card ×
    ((Fin (MatchedZ a b).card ≃ MatchedZ a b) ×
      (Fin (MatchedX a b).card ≃ MatchedX a b))

/-- Extract the explicit interleaving coordinates of one actual matched shuffle. -/
def shuffleInterleaveForward {N : ℕ} (a b : Fin N → Basis) (o : Shuffle a b) :
    ShuffleInterleaveData a b :=
  ⟨shuffleZSlots a b o, shuffleZSequenceEquiv a b o, shuffleXSequenceEquiv a b o⟩

/-- Reconstruct the partition-domain ordering from arbitrary interleaving coordinates. -/
def interleavePartitionOrder {N : ℕ} (a b : Fin N → Basis)
    (d : ShuffleInterleaveData a b) :
    Fin ((MatchedZ a b).card + (MatchedX a b).card) ≃ Matched a b :=
  (finSumEquivOfFinset d.1.2 (interleaveSubset_compl_card a b d.1)).symm.trans
    ((Equiv.sumCongr d.2.1 d.2.2).trans (matchedBasisSumEquiv a b))

/-- Reconstruct an actual shuffle from explicit Z slots and ordered basis enumerations. -/
def shuffleInterleaveBackward {N : ℕ} (a b : Fin N → Basis)
    (d : ShuffleInterleaveData a b) : Shuffle a b :=
  (finCongr (matchedBasis_partition_card a b)).trans (interleavePartitionOrder a b d)

/-- Reconstructing the extracted coordinates recovers the original shuffle. -/
theorem shuffleInterleaveBackward_forward {N : ℕ} (a b : Fin N → Basis)
    (o : Shuffle a b) :
    shuffleInterleaveBackward a b (shuffleInterleaveForward a b o) = o := by
  apply Equiv.ext
  intro k
  let e := finSumEquivOfFinset (shuffleZSlot_card a b o)
    (interleaveSubset_compl_card a b (shuffleZSlots a b o))
  let t := finCongr (matchedBasis_partition_card a b) k
  change (matchedBasisSumEquiv a b)
    ((Equiv.sumCongr (shuffleZSequenceEquiv a b o) (shuffleXSequenceEquiv a b o))
      (e.symm t)) = o k
  generalize hs : e.symm t = s
  have hs' := congrArg e hs
  simp only [Equiv.apply_symm_apply] at hs'
  rcases s with j | j
  · change matchedZInclusion a b (shuffleZSequenceForward a b o j) = o k
    apply Subtype.ext
    change (shufflePartitionOrder a b o (shuffleZSlotOrderEquiv a b o j).1).1 =
      (o k).1
    have hslot : (shuffleZSlotOrderEquiv a b o j).1 = t := by
      exact hs'.symm
    rw [hslot]
    simp [t, shufflePartitionOrder]
  · change matchedXInclusion a b (shuffleXSequenceForward a b o j) = o k
    apply Subtype.ext
    change (shufflePartitionOrder a b o (shuffleXSlotOrderEquiv a b o j).1).1 =
      (o k).1
    have hslot : (shuffleXSlotOrderEquiv a b o j).1 = t := by
      exact hs'.symm
    rw [hslot]
    simp [t, shufflePartitionOrder]

/-- Extracting after reconstruction recovers every interleaving coordinate. -/
theorem shuffleInterleaveForward_backward {N : ℕ} (a b : Fin N → Basis)
    (d : ShuffleInterleaveData a b) :
    shuffleInterleaveForward a b (shuffleInterleaveBackward a b d) = d := by
  have hpartition :
      shufflePartitionOrder a b (shuffleInterleaveBackward a b d) =
        interleavePartitionOrder a b d := by
    apply Equiv.ext
    intro k
    simp [shufflePartitionOrder, shuffleInterleaveBackward]
  have hslots :
      shuffleZSlotFinset a b (shuffleInterleaveBackward a b d) = d.1.1 := by
    ext k
    rw [shuffleZSlotFinset, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    let e := finSumEquivOfFinset d.1.2 (interleaveSubset_compl_card a b d.1)
    change
      ((matchedBasisSumEquiv a b)
        ((Equiv.sumCongr d.2.1 d.2.2) (e.symm k))).1 ∈ MatchedZ a b ↔ k ∈ d.1.1
    generalize hs : e.symm k = s
    have hs' := congrArg e hs
    simp only [Equiv.apply_symm_apply] at hs'
    rcases s with j | j
    · change (d.2.1 j).1 ∈ MatchedZ a b ↔ k ∈ d.1.1
      constructor
      · intro _
        rw [hs']
        exact Finset.orderEmbOfFin_mem d.1.1 d.1.2 j
      · intro _
        exact (d.2.1 j).2
    · change (d.2.2 j).1 ∈ MatchedZ a b ↔ k ∈ d.1.1
      constructor
      · intro hZ
        exact (Finset.disjoint_left.mp (matchedBasis_disjoint a b) hZ (d.2.2 j).2).elim
      · intro hk
        rw [hs'] at hk
        have hj := Finset.orderEmbOfFin_mem (d.1.1ᶜ)
          (interleaveSubset_compl_card a b d.1) j
        exact (Finset.mem_compl.mp hj hk).elim
  have hZorder :
      (shuffleZSlotFinset a b (shuffleInterleaveBackward a b d)).orderEmbOfFin
          (shuffleZSlot_card a b (shuffleInterleaveBackward a b d)) =
        d.1.1.orderEmbOfFin d.1.2 := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro j
    rw [hslots]
    exact Finset.orderEmbOfFin_mem d.1.1 d.1.2 j
  have hXorder :
      ((shuffleZSlotFinset a b (shuffleInterleaveBackward a b d))ᶜ).orderEmbOfFin
          (interleaveSubset_compl_card a b
            (shuffleZSlots a b (shuffleInterleaveBackward a b d))) =
        (d.1.1ᶜ).orderEmbOfFin (interleaveSubset_compl_card a b d.1) := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro j
    apply Finset.mem_compl.mpr
    intro hj
    rw [hslots] at hj
    exact (Finset.mem_compl.mp (Finset.orderEmbOfFin_mem (d.1.1ᶜ)
      (interleaveSubset_compl_card a b d.1) j)) hj
  apply Prod.ext
  · apply Subtype.ext
    exact hslots
  · apply Prod.ext
    · apply Equiv.ext
      intro j
      apply Subtype.ext
      change (shufflePartitionOrder a b (shuffleInterleaveBackward a b d)
        (shuffleZSlotOrderEquiv a b (shuffleInterleaveBackward a b d) j).1).1 =
          (d.2.1 j).1
      have hj :
          (shuffleZSlotOrderEquiv a b (shuffleInterleaveBackward a b d) j).1 =
            d.1.1.orderEmbOfFin d.1.2 j := by
        exact congrArg (fun f => f j) hZorder
      rw [hpartition, hj]
      simp only [interleavePartitionOrder, Equiv.trans_apply, Equiv.sumCongr_apply]
      rw [← finSumEquivOfFinset_inl d.1.2 (interleaveSubset_compl_card a b d.1) j,
        Equiv.symm_apply_apply]
      rfl
    · apply Equiv.ext
      intro j
      apply Subtype.ext
      change (shufflePartitionOrder a b (shuffleInterleaveBackward a b d)
        (shuffleXSlotOrderEquiv a b (shuffleInterleaveBackward a b d) j).1).1 =
          (d.2.2 j).1
      have hj :
          (shuffleXSlotOrderEquiv a b (shuffleInterleaveBackward a b d) j).1 =
            (d.1.1ᶜ).orderEmbOfFin (interleaveSubset_compl_card a b d.1) j := by
        exact congrArg (fun f => f j) hXorder
      rw [hpartition, hj]
      simp only [interleavePartitionOrder, Equiv.trans_apply, Equiv.sumCongr_apply]
      rw [← finSumEquivOfFinset_inr d.1.2 (interleaveSubset_compl_card a b d.1) j,
        Equiv.symm_apply_apply]
      rfl

/-- Actual matched shuffles are equivalent to their explicit Z/X interleaving coordinates. -/
def shuffleInterleaveEquiv {N : ℕ} (a b : Fin N → Basis) :
    Shuffle a b ≃ ShuffleInterleaveData a b where
  toFun := shuffleInterleaveForward a b
  invFun := shuffleInterleaveBackward a b
  left_inv := shuffleInterleaveBackward_forward a b
  right_inv := shuffleInterleaveForward_backward a b

/-- The two sequence coordinates are exactly the literal stable-filtered production orders.

The statement compares ordered lists of underlying `Fin N` values, not merely equal finsets. -/
theorem shuffleInterleave_basisLists {N : ℕ} (a b : Fin N → Basis)
    (o : Shuffle a b) :
    (List.ofFn fun k : Fin (MatchedZ a b).card => (shuffleZSequenceEquiv a b o k).1) =
        zOrder ⟨a, b, o⟩ ∧
      (List.ofFn fun k : Fin (MatchedX a b).card =>
        (shuffleXSequenceEquiv a b o k).1) = xOrder ⟨a, b, o⟩ := by
  have orderedFilter (n m : ℕ) (S : Finset (Fin n)) (h : S.card = m) :
      List.ofFn (fun j : Fin m => S.orderEmbOfFin h j) =
        (List.ofFn fun k : Fin n => k).filter fun k => decide (k ∈ S) := by
    rw [List.ofFn_eq_map, Finset.listMap_orderEmbOfFin_finRange,
      show (List.ofFn fun k : Fin n => k) = List.finRange n by exact List.ofFn_id n]
    let l := (List.finRange n).filter fun k => decide (k ∈ S)
    have hl : l.toFinset = S := by
      ext k
      simp [l]
    calc
      S.sort = l.toFinset.sort := by rw [hl]
      _ = l := (List.toFinset_sort (r := fun a b => a ≤ b)
        ((List.nodup_finRange n).filter _)).mpr
          (((List.sortedLT_finRange n).pairwise.filter _).imp fun h => h.le)
      _ = _ := rfl
  let q := shufflePartitionOrder a b o
  have hq :
      List.ofFn (fun k : Fin ((MatchedZ a b).card + (MatchedX a b).card) => (q k).1) =
        matchedOrder ⟨a, b, o⟩ := by
    change List.ofFn (fun k => (q k).1) =
      List.ofFn (fun k : Fin (Matched a b).card => (o k).1)
    rw [List.ofFn_congr (matchedBasis_partition_card a b).symm]
    congr 1
  have hZpred (k : Fin ((MatchedZ a b).card + (MatchedX a b).card)) :
      decide (k ∈ shuffleZSlotFinset a b o) = decide (a (q k).1 = Basis.z) := by
    simp [shuffleZSlotFinset, q, mem_matchedZ_iff]
  have hXpred (k : Fin ((MatchedZ a b).card + (MatchedX a b).card)) :
      decide (k ∈ (shuffleZSlotFinset a b o)ᶜ) = decide (a (q k).1 = Basis.x) := by
    apply decide_eq_decide.mpr
    rw [Finset.mem_compl]
    constructor
    · intro hnotZ
      have hall : (q k).1 ∈ MatchedZ a b ∪ MatchedX a b := by
        rw [matchedBasis_union]
        exact (q k).2
      rcases Finset.mem_union.mp hall with hZ | hX
      · exact (hnotZ (by simpa [shuffleZSlotFinset, q] using hZ)).elim
      · exact (mem_matchedX_iff a b (q k).1).mp hX |>.2
    · intro hX hslot
      have hZ : (q k).1 ∈ MatchedZ a b := by
        simpa [shuffleZSlotFinset, q] using hslot
      have hXmem : (q k).1 ∈ MatchedX a b :=
        (mem_matchedX_iff a b (q k).1).mpr ⟨(q k).2, hX⟩
      exact Finset.disjoint_left.mp (matchedBasis_disjoint a b) hZ hXmem
  constructor
  · change List.ofFn (fun k : Fin (MatchedZ a b).card =>
      (q (shuffleZSlotOrderEquiv a b o k).1).1) = zOrder ⟨a, b, o⟩
    calc
      _ = (List.ofFn fun k : Fin (MatchedZ a b).card =>
          (shuffleZSlotOrderEquiv a b o k).1).map (fun k => (q k).1) := by
            rw [List.map_ofFn]
            rfl
      _ = ((List.ofFn fun k : Fin ((MatchedZ a b).card + (MatchedX a b).card) => k).filter
          fun k => decide (k ∈ shuffleZSlotFinset a b o)).map (fun k => (q k).1) := by
            apply congrArg (List.map fun k => (q k).1)
            simpa [shuffleZSlotOrderEquiv] using
              orderedFilter _ _ (shuffleZSlotFinset a b o) (shuffleZSlot_card a b o)
      _ = (List.ofFn fun k : Fin ((MatchedZ a b).card + (MatchedX a b).card) =>
          (q k).1).filter fun i => decide (a i = Basis.z) := by
            rw [show (fun k => decide (k ∈ shuffleZSlotFinset a b o)) =
              (fun i => decide (a i = Basis.z)) ∘ (fun k => (q k).1) by
                funext k
                exact hZpred k]
            rw [← List.filter_map]
            simp [List.map_ofFn, Function.comp_def]
      _ = zOrder ⟨a, b, o⟩ := by rw [hq]; rfl
  · change List.ofFn (fun k : Fin (MatchedX a b).card =>
      (q (shuffleXSlotOrderEquiv a b o k).1).1) = xOrder ⟨a, b, o⟩
    calc
      _ = (List.ofFn fun k : Fin (MatchedX a b).card =>
          (shuffleXSlotOrderEquiv a b o k).1).map (fun k => (q k).1) := by
            rw [List.map_ofFn]
            rfl
      _ = ((List.ofFn fun k : Fin ((MatchedZ a b).card + (MatchedX a b).card) => k).filter
          fun k => decide (k ∈ (shuffleZSlotFinset a b o)ᶜ)).map (fun k => (q k).1) := by
            apply congrArg (List.map fun k => (q k).1)
            exact orderedFilter _ _ ((shuffleZSlotFinset a b o)ᶜ)
                (interleaveSubset_compl_card a b (shuffleZSlots a b o))
      _ = (List.ofFn fun k : Fin ((MatchedZ a b).card + (MatchedX a b).card) =>
          (q k).1).filter fun i => decide (a i = Basis.x) := by
            rw [show (fun k => decide (k ∈ (shuffleZSlotFinset a b o)ᶜ)) =
              (fun i => decide (a i = Basis.x)) ∘ (fun k => (q k).1) by
                funext k
                exact hXpred k]
            rw [← List.filter_map]
            simp [List.map_ofFn, Function.comp_def]
      _ = xOrder ⟨a, b, o⟩ := by rw [hq]; rfl

/-- Equality of subtype-valued literal prefixes is equivalent to equality after mapping
`Subtype.val`; `List.map_take` and `List.map_ofFn` identify the latter with the actual underlying
value-list prefixes. -/
theorem subtypePrefix_eq_iff_valPrefix {N r : ℕ} (T : Finset (Fin N))
    (u : Fin r ↪ T) (q : Fin T.card ≃ T) :
    (List.ofFn fun k : Fin T.card => q k).take r = List.ofFn (fun k : Fin r => u k) ↔
      (List.ofFn fun k : Fin T.card => (q k).1).take r =
        List.ofFn (fun k : Fin r => (u k).1) := by
  constructor
  · intro h
    simpa [List.map_take, List.map_ofFn, Function.comp_def] using
      congrArg (List.map Subtype.val) h
  · intro h
    apply (List.map_injective_iff.mpr Subtype.val_injective)
    simpa [List.map_take, List.map_ofFn, Function.comp_def] using h

end QKD.BB84.Sampling
