import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Basic

/-!
# Partition matched BB84 positions by basis

The actual `Matched` identifiers split into Z and X subtypes, with an explicit sum equivalence.
Renner, arXiv:quant-ph/0512258v2, lines 673--736, and Pfister et al.,
arXiv:1506.07502v3, Sections IV--V, motivate late fixed-batch sifting; this partition is an
explicit finite construction.
-/

namespace QKD.BB84.Sampling

open QKD.BB84.Measurement

/-- Matched positions at which Alice used the Z basis. -/
def MatchedZ {N : ℕ} (a b : Fin N → Basis) : Finset (Fin N) :=
  (Matched a b).filter fun i => a i = Basis.z

/-- Matched positions at which Alice used the X basis. -/
def MatchedX {N : ℕ} (a b : Fin N → Basis) : Finset (Fin N) :=
  (Matched a b).filter fun i => a i = Basis.x

/-- Membership in `MatchedZ` is matched membership together with Alice's Z basis. -/
@[simp]
theorem mem_matchedZ_iff {N : ℕ} (a b : Fin N → Basis) (i : Fin N) :
    i ∈ MatchedZ a b ↔ i ∈ Matched a b ∧ a i = Basis.z := by
  simp [MatchedZ]

/-- Membership in `MatchedX` is matched membership together with Alice's X basis. -/
@[simp]
theorem mem_matchedX_iff {N : ℕ} (a b : Fin N → Basis) (i : Fin N) :
    i ∈ MatchedX a b ↔ i ∈ Matched a b ∧ a i = Basis.x := by
  simp [MatchedX]

/-- The Z and X matched-position finsets are disjoint. -/
theorem matchedBasis_disjoint {N : ℕ} (a b : Fin N → Basis) :
    Disjoint (MatchedZ a b) (MatchedX a b) := by
  rw [Finset.disjoint_left]
  intro i hiZ hiX
  have hZ := (mem_matchedZ_iff a b i).mp hiZ
  have hX := (mem_matchedX_iff a b i).mp hiX
  simp [hZ.2] at hX

/-- The Z and X matched-position finsets cover the complete matched finset. -/
theorem matchedBasis_union {N : ℕ} (a b : Fin N → Basis) :
    MatchedZ a b ∪ MatchedX a b = Matched a b := by
  ext i
  constructor
  · intro hi
    rcases Finset.mem_union.mp hi with hiZ | hiX
    · exact (mem_matchedZ_iff a b i).mp hiZ |>.1
    · exact (mem_matchedX_iff a b i).mp hiX |>.1
  · intro hi
    cases hbasis : a i with
    | z =>
        exact Finset.mem_union_left _ ((mem_matchedZ_iff a b i).mpr ⟨hi, hbasis⟩)
    | x =>
        exact Finset.mem_union_right _ ((mem_matchedX_iff a b i).mpr ⟨hi, hbasis⟩)

/-- Cardinality of the disjoint Z/X partition of the actual matched positions. -/
theorem matchedBasis_partition_card {N : ℕ} (a b : Fin N → Basis) :
    (Matched a b).card = (MatchedZ a b).card + (MatchedX a b).card := by
  rw [← matchedBasis_union a b,
    Finset.card_union_of_disjoint (matchedBasis_disjoint a b)]

/-- Inclusion of a matched Z position into the full matched-position subtype. -/
def matchedZInclusion {N : ℕ} (a b : Fin N → Basis) :
    MatchedZ a b ↪ Matched a b where
  toFun i := ⟨i.1, (mem_matchedZ_iff a b i).mp i.2 |>.1⟩
  inj' := fun _ _ h =>
    Subtype.ext (congrArg (fun j : Matched a b => j.1) h)

/-- Inclusion of a matched X position into the full matched-position subtype. -/
def matchedXInclusion {N : ℕ} (a b : Fin N → Basis) :
    MatchedX a b ↪ Matched a b where
  toFun i := ⟨i.1, (mem_matchedX_iff a b i).mp i.2 |>.1⟩
  inj' := fun _ _ h =>
    Subtype.ext (congrArg (fun j : Matched a b => j.1) h)

/-- Forward inclusion of the basis-partitioned sum into the full matched subtype. -/
def matchedBasisSumForward {N : ℕ} (a b : Fin N → Basis) :
    MatchedZ a b ⊕ MatchedX a b → Matched a b :=
  Sum.elim (matchedZInclusion a b) (matchedXInclusion a b)

/-- Explicit inverse, determined by the two constructors of the actual BB84 basis. -/
def matchedBasisSumBackward {N : ℕ} (a b : Fin N → Basis) :
    Matched a b → MatchedZ a b ⊕ MatchedX a b := fun i =>
  match hbasis : a i.1 with
  | Basis.z => Sum.inl ⟨i.1, by simp [MatchedZ, i.2, hbasis]⟩
  | Basis.x => Sum.inr ⟨i.1, by simp [MatchedX, i.2, hbasis]⟩

/-- The explicit basis case split is a left inverse of the two inclusions. -/
theorem matchedBasisSumBackward_forward {N : ℕ} (a b : Fin N → Basis)
    (i : MatchedZ a b ⊕ MatchedX a b) :
    matchedBasisSumBackward a b (matchedBasisSumForward a b i) = i := by
  rcases i with i | i
  · unfold matchedBasisSumForward matchedBasisSumBackward
    simp only [Sum.elim_inl, matchedZInclusion]
    split
    · rfl
    · rename_i hbasis
      change a i.1 = Basis.x at hbasis
      have hi := (mem_matchedZ_iff a b i).mp i.2
      simp_all
  · unfold matchedBasisSumForward matchedBasisSumBackward
    simp only [Sum.elim_inr, matchedXInclusion]
    split
    · rename_i hbasis
      change a i.1 = Basis.z at hbasis
      have hi := (mem_matchedX_iff a b i).mp i.2
      simp_all
    · rfl

/-- The two inclusions are a left inverse of the explicit basis case split. -/
theorem matchedBasisSumForward_backward {N : ℕ} (a b : Fin N → Basis)
    (i : Matched a b) :
    matchedBasisSumForward a b (matchedBasisSumBackward a b i) = i := by
  unfold matchedBasisSumBackward
  split
  · apply Subtype.ext
    rfl
  · apply Subtype.ext
    rfl

/-- Explicit equivalence between the disjoint basis subtypes and all matched positions. -/
def matchedBasisSumEquiv {N : ℕ} (a b : Fin N → Basis) :
    MatchedZ a b ⊕ MatchedX a b ≃ Matched a b where
  toFun := matchedBasisSumForward a b
  invFun := matchedBasisSumBackward a b
  left_inv := matchedBasisSumBackward_forward a b
  right_inv := matchedBasisSumForward_backward a b

end QKD.BB84.Sampling
