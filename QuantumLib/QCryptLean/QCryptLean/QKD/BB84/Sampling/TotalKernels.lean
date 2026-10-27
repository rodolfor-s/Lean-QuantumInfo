import QCryptLean.Math.FiniteEmbedding
import QCryptLean.Math.FiniteEmbedding.SubsetPerm
import QCryptLean.Math.Probability.PMFFilterOrPure
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Basic
import QCryptLean.QKD.BB84.Sampling.Disintegration
import QCryptLean.QKD.BB84.Sampling.FiberMass
import QCryptLean.QKD.BB84.Sampling.Selection

/-! # Total Kernels -/


open scoped ENNReal BigOperators

noncomputable section

namespace QKD.BB84.Sampling

open QKD.BB84.Measurement
open Math.FiniteEmbedding

/-- The X-role block of a packed selected embedding. -/
def fiberDefaultXEmbedding
    {N nK mZ mX : ℕ} (f : Fin (nK + mZ + mX) ↪ Fin N) : Fin mX ↪ Fin N where
  toFun k := f (Fin.natAdd (nK + mZ) k)
  inj' := by
    intro k l h
    have h' := congrArg Fin.val (f.injective h)
    apply Fin.ext
    simpa using h'

/-- Basis string that is X precisely on the X-role image and Z everywhere else. -/
def fiberDefaultBasis
    {N nK mZ mX : ℕ} (f : Fin (nK + mZ + mX) ↪ Fin N) : Fin N → Basis :=
  fun i =>
    if i ∈ embeddingRange (fiberDefaultXEmbedding f) then Basis.x else Basis.z

/-- Every basis string is explicitly equivalent to its self-matched subtype. -/
def selfMatchedEquiv {N : ℕ} (a : Fin N → Basis) :
    Fin N ≃ {i : Fin N // i ∈ Matched a a} where
  toFun i := ⟨i, by simp [Matched]⟩
  invFun i := i.1
  left_inv _ := rfl
  right_inv i := by
    apply Subtype.ext
    rfl

/-- The selected embedding followed by the increasing enumeration of its complement. -/
def fiberDefaultOrderEquiv
    {N nK mZ mX : ℕ} (f : Fin (nK + mZ + mX) ↪ Fin N) : Fin N ≃ Fin N :=
  let hN : nK + mZ + mX ≤ N := by
    simpa using Fintype.card_le_of_injective f f.injective
  (finCongr (Nat.add_sub_of_le hN)).symm |>.trans
    (finSumFinEquiv :
      Fin (nK + mZ + mX) ⊕ Fin (N - (nK + mZ + mX)) ≃
        Fin ((nK + mZ + mX) + (N - (nK + mZ + mX)))).symm |>.trans
    (embeddingSplitEquiv f)


/-- The X-role embedding is the final block of the supplied packed embedding. -/
theorem fiberDefaultXEmbedding_apply
    {N nK mZ mX : ℕ} (f : Fin (nK + mZ + mX) ↪ Fin N) (k : Fin mX) :
    fiberDefaultXEmbedding f k = f (Fin.natAdd (nK + mZ) k) := by
  rfl

/-- The first block of the order equivalence follows the supplied embedding in its actual order. -/
theorem fiberDefaultOrderEquiv_apply_selected
    {N nK mZ mX : ℕ} (f : Fin (nK + mZ + mX) ↪ Fin N)
    (k : Fin (nK + mZ + mX)) :
    fiberDefaultOrderEquiv f
        (Fin.castLE
          (by simpa using Fintype.card_le_of_injective f f.injective) k) = f k := by
  let hN : nK + mZ + mX ≤ N := by
    simpa using Fintype.card_le_of_injective f f.injective
  let hsum : (nK + mZ + mX) + (N - (nK + mZ + mX)) = N :=
    Nat.add_sub_of_le hN
  change
    embeddingSplitEquiv f
        (finSumFinEquiv.symm
          ((finCongr hsum).symm (Fin.castLE hN k))) = f k
  have hcast :
      (finCongr hsum).symm (Fin.castLE hN k) =
        Fin.castAdd (N - (nK + mZ + mX)) k := by
    apply Fin.ext
    rfl
  rw [hcast, finSumFinEquiv_symm_apply_castAdd,
    embeddingSplitEquiv_apply_range]

/-- The residual block of the order equivalence uses the increasing complement in forward order. -/
theorem fiberDefaultOrderEquiv_apply_complement
    {N nK mZ mX : ℕ} (f : Fin (nK + mZ + mX) ↪ Fin N)
    (k : Fin (N - (nK + mZ + mX))) :
    fiberDefaultOrderEquiv f
        ⟨nK + mZ + mX + k.val,
          by
            have hN : nK + mZ + mX ≤ N := by
              simpa using Fintype.card_le_of_injective f f.injective
            omega⟩ =
      embeddingComplementEquiv f k := by
  let hN : nK + mZ + mX ≤ N := by
    simpa using Fintype.card_le_of_injective f f.injective
  let hsum : (nK + mZ + mX) + (N - (nK + mZ + mX)) = N :=
    Nat.add_sub_of_le hN
  change
    embeddingSplitEquiv f
        (finSumFinEquiv.symm
          ((finCongr hsum).symm
            ⟨nK + mZ + mX + k.val, by omega⟩)) =
      embeddingComplementEquiv f k
  have hcast :
      (finCongr hsum).symm
          ⟨nK + mZ + mX + k.val, by omega⟩ =
        Fin.natAdd (nK + mZ + mX) k := by
    apply Fin.ext
    rfl
  rw [hcast, finSumFinEquiv_symm_apply_natAdd,
    embeddingSplitEquiv_apply_complement]

/-- The all-matched shuffle whose selected prefix follows `f` and whose remaining identifiers
follow the increasing complement of `range f`. -/
def fiberDefaultShuffle
    {N nK mZ mX : ℕ} (f : Fin (nK + mZ + mX) ↪ Fin N) :
    Shuffle (fiberDefaultBasis f) (fiberDefaultBasis f) :=
  (finCongr (by simp [Matched])).trans
    ((fiberDefaultOrderEquiv f).trans (selfMatchedEquiv (fiberDefaultBasis f)))

/-- Explicit raw control in the selected fibre of `f`.

Alice and Bob agree on every basis.  The first `nK + mZ` selected positions are Z, the next `mX`
selected positions are X, and all remaining positions are ordered by the increasing complement
enumeration. -/
def fiberDefaultRawControl
    {N nK mZ mX : ℕ} (f : Fin (nK + mZ + mX) ↪ Fin N) : RawControl N :=
  ⟨fiberDefaultBasis f, fiberDefaultBasis f, fiberDefaultShuffle f⟩

/-- The explicit selected-fibre fallback meets both quotas. -/
theorem hasQuotas_fiberDefaultRawControl
    {N nK mZ mX : ℕ} (f : Fin (nK + mZ + mX) ↪ Fin N) :
    HasQuotas nK mZ mX (fiberDefaultRawControl f) := by
  let hN : nK + mZ + mX ≤ N := by
    simpa using Fintype.card_le_of_injective f f.injective
  have hmatchedOrder :
      matchedOrder (fiberDefaultRawControl f) =
        List.ofFn (fiberDefaultOrderEquiv f) := by
    apply List.ext_get
    · simp [matchedOrder, fiberDefaultRawControl, Matched]
    · intro n h1 h2
      simp [matchedOrder, fiberDefaultRawControl, fiberDefaultShuffle,
        selfMatchedEquiv, Matched]
      rfl
  have hZMem (k : Fin (nK + mZ)) :
      f (Fin.castAdd mX k) ∈ zOrder (fiberDefaultRawControl f) := by
    have hnotX :
        f (Fin.castAdd mX k) ∉ embeddingRange (fiberDefaultXEmbedding f) := by
      intro hmem
      rw [mem_embeddingRange_iff] at hmem
      obtain ⟨x, hx⟩ := hmem
      rw [fiberDefaultXEmbedding_apply] at hx
      have hk := f.injective hx
      have hkval := congrArg Fin.val hk
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hkval
      omega
    have hmatched :
        f (Fin.castAdd mX k) ∈ matchedOrder (fiberDefaultRawControl f) := by
      rw [hmatchedOrder, List.mem_ofFn']
      refine ⟨Fin.castLE hN (Fin.castAdd mX k), ?_⟩
      exact fiberDefaultOrderEquiv_apply_selected f (Fin.castAdd mX k)
    rw [zOrder, List.mem_filter]
    exact ⟨hmatched, by
      simp [fiberDefaultRawControl, fiberDefaultBasis, hnotX]⟩
  have hXMem (k : Fin mX) :
      f (Fin.natAdd (nK + mZ) k) ∈ xOrder (fiberDefaultRawControl f) := by
    have hmemX :
        f (Fin.natAdd (nK + mZ) k) ∈
          embeddingRange (fiberDefaultXEmbedding f) := by
      rw [mem_embeddingRange_iff]
      exact ⟨k, fiberDefaultXEmbedding_apply f k⟩
    have hmatched :
        f (Fin.natAdd (nK + mZ) k) ∈
          matchedOrder (fiberDefaultRawControl f) := by
      rw [hmatchedOrder, List.mem_ofFn']
      refine ⟨Fin.castLE hN (Fin.natAdd (nK + mZ) k), ?_⟩
      exact fiberDefaultOrderEquiv_apply_selected f (Fin.natAdd (nK + mZ) k)
    rw [xOrder, List.mem_filter]
    exact ⟨hmatched, by
      simp [fiberDefaultRawControl, fiberDefaultBasis, hmemX]⟩
  have horders := basisOrders_nodup_disjoint (fiberDefaultRawControl f)
  let eZ : Fin (nK + mZ) ↪
      {i // i ∈ (zOrder (fiberDefaultRawControl f)).toFinset} := {
    toFun k := ⟨f (Fin.castAdd mX k), by simpa using hZMem k⟩
    inj' := by
      intro k l h
      have hfl := f.injective (congrArg Subtype.val h)
      apply Fin.ext
      simpa using congrArg Fin.val hfl }
  let eX : Fin mX ↪
      {i // i ∈ (xOrder (fiberDefaultRawControl f)).toFinset} := {
    toFun k := ⟨f (Fin.natAdd (nK + mZ) k), by simpa using hXMem k⟩
    inj' := by
      intro k l h
      have hfl := f.injective (congrArg Subtype.val h)
      apply Fin.ext
      simpa using congrArg Fin.val hfl }
  constructor
  · have hle := Fintype.card_le_of_injective eZ eZ.injective
    simp only [Fintype.card_fin, Fintype.card_coe] at hle
    simpa [List.toFinset_card_of_nodup horders.1] using hle
  · have hle := Fintype.card_le_of_injective eX eX.injective
    simp only [Fintype.card_fin, Fintype.card_coe] at hle
    simpa [List.toFinset_card_of_nodup horders.2.1] using hle

/-- The actual selector returns the supplied embedding on its explicit selected-fibre fallback. -/
theorem select_fiberDefaultRawControl
    {N nK mZ mX : ℕ} (f : Fin (nK + mZ + mX) ↪ Fin N) :
    select nK mZ mX (fiberDefaultRawControl f) = some f := by
  let hN : nK + mZ + mX ≤ N := by
    simpa using Fintype.card_le_of_injective f f.injective
  let hsum : (nK + mZ + mX) + (N - (nK + mZ + mX)) = N :=
    Nat.add_sub_of_le hN
  have hmatchedOrder :
      matchedOrder (fiberDefaultRawControl f) =
        List.ofFn (fiberDefaultOrderEquiv f) := by
    apply List.ext_get
    · simp [matchedOrder, fiberDefaultRawControl, Matched]
    · intro n h1 h2
      simp [matchedOrder, fiberDefaultRawControl, fiberDefaultShuffle,
        selfMatchedEquiv, Matched]
      rfl
  have hsequence :
      matchedOrder (fiberDefaultRawControl f) =
        List.ofFn f ++
          List.ofFn (fun k => (embeddingComplementEquiv f k).1) := by
    rw [hmatchedOrder]
    calc
      List.ofFn (fiberDefaultOrderEquiv f) =
          List.ofFn (fun i : Fin ((nK + mZ + mX) + (N - (nK + mZ + mX))) =>
            fiberDefaultOrderEquiv f (Fin.cast hsum i)) :=
        List.ofFn_congr hsum.symm (fiberDefaultOrderEquiv f)
      _ = List.ofFn f ++
          List.ofFn (fun k => (embeddingComplementEquiv f k).1) := by
        rw [← List.ofFn_fin_append]
        congr 1
        funext i
        refine Fin.addCases (m := nK + mZ + mX)
          (n := N - (nK + mZ + mX)) (fun k => ?_) (fun k => ?_) i
        · rw [Fin.append_left]
          exact fiberDefaultOrderEquiv_apply_selected f k
        · rw [Fin.append_right]
          exact fiberDefaultOrderEquiv_apply_complement f k
  have hfSplit :
      List.ofFn f =
        List.ofFn (fun k : Fin (nK + mZ) => f (Fin.castAdd mX k)) ++
          List.ofFn (fun k : Fin mX => f (Fin.natAdd (nK + mZ) k)) := by
    rw [← List.ofFn_fin_append]
    congr 1
    funext i
    refine Fin.addCases (m := nK + mZ) (n := mX)
      (fun k => by rw [Fin.append_left])
      (fun k => by rw [Fin.append_right]) i
  have hZnotX (k : Fin (nK + mZ)) :
      f (Fin.castAdd mX k) ∉ embeddingRange (fiberDefaultXEmbedding f) := by
    intro hmem
    rw [mem_embeddingRange_iff] at hmem
    obtain ⟨x, hx⟩ := hmem
    rw [fiberDefaultXEmbedding_apply] at hx
    have hk := f.injective hx
    have hkval := congrArg Fin.val hk
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hkval
    omega
  have hXmem (k : Fin mX) :
      f (Fin.natAdd (nK + mZ) k) ∈ embeddingRange (fiberDefaultXEmbedding f) := by
    rw [mem_embeddingRange_iff]
    exact ⟨k, fiberDefaultXEmbedding_apply f k⟩
  have hCompNotX (k : Fin (N - (nK + mZ + mX))) :
      (embeddingComplementEquiv f k).1 ∉
        embeddingRange (fiberDefaultXEmbedding f) := by
    intro hmem
    rw [mem_embeddingRange_iff] at hmem
    obtain ⟨x, hx⟩ := hmem
    apply (embeddingComplementEquiv f k).2
    exact ⟨Fin.natAdd (nK + mZ) x, by
      simpa [fiberDefaultXEmbedding_apply] using hx⟩
  have hZSelf :
      (List.ofFn (fun k : Fin (nK + mZ) => f (Fin.castAdd mX k))).filter
          (fun i => decide ((fiberDefaultRawControl f).a i = Basis.z)) =
        List.ofFn (fun k : Fin (nK + mZ) => f (Fin.castAdd mX k)) := by
    apply List.filter_eq_self.mpr
    intro i hi
    rw [List.mem_ofFn'] at hi
    obtain ⟨k, rfl⟩ := hi
    simp [fiberDefaultRawControl, fiberDefaultBasis, hZnotX k]
  have hXNilZ :
      (List.ofFn (fun k : Fin mX => f (Fin.natAdd (nK + mZ) k))).filter
          (fun i => decide ((fiberDefaultRawControl f).a i = Basis.z)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro i hi
    rw [List.mem_ofFn'] at hi
    obtain ⟨k, rfl⟩ := hi
    simp [fiberDefaultRawControl, fiberDefaultBasis, hXmem k]
  have hCompSelfZ :
      (List.ofFn (fun k => (embeddingComplementEquiv f k).1)).filter
          (fun i => decide ((fiberDefaultRawControl f).a i = Basis.z)) =
        List.ofFn (fun k => (embeddingComplementEquiv f k).1) := by
    apply List.filter_eq_self.mpr
    intro i hi
    rw [List.mem_ofFn'] at hi
    obtain ⟨k, rfl⟩ := hi
    simp [fiberDefaultRawControl, fiberDefaultBasis, hCompNotX k]
  have hZNilX :
      (List.ofFn (fun k : Fin (nK + mZ) => f (Fin.castAdd mX k))).filter
          (fun i => decide ((fiberDefaultRawControl f).a i = Basis.x)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro i hi
    rw [List.mem_ofFn'] at hi
    obtain ⟨k, rfl⟩ := hi
    simp [fiberDefaultRawControl, fiberDefaultBasis, hZnotX k]
  have hXSelf :
      (List.ofFn (fun k : Fin mX => f (Fin.natAdd (nK + mZ) k))).filter
          (fun i => decide ((fiberDefaultRawControl f).a i = Basis.x)) =
        List.ofFn (fun k : Fin mX => f (Fin.natAdd (nK + mZ) k)) := by
    apply List.filter_eq_self.mpr
    intro i hi
    rw [List.mem_ofFn'] at hi
    obtain ⟨k, rfl⟩ := hi
    simp [fiberDefaultRawControl, fiberDefaultBasis, hXmem k]
  have hCompNilX :
      (List.ofFn (fun k => (embeddingComplementEquiv f k).1)).filter
          (fun i => decide ((fiberDefaultRawControl f).a i = Basis.x)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro i hi
    rw [List.mem_ofFn'] at hi
    obtain ⟨k, rfl⟩ := hi
    simp [fiberDefaultRawControl, fiberDefaultBasis, hCompNotX k]
  have hzPrefix :
      zPrefix (nK := nK) (mZ := mZ) (fiberDefaultRawControl f) =
        List.ofFn (fun k : Fin (nK + mZ) => f (Fin.castAdd mX k)) := by
    simp only [zPrefix, zOrder, hsequence, hfSplit, List.filter_append]
    rw [hZSelf, hXNilZ, hCompSelfZ]
    simp
  have hxPrefix :
      xPrefix (mX := mX) (fiberDefaultRawControl f) =
        List.ofFn (fun k : Fin mX => f (Fin.natAdd (nK + mZ) k)) := by
    simp only [xPrefix, xOrder, hsequence, hfSplit, List.filter_append]
    rw [hZNilX, hXSelf, hCompNilX]
    simp
  have hq := hasQuotas_fiberDefaultRawControl f
  have hzGet (i : Fin (nK + mZ)) :
      (zPrefix (nK := nK) (mZ := mZ) (fiberDefaultRawControl f)).get
          (Fin.cast (List.length_take_of_le hq.1).symm i) =
        f (Fin.castAdd mX i) := by
    rw [List.get_eq_getElem]
    rw [← Option.some_inj, ← List.getElem?_eq_getElem]
    change (zPrefix (nK := nK) (mZ := mZ) (fiberDefaultRawControl f))[i.val]? =
      some (f (Fin.castAdd mX i))
    rw [hzPrefix]
    simp
  have hxGet (i : Fin mX) :
      (xPrefix (mX := mX) (fiberDefaultRawControl f)).get
          (Fin.cast (List.length_take_of_le hq.2).symm i) =
        f (Fin.natAdd (nK + mZ) i) := by
    rw [List.get_eq_getElem]
    rw [← Option.some_inj, ← List.getElem?_eq_getElem]
    change (xPrefix (mX := mX) (fiberDefaultRawControl f))[i.val]? =
      some (f (Fin.natAdd (nK + mZ) i))
    rw [hxPrefix]
    simp
  unfold select
  rw [dite_eq_left hq]
  congr 1
  apply Function.Embedding.ext
  intro k
  generalize hrole : (packedRoleEquiv nK mZ mX).symm k = role
  have hk := congrArg (packedRoleEquiv nK mZ mX) hrole
  simp only [Equiv.apply_symm_apply] at hk
  subst k
  rcases role with (⟨k | z⟩ | x)
  · rw [(selectedEmbedding_role_lookup (fiberDefaultRawControl f) hq).1 k]
    rw [hzGet (Fin.castAdd mZ k)]
    apply congrArg f
    apply Fin.ext
    rfl
  · rw [(selectedEmbedding_role_lookup (fiberDefaultRawControl f) hq).2.1 z]
    rw [hzGet (Fin.natAdd nK z)]
    apply congrArg f
    apply Fin.ext
    rfl
  · rw [(selectedEmbedding_role_lookup (fiberDefaultRawControl f) hq).2.2 x]
    rw [hxGet x]
    apply congrArg f
    apply Fin.ext
    rfl

/-- The constant-X basis string. -/
def constantX (N : ℕ) : Fin N → Basis := fun _ => Basis.x

/-- Explicit quota-failure control indexed by a witness that the total quota is positive.

Alice uses Z everywhere, Bob uses X everywhere, and the matched shuffle is the unique empty
ordering. -/
def failureDefaultRawControl
    {N nK mZ mX : ℕ} (_j : Fin (nK + mZ + mX)) : RawControl N :=
  ⟨constantZ N, constantX N, increasingShuffle (constantZ N) (constantX N)⟩

/-- The explicit all-Z/all-X fallback fails at least one positive quota. -/
theorem not_hasQuotas_failureDefaultRawControl
    {N nK mZ mX : ℕ} (j : Fin (nK + mZ + mX)) :
    ¬HasQuotas nK mZ mX (failureDefaultRawControl (N := N) j) := by
  intro hq
  simp [HasQuotas, zOrder, xOrder, matchedOrder, failureDefaultRawControl,
    Matched, constantZ, constantX] at hq
  have hj := j.isLt
  omega

/-- Selected-fibre kernel with an explicit fallback that remains in the requested fibre even
when that fibre has zero probability. -/
def totalSelectedControlKernel
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (f : Fin (nK + mZ + mX) ↪ Fin N) : PMF (RawControl N) :=
  PMF.filterOrPure (rawControlLaw N pA pB)
    (selectedFiberSet nK mZ mX f) (fiberDefaultRawControl f)

/-- Failure kernel with an explicit fallback that remains in the quota-failure set even when
failure has zero probability. -/
def totalFailureControlKernel
    (N nK mZ mX : ℕ) (pA pB : PMF Basis) (j : Fin (nK + mZ + mX)) :
    PMF (RawControl N) :=
  PMF.filterOrPure (rawControlLaw N pA pB)
    (failureSet nK mZ mX) (failureDefaultRawControl j)

/-- Every positive-mass output of the total selected kernel selects the requested embedding. -/
theorem totalSelectedControlKernel_select
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (f : Fin (nK + mZ + mX) ↪ Fin N) (omega : RawControl N)
    (hpositive : 0 < totalSelectedControlKernel N nK mZ mX pA pB f omega) :
    select nK mZ mX omega = some f := by
  classical
  unfold totalSelectedControlKernel at hpositive
  by_cases hexists : ∃ x ∈ selectedFiberSet nK mZ mX f,
      x ∈ (rawControlLaw N pA pB).support
  · rw [PMF.filterOrPure_apply_of_exists _ _ _ _ hexists] at hpositive
    by_contra hselect
    have hnotmem : omega ∉ selectedFiberSet nK mZ mX f := by
      simpa [selectedFiberSet] using hselect
    rw [Set.indicator_of_notMem hnotmem] at hpositive
    simp at hpositive
  · rw [PMF.filterOrPure_apply_of_not_exists _ _ _ _ hexists] at hpositive
    have homega : omega = fiberDefaultRawControl f := by
      by_contra hne
      simp [PMF.pure_apply, hne] at hpositive
    subst omega
    exact select_fiberDefaultRawControl f

/-- Every positive-mass output of the total failure kernel fails the quotas. -/
theorem totalFailureControlKernel_not_hasQuotas
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (j : Fin (nK + mZ + mX)) (omega : RawControl N)
    (hpositive : 0 < totalFailureControlKernel N nK mZ mX pA pB j omega) :
    ¬HasQuotas nK mZ mX omega := by
  classical
  unfold totalFailureControlKernel at hpositive
  by_cases hexists : ∃ x ∈ failureSet nK mZ mX,
      x ∈ (rawControlLaw N pA pB).support
  · rw [PMF.filterOrPure_apply_of_exists _ _ _ _ hexists] at hpositive
    by_contra hquota
    have hnotmem : omega ∉ failureSet nK mZ mX := by
      simpa [failureSet] using hquota
    rw [Set.indicator_of_notMem hnotmem] at hpositive
    simp at hpositive
  · rw [PMF.filterOrPure_apply_of_not_exists _ _ _ _ hexists] at hpositive
    have homega : omega = failureDefaultRawControl j := by
      by_contra hne
      simp [PMF.pure_apply, hne] at hpositive
    subst omega
    exact not_hasQuotas_failureDefaultRawControl j

/-- Under the success weight, changing only the zero-mass selected-fibre fallback has no effect. -/
theorem totalSelectedControlKernel_weighted_eq
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (π : Equiv.Perm (Fin (nK + mZ + mX))) (omega : RawControl N) :
    selectionSuccessMass N nK mZ mX pA pB *
        totalSelectedControlKernel N nK mZ mX pA pB (joinSubsetPerm S π) omega =
      selectionSuccessMass N nK mZ mX pA pB *
        selectedControlKernel N nK mZ mX pA pB (joinSubsetPerm S π) omega := by
  classical
  by_cases hexists : ∃ x ∈ selectedFiberSet nK mZ mX (joinSubsetPerm S π),
      x ∈ (rawControlLaw N pA pB).support
  · unfold totalSelectedControlKernel selectedControlKernel
    rw [PMF.filterOrPure_apply_of_exists _ _ _ _ hexists,
      PMF.filterOrPure_apply_of_exists _ _ _ _ hexists]
  · have hfiberzero :
        selectedInjectionFiberMass N nK mZ mX pA pB (joinSubsetPerm S π) = 0 := by
      rw [selectedInjectionFiberMass]
      apply Finset.sum_eq_zero
      intro x _
      by_cases hx : select nK mZ mX x = some (joinSubsetPerm S π)
      · have hxzero : rawControlLaw N pA pB x = 0 := by
          by_contra hxne
          exact hexists ⟨x, by simpa [selectedFiberSet] using hx,
            (PMF.mem_support_iff _ _).mpr hxne⟩
        simp [hx, hxzero]
      · simp [hx]
    have hformula := selectedInjection_fiberMass N nK mZ mX pA pB (joinSubsetPerm S π)
    rw [hfiberzero] at hformula
    have hsuccess : selectionSuccessMass N nK mZ mX pA pB = 0 := by
      rcases ENNReal.div_eq_zero_iff.mp hformula.symm with h | h
      · exact h
      · simp at h
    simp [hsuccess]

/-- Under the failure weight, changing only the zero-mass failure fallback has no effect. -/
theorem totalFailureControlKernel_weighted_eq
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (j : Fin (nK + mZ + mX)) (omega : RawControl N) :
    selectionFailureMass N nK mZ mX pA pB *
        totalFailureControlKernel N nK mZ mX pA pB j omega =
      selectionFailureMass N nK mZ mX pA pB *
        failureControlKernel N nK mZ mX pA pB omega := by
  classical
  by_cases hexists : ∃ x ∈ failureSet nK mZ mX,
      x ∈ (rawControlLaw N pA pB).support
  · unfold totalFailureControlKernel failureControlKernel
    rw [PMF.filterOrPure_apply_of_exists _ _ _ _ hexists,
      PMF.filterOrPure_apply_of_exists _ _ _ _ hexists]
  · have hfailure : selectionFailureMass N nK mZ mX pA pB = 0 := by
      rw [← tsum_failureSet_indicator]
      apply ENNReal.tsum_eq_zero.mpr
      intro x
      by_cases hx : x ∈ failureSet nK mZ mX
      · have hxzero : rawControlLaw N pA pB x = 0 := by
          by_contra hxne
          exact hexists ⟨x, hx, (PMF.mem_support_iff _ _).mpr hxne⟩
        simp [Set.indicator_of_mem hx, hxzero]
      · simp [Set.indicator_of_notMem hx]
    simp [hfailure]

/-- Reconstruct a successful raw control by choosing a retained subset, an inner order,
then sampling the selected-control kernel and recording success. -/
@[reducible] def reconstructedSuccessStatusRawLaw (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) : PMF (Bool × RawControl N) :=
  (uniformRetainedSubset hN).bind fun S =>
    (uniformInnerPerm (nK + mZ + mX)).bind fun π =>
      (totalSelectedControlKernel N nK mZ mX pA pB (joinSubsetPerm S π)).bind
        fun omega => PMF.pure (true, omega)

/-- Reconstructed status-tagged law using structurally valid fallbacks.

At zero total quota the impossible failure sector is omitted.  At positive total quota, failure
uses the explicit witness `0 : Fin (nK + mZ + mX)`. -/
def totalizedReconstructedStatusRawLaw
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) : PMF (Bool × RawControl N) :=
  if hn : nK + mZ + mX = 0 then
    reconstructedSuccessStatusRawLaw N nK mZ mX pA pB hN
  else
    let j : Fin (nK + mZ + mX) := ⟨0, Nat.pos_of_ne_zero hn⟩
    (selectionStatusLaw N nK mZ mX pA pB).bind fun status =>
      if status then reconstructedSuccessStatusRawLaw N nK mZ mX pA pB hN
      else (totalFailureControlKernel N nK mZ mX pA pB j).bind fun omega =>
        PMF.pure (false, omega)

/-- Exact weighted reconstruction with structurally valid selected and failure fallbacks. -/
theorem totalizedReconstructedStatusRawLaw_eq
    (N nK mZ mX : ℕ) (pA pB : PMF Basis)
    (hN : nK + mZ + mX ≤ N) :
    totalizedReconstructedStatusRawLaw N nK mZ mX pA pB hN =
      taggedRawControlLaw N nK mZ mX pA pB := by
  rw [← reconstructedStatusRawLaw_eq N nK mZ mX pA pB hN]
  apply PMF.ext
  rintro ⟨status, omega⟩
  have hselected :
      selectionSuccessMass N nK mZ mX pA pB *
          ((uniformRetainedSubset hN).bind fun S =>
            (uniformInnerPerm (nK + mZ + mX)).bind fun π =>
              (totalSelectedControlKernel N nK mZ mX pA pB
                (joinSubsetPerm S π)).bind fun omega =>
                  PMF.pure (true, omega)) (status, omega) =
        selectionSuccessMass N nK mZ mX pA pB *
          ((uniformRetainedSubset hN).bind fun S =>
            (uniformInnerPerm (nK + mZ + mX)).bind fun π =>
              (selectedControlKernel N nK mZ mX pA pB
                (joinSubsetPerm S π)).bind fun omega =>
                  PMF.pure (true, omega)) (status, omega) := by
    simp only [PMF.bind_apply, tsum_fintype]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    apply Finset.sum_congr rfl
    intro π _
    apply Finset.sum_congr rfl
    intro x _
    calc
      selectionSuccessMass N nK mZ mX pA pB *
          ((uniformRetainedSubset hN) S *
            ((uniformInnerPerm (nK + mZ + mX)) π *
              (totalSelectedControlKernel N nK mZ mX pA pB
                (joinSubsetPerm S π) x *
                  PMF.pure (true, x) (status, omega)))) =
        ((uniformRetainedSubset hN) S *
          (uniformInnerPerm (nK + mZ + mX)) π *
            PMF.pure (true, x) (status, omega)) *
          (selectionSuccessMass N nK mZ mX pA pB *
            totalSelectedControlKernel N nK mZ mX pA pB
              (joinSubsetPerm S π) x) := by
        ac_rfl
      _ = ((uniformRetainedSubset hN) S *
          (uniformInnerPerm (nK + mZ + mX)) π *
            PMF.pure (true, x) (status, omega)) *
          (selectionSuccessMass N nK mZ mX pA pB *
            selectedControlKernel N nK mZ mX pA pB
              (joinSubsetPerm S π) x) := by
        rw [totalSelectedControlKernel_weighted_eq]
      _ = selectionSuccessMass N nK mZ mX pA pB *
          ((uniformRetainedSubset hN) S *
            ((uniformInnerPerm (nK + mZ + mX)) π *
              (selectedControlKernel N nK mZ mX pA pB
                (joinSubsetPerm S π) x *
                  PMF.pure (true, x) (status, omega)))) := by
        ac_rfl
  have hfailure (j : Fin (nK + mZ + mX)) :
      selectionFailureMass N nK mZ mX pA pB *
          ((totalFailureControlKernel N nK mZ mX pA pB j).bind fun omega =>
            PMF.pure (false, omega)) (status, omega) =
        selectionFailureMass N nK mZ mX pA pB *
          ((failureControlKernel N nK mZ mX pA pB).bind fun omega =>
            PMF.pure (false, omega)) (status, omega) := by
    simp only [PMF.bind_apply, tsum_fintype]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    calc
      selectionFailureMass N nK mZ mX pA pB *
          (totalFailureControlKernel N nK mZ mX pA pB j x *
            PMF.pure (false, x) (status, omega)) =
        PMF.pure (false, x) (status, omega) *
          (selectionFailureMass N nK mZ mX pA pB *
            totalFailureControlKernel N nK mZ mX pA pB j x) := by
        ac_rfl
      _ = PMF.pure (false, x) (status, omega) *
          (selectionFailureMass N nK mZ mX pA pB *
            failureControlKernel N nK mZ mX pA pB x) := by
        rw [totalFailureControlKernel_weighted_eq]
      _ = selectionFailureMass N nK mZ mX pA pB *
          (failureControlKernel N nK mZ mX pA pB x *
            PMF.pure (false, x) (status, omega)) := by
        ac_rfl
  by_cases hn : nK + mZ + mX = 0
  · rw [totalizedReconstructedStatusRawLaw,
    QKD.BB84.Sampling.reconstructedSuccessStatusRawLaw, dite_eq_left hn,
      reconstructedStatusRawLaw]
    simp only [PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
    have hnK : nK = 0 := by omega
    have hmZ : mZ = 0 := by omega
    have hmX : mX = 0 := by omega
    subst nK
    subst mZ
    subst mX
    simp only [ite_true, Bool.false_eq_true, ite_false,
      selectionStatusLaw_apply, selectionStatusWeight,
      selectionSuccessMass_zero_quotas, selectionFailureMass_zero_quotas,
      one_mul, zero_mul, add_zero]
    simpa [selectionSuccessMass_zero_quotas] using hselected
  · rw [totalizedReconstructedStatusRawLaw,
    QKD.BB84.Sampling.reconstructedSuccessStatusRawLaw, dite_eq_right hn,
      reconstructedStatusRawLaw]
    simp only [PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
    simp only [ite_true, Bool.false_eq_true, ite_false,
      selectionStatusLaw_apply, selectionStatusWeight]
    exact congrArg₂ (fun x y => x + y) hselected
      (hfailure ⟨0, Nat.pos_of_ne_zero hn⟩)

end QKD.BB84.Sampling
