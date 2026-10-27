import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Basic

/-!
# Fixed-quota selection from matched BB84 rounds

This module filters a shuffled list of matched identifiers by basis, takes fixed Z-key, Z-test,
and X-test quotas, and packs the selected identifiers into one injection guarded by quota
availability.

The late basis-comparison schedule follows Renner, arXiv:quant-ph/0512258v2, lines 673--736, and
the fixed-batch sampling conditions follow Pfister et al., arXiv:1506.07502v3, Sections IV--V.
-/

namespace QKD.BB84.Sampling

open QKD.BB84.Measurement

/-- The shuffled matched identifiers in their sampled order. -/
def matchedOrder {N : ℕ} (omega : RawControl N) : List (Fin N) :=
  List.ofFn fun j : Fin (Matched omega.a omega.b).card => (omega.order j).1

/-- The shuffled matched identifiers on which Alice used the Z basis. -/
def zOrder {N : ℕ} (omega : RawControl N) : List (Fin N) :=
  (matchedOrder omega).filter fun i => decide (omega.a i = Basis.z)

/-- The shuffled matched identifiers on which Alice used the X basis. -/
def xOrder {N : ℕ} (omega : RawControl N) : List (Fin N) :=
  (matchedOrder omega).filter fun i => decide (omega.a i = Basis.x)

/-- Z-key followed by Z-test identifiers, truncated at the requested total Z quota. -/
def zPrefix {N nK mZ : ℕ} (omega : RawControl N) : List (Fin N) :=
  (zOrder omega).take (nK + mZ)

/-- X-test identifiers, truncated at the requested X quota. -/
def xPrefix {N mX : ℕ} (omega : RawControl N) : List (Fin N) :=
  (xOrder omega).take mX

/-- There are at least `nK + mZ` matched Z-basis rounds for the key and Z tests,
and at least `mX` matched X-basis rounds for the X tests. -/
def HasQuotas {N : ℕ} (nK mZ mX : ℕ) (omega : RawControl N) : Prop :=
  nK + mZ ≤ (zOrder omega).length ∧ mX ≤ (xOrder omega).length

/-- Quota availability is decidable from the two finite list lengths. -/
instance hasQuotasDecidable {N : ℕ} (nK mZ mX : ℕ) (omega : RawControl N) :
    Decidable (HasQuotas nK mZ mX omega) := by
  unfold HasQuotas
  infer_instance

/-- The shuffled Z and X orders have no duplicates and no identifier occurs in both.

This structural fact separates the Z-key and Z-test prefix from the X-test prefix when the
three role blocks are packed into one injection. -/
theorem basisOrders_nodup_disjoint {N : ℕ} (omega : RawControl N) :
    (zOrder omega).Nodup ∧ (xOrder omega).Nodup ∧
      ∀ i : Fin N, i ∈ zOrder omega → i ∉ xOrder omega := by
  have hmatched : (matchedOrder omega).Nodup := by
    rw [matchedOrder, List.nodup_ofFn]
    intro i j hij
    exact omega.order.injective (Subtype.ext hij)
  refine ⟨hmatched.filter _, hmatched.filter _, ?_⟩
  intro i hiZ hiX
  simp only [zOrder, List.mem_filter] at hiZ
  simp only [xOrder, List.mem_filter] at hiX
  have hz : omega.a i = Basis.z := of_decide_eq_true hiZ.2
  have hx : omega.a i = Basis.x := of_decide_eq_true hiX.2
  rw [hz] at hx
  exact Basis.noConfusion hx

/-- The three selected roles, ordered as Z-key, Z-test, then X-test. -/
abbrev RoleIndex (nK mZ mX : ℕ) := (Fin nK ⊕ Fin mZ) ⊕ Fin mX

/-- Pack the three role blocks into consecutive output positions. -/
def packedRoleEquiv (nK mZ mX : ℕ) :
    RoleIndex nK mZ mX ≃ Fin (nK + mZ + mX) :=
  (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin mX))).trans finSumFinEquiv

/-- Read the physical round identifier assigned to one role from the actual list prefixes. -/
def selectedRoleValue
    {N nK mZ mX : ℕ} (omega : RawControl N) (h : HasQuotas nK mZ mX omega) :
    RoleIndex nK mZ mX → Fin N := fun role =>
  match role with
  | Sum.inl (Sum.inl k) =>
      (zPrefix (nK := nK) (mZ := mZ) omega).get
        (Fin.cast (List.length_take_of_le h.1).symm (Fin.castAdd mZ k))
  | Sum.inl (Sum.inr z) =>
      (zPrefix (nK := nK) (mZ := mZ) omega).get
        (Fin.cast (List.length_take_of_le h.1).symm (Fin.natAdd nK z))
  | Sum.inr x =>
      (xPrefix (mX := mX) omega).get
        (Fin.cast (List.length_take_of_le h.2).symm x)

/-- Distinct packed roles select distinct physical round identifiers.

The proof uses nodup of each filtered order and disjointness of the Z and X filters; no numerical
bound such as `nK + mZ + mX ≤ N` is assumed separately. -/
theorem selectedRoleValue_injective
    {N nK mZ mX : ℕ} (omega : RawControl N) (h : HasQuotas nK mZ mX omega) :
    Function.Injective (selectedRoleValue omega h) := by
  have horders := basisOrders_nodup_disjoint omega
  have hzPrefix : (zPrefix (nK := nK) (mZ := mZ) omega).Nodup := by
    unfold zPrefix
    exact horders.1.take
  have hxPrefix : (xPrefix (mX := mX) omega).Nodup := by
    unfold xPrefix
    exact horders.2.1.take
  let zValue : Fin (nK + mZ) → Fin N := fun i =>
    (zPrefix (nK := nK) (mZ := mZ) omega).get
      (Fin.cast (List.length_take_of_le h.1).symm i)
  let xValue : Fin mX → Fin N := fun i =>
    (xPrefix (mX := mX) omega).get
      (Fin.cast (List.length_take_of_le h.2).symm i)
  have hzValue : Function.Injective zValue := by
    intro i j hij
    exact Fin.cast_injective _ (hzPrefix.injective_get hij)
  have hxValue : Function.Injective xValue := by
    intro i j hij
    exact Fin.cast_injective _ (hxPrefix.injective_get hij)
  have hzx : ∀ i j, zValue i ≠ xValue j := by
    intro i j hij
    have hziPrefix : zValue i ∈ zPrefix (nK := nK) (mZ := mZ) omega := by
      dsimp [zValue]
      exact List.get_mem _ _
    have hxjPrefix : xValue j ∈ xPrefix (mX := mX) omega := by
      dsimp [xValue]
      exact List.get_mem _ _
    have hzi : zValue i ∈ zOrder omega :=
      (List.take_sublist _ _).mem hziPrefix
    have hxj : xValue j ∈ xOrder omega :=
      (List.take_sublist _ _).mem hxjPrefix
    exact horders.2.2 (zValue i) hzi (hij ▸ hxj)
  have hzRoles : Function.Injective
      (fun role : Fin nK ⊕ Fin mZ => zValue (finSumFinEquiv role)) :=
    hzValue.comp finSumFinEquiv.injective
  have hall : Function.Injective
      (Sum.elim (fun role : Fin nK ⊕ Fin mZ => zValue (finSumFinEquiv role)) xValue) :=
    hzRoles.sumElim hxValue fun role x => hzx (finSumFinEquiv role) x
  have hfunction : selectedRoleValue omega h =
      Sum.elim (fun role : Fin nK ⊕ Fin mZ => zValue (finSumFinEquiv role)) xValue := by
    funext role
    rcases role with (⟨k | z⟩ | x) <;> rfl
  rw [hfunction]
  exact hall

/-- Choose the first `nK` matched Z-basis rounds for the key, the next `mZ` for
Z tests, and the first `mX` matched X-basis rounds for X tests, following the announced shuffle;
list the retained rounds in that key, Z-test, X-test order. -/
def selectedEmbedding
    {N nK mZ mX : ℕ} (omega : RawControl N) (h : HasQuotas nK mZ mX omega) :
    Fin (nK + mZ + mX) ↪ Fin N where
  toFun k := selectedRoleValue omega h ((packedRoleEquiv nK mZ mX).symm k)
  inj' := (selectedRoleValue_injective omega h).comp (packedRoleEquiv nK mZ mX).symm.injective

/-- Return the role-packed injection exactly when both quotas are available. -/
def select {N : ℕ} (nK mZ mX : ℕ) (omega : RawControl N) :
    Option (Fin (nK + mZ + mX) ↪ Fin N) :=
  if h : HasQuotas nK mZ mX omega then some (selectedEmbedding omega h) else none

/-- Selection returns an injection exactly on the quota-sufficient controls. -/
theorem select_isSome_iff
    {N : ℕ} (nK mZ mX : ℕ) (omega : RawControl N) :
    (select nK mZ mX omega).isSome = true ↔ HasQuotas nK mZ mX omega := by
  simp [select]

/-- Parameter-estimation mask for the packed Z-key/Z-test/X-test layout. -/
def packedPESel {nK mZ mX : ℕ} (k : Fin (nK + mZ + mX)) : Bool :=
  decide (nK ≤ k.val)

/-- X-test mask for the packed Z-key/Z-test/X-test layout. -/
def packedXSel {nK mZ mX : ℕ} (k : Fin (nK + mZ + mX)) : Bool :=
  decide (nK + mZ ≤ k.val)

/-- The packed selector reserves exactly `nK` positions for key bits. -/
theorem card_packedPESel_eq_false (nK mZ mX : ℕ) :
    Fintype.card {i : Fin (nK + mZ + mX) //
      @packedPESel nK mZ mX i = false} = nK := by
  classical
  let e : Fin nK ≃
      {i : Fin (nK + mZ + mX) // packedPESel i = false} := {
    toFun i := ⟨⟨i.val, by omega⟩, by
      simp [packedPESel]⟩
    invFun i := ⟨i.1.val, by
      have hi : ¬nK ≤ i.1.val := by
        simpa [packedPESel] using i.2
      omega⟩
    left_inv i := by
      apply Fin.ext
      rfl
    right_inv i := by
      apply Subtype.ext
      apply Fin.ext
      rfl }
  exact (Fintype.card_congr e.symm).trans (Fintype.card_fin nK)

/-- Exact list lookups for the key, Z-test, and X-test role blocks.

The index casts expose only the equalities supplied by `List.length_take_of_le`; the three list
positions are respectively `Fin.castAdd mZ k`, `Fin.natAdd nK z`, and `x`. -/
theorem selectedEmbedding_role_lookup
    {N nK mZ mX : ℕ} (omega : RawControl N) (h : HasQuotas nK mZ mX omega) :
    (∀ k : Fin nK,
      selectedEmbedding omega h
          (packedRoleEquiv nK mZ mX (Sum.inl (Sum.inl k))) =
        (zPrefix (nK := nK) (mZ := mZ) omega).get
          (Fin.cast (List.length_take_of_le h.1).symm (Fin.castAdd mZ k))) ∧
    (∀ z : Fin mZ,
      selectedEmbedding omega h
          (packedRoleEquiv nK mZ mX (Sum.inl (Sum.inr z))) =
        (zPrefix (nK := nK) (mZ := mZ) omega).get
          (Fin.cast (List.length_take_of_le h.1).symm (Fin.natAdd nK z))) ∧
    (∀ x : Fin mX,
      selectedEmbedding omega h
          (packedRoleEquiv nK mZ mX (Sum.inr x)) =
        (xPrefix (mX := mX) omega).get
          (Fin.cast (List.length_take_of_le h.2).symm x)) := by
  constructor
  · intro k
    simp [selectedEmbedding, packedRoleEquiv, selectedRoleValue]
  constructor
  · intro z
    simp [selectedEmbedding, packedRoleEquiv, selectedRoleValue]
  · intro x
    simp [selectedEmbedding, packedRoleEquiv, selectedRoleValue]

end QKD.BB84.Sampling
