import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.Instrument.Classical
import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.LOCC.LocalAction.ComputationalMeasurement
import QCryptLean.Math.FiniteEmbedding
import QCryptLean.Math.FiniteEmbedding.SubsetPerm
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.Math.LinearAlgebra.Matrix.TensorPermutation
import QCryptLean.QKD.BB84.Measurement
import QCryptLean.QKD.BB84.Measurement.OutputLaw
import QCryptLean.QKD.BB84.Measurement.SelectedMarginal
import QCryptLean.QKD.BB84.Measurement.SelectedRecords
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Basic
import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.QKD.BB84.SiftOperation
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Gates
import QCryptLean.Quantum.Symmetry.Basic

/-! # Selected Born Rule -/


open Quantum.Operators (Op)

open scoped Matrix BigOperators
open Matrix

noncomputable section

namespace QKD.BB84.Measurement
open LOCC

/-- The physical basis assigned to a packed key/Z-test/X-test role. -/
def packedRoleBasis {nK mZ mX : ℕ} (k : Fin (nK + mZ + mX)) : Basis :=
  if k.val < nK + mZ then .z else .x

/-- The actual selected identifier has the packed role's basis for both parties.

The selected identifier comes from the Z or X filtered matched-order prefix.  Thus its Alice and
Bob bases agree, and the first `nK + mZ` packed positions are Z while the final `mX` positions are
X. -/
theorem selectedEmbedding_basis_lookup
    {N nK mZ mX : ℕ} (omega : Sampling.RawControl N)
    (h : Sampling.HasQuotas nK mZ mX omega)
    (k : Fin (nK + mZ + mX)) :
    omega.a (Sampling.selectedEmbedding omega h k) = packedRoleBasis k ∧
      omega.b (Sampling.selectedEmbedding omega h k) = packedRoleBasis k := by
  have hzBasis {i : Fin N}
      (hi : i ∈ Sampling.zPrefix (nK := nK) (mZ := mZ) omega) :
      omega.a i = .z := by
    have hiZ : i ∈ Sampling.zOrder omega :=
      (List.take_sublist _ _).mem hi
    exact of_decide_eq_true (List.mem_filter.mp hiZ).2
  have hxBasis {i : Fin N}
      (hi : i ∈ Sampling.xPrefix (mX := mX) omega) :
      omega.a i = .x := by
    have hiX : i ∈ Sampling.xOrder omega :=
      (List.take_sublist _ _).mem hi
    exact of_decide_eq_true (List.mem_filter.mp hiX).2
  have hmatched {i : Fin N} (hi : i ∈ Sampling.matchedOrder omega) :
      omega.a i = omega.b i := by
    rw [Sampling.matchedOrder, List.mem_ofFn'] at hi
    rcases hi with ⟨j, rfl⟩
    have hj := (omega.order j).2
    change (omega.order j).1 ∈
      Finset.univ.filter (fun i => omega.a i = omega.b i) at hj
    exact (Finset.mem_filter.mp hj).2
  rw [← (Sampling.packedRoleEquiv nK mZ mX).apply_symm_apply k]
  generalize (Sampling.packedRoleEquiv nK mZ mX).symm k = role
  rcases role with (⟨key | z⟩ | x)
  · have hlookup := (Sampling.selectedEmbedding_role_lookup omega h).1 key
    have hiPrefix : Sampling.selectedEmbedding omega h
        (Sampling.packedRoleEquiv nK mZ mX (Sum.inl (Sum.inl key))) ∈
        Sampling.zPrefix (nK := nK) (mZ := mZ) omega := by
      rw [hlookup]
      exact List.get_mem _ _
    have hiOrder : Sampling.selectedEmbedding omega h
        (Sampling.packedRoleEquiv nK mZ mX (Sum.inl (Sum.inl key))) ∈
        Sampling.matchedOrder omega := by
      exact (List.mem_filter.mp
        ((List.take_sublist _ _).mem hiPrefix)).1
    have ha := hzBasis hiPrefix
    have hab := hmatched hiOrder
    have hkey : key.val < nK + mZ := by omega
    constructor
    · simpa [packedRoleBasis, Sampling.packedRoleEquiv, hkey] using ha
    · simpa [packedRoleBasis, Sampling.packedRoleEquiv, hkey] using hab.symm.trans ha
  · have hlookup := (Sampling.selectedEmbedding_role_lookup omega h).2.1 z
    have hiPrefix : Sampling.selectedEmbedding omega h
        (Sampling.packedRoleEquiv nK mZ mX (Sum.inl (Sum.inr z))) ∈
        Sampling.zPrefix (nK := nK) (mZ := mZ) omega := by
      rw [hlookup]
      exact List.get_mem _ _
    have hiOrder : Sampling.selectedEmbedding omega h
        (Sampling.packedRoleEquiv nK mZ mX (Sum.inl (Sum.inr z))) ∈
        Sampling.matchedOrder omega := by
      exact (List.mem_filter.mp
        ((List.take_sublist _ _).mem hiPrefix)).1
    have ha := hzBasis hiPrefix
    have hab := hmatched hiOrder
    constructor
    · simpa [packedRoleBasis, Sampling.packedRoleEquiv] using ha
    · simpa [packedRoleBasis, Sampling.packedRoleEquiv] using hab.symm.trans ha
  · have hlookup := (Sampling.selectedEmbedding_role_lookup omega h).2.2 x
    have hiPrefix : Sampling.selectedEmbedding omega h
        (Sampling.packedRoleEquiv nK mZ mX (Sum.inr x)) ∈
        Sampling.xPrefix (mX := mX) omega := by
      rw [hlookup]
      exact List.get_mem _ _
    have hiOrder : Sampling.selectedEmbedding omega h
        (Sampling.packedRoleEquiv nK mZ mX (Sum.inr x)) ∈
        Sampling.matchedOrder omega := by
      exact (List.mem_filter.mp
        ((List.take_sublist _ _).mem hiPrefix)).1
    have ha := hxBasis hiPrefix
    have hab := hmatched hiOrder
    constructor
    · simpa [packedRoleBasis, Sampling.packedRoleEquiv] using ha
    · simpa [packedRoleBasis, Sampling.packedRoleEquiv] using hab.symm.trans ha

/-- The increasing enumeration of a fixed-cardinality subset, viewed as an embedding into the
ambient finite type. -/
def increasingSubsetEmbedding {n N : ℕ} (S : Set.powersetCard (Fin N) n) :
    Fin n ↪ Fin N where
  toFun k := (Math.FiniteEmbedding.increasingSubsetEquiv S k).1
  inj' := by
    intro k l h
    apply (Math.FiniteEmbedding.increasingSubsetEquiv S).injective
    exact Subtype.ext h

/-- Extract the arbitrary physical-input operator block at independent reference row and column
coordinates. -/
def selectedReferenceInputBlock
    {N : ℕ} {R : Type}
    (W : Op (((Fin N → Bit) × (Fin N → Bit)) × R)) (s t : R) :
    Op ((Fin N → Bit) × (Fin N → Bit)) :=
  W.submatrix (fun x => (x, s)) (fun x => (x, t))

/-- One native computational-measurement row after the actual sift/permutation operator.

The outcome projector is the Kraus matrix of
`LOCC.Instrument.computationalMeasurement`; its input is first transformed by the literal
`QKD.BB84.Model.siftPermHalf`.  Both matrices act on the actual retained bit strings. -/
def nativeSiftMeasurementRow
    (n : ℕ) (peSel xSel : Fin n → Bool) (pi : Equiv.Perm (Fin n))
    (u : Fin n → Bit) : Matrix Unit (Fin n → Bit) ℂ :=
  fun _ x =>
    (((Instrument.computationalMeasurement (Bits n)).kraus
          u () *
        QKD.BB84.Model.siftPermHalf n peSel xSel pi)
      u x)

/-- Alice's and Bob's native computational-measurement rows after applying the same public
sift/permutation operator locally. -/
def nativeSiftPairKraus
    (n : ℕ) (peSel xSel : Fin n → Bool) (pi : Equiv.Perm (Fin n))
    (uA uB : Fin n → Bit) :
    Matrix Unit ((Fin n → Bit) × (Fin n → Bit)) ℂ :=
  fun _ x =>
    nativeSiftMeasurementRow n peSel xSel pi uA () x.1 *
      nativeSiftMeasurementRow n peSel xSel pi uB () x.2

/-- The unweighted actual selected fixed-basis Born block at two reference coordinates. -/
def fixedBasisSelectedBornBlock
    {N n : ℕ} {R : Type}
    (f : Fin n ↪ Fin N) (a b : Fin N → Basis)
    (uA uB : Fin n → Bit)
    (W : Op (((Fin N → Bit) × (Fin N → Bit)) × R)) (s t : R) : ℂ :=
  (Matrix.conjLinearMap
      (fixedBasisPairKraus
        (selectedStoredRecords f a uA)
        (selectedStoredRecords f b uB))
      ((selectedInputMarginalInstrument f).channel
        (selectedReferenceInputBlock W s t))) () ()

/-- The unweighted native sift/permutation and computational-measurement Born block at two
reference coordinates. -/
def nativeSelectedBornBlock
    {N n : ℕ} {R : Type}
    (S : Set.powersetCard (Fin N) n)
    (peSel xSel : Fin n → Bool) (pi : Equiv.Perm (Fin n))
    (uA uB : Fin n → Bit)
    (W : Op (((Fin N → Bit) × (Fin N → Bit)) × R)) (s t : R) : ℂ :=
  (Matrix.conjLinearMap
      (nativeSiftPairKraus n peSel xSel pi uA uB)
      ((selectedInputMarginalInstrument (increasingSubsetEmbedding S)).channel
        (selectedReferenceInputBlock W s t))) () ()

/-- Unweighted fixed-basis selected measurement equals the native retained-prefix measurement.

The structural equality identifies the actual selected embedding with increasing subset order
composed with `pi.symm`, as stated by `Math.FiniteEmbedding.joinSubsetPerm_apply`.  The input `W`
is an arbitrary complex operator; `s` and `t` are independent finite reference coordinates.
There is no basis-law or shuffle coefficient in either side.

Renner, arXiv:quant-ph/0512258v2, source lines 673--736 supplies the measurement/sifting
motivation, and Christandl--Koenig--Renner, arXiv:0809.3019, source lines 423--455 supplies the
permutation orientation; the exact equality is an implementation-specific finite coordinate
theorem. -/
theorem selectedMeasurement_joinSubsetPerm_eq_native
    {N nK mZ mX : ℕ} {R : Type}
    (omega : Sampling.RawControl N)
    (h : Sampling.HasQuotas nK mZ mX omega)
    (S : Set.powersetCard (Fin N) (nK + mZ + mX))
    (pi : Equiv.Perm (Fin (nK + mZ + mX)))
    (hselected : Sampling.selectedEmbedding omega h =
      Math.FiniteEmbedding.joinSubsetPerm S pi)
    (uA uB : Fin (nK + mZ + mX) → Bit)
    (W : Op (((Fin N → Bit) × (Fin N → Bit)) × R)) (s t : R) :
    fixedBasisSelectedBornBlock
        (Sampling.selectedEmbedding omega h) omega.a omega.b uA uB W s t =
      nativeSelectedBornBlock S
        (@Sampling.packedPESel nK mZ mX)
        (@Sampling.packedXSel nK mZ mX) pi uA uB W s t := by
  rw [hselected]
  have hmask (k : Fin (nK + mZ + mX)) :
      (if (@Sampling.packedPESel nK mZ mX k) &&
          (@Sampling.packedXSel nK mZ mX k) then
        Matrix.reindex finTwoEquiv.symm finTwoEquiv.symm Quantum.Gates.hadamard
      else (1 : Matrix Bit Bit ℂ)) =
        basisUnitary (packedRoleBasis k) := by
    by_cases hk : k.val < nK + mZ
    · have hk' : ¬nK + mZ ≤ k.val := by omega
      simp [Sampling.packedPESel, Sampling.packedXSel,
        packedRoleBasis, basisUnitary, hk, hk']
    · have hk' : nK + mZ ≤ k.val := by omega
      have hnK : nK ≤ k.val := by omega
      simp [Sampling.packedPESel, Sampling.packedXSel,
        packedRoleBasis, basisUnitary, hk, hk', hnK]
  have hnative (u x : Fin (nK + mZ + mX) → Bit) :
      nativeSiftMeasurementRow (nK + mZ + mX)
          (@Sampling.packedPESel nK mZ mX)
          (@Sampling.packedXSel nK mZ mX) pi u () x =
        ∏ k : Fin (nK + mZ + mX),
          basisUnitary (packedRoleBasis k) (u k) (x (pi.symm k)) := by
    unfold nativeSiftMeasurementRow Instrument.computationalMeasurement
      Instrument.nondemolitionReadout Instrument.nondemolitionReadoutKraus
      QKD.BB84.Model.siftPermHalf
    simp_rw [hmask]
    simp only [id_eq, diagonal_mul]
    rw [ite_eq_left trivial, one_mul]
    simp only [Matrix.mul_apply, Matrix.piTensorProduct,
      Quantum.Symmetry.permutationRepresentation, Matrix.tensorPermutation,
      Matrix.of_apply]
    rw [Fintype.sum_eq_single (x ∘ (pi.symm : Fin (nK + mZ + mX) → _))]
    · simp
    · intro y hy
      rw [ite_eq_right hy]
      simp
  let bitPerm : (Fin (nK + mZ + mX) → Bit) ≃
      (Fin (nK + mZ + mX) → Bit) := {
    toFun := fun x => x ∘ pi.symm
    invFun := fun x => x ∘ pi
    left_inv := fun x => by
      funext k
      simp
    right_inv := fun x => by
      funext k
      simp }
  let pairPerm := Equiv.prodCongr bitPerm bitPerm
  have hRange :
      Math.FiniteEmbedding.embeddingRange
          (Math.FiniteEmbedding.joinSubsetPerm S pi) =
        Math.FiniteEmbedding.embeddingRange (increasingSubsetEmbedding S) := by
    ext i
    simp only [Math.FiniteEmbedding.mem_embeddingRange_iff]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨pi.symm k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨pi k, congrArg (fun i => ((Math.FiniteEmbedding.increasingSubsetEquiv S) i).val)
        (pi.symm_apply_apply k)⟩
  have hSetRange :
      Set.range (Math.FiniteEmbedding.joinSubsetPerm S pi) =
        Set.range (increasingSubsetEmbedding S) := by
    rw [← Math.FiniteEmbedding.coe_embeddingRange,
      ← Math.FiniteEmbedding.coe_embeddingRange, hRange]
  have hSetComplement :
      (Set.range (Math.FiniteEmbedding.joinSubsetPerm S pi))ᶜ =
        (Set.range (increasingSubsetEmbedding S))ᶜ := congrArg (·ᶜ) hSetRange
  let complementPerm : Equiv.Perm (Fin (N - (nK + mZ + mX))) :=
    (Math.FiniteEmbedding.embeddingComplementEquiv
        (Math.FiniteEmbedding.joinSubsetPerm S pi)).trans
      ((Set.equivOfEq hSetComplement).trans
        (Math.FiniteEmbedding.embeddingComplementEquiv
          (increasingSubsetEmbedding S)).symm)
  have hComplement (j : Fin (N - (nK + mZ + mX))) :
      Math.FiniteEmbedding.embeddingComplementEquiv
          (increasingSubsetEmbedding S) (complementPerm j) =
        Set.equivOfEq hSetComplement
          (Math.FiniteEmbedding.embeddingComplementEquiv
            (Math.FiniteEmbedding.joinSubsetPerm S pi) j) := by
    simp [complementPerm]
  let complementBitPerm : (Fin (N - (nK + mZ + mX)) → Bit) ≃
      (Fin (N - (nK + mZ + mX)) → Bit) := {
    toFun := fun u => u ∘ complementPerm
    invFun := fun u => u ∘ complementPerm.symm
    left_inv := fun u => by
      funext j
      simp
    right_inv := fun u => by
      funext j
      simp }
  let complementPairPerm := Equiv.prodCongr complementBitPerm complementBitPerm
  have hSplit
      (x : Fin (nK + mZ + mX) → Bit)
      (u : Fin (N - (nK + mZ + mX)) → Bit) :
      selectedBitSplit (Math.FiniteEmbedding.joinSubsetPerm S pi)
          ((selectedBitSplit (increasingSubsetEmbedding S)).symm (x, u)) =
        (bitPerm x, complementBitPerm u) := by
    apply Prod.ext
    · funext k
      change ((selectedBitSplit (increasingSubsetEmbedding S)).symm (x, u))
          (Math.FiniteEmbedding.joinSubsetPerm S pi k) = x (pi.symm k)
      rw [show Math.FiniteEmbedding.joinSubsetPerm S pi k =
        increasingSubsetEmbedding S (pi.symm k) by rfl]
      have happly := congrArg Prod.fst
        ((selectedBitSplit (increasingSubsetEmbedding S)).apply_symm_apply (x, u))
      exact congrFun happly (pi.symm k)
    · funext j
      change ((selectedBitSplit (increasingSubsetEmbedding S)).symm (x, u))
          (Math.FiniteEmbedding.embeddingComplementEquiv
            (Math.FiniteEmbedding.joinSubsetPerm S pi) j) = u (complementPerm j)
      have hvalue := congrArg Subtype.val (hComplement j)
      have hvalue' :
          (Math.FiniteEmbedding.embeddingComplementEquiv
            (increasingSubsetEmbedding S) (complementPerm j)).1 =
          (Math.FiniteEmbedding.embeddingComplementEquiv
            (Math.FiniteEmbedding.joinSubsetPerm S pi) j).1 := by
        simpa using hvalue
      rw [← hvalue']
      have happly := congrArg Prod.snd
        ((selectedBitSplit (increasingSubsetEmbedding S)).apply_symm_apply (x, u))
      exact congrFun happly (complementPerm j)
  have hPairSplit
      (x : (Fin (nK + mZ + mX) → Bit) × (Fin (nK + mZ + mX) → Bit))
      (u : (Fin (N - (nK + mZ + mX)) → Bit) ×
        (Fin (N - (nK + mZ + mX)) → Bit)) :
      selectedPairBitSplit (Math.FiniteEmbedding.joinSubsetPerm S pi)
          ((selectedPairBitSplit (increasingSubsetEmbedding S)).symm (x, u)) =
        (pairPerm x, complementPairPerm u) := by
    rcases x with ⟨xA, xB⟩
    rcases u with ⟨vA, vB⟩
    apply Prod.ext
    · apply Prod.ext
      · change
          ((selectedBitSplit (Math.FiniteEmbedding.joinSubsetPerm S pi))
            ((selectedBitSplit (increasingSubsetEmbedding S)).symm (xA, vA))).1 =
            bitPerm xA
        exact congrArg Prod.fst (hSplit xA vA)
      · change
          ((selectedBitSplit (Math.FiniteEmbedding.joinSubsetPerm S pi))
            ((selectedBitSplit (increasingSubsetEmbedding S)).symm (xB, vB))).1 =
            bitPerm xB
        exact congrArg Prod.fst (hSplit xB vB)
    · apply Prod.ext
      · change
          ((selectedBitSplit (Math.FiniteEmbedding.joinSubsetPerm S pi))
            ((selectedBitSplit (increasingSubsetEmbedding S)).symm (xA, vA))).2 =
            complementBitPerm vA
        exact congrArg Prod.snd (hSplit xA vA)
      · change
          ((selectedBitSplit (Math.FiniteEmbedding.joinSubsetPerm S pi))
            ((selectedBitSplit (increasingSubsetEmbedding S)).symm (xB, vB))).2 =
            complementBitPerm vB
        exact congrArg Prod.snd (hSplit xB vB)
  have hPairSplitSymm
      (x : (Fin (nK + mZ + mX) → Bit) × (Fin (nK + mZ + mX) → Bit))
      (u : (Fin (N - (nK + mZ + mX)) → Bit) ×
        (Fin (N - (nK + mZ + mX)) → Bit)) :
      (selectedPairBitSplit (Math.FiniteEmbedding.joinSubsetPerm S pi)).symm
          (pairPerm x, complementPairPerm u) =
        (selectedPairBitSplit (increasingSubsetEmbedding S)).symm (x, u) := by
    rw [← hPairSplit x u,
      (selectedPairBitSplit
        (Math.FiniteEmbedding.joinSubsetPerm S pi)).symm_apply_apply]
  have hReindex
      (x y : (Fin (nK + mZ + mX) → Bit) ×
        (Fin (nK + mZ + mX) → Bit))
      (u : (Fin (N - (nK + mZ + mX)) → Bit) ×
        (Fin (N - (nK + mZ + mX)) → Bit)) :
      ((Matrix.reindexLinearEquiv ℂ ℂ (selectedPairBitSplit (Math.FiniteEmbedding.joinSubsetPerm S
        pi)) (selectedPairBitSplit (Math.FiniteEmbedding.joinSubsetPerm S pi))).toLinearMap
          (selectedReferenceInputBlock W s t))
            (pairPerm x, complementPairPerm u) (pairPerm y, complementPairPerm u) =
        ((Matrix.reindexLinearEquiv ℂ ℂ (selectedPairBitSplit (increasingSubsetEmbedding S))
          (selectedPairBitSplit (increasingSubsetEmbedding S))).toLinearMap
          (selectedReferenceInputBlock W s t)) (x, u) (y, u) := by
    change selectedReferenceInputBlock W s t
        ((selectedPairBitSplit (Math.FiniteEmbedding.joinSubsetPerm S pi)).symm
          (pairPerm x, complementPairPerm u))
        ((selectedPairBitSplit (Math.FiniteEmbedding.joinSubsetPerm S pi)).symm
          (pairPerm y, complementPairPerm u)) = _
    rw [hPairSplitSymm x u, hPairSplitSymm y u]
    rfl
  have hMarginal
      (x y : (Fin (nK + mZ + mX) → Bit) ×
        (Fin (nK + mZ + mX) → Bit)) :
      (∑ u,
        ((Matrix.reindexLinearEquiv ℂ ℂ (selectedPairBitSplit (Math.FiniteEmbedding.joinSubsetPerm S
          pi)) (selectedPairBitSplit (Math.FiniteEmbedding.joinSubsetPerm S pi))).toLinearMap
          (selectedReferenceInputBlock W s t))
            (pairPerm x, u) (pairPerm y, u)) =
        ∑ u,
          ((Matrix.reindexLinearEquiv ℂ ℂ (selectedPairBitSplit (increasingSubsetEmbedding S))
            (selectedPairBitSplit (increasingSubsetEmbedding S))).toLinearMap
            (selectedReferenceInputBlock W s t)) (x, u) (y, u) := by
    rw [← Equiv.sum_comp complementPairPerm]
    simp_rw [hReindex]
  let Kactual := fixedBasisPairKraus
    (selectedStoredRecords (Math.FiniteEmbedding.joinSubsetPerm S pi) omega.a uA)
    (selectedStoredRecords (Math.FiniteEmbedding.joinSubsetPerm S pi) omega.b uB)
  let Knative := nativeSiftPairKraus (nK + mZ + mX)
    (@Sampling.packedPESel nK mZ mX) (@Sampling.packedXSel nK mZ mX) pi uA uB
  have hK
      (x : (Fin (nK + mZ + mX) → Bit) × (Fin (nK + mZ + mX) → Bit)) :
      Kactual () (pairPerm x) = Knative () x := by
    rcases x with ⟨xA, xB⟩
    simp only [Kactual, Knative, fixedBasisPairKraus, selectedStoredRecords,
      nativeSiftPairKraus]
    rw [hnative uA xA, hnative uB xB, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro k _
    have hbasis := selectedEmbedding_basis_lookup omega h k
    rw [hselected] at hbasis
    rw [hbasis.1, hbasis.2]
    rfl
  change (Kactual *
      (selectedInputMarginalInstrument
        (Math.FiniteEmbedding.joinSubsetPerm S pi)).channel
          (selectedReferenceInputBlock W s t) * Kactualᴴ) () () =
    (Knative *
      (selectedInputMarginalInstrument (increasingSubsetEmbedding S)).channel
        (selectedReferenceInputBlock W s t) * Knativeᴴ) () ()
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [selectedInputMarginalInstrument_channel_apply]
  rw [← Equiv.sum_comp pairPerm]
  apply Finset.sum_congr rfl
  intro x _
  rw [hK x, ← Equiv.sum_comp pairPerm]
  simp_rw [hK, hMarginal]

end QKD.BB84.Measurement
