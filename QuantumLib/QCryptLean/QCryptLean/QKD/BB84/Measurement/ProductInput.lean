import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.Program.ExitWeight
import QCryptLean.LOCC.TwoParty
import QCryptLean.Math.Combinatorics.DoubleProductSum
import QCryptLean.Math.FiniteEmbedding
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.QKD.BB84.Measurement
import QCryptLean.QKD.BB84.Measurement.Classicality
import QCryptLean.QKD.BB84.Measurement.LatePublicControl.BranchValues
import QCryptLean.QKD.BB84.Measurement.OutputLaw
import QCryptLean.QKD.BB84.Measurement.Records
import QCryptLean.QKD.BB84.Measurement.Schedule
import QCryptLean.QKD.BB84.Measurement.SelectedBornRule
import QCryptLean.QKD.BB84.Measurement.SelectedMarginal
import QCryptLean.QKD.BB84.Measurement.SelectedRecords
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Basic
import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Gates

/-! # Product Input -/


open Quantum.Operators (Op)

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QKD.BB84.Measurement
open LOCC

open LOCC.TwoParty
open QKD.BB84.Sampling

attribute [local instance] storedRecordVectorDecidableEq


/-- **The `N`-fold product of a two-qubit operator** in Alice/Bob bit-string coordinates: the
entry between `(xA, xB)` and `(xA', xB')` is the product over rounds of the entries of `σ` between
the round-`i` bit pairs. -/
def roundProductOp (N : ℕ) (σ : Op (Bit × Bit)) : Op ((Fin N → Bit) × (Fin N → Bit)) :=
  Matrix.of fun x x' => ∏ i, σ (x.1 i, x.2 i) (x'.1 i, x'.2 i)

/-- **The i.i.d. source `σ^{⊗N}` on the physical input multipartite system**: round `i` of Alice's
and Bob's input streams carries the `i`-th copy of `σ`. -/
def productSource (N : ℕ) (σ : Op (Bit × Bit)) : Op (weightedStreamSystem Unit N).total :=
  (Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleUnitInputEquiv N).symm
    (weightedScheduleUnitInputEquiv N).symm).toLinearMap (roundProductOp N σ)

/-- In the physical Alice/Bob bit-string coordinates the product source is the round product. -/
@[simp] theorem reindexOp_productSource (N : ℕ) (σ : Op (Bit × Bit)) :
    (Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleUnitInputEquiv N)
      (weightedScheduleUnitInputEquiv N)).toLinearMap (productSource N σ) = roundProductOp N σ := by
  ext x x'
  exact congrArg₂ (roundProductOp N σ)
    ((weightedScheduleUnitInputEquiv N).apply_symm_apply x)
    ((weightedScheduleUnitInputEquiv N).apply_symm_apply x')

/-- **One-round Born weight.**  Alice measures her qubit of one copy of `σ` in basis `θA` and reads
`x`; Bob measures his in basis `θB` and reads `y`.  For a state this is the joint probability of
the two outcomes. -/
def pairBornWeight (σ : Op (Bit × Bit)) (θA θB : Basis) (x y : Bit) : ℂ :=
  ∑ c : Bit × Bit, ∑ c' : Bit × Bit,
    basisUnitary θA x c.1 * basisUnitary θB y c.2 * σ c c' *
      star (basisUnitary θA x c'.1 * basisUnitary θB y c'.2)

/-- The Z-basis measurement row is the computational-basis indicator. -/
theorem basisUnitary_z_apply (x j : Bit) : basisUnitary .z x j = if x = j then 1 else 0 := by
  simp [basisUnitary, Matrix.one_apply]

/-- The X-basis measurement row is a Hadamard row: amplitude `1/√2`, with sign `-1` exactly when
the outcome and the input bit are both `1`. -/
theorem basisUnitary_x_apply (x j : Bit) :
    basisUnitary .x x j = ((Real.sqrt 2 : ℂ))⁻¹ * (if x = 1 ∧ j = 1 then -1 else 1) := by
  fin_cases x <;> fin_cases j <;>
    simp [basisUnitary, Quantum.Gates.hadamard, Matrix.reindex_apply,
      Matrix.submatrix_apply, finTwoEquiv]

/-- Measuring both halves in the Z basis reads the computational diagonal of `σ`. -/
theorem pairBornWeight_z_z (σ : Op (Bit × Bit)) (x y : Bit) :
    pairBornWeight σ .z .z x y = σ (x, y) (x, y) := by
  fin_cases x <;> fin_cases y <;>
    simp [pairBornWeight, basisUnitary_z_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- **Round products over pairs of bit strings factor round by round**: summing
`∏ i, g i (xA i, xB i)` over all Alice/Bob bit-string pairs gives `∏ i, ∑ c, g i c`. -/
theorem sum_pairStrings_prod {R : Type*} [CommSemiring R] {n : ℕ} (g : Fin n → Bit × Bit → R) :
    (∑ x : (Fin n → Bit) × (Fin n → Bit), ∏ i, g i (x.1 i, x.2 i)) = ∏ i, ∑ c, g i c := by
  rw [Fintype.prod_sum,
    ← (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Bit) (fun _ => Bit)).sum_comp]
  rfl

/-- The same factorization for a row and a column pair of bit strings. -/
theorem sum_sum_pairStrings_prod {R : Type*} [CommSemiring R] {n : ℕ}
    (g : Fin n → Bit × Bit → Bit × Bit → R) :
    (∑ x : (Fin n → Bit) × (Fin n → Bit), ∑ x' : (Fin n → Bit) × (Fin n → Bit),
        ∏ i, g i (x.1 i, x.2 i) (x'.1 i, x'.2 i)) = ∏ i, ∑ c, ∑ c', g i c c' := by
  rw [← Fintype.sum_sum_prod,
    ← (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Bit) (fun _ => Bit)).sum_comp]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Bit) (fun _ => Bit)).sum_comp]
  rfl

/-- **The fixed-basis Born weight of a round product factorizes over rounds.**  For any
chronological records `rA`, `rB`, the rank-one measurement row of those records applied to
`σ^{⊗n}` is the product of the one-round Born weights at each round's bases and outcomes. -/
theorem Matrix.conjLinearMap_fixedBasisPairKraus_roundProductOp {n : ℕ} (σ : Op (Bit × Bit))
    (rA rB : Fin n → StoredRecord) :
    Matrix.conjLinearMap (fixedBasisPairKraus rA rB) (roundProductOp n σ) () () =
      ∏ i, pairBornWeight σ (rA i).2.1 (rB i).2.1 (rA i).2.2 (rB i).2.2 := by
  simp only [Matrix.conjLinearMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply,
    Matrix.conjTranspose_apply, fixedBasisPairKraus, roundProductOp, Matrix.of_apply,
    Finset.sum_mul, star_prod]
  rw [Finset.sum_comm]
  simp only [← Finset.prod_mul_distrib]
  exact sum_sum_pairStrings_prod fun i c c' =>
    basisUnitary (rA i).2.1 (rA i).2.2 c.1 * basisUnitary (rB i).2.1 (rB i).2.2 c.2 *
      σ c c' * star (basisUnitary (rA i).2.1 (rA i).2.2 c'.1 *
        basisUnitary (rB i).2.1 (rB i).2.2 c'.2)

/-- The trace of a round product is the `N`-th power of the one-copy trace. -/
theorem trace_roundProductOp (N : ℕ) (σ : Op (Bit × Bit)) :
    (roundProductOp N σ).trace = σ.trace ^ N := by
  rw [Matrix.trace, ← Fin.prod_const]
  simp only [Matrix.diag, roundProductOp, Matrix.of_apply]
  exact sum_pairStrings_prod fun _ c => σ c c

/-- The product source has the trace of the round product. -/
theorem trace_productSource (N : ℕ) (σ : Op (Bit × Bit)) :
    (productSource N σ).trace = σ.trace ^ N := by
  rw [← trace_roundProductOp]
  exact trace_reindexOp _ _

/-- **The selected-round marginal of a round product** is the round product on the selected
rounds, times the one-copy trace once for every discarded round.  The embedding may select the
rounds in any order. -/
theorem selectedInputMarginalInstrument_roundProductOp {n N : ℕ} (f : Fin n ↪ Fin N)
    (σ : Op (Bit × Bit)) :
    (selectedInputMarginalInstrument f).channel (roundProductOp N σ) =
      σ.trace ^ (N - n) • roundProductOp n σ := by
  ext v v'
  rw [selectedInputMarginalInstrument_channel_apply]
  have hsplit (u : (Fin (N - n) → Bit) × (Fin (N - n) → Bit)) :
      ((Matrix.reindexLinearEquiv ℂ ℂ (selectedPairBitSplit f) (selectedPairBitSplit f)).toLinearMap
        (roundProductOp N σ)) (v, u) (v', u) =
        (∏ k, σ (v.1 k, v.2 k) (v'.1 k, v'.2 k)) * ∏ j, σ (u.1 j, u.2 j) (u.1 j, u.2 j) := by
    simp only [LinearEquiv.coe_coe, Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply,
      Matrix.submatrix_apply,
      roundProductOp, Matrix.of_apply, selectedPairBitSplit, selectedBitSplit,
      Equiv.coe_fn_symm_mk]
    rw [← (Math.FiniteEmbedding.embeddingSplitEquiv f).prod_comp, Fintype.prod_sum_type]
    simp
  simp_rw [hsplit, ← Finset.mul_sum]
  rw [sum_pairStrings_prod (fun _ c => σ c c)]
  simp [roundProductOp, Matrix.trace, mul_comm]


/-- **Records of the measurement schedule on a product source.**  The terminal record block is
diagonal; its diagonal entry is the product basis-string mass of both parties times the product of
the one-round Born weights at the recorded bases and outcomes. -/
theorem weightedMeasurementSchedule_productSource_apply (pA pB : PMF Basis) (N : ℕ)
    (σ : Op (Bit × Bit)) (rA rA' rB rB' : Fin N → StoredRecord) :
    ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleOutputEquiv Unit N)
      (weightedScheduleOutputEquiv Unit N)).toLinearMap
      (measurementState pA pB Unit N (productSource N σ)))
        (((), rA), ((), rB)) (((), rA'), ((), rB')) =
      if rA = rA' ∧ rB = rB' then
        ((Sampling.basisStringLaw N pA (storedBasisString rA)).toReal : ℂ) *
        ((Sampling.basisStringLaw N pB (storedBasisString rB)).toReal : ℂ) *
        ∏ i, pairBornWeight σ (rA i).2.1 (rB i).2.1 (rA i).2.2 (rB i).2.2
      else 0 := by
  rw [weightedMeasurementSchedule_output_apply, weightedScheduleInputBlock_unit_eq_reindex,
    reindexOp_productSource, Matrix.conjLinearMap_fixedBasisPairKraus_roundProductOp]

/-- **Selected records of a product source at a quota-feasible control.**

At every public control `ω` meeting the quotas, the selected-record entry between `r` and `r'` is
zero unless `r = r'` and both records carry the announced basis strings; then it is the raw-control
mass of `ω`, times one trace of `σ` for each of the `N - (nK + mZ + mX)` unselected rounds, times
the product over the selected positions `k` of the one-round Born weight in the packed role basis
`packedRoleBasis k` at the selected bits.  The control enters only through its mass: the selected
rounds are matched, with Z on the key and Z-test roles and X on the X-test roles
(`selectedEmbedding_basis_lookup`). -/
theorem selectionProgram_productSource_success
    (pA pB : PMF Basis) (N nK mZ mX : ℕ) (σ : Op (Bit × Bit)) (ω : RawControl N)
    (h : HasQuotas nK mZ mX ω)
    (r r' : SelectedLocalRecord N (nK + mZ + mX) × SelectedLocalRecord N (nK + mZ + mX)) :
    let sigma : Op (system (CompletedLocalRecord N) (CompletedLocalRecord N)).total :=
      measurementState pA pB Unit N (productSource N σ)
    let upsilon : Op (LOCC.TwoParty.system (CompletedLocalRecord N)
        (CompletedLocalRecord N)).total :=
      (announceBobBases (A := CompletedLocalRecord N) N).successorOperation ω.b
      ((announceAliceBases (B := CompletedLocalRecord N) N).successorOperation ω.a sigma)
    (retainBob (A := SelectedLocalRecord N (nK + mZ + mX))
      (selectedEmbedding ω h)).successorOperation ()
      ((retainAlice (B := CompletedLocalRecord N) (selectedEmbedding ω h)).successorOperation ()
        ((announceShuffle (B := CompletedLocalRecord N) ω.a ω.b).successorOperation
          ω.order upsilon))
      ((pairEquiv _ _).symm r) ((pairEquiv _ _).symm r') =
      if r = r' ∧ r.1.1 = ω.a ∧ r.2.1 = ω.b then
        ((rawControlLaw N pA pB ω).toReal : ℂ) * σ.trace ^ (N - (nK + mZ + mX)) *
          ∏ k, pairBornWeight σ (packedRoleBasis k) (packedRoleBasis k) (r.1.2 k) (r.2.2 k)
      else 0 := by
  refine (weightedLatePublicSelectionProgram_success_apply pA pB N nK mZ mX
    ω h (productSource N σ) r r').trans ?_
  rcases r with ⟨⟨a, uA⟩, ⟨b, uB⟩⟩
  rcases r' with ⟨⟨a', uA'⟩, ⟨b', uB'⟩⟩
  rw [selectedMeasurementLaw_apply, reindexOp_productSource,
    selectedInputMarginalInstrument_roundProductOp, map_smul, Matrix.smul_apply,
    Matrix.conjLinearMap_fixedBasisPairKraus_roundProductOp]
  by_cases hr : ((a, uA), (b, uB)) = ((a', uA'), (b', uB')) ∧ a = ω.a ∧ b = ω.b
  · obtain ⟨hrr, rfl, rfl⟩ := hr
    simp only [Prod.mk.injEq] at hrr
    obtain ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩ := hrr
    have hbases (k : Fin (nK + mZ + mX)) :
        (selectedStoredRecords (selectedEmbedding ω h) ω.a uA k).2.1 = packedRoleBasis k ∧
          (selectedStoredRecords (selectedEmbedding ω h) ω.b uB k).2.1 = packedRoleBasis k :=
      selectedEmbedding_basis_lookup ω h k
    simp only [and_self, ite_true, smul_eq_mul]
    rw [rawControlLaw_toReal_eq]
    simp only [selectedStoredRecords] at hbases ⊢
    simp_rw [(hbases _).1, (hbases _).2]
    ring
  · rw [ite_eq_right hr]
    by_cases hbase : a = ω.a ∧ a' = ω.a ∧ b = ω.b ∧ b' = ω.b
    · rw [ite_eq_left hbase, ite_eq_right, mul_zero]
      rintro ⟨h1, h2⟩
      exact hr ⟨Prod.ext h1 h2, hbase.1, hbase.2.2.1⟩
    · rw [ite_eq_right hbase]

end QKD.BB84.Measurement
