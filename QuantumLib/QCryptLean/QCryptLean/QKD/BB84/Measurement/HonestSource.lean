import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.TwoParty
import QCryptLean.Math.LinearAlgebra.Matrix.PiTensorProduct
import QCryptLean.QKD.BB84.Completeness
import QCryptLean.QKD.BB84.Measurement
import QCryptLean.QKD.BB84.Measurement.Classicality
import QCryptLean.QKD.BB84.Measurement.ProductInput
import QCryptLean.QKD.BB84.Measurement.Records
import QCryptLean.QKD.BB84.Measurement.Schedule
import QCryptLean.QKD.BB84.Measurement.SelectedRecords
import QCryptLean.QKD.BB84.Model.TwoBasisMeasurement
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Basic
import QCryptLean.QKD.BB84.Sampling.Selection
import QCryptLean.Quantum.Operators.Basic
import QCryptLean.Quantum.Operators.Gates
import QCryptLean.Quantum.Symmetry.Paired

/-! # Honest Source -/


open Quantum.Operators (Op)

open scoped Matrix BigOperators ComplexOrder Kronecker
open Matrix

noncomputable section

namespace QKD.BB84.Measurement
open LOCC

open QKD.BB84.Sampling
open QKD.BB84.FiniteKey

attribute [local instance] storedRecordVectorDecidableEq


/-- Group the physical Alice and Bob strings into their natural round pairs. -/
def honestRoundEquiv (N : ℕ) : (weightedStreamSystem Unit N).total ≃ Signals N :=
  (weightedScheduleUnitInputEquiv N).trans
    (Quantum.Symmetry.pairFunctions Bit Bit N).symm

/-- **The honest source on the physical input multipartite system**: `honestTensorSource N q` read
in
the program's input coordinates, round `i` of the transmitted stream carrying the `i`-th honest
pair. -/
def honestSource (N : ℕ) (q : ℝ) : Op (weightedStreamSystem Unit N).total :=
  Matrix.reindex (honestRoundEquiv N).symm (honestRoundEquiv N).symm (honestTensorSource N q)

/-- **The honest source is the i.i.d. product of the honest pair.** -/
theorem honestSource_eq_productSource (N : ℕ) (q : ℝ) :
    honestSource N q = productSource N (honestSourceSingle q) := by
  ext s s'
  simp [honestSource, productSource, honestTensorSource, honestRoundEquiv,
    Quantum.Symmetry.pairFunctions,
    Matrix.piTensorProduct_apply,
    roundProductOp, Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply]

/-- The honest source has unit trace, for every `q`. -/
theorem honestSource_trace (N : ℕ) (q : ℝ) : (honestSource N q).trace = 1 := by
  rw [honestSource_eq_productSource, trace_productSource, trace_honestSourceSingle, one_pow]


/-- **The honest law of one matched round's two bits**: agreement with probability `1 - q`,
disagreement with probability `q`, each ordered bit pair equally likely within either case. -/
def honestPairWeight (q : ℝ) (x y : Bit) : ℝ := if x = y then (1 - q) / 2 else q / 2

/-- **The honest law of one round's two recorded bits given both bases**: `honestPairWeight q` for
equal bases and uniform `1/4` for different bases. -/
def honestRoundLaw (q : ℝ) (θA θB : Basis) (x y : Bit) : ℝ :=
  if θA = θB then honestPairWeight q x y else 1 / 4

/-- For equal bases the honest round law is the matched-round law. -/
@[simp] theorem honestRoundLaw_self (q : ℝ) (θ : Basis) (x y : Bit) :
    honestRoundLaw q θ θ x y = honestPairWeight q x y := by
  simp [honestRoundLaw]

/-- The four honest matched-round weights add up to one. -/
theorem sum_honestPairWeight (q : ℝ) : ∑ x : Bit, ∑ y : Bit, honestPairWeight q x y = 1 := by
  simp [honestPairWeight, Fin.sum_univ_two]
  ring

/-- The honest matched-round weights are nonnegative on `0 ≤ q ≤ 1`. -/
theorem honestPairWeight_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (x y : Bit) :
    0 ≤ honestPairWeight q x y := by
  unfold honestPairWeight
  split_ifs <;> linarith

/-- Measuring both halves in the X basis reads the diagonal of the `H ⊗ H`-rotated operator. -/
private theorem pairBornWeight_x_x (σ : Op (Bit × Bit)) (x y : Bit) :
    pairBornWeight σ .x .x x y =
      (QKD.BB84.Model.hadamardPair * σ *
        QKD.BB84.Model.hadamardPair) (x, y) (x, y) := by
  have hH : ∀ i j : Bit, star (basisUnitary .x i j) = basisUnitary .x j i := by
    intro i j
    simp only [basisUnitary, Matrix.reindex_apply, Matrix.submatrix_apply]
    exact congrFun (congrFun Quantum.Gates.isHermitian_hadamard.eq
      (finTwoEquiv j)) (finTwoEquiv i)
  have hB : QKD.BB84.Model.hadamardPair = basisUnitary .x ⊗ₖ basisUnitary .x := rfl
  rw [hB]
  simp only [pairBornWeight, mul_apply, kroneckerMap_apply,
    Finset.sum_mul, star_mul', hH]
  exact Finset.sum_comm

/-- A Z-basis measurement of Alice's half selects her bit-`x` block of `σ`. -/
private theorem pairBornWeight_z_left (σ : Op (Bit × Bit)) (θB : Basis) (x y : Bit) :
    pairBornWeight σ .z θB x y = ∑ j : Bit, ∑ j' : Bit,
      basisUnitary θB y j * σ (x, j) (x, j') * star (basisUnitary θB y j') := by
  -- the Z-basis row of Alice's outcome `x` is the indicator of `x`; collapse its two sums
  simp only [pairBornWeight, Fintype.sum_prod_type, basisUnitary_z_apply, apply_ite star,
    star_zero, ite_mul, mul_ite, one_mul, zero_mul, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, Finset.sum_const_zero, Finset.sum_ite_irrel]

/-- A Z-basis measurement of Bob's half selects his bit-`y` block of `σ`. -/
private theorem pairBornWeight_z_right (σ : Op (Bit × Bit)) (θA : Basis) (x y : Bit) :
    pairBornWeight σ θA .z x y = ∑ i : Bit, ∑ i' : Bit,
      basisUnitary θA x i * σ (i, y) (i', y) * star (basisUnitary θA x i') := by
  -- the Z-basis row of Bob's outcome `y` is the indicator of `y`; collapse its two sums
  simp only [pairBornWeight, Fintype.sum_prod_type, basisUnitary_z_apply, apply_ite star,
    star_zero, ite_mul, mul_ite, zero_mul, mul_zero, mul_one, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Finset.sum_const_zero, Finset.sum_ite_irrel]

/-- Every X-basis amplitude has modulus squared `1/2`. -/
private theorem basisUnitary_x_mul_mul_star (x j : Bit) (c : ℂ) :
    basisUnitary .x x j * c * star (basisUnitary .x x j) = c / 2 := by
  have hs : ((Real.sqrt 2 : ℂ))⁻¹ * ((Real.sqrt 2 : ℂ))⁻¹ = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hstar : star ((Real.sqrt 2 : ℂ))⁻¹ = ((Real.sqrt 2 : ℂ))⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [basisUnitary_x_apply, star_mul', hstar]
  split_ifs
  · rw [star_neg, star_one]; linear_combination c * hs
  · rw [star_one]; linear_combination c * hs

/-- **The Born table of one honest pair.**  Measuring Alice's half in basis `θA` and Bob's in basis
`θB` yields `(x, y)` with probability `honestRoundLaw q θA θB x y`.  The Z–Z entries are the
computational diagonal; the X–X entries coincide with them because the honest pair is invariant
under `H ⊗ H` (`hadamardPair_honestSourceSingle_conj`); mixed bases give `1/4`. -/
theorem pairBornWeight_honestPair (q : ℝ) (θA θB : Basis) (x y : Bit) :
    pairBornWeight (honestSourceSingle q) θA θB x y = (honestRoundLaw q θA θB x y : ℂ) := by
  -- Z–Z: the computational diagonal of the honest pair
  have hzz : pairBornWeight (honestSourceSingle q) .z .z x y = (honestPairWeight q x y : ℂ) := by
    rw [pairBornWeight_z_z, honestSourceSingle_eq_matrix]
    simp only [ite_true, honestPairWeight]
    split_ifs <;> push_cast <;> rfl
  cases θA <;> cases θB
  · rw [hzz, honestRoundLaw_self]
  · -- Z–X: Alice's outcome selects her bit-`x` block, which is diagonal with trace `1/2`
    have h01 : honestSourceSingle q (x, 0) (x, 1) = 0 ∧ honestSourceSingle q (x, 1) (x, 0) = 0 := by
      fin_cases x <;> simp [honestSourceSingle_eq_matrix]
    have hdiag : honestSourceSingle q (x, 0) (x, 0) +
        honestSourceSingle q (x, 1) (x, 1) = 1 / 2 := by
      fin_cases x <;> simp [honestSourceSingle_eq_matrix] <;> ring
    rw [pairBornWeight_z_left]
    simp only [Fin.sum_univ_two, h01.1, h01.2, mul_zero, zero_mul, add_zero, zero_add,
      basisUnitary_x_mul_mul_star, honestRoundLaw, reduceCtorEq, ite_false]
    push_cast
    linear_combination hdiag / 2
  · -- X–Z: Bob's outcome selects his bit-`y` block, which is diagonal with trace `1/2`
    have h01 : honestSourceSingle q (0, y) (1, y) = 0 ∧ honestSourceSingle q (1, y) (0, y) = 0 := by
      fin_cases y <;> simp [honestSourceSingle_eq_matrix]
    have hdiag : honestSourceSingle q (0, y) (0, y) +
        honestSourceSingle q (1, y) (1, y) = 1 / 2 := by
      fin_cases y <;> simp [honestSourceSingle_eq_matrix] <;> ring
    rw [pairBornWeight_z_right]
    simp only [Fin.sum_univ_two, h01.1, h01.2, mul_zero, zero_mul, add_zero, zero_add,
      basisUnitary_x_mul_mul_star, honestRoundLaw, reduceCtorEq, ite_false]
    push_cast
    linear_combination hdiag / 2
  · -- X–X: `H ⊗ H` fixes the honest pair, so the X–X weights are the Z–Z weights
    rw [pairBornWeight_x_x, hadamardPair_honestSourceSingle_conj,
      ← pairBornWeight_z_z (honestSourceSingle q), hzz, honestRoundLaw_self]


/-- **The recorded bases and outcomes of the honest run.**  The measurement schedule's record
block is diagonal; its diagonal entry is the product of both parties' basis-string masses and of
the honest round law at every round's recorded bases and outcomes. -/
theorem weightedMeasurementSchedule_honestSource_apply (pA pB : PMF Basis) (N : ℕ) (q : ℝ)
    (rA rA' rB rB' : Fin N → StoredRecord) :
    ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleOutputEquiv Unit N)
      (weightedScheduleOutputEquiv Unit N)).toLinearMap
      (measurementState pA pB Unit N (honestSource N q)))
        (((), rA), ((), rB)) (((), rA'), ((), rB')) =
      if rA = rA' ∧ rB = rB' then
        ((basisStringLaw N pA (storedBasisString rA)).toReal : ℂ) *
        ((basisStringLaw N pB (storedBasisString rB)).toReal : ℂ) *
        ∏ i, (honestRoundLaw q (rA i).2.1 (rB i).2.1 (rA i).2.2 (rB i).2.2 : ℂ)
      else 0 := by
  rw [honestSource_eq_productSource, weightedMeasurementSchedule_productSource_apply]
  simp_rw [pairBornWeight_honestPair]

/-- **The selected data of the honest run, at every quota-feasible control.**

The selected-record entry between `r` and `r'` is zero unless `r = r'` and both records carry the
announced basis strings; then it is the raw-control mass of `ω` times the honest matched-round law
of every selected round's two bits.  This holds for every control meeting the quotas, including
controls of zero mass; the selected law is the same for all of them. -/
theorem selectionProgram_honestSource_success
    (pA pB : PMF Basis) (N nK mZ mX : ℕ) (q : ℝ) (ω : RawControl N)
    (h : HasQuotas nK mZ mX ω)
    (r r' : SelectedLocalRecord N (nK + mZ + mX) × SelectedLocalRecord N (nK + mZ + mX)) :
    let sigma : Op (TwoParty.system (CompletedLocalRecord N) (CompletedLocalRecord N)).total :=
      measurementState pA pB Unit N (honestSource N q)
    let upsilon : Op (LOCC.TwoParty.system (CompletedLocalRecord N)
        (CompletedLocalRecord N)).total :=
      (announceBobBases (A := CompletedLocalRecord N) N).successorOperation ω.b
      ((announceAliceBases (B := CompletedLocalRecord N) N).successorOperation ω.a sigma)
    (retainBob (A := SelectedLocalRecord N (nK + mZ + mX))
      (selectedEmbedding ω h)).successorOperation ()
      ((retainAlice (B := CompletedLocalRecord N) (selectedEmbedding ω h)).successorOperation ()
        ((announceShuffle (B := CompletedLocalRecord N) ω.a ω.b).successorOperation
          ω.order upsilon))
      ((TwoParty.pairEquiv _ _).symm r) ((TwoParty.pairEquiv _ _).symm r') =
      if r = r' ∧ r.1.1 = ω.a ∧ r.2.1 = ω.b then
        ((rawControlLaw N pA pB ω).toReal : ℂ) *
          ∏ k, (honestPairWeight q (r.1.2 k) (r.2.2 k) : ℂ)
      else 0 := by
  rw [honestSource_eq_productSource]
  refine (selectionProgram_productSource_success pA pB N nK mZ mX
    (honestSourceSingle q) ω h r r').trans ?_
  rw [trace_honestSourceSingle, one_pow, mul_one]
  simp_rw [pairBornWeight_honestPair, honestRoundLaw_self]


/-- A physical pair with uniform matched-basis marginals and disagreement rate `q` in both
Z and X bases. Equal matched tables do not characterize invariance under `H ⊗ H`.
Mixed-basis tables are unconstrained because unmatched rounds are discarded. -/
structure HonestPairLaw (q : ℝ) (σ : Op (Bit × Bit)) : Prop where
  /-- The pair has unit trace. -/
  trace_eq_one : σ.trace = 1
  /-- The pair is a positive semidefinite operator. -/
  posSemidef : σ.PosSemidef
  /-- Both matched measurement bases have the symmetric binary error law. -/
  pairBornWeight_self : ∀ θ x y,
    pairBornWeight σ θ θ x y = (honestPairWeight q x y : ℂ)

/-- Independent identical physical pairs with the prescribed matched-basis law.
This shares the IID input form of Renner, quant-ph/0512258, main.tex:1655–1660; Renner's
class Γ there is defined by non-abortion, rather than by this specific Born table. -/
def HonestOperation (N : ℕ) (q : ℝ) (ρ : Op (weightedStreamSystem Unit N).total) : Prop :=
  ∃ σ : Op (Bit × Bit), HonestPairLaw q σ ∧ ρ = productSource N σ

/-- Positivity of a disagreeing Z-basis outcome implies a nonnegative error rate. -/
lemma HonestPairLaw.rate_nonneg {q : ℝ} {σ : Op (Bit × Bit)} (h : HonestPairLaw q σ) :
    0 ≤ q := by
  have hd := h.posSemidef.diag_nonneg (i := ((0 : Bit), (1 : Bit)))
  rw [← pairBornWeight_z_z σ 0 1, h.pairBornWeight_self] at hd
  have hr := (Complex.nonneg_iff.mp hd).1
  norm_num [honestPairWeight] at hr
  linarith

/-- Positivity of an agreeing Z-basis outcome bounds the error rate by one. -/
lemma HonestPairLaw.rate_le_one {q : ℝ} {σ : Op (Bit × Bit)} (h : HonestPairLaw q σ) :
    q ≤ 1 := by
  have hd := h.posSemidef.diag_nonneg (i := ((0 : Bit), (0 : Bit)))
  rw [← pairBornWeight_z_z σ 0 0, h.pairBornWeight_self] at hd
  have hr := (Complex.nonneg_iff.mp hd).1
  norm_num [honestPairWeight] at hr
  linarith

/-- A physical honest operation has nonnegative error rate. -/
lemma HonestOperation.rate_nonneg {N : ℕ} {q : ℝ}
    {ρ : Op (weightedStreamSystem Unit N).total} (h : HonestOperation N q ρ) : 0 ≤ q := by
  obtain ⟨σ, hσ, -⟩ := h
  exact hσ.rate_nonneg

/-- A physical honest operation has error rate at most one. -/
lemma HonestOperation.rate_le_one {N : ℕ} {q : ℝ}
    {ρ : Op (weightedStreamSystem Unit N).total} (h : HonestOperation N q ρ) : q ≤ 1 := by
  obtain ⟨σ, hσ, -⟩ := h
  exact hσ.rate_le_one

/-- A product of unit-trace honest pairs has unit trace. -/
lemma HonestOperation.trace_eq_one {N : ℕ} {q : ℝ}
    {ρ : Op (weightedStreamSystem Unit N).total} (h : HonestOperation N q ρ) : ρ.trace = 1 := by
  obtain ⟨σ, hσ, rfl⟩ := h
  rw [trace_productSource, hσ.trace_eq_one, one_pow]

/-- The library's Bell-diagonal pair has the physical honest law for `0 ≤ q ≤ 1/2`. -/
theorem honestPairLaw_honestPair (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    HonestPairLaw q (honestSourceSingle q) :=
  ⟨trace_honestSourceSingle q, posSemidef_honestSourceSingle q hq0 hq, fun θ x y => by
    rw [pairBornWeight_honestPair, honestRoundLaw_self]⟩

/-- The product of the library's honest pairs is an honest operation for `0 ≤ q ≤ 1/2`. -/
theorem honestOperation_honestSource (N : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    HonestOperation N q (honestSource N q) :=
  ⟨honestSourceSingle q, honestPairLaw_honestPair q hq0 hq, honestSource_eq_productSource N q⟩

end QKD.BB84.Measurement
