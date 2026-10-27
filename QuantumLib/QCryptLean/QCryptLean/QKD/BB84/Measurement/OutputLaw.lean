import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.LOCC.Instrument.WeightedChoice
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.TwoParty
import QCryptLean.Math.Combinatorics.DoubleProductSum
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.QKD.BB84.Measurement
import QCryptLean.QKD.BB84.Measurement.Classicality
import QCryptLean.QKD.BB84.Measurement.Records
import QCryptLean.QKD.BB84.Measurement.Schedule
import QCryptLean.QKD.BB84.Measurement.Weighted
import QCryptLean.QKD.BB84.Registers
import QCryptLean.QKD.BB84.Sampling.Basic
import QCryptLean.Quantum.Operators.Basic

/-! # Output Law -/


open Quantum.Operators (Op)

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QKD.BB84.Measurement
open LOCC

open LOCC.TwoParty

attribute [local instance] storedRecordVectorDecidableEq

/-- The rectangular rank-one row for fixed Alice and Bob chronological records.

Its columns are pairs of input bit strings.  The coefficient is the chronological product of the
two local BB84 basis-unitary entries, with Alice's and Bob's records kept separate. -/
def fixedBasisPairKraus {N : ℕ}
    (rA rB : Fin N → StoredRecord) :
    Matrix Unit ((Fin N → Bit) × (Fin N → Bit)) ℂ :=
  fun _ x =>
    ∏ i : Fin N,
      basisUnitary (rA i).2.1 (rA i).2.2 (x.1 i) *
      basisUnitary (rB i).2.1 (rB i).2.2 (x.2 i)

/-- The arbitrary input-operator block between four fixed accumulator coordinates.

The Alice and Bob input bit strings remain independent coordinates.  This is only a structural
submatrix of the actual schedule input and assumes no positivity, trace, or Hermiticity. -/
def weightedScheduleInputBlock
    (F : Type) [Fintype F] [DecidableEq F]
    (N : ℕ) (rho : Op (weightedStreamSystem F N).total)
    (fA fA' fB fB' : F) :
    Op ((Fin N → Bit) × (Fin N → Bit)) :=
  ((Matrix.reindexLinearEquiv ℂ ℂ (weightedStreamPairEquiv F N) (weightedStreamPairEquiv F
    N)).toLinearMap rho).submatrix
    (fun x => ((fA, x.1), (fB, x.2)))
    (fun x => ((fA', x.1), (fB', x.2)))

/-- The native private loop has the exact product-measurement kernel in record coordinates. -/
theorem scheduleWithMemory_output_apply
    (pA pB : PMF Basis)
    (F : Type) [Fintype F] [DecidableEq F]
    (N : ℕ) (rho : Op (weightedStreamSystem F N).total)
    (fA fA' fB fB' : F)
    (rA rA' rB rB' : Fin N → StoredRecord) :
    ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleOutputEquiv F N) (weightedScheduleOutputEquiv F
      N)).toLinearMap
      ((measurementState pA pB F N) rho))
        ((fA, rA), (fB, rB)) ((fA', rA'), (fB', rB')) =
      if rA = rA' ∧ rB = rB' then
        ((Sampling.basisStringLaw N pA
          (storedBasisString rA)).toReal : ℂ) *
        ((Sampling.basisStringLaw N pB
          (storedBasisString rB)).toReal : ℂ) *
        (Matrix.conjLinearMap (fixedBasisPairKraus rA rB)
          (weightedScheduleInputBlock F N rho fA fA' fB fB')) () ()
      else 0 := by
  have weightedOperationApply (p : PMF Basis) (observed : Record)
      (sigma : Op Bit) (stored stored' : StoredRecord) :
      (weightedMeasureAndRecord p).operation observed sigma stored stored' =
        if stored.2 = observed ∧ stored'.2 = observed then
          ((p observed.1).toReal : ℂ) *
            ∑ j : Bit, ∑ k : Bit,
              basisUnitary observed.1 observed.2 j * sigma j k *
                star (basisUnitary observed.1 observed.2 k)
        else 0 := by
    obtain ⟨θ, x⟩ := observed
    have hbranch :
        (fixedBasisMeasurement θ).operation x = Matrix.conjLinearMap (fixedBasisKraus θ x) := by
      change (∑ _ : Unit, Matrix.conjLinearMap (fixedBasisKraus θ x)) = _
      exact Fintype.sum_unique _
    have hentry : (Matrix.conjLinearMap (fixedBasisKraus θ x) sigma) () () =
        ∑ j : Bit, ∑ k : Bit, basisUnitary θ x j * sigma j k * star (basisUnitary θ x k) := by
      rw [Matrix.conjLinearMap_apply_apply, Finset.sum_comm]
      rfl
    rw [weightedMeasureAndRecord, Instrument.keeping_operation_apply,
      Instrument.weightedChoice_operation, LinearMap.smul_apply, Matrix.smul_apply, smul_eq_mul,
      hbranch, hentry]
  by_cases hrecords : rA = rA' ∧ rB = rB'
  · rcases hrecords with ⟨rfl, rfl⟩
    rw [ite_eq_left ⟨rfl, rfl⟩]
    induction N generalizing F with
    | zero =>
        have hempty (x : Fin 0 → Bit) : x = fun i => Fin.elim0 i := funext fun i => Fin.elim0 i
        let : Unique ((Fin 0 → Bit) × (Fin 0 → Bit)) :=
          { default := ((fun i => Fin.elim0 i), fun i => Fin.elim0 i)
            uniq := fun x => Prod.ext (hempty x.1) (hempty x.2) }
        rw [Matrix.conjLinearMap_apply_apply, Fintype.sum_unique, Fintype.sum_unique]
        simp only [Sampling.basisStringLaw_apply, fixedBasisPairKraus, Fin.prod_univ_zero,
          ENNReal.toReal_one, Complex.ofReal_one, one_mul, mul_one, star_one]
        rfl
    | succ n ih =>
        let sigma (observedA observedB : Record) :=
          measureBobOperation pB F n observedB (measureAliceOperation pA F n observedA rho)
        change (measurementState pA pB F (n + 1)) rho
          ((weightedScheduleOutputEquiv F (n + 1)).symm ((fA, rA), (fB, rB)))
          ((weightedScheduleOutputEquiv F (n + 1)).symm ((fA', rA), (fB', rB))) = _
        rw [measurementState_succ]
        simp only [Matrix.sum_apply]
        have hrec (observedA observedB : Record) :
            (measurementState pA pB (F × StoredRecord) n)
                (sigma observedA observedB)
                ((weightedScheduleOutputEquiv F (n + 1)).symm
                  ((fA, rA), (fB, rB)))
                ((weightedScheduleOutputEquiv F (n + 1)).symm
                  ((fA', rA), (fB', rB))) =
              ((Sampling.basisStringLaw n pA
                (storedBasisString (Fin.tail rA))).toReal : ℂ) *
              ((Sampling.basisStringLaw n pB
                (storedBasisString (Fin.tail rB))).toReal : ℂ) *
              (Matrix.conjLinearMap
                (fixedBasisPairKraus (Fin.tail rA) (Fin.tail rB))
                (weightedScheduleInputBlock (F × StoredRecord) n
                  (sigma observedA observedB)
                  (fA, rA 0) (fA', rA 0)
                  (fB, rB 0) (fB', rB 0))) () () := by
          have h := ih (F := F × StoredRecord)
            (rho := sigma observedA observedB)
            (fA := (fA, rA 0)) (fA' := (fA', rA 0))
            (fB := (fB, rB 0)) (fB' := (fB', rB 0))
            (Fin.tail rA) (Fin.tail rB)
          exact h
        let rhoPair : ((F × (Fin (n + 1) → Bit)) × (F × (Fin (n + 1) → Bit))) →
            ((F × (Fin (n + 1) → Bit)) × (F × (Fin (n + 1) → Bit))) → ℂ :=
          (Matrix.reindexLinearEquiv ℂ ℂ (weightedStreamPairEquiv F (n + 1))
            (weightedStreamPairEquiv F (n + 1))).toLinearMap rho
        have hstep (observedA observedB : Record)
            (tailA tailA' tailB tailB' : Fin n → Bit) :
            weightedScheduleInputBlock (F × StoredRecord) n
                (sigma observedA observedB)
                (fA, rA 0) (fA', rA 0) (fB, rB 0) (fB', rB 0)
                (tailA, tailB) (tailA', tailB') =
              ((weightedMeasureAndRecord pB).operation observedB
                (Matrix.of fun j k =>
                  ((weightedMeasureAndRecord pA).operation observedA
                    (Matrix.of fun l m => rhoPair
                      ((fA, Fin.cons l tailA), (fB, Fin.cons j tailB))
                      ((fA', Fin.cons m tailA'), (fB', Fin.cons k tailB')))
                    (rA 0) (rA 0)))
                (rB 0) (rB 0)) := by
          change (measureBobOperation pB F n observedB
            (measureAliceOperation pA F n observedA rho))
              ((pairEquiv _ _).symm (((fA, rA 0), tailA), ((fB, rB 0), tailB)))
              ((pairEquiv _ _).symm (((fA', rA 0), tailA'), ((fB', rB 0), tailB'))) = _
          rw [measureBob_operation_apply, weightedStreamStep_operation_apply]
          apply congrArg (fun tau : Op Bit =>
            ((weightedMeasureAndRecord pB).operation observedB tau) (rB 0) (rB 0))
          funext j k
          change (measureAliceOperation pA F n observedA rho)
            ((pairEquiv _ _).symm (((fA, rA 0), tailA), (fB, Fin.cons j tailB)))
            ((pairEquiv _ _).symm (((fA', rA 0), tailA'), (fB', Fin.cons k tailB'))) = _
          refine (measureAlice_operation_apply pA F n observedA rho
            ((fA, rA 0), tailA) ((fA', rA 0), tailA')
            (fB, Fin.cons j tailB) (fB', Fin.cons k tailB')).trans ?_
          rw [weightedStreamStep_operation_apply]
          rfl
        let allCons :
            (((Fin n → Bit) × (Fin n → Bit)) ×
              (((Fin n → Bit) × (Fin n → Bit)) ×
                (Bit × (Bit × (Bit × Bit))))) ≃
              (((Fin (n + 1) → Bit) × (Fin (n + 1) → Bit)) ×
                ((Fin (n + 1) → Bit) × (Fin (n + 1) → Bit))) :=
          { toFun := fun q =>
              ((Fin.cons q.2.2.2.2.2 q.1.1,
                  Fin.cons q.2.2.2.1 q.1.2),
                (Fin.cons q.2.2.2.2.1 q.2.1.1,
                  Fin.cons q.2.2.1 q.2.1.2))
            invFun := fun q =>
              ((Fin.tail q.1.1, Fin.tail q.1.2),
                ((Fin.tail q.2.1, Fin.tail q.2.2),
                  (q.2.2 0, (q.1.2 0, (q.2.1 0, q.1.1 0)))))
            left_inv := by
              intro q
              rcases q with ⟨tc, tr, br, bc, ar, ac⟩
              simp [Fin.tail_cons]
            right_inv := by
              intro q
              rcases q with ⟨⟨cA, cB⟩, ⟨uA, uB⟩⟩
              simp [Fin.cons_self_tail] }
        have sumAll
            (g : ((Fin (n + 1) → Bit) × (Fin (n + 1) → Bit)) →
              ((Fin (n + 1) → Bit) × (Fin (n + 1) → Bit)) → ℂ) :
            (∑ col, ∑ row, g col row) =
              ∑ tailCol : (Fin n → Bit) × (Fin n → Bit),
              ∑ tailRow : (Fin n → Bit) × (Fin n → Bit),
              ∑ bobRow : Bit, ∑ bobCol : Bit,
              ∑ aliceRow : Bit, ∑ aliceCol : Bit,
                g (Fin.cons aliceCol tailCol.1, Fin.cons bobCol tailCol.2)
                  (Fin.cons aliceRow tailRow.1, Fin.cons bobRow tailRow.2) := by
          calc
            _ = ∑ q :
                (((Fin (n + 1) → Bit) × (Fin (n + 1) → Bit)) ×
                  ((Fin (n + 1) → Bit) × (Fin (n + 1) → Bit))),
                g q.1 q.2 := by
              exact (Fintype.sum_prod_type (f := fun q => g q.1 q.2)).symm
            _ = ∑ q, g (allCons q).1 (allCons q).2 := by
              exact (Equiv.sum_comp allCons (fun q => g q.1 q.2)).symm
            _ = _ := by
              rw [Fintype.sum_prod_type]
              apply Finset.sum_congr rfl
              intro tailCol _
              rw [Fintype.sum_prod_type]
              apply Finset.sum_congr rfl
              intro tailRow _
              rw [Fintype.sum_prod_type]
              apply Finset.sum_congr rfl
              intro bobRow _
              rw [Fintype.sum_prod_type]
              apply Finset.sum_congr rfl
              intro bobCol _
              rw [Fintype.sum_prod_type]
              rfl
        calc
          _ = ∑ observedA : Record, ∑ observedB : Record,
              ((Sampling.basisStringLaw n pA
                (storedBasisString (Fin.tail rA))).toReal : ℂ) *
              ((Sampling.basisStringLaw n pB
                (storedBasisString (Fin.tail rB))).toReal : ℂ) *
              (Matrix.conjLinearMap
                (fixedBasisPairKraus (Fin.tail rA) (Fin.tail rB))
                (weightedScheduleInputBlock (F × StoredRecord) n
                  (sigma observedA observedB)
                  (fA, rA 0) (fA', rA 0)
                  (fB, rB 0) (fB', rB 0))) () () := by
            apply Finset.sum_congr rfl
            intro observedA _
            apply Finset.sum_congr rfl
            intro observedB _
            exact hrec observedA observedB
          _ = _ := by
            have hlaw (p : PMF Basis) (r : Fin (n + 1) → StoredRecord) :
                ((Sampling.basisStringLaw (n + 1) p (storedBasisString r)).toReal : ℂ) =
                  ((p (r 0).2.1).toReal : ℂ) *
                    ((Sampling.basisStringLaw n p (storedBasisString (Fin.tail r))).toReal :
                      ℂ) := by
              rw [Sampling.basisStringLaw_apply, Sampling.basisStringLaw_apply,
                Fin.prod_univ_succ, ENNReal.toReal_mul, Complex.ofReal_mul]
              rfl
            have hK (a b : Bit) (x y : Fin n → Bit) :
                fixedBasisPairKraus rA rB () (Fin.cons a x, Fin.cons b y) =
                  basisUnitary (rA 0).2.1 (rA 0).2.2 a * basisUnitary (rB 0).2.1 (rB 0).2.2 b *
                    fixedBasisPairKraus (Fin.tail rA) (Fin.tail rB) () (x, y) := by
              simp only [fixedBasisPairKraus, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
              rfl
            have hblk (P Q : (Fin (n + 1) → Bit) × (Fin (n + 1) → Bit)) :
                weightedScheduleInputBlock F (n + 1) rho fA fA' fB fB' P Q =
                  rhoPair ((fA, P.1), (fB, P.2)) ((fA', Q.1), (fB', Q.2)) :=
              rfl
            have hblk_zero (observedA observedB : Record)
                (hne : observedA ≠ (rA 0).2 ∨ observedB ≠ (rB 0).2) :
                weightedScheduleInputBlock (F × StoredRecord) n
                  (sigma observedA observedB)
                  (fA, rA 0) (fA', rA 0) (fB, rB 0) (fB', rB 0) = 0 := by
              ext ⟨tailA, tailB⟩ ⟨tailA', tailB'⟩
              rw [hstep, Matrix.zero_apply]
              rcases hne with hne | hne <;>
                simp [weightedOperationApply, Matrix.of_apply, Ne.symm hne]
            rw [Fintype.sum_eq_single (rA 0).2 fun observedA hne =>
                Fintype.sum_eq_zero _ fun observedB => by
                  rw [hblk_zero observedA observedB (Or.inl hne), map_zero, Matrix.zero_apply,
                    mul_zero],
              Fintype.sum_eq_single (rB 0).2 fun observedB hne => by
                rw [hblk_zero _ observedB (Or.inr hne), map_zero, Matrix.zero_apply, mul_zero]]
            rw [Matrix.conjLinearMap_apply_apply, Matrix.conjLinearMap_apply_apply, sumAll, hlaw,
              hlaw,
              Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun tailCol _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun tailRow _ => ?_
            generalize fixedBasisPairKraus (Fin.tail rA) (Fin.tail rB) = Ktail at *
            generalize fixedBasisPairKraus rA rB = Kall at *
            change Unit → ((Fin n → Bit) × (Fin n → Bit)) → ℂ at Ktail
            change Unit → ((Fin (n + 1) → Bit) × (Fin (n + 1) → Bit)) → ℂ at Kall
            rw [hstep, weightedOperationApply, ite_eq_left ⟨rfl, rfl⟩]
            simp only [weightedOperationApply, Matrix.of_apply, and_self, ite_true]
            simp only [hK, hblk, star_mul']
            simp only [Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun bobRow _ => Finset.sum_congr rfl fun bobCol _ =>
              Finset.sum_congr rfl fun aliceRow _ => Finset.sum_congr rfl fun aliceCol _ => ?_
            ring
  · rw [ite_eq_right hrecords]
    exact scheduleWithMemory_recordsDiagonal pA pB F N rho
      fA fA' fB fB' rA rA' rB rB' (not_and_or.mp hrecords)

/-- Exact terminal-coordinate law for the physical Unit-accumulator schedule.

This specializes `scheduleWithMemory_output_apply` to the physical Unit accumulator and reads
the completed records of `measurementState`. -/
theorem weightedMeasurementSchedule_output_apply
    (pA pB : PMF Basis) (N : ℕ)
    (rho : Op (weightedStreamSystem Unit N).total)
    (rA rA' rB rB' : Fin N → StoredRecord) :
    ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleOutputEquiv Unit N)
      (weightedScheduleOutputEquiv Unit N)).toLinearMap
      ((measurementState pA pB Unit N) rho))
        (((), rA), ((), rB)) (((), rA'), ((), rB')) =
      if rA = rA' ∧ rB = rB' then
        ((Sampling.basisStringLaw N pA
          (storedBasisString rA)).toReal : ℂ) *
        ((Sampling.basisStringLaw N pB
          (storedBasisString rB)).toReal : ℂ) *
        (Matrix.conjLinearMap (fixedBasisPairKraus rA rB)
          (weightedScheduleInputBlock Unit N rho () () () ())) () ()
      else 0 := by
  simpa using
    scheduleWithMemory_output_apply pA pB Unit N rho
      () () () () rA rA' rB rB'

end QKD.BB84.Measurement
