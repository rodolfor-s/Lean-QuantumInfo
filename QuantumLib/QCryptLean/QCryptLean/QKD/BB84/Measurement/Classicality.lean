import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.LOCC.Instrument.TwoParty
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.Program.ExitWeight
import QCryptLean.LOCC.TwoParty
import QCryptLean.Math.LinearAlgebra.Matrix.Conjugation
import QCryptLean.QKD.BB84.Measurement.Records
import QCryptLean.QKD.BB84.Measurement.Schedule
import QCryptLean.QKD.BB84.Measurement.Weighted
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Operators.Basic

/-! # Classicality -/


open Quantum.Operators (Op)

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QKD.BB84.Measurement
open LOCC

open LOCC.TwoParty

/-- Explicit decidable equality for finite chronological stored-record vectors. -/
@[implicit_reducible] def storedRecordVectorDecidableEq (N : ℕ) :
    DecidableEq (Fin N → StoredRecord) :=
  Fintype.decidablePiFintype

attribute [local instance] storedRecordVectorDecidableEq


/-- Forward coordinate formula for the finished stream equivalence. -/
@[simp] theorem finishedStreamEquiv_apply (F : Type) (N : ℕ)
    (q : streamRegister (finishAcc F N) 0) :
    finishedStreamEquiv F N q = finishAccEquiv F N q.1 := by
  rfl

/-- Inverse coordinate formula, with the unique empty remaining stream made explicit. -/
@[simp] theorem finishedStreamEquiv_symm_apply (F : Type) (N : ℕ)
    (q : F × (Fin N → StoredRecord)) :
    (finishedStreamEquiv F N).symm q =
      ((finishAccEquiv F N).symm q, fun i => Fin.elim0 i) := by
  rfl

/-- Product coordinates of the two-party input stream multipartite system. -/
def weightedStreamPairEquiv (F : Type)
    [Fintype F] [DecidableEq F] (N : ℕ) :
    (weightedStreamSystem F N).total ≃
      streamRegister F N × streamRegister F N :=
  TwoParty.pairEquiv (streamRegister F N) (streamRegister F N)

/-- Forward input coordinate formula: Alice's local stream followed by Bob's local stream. -/
@[simp] theorem weightedStreamPairEquiv_apply (F : Type)
    [Fintype F] [DecidableEq F] (N : ℕ)
    (q : (weightedStreamSystem F N).total) :
    weightedStreamPairEquiv F N q = (q .alice, q .bob) := by
  rfl

/-- Terminal coordinates displaying both initial accumulators and both record vectors. -/
def weightedScheduleOutputEquiv (F : Type)
    [Fintype F] [DecidableEq F] (N : ℕ) :
    (weightedStreamSystem (finishAcc F N) 0).total ≃
      (F × (Fin N → StoredRecord)) × (F × (Fin N → StoredRecord)) :=
  (TwoParty.pairEquiv _ _).trans
    (Equiv.prodCongr (finishedStreamEquiv F N) (finishedStreamEquiv F N))

/-- Record diagonality leaves the initial accumulator coordinates independent. -/
def ScheduleRecordsDiagonal (F : Type)
    [Fintype F] [DecidableEq F] (N : ℕ)
    (sigma : Op (weightedStreamSystem (finishAcc F N) 0).total) : Prop :=
  ∀ (fA fA' fB fB' : F) (rA rA' rB rB' : Fin N → StoredRecord),
    rA ≠ rA' ∨ rB ≠ rB' →
      ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleOutputEquiv F N) (weightedScheduleOutputEquiv
        F N)).toLinearMap sigma)
        ((fA, rA), (fB, rB)) ((fA', rA'), (fB', rB')) = 0

/-- Alice's head measurement operation in the natural successor coordinates. -/
def measureAliceOperation (p : PMF Basis) (F : Type)
    [Fintype F] [DecidableEq F] (n : ℕ) (observed : Record) :
    Op (weightedStreamSystem F (n + 1)).total →ₗ[ℂ]
      Op (system (streamRegister (F × StoredRecord) n) (streamRegister F (n + 1))).total :=
  Matrix.conjLinearMap ((QKD.BB84.measureAlice p F n).successorKraus observed ())

/-- Bob's head measurement operation after Alice has appended her record. -/
def measureBobOperation (p : PMF Basis) (F : Type)
    [Fintype F] [DecidableEq F] (n : ℕ) (observed : Record) :
    Op (system (streamRegister (F × StoredRecord) n) (streamRegister F (n + 1))).total →ₗ[ℂ]
      Op (weightedStreamSystem (F × StoredRecord) n).total :=
  Matrix.conjLinearMap ((QKD.BB84.measureBob p F n).successorKraus observed ())

/-- Alice's normalized measurement acts on her stream while preserving Bob's coordinates. -/
theorem measureAlice_operation_apply (p : PMF Basis) (F : Type)
    [Fintype F] [DecidableEq F] (n : ℕ) (observed : Record)
    (rho : Op (system (streamRegister F (n + 1)) (streamRegister F (n + 1))).total)
    (a a' : streamRegister (F × StoredRecord) n) (b b' : streamRegister F (n + 1)) :
    ((measureAliceOperation p F n) observed rho)
        ((pairEquiv _ _).symm (a, b)) ((pairEquiv _ _).symm (a', b')) =
      (weightedStreamStep p F n).operation observed
        (rho.submatrix (fun x => (pairEquiv _ _).symm (x, b))
          (fun x => (pairEquiv _ _).symm (x, b'))) a a' :=
by
  let R := weightedStreamSystem F (n + 1)
  let A := QKD.BB84.measureAlice (B := streamRegister F (n + 1)) p F n
  have hcast (a : streamRegister (F × StoredRecord) n) (b : streamRegister F (n + 1)) :
      (Equiv.cast (congrArg MultipartiteSystem.total
        (SystemPresentation.update_eq_set R A.actor A.Output)))
          ((pairEquiv _ _).symm (a, b)) = (A.out.pairEquiv.symm (a, b)) := by
    exact MultipartiteSystem.cast_pairEquiv_symm
      (SystemPresentation.update_eq_set R A.actor A.Output) (a, b)
  have hop := Instrument.liftAt_alice_operation_apply R
    (weightedStreamStep p F n) observed rho a a' b b'
  change A.liftedOperation observed rho _ _ = _ at hop
  change (∑ _ : Unit, Matrix.conjLinearMap (A.liftedKraus observed ())) rho _ _ = _ at hop
  simp only [Fintype.sum_unique] at hop
  change Matrix.conjLinearMap (A.successorKraus observed ()) rho
    ((pairEquiv _ _).symm (a, b)) ((pairEquiv _ _).symm (a', b')) = _
  calc
    _ = Matrix.conjLinearMap (A.liftedKraus observed ()) rho
        ((Equiv.cast (congrArg MultipartiteSystem.total
          (SystemPresentation.update_eq_set R A.actor A.Output)))
            ((pairEquiv _ _).symm (a, b)))
        ((Equiv.cast (congrArg MultipartiteSystem.total
          (SystemPresentation.update_eq_set R A.actor A.Output)))
            ((pairEquiv _ _).symm (a', b'))) := by
      rfl
    _ = _ := by rw [hcast, hcast]; exact hop

/-- Bob's normalized measurement acts on his stream after Alice has stored her new record. -/
theorem measureBob_operation_apply (p : PMF Basis) (F : Type)
    [Fintype F] [DecidableEq F] (n : ℕ) (observed : Record)
    (rho : Op (system (streamRegister (F × StoredRecord) n)
      (streamRegister F (n + 1))).total)
    (a a' b b' : streamRegister (F × StoredRecord) n) :
    ((measureBobOperation p F n) observed rho)
        ((pairEquiv _ _).symm (a, b)) ((pairEquiv _ _).symm (a', b')) =
      (weightedStreamStep p F n).operation observed
        (rho.submatrix (fun x => (pairEquiv _ _).symm (a, x))
          (fun x => (pairEquiv _ _).symm (a', x))) b b' :=
by
  let R := system (streamRegister (F × StoredRecord) n) (streamRegister F (n + 1))
  let A := QKD.BB84.measureBob (A := streamRegister (F × StoredRecord) n) p F n
  have hcast (a b : streamRegister (F × StoredRecord) n) :
      (Equiv.cast (congrArg MultipartiteSystem.total
        (SystemPresentation.update_eq_set R A.actor A.Output)))
          ((pairEquiv _ _).symm (a, b)) = (A.out.pairEquiv.symm (a, b)) := by
    exact MultipartiteSystem.cast_pairEquiv_symm
      (SystemPresentation.update_eq_set R A.actor A.Output) (a, b)
  have hop := Instrument.liftAt_bob_operation_apply R
    (weightedStreamStep p F n) observed rho a a' b b'
  change A.liftedOperation observed rho _ _ = _ at hop
  change (∑ _ : Unit, Matrix.conjLinearMap (A.liftedKraus observed ())) rho _ _ = _ at hop
  simp only [Fintype.sum_unique] at hop
  change Matrix.conjLinearMap (A.successorKraus observed ()) rho
    ((pairEquiv _ _).symm (a, b)) ((pairEquiv _ _).symm (a', b')) = _
  calc
    _ = Matrix.conjLinearMap (A.liftedKraus observed ()) rho
        ((Equiv.cast (congrArg MultipartiteSystem.total
          (SystemPresentation.update_eq_set R A.actor A.Output)))
            ((pairEquiv _ _).symm (a, b)))
        ((Equiv.cast (congrArg MultipartiteSystem.total
          (SystemPresentation.update_eq_set R A.actor A.Output)))
            ((pairEquiv _ _).symm (a', b'))) := by
      rfl
    _ = _ := by rw [hcast, hcast]; exact hop

/-- The measurement phase processes both head measurements before the remaining stream. -/
theorem measurementState_succ (pA pB : PMF Basis) (F : Type)
    [Fintype F] [DecidableEq F] (n : ℕ)
    (rho : Op (weightedStreamSystem F (n + 1)).total) :
    measurementState pA pB F (n + 1) rho =
      ∑ a : Record, ∑ b : Record,
        measurementState pA pB (F × StoredRecord) n
          (measureBobOperation pB F n b (measureAliceOperation pA F n a rho)) := by
  change (∑ a : Record, ∑ _ : Unit, ∑ b : Record, ∑ _ : Unit,
    (measurementState pA pB (F × StoredRecord) n).comp
      ((measureBobOperation pB F n b).comp (measureAliceOperation pA F n a))) rho = _
  simp only [Fintype.sum_unique, LinearMap.sum_apply, LinearMap.comp_apply]

/-- Processing every remaining signal preserves any zero block of the initial accumulator. -/
theorem scheduleWithMemory_preserves_accumulator_block_zero
    (pA pB : PMF Basis) (F : Type)
    [Fintype F] [DecidableEq F] (N : ℕ)
    (rho : Op (system (streamRegister F N) (streamRegister F N)).total) (fA fA' fB fB' : F)
    (hzero : ∀ (xA xA' xB xB' : Fin N → Bit),
      ((Matrix.reindexLinearEquiv ℂ ℂ (weightedStreamPairEquiv F N) (weightedStreamPairEquiv F
        N)).toLinearMap rho)
        ((fA, xA), (fB, xB)) ((fA', xA'), (fB', xB')) = 0) :
    ∀ (rA rA' rB rB' : Fin N → StoredRecord),
      ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleOutputEquiv F N) (weightedScheduleOutputEquiv
        F N)).toLinearMap
        ((measurementState pA pB F N) rho))
          ((fA, rA), (fB, rB)) ((fA', rA'), (fB', rB')) = 0 := by
  induction N generalizing F with
  | zero =>
      intro rA rA' rB rB'
      exact hzero Fin.elim0 Fin.elim0 Fin.elim0 Fin.elim0
  | succ n ih =>
      intro rA rA' rB rB'
      have hAliceZero (observed : Record) (stored stored' : StoredRecord)
          (tailA tailA' : Fin n → Bit) (xB xB' : Fin (n + 1) → Bit) :
          ((measureAliceOperation pA F n) observed rho)
            ((pairEquiv _ _).symm (((fA, stored), tailA), (fB, xB)))
            ((pairEquiv _ _).symm (((fA', stored'), tailA'), (fB', xB'))) = 0 := by
        rw [measureAlice_operation_apply, weightedStreamStep_operation_apply]
        have hlocal : (rho.submatrix
            (fun j => (pairEquiv _ _).symm ((fA, Fin.cons j tailA), (fB, xB)))
            (fun j => (pairEquiv _ _).symm ((fA', Fin.cons j tailA'), (fB', xB')))) = 0 := by
          ext j k
          exact hzero (Fin.cons j tailA) (Fin.cons k tailA') xB xB'
        have h := congrArg
          (fun M => (weightedMeasureAndRecord pA).operation observed M stored stored') hlocal
        simp only [map_zero, Matrix.zero_apply] at h
        exact h
      have hBobZero (observedA observedB : Record)
          (storedA storedA' storedB storedB' : StoredRecord)
          (tailA tailA' tailB tailB' : Fin n → Bit) :
          ((measureBobOperation pB F n) observedB
            ((measureAliceOperation pA F n) observedA rho))
              ((pairEquiv _ _).symm (((fA, storedA), tailA), ((fB, storedB), tailB)))
              ((pairEquiv _ _).symm (((fA', storedA'), tailA'), ((fB', storedB'), tailB'))) =
                0 := by
        rw [measureBob_operation_apply, weightedStreamStep_operation_apply]
        let sigmaA :=
          (measureAliceOperation pA F n) observedA rho
        have hlocal : (sigmaA.submatrix
            (fun x => (pairEquiv _ _).symm (((fA, storedA), tailA), x))
            (fun x => (pairEquiv _ _).symm (((fA', storedA'), tailA'), x))).submatrix
              (fun j => (fB, Fin.cons j tailB)) (fun j => (fB', Fin.cons j tailB')) = 0 := by
          ext j k
          exact hAliceZero observedA storedA storedA' tailA tailA'
            (Fin.cons j tailB) (Fin.cons k tailB')
        rw [hlocal, map_zero]
        rfl
      change ((measurementState pA pB F (n + 1)) rho)
        ((weightedScheduleOutputEquiv F (n + 1)).symm ((fA, rA), (fB, rB)))
        ((weightedScheduleOutputEquiv F (n + 1)).symm ((fA', rA'), (fB', rB'))) = 0
      rw [measurementState_succ]
      simp only [Matrix.sum_apply]
      apply Finset.sum_eq_zero
      intro observedA _
      apply Finset.sum_eq_zero
      intro observedB _
      exact ih (F := F × StoredRecord) _ (fA, rA 0) (fA', rA' 0)
        (fB, rB 0) (fB', rB' 0)
        (hBobZero observedA observedB (rA 0) (rA' 0) (rB 0) (rB' 0))
        (Fin.tail rA) (Fin.tail rA') (Fin.tail rB) (Fin.tail rB')

/-- Newly generated chronological records are diagonal for every initial accumulator operator. -/
theorem scheduleWithMemory_recordsDiagonal
    (pA pB : PMF Basis) (F : Type)
    [Fintype F] [DecidableEq F] (N : ℕ)
    (rho : Op (system (streamRegister F N) (streamRegister F N)).total) :
    ScheduleRecordsDiagonal F N
      ((measurementState pA pB F N) rho) := by
  unfold ScheduleRecordsDiagonal
  induction N generalizing F with
  | zero =>
      intro fA fA' fB fB' rA rA' rB rB' h
      exfalso
      apply h.elim
      · intro hA
        apply hA
        funext i
        exact Fin.elim0 i
      · intro hB
        apply hB
        funext i
        exact Fin.elim0 i
  | succ n ih =>
      intro fA fA' fB fB' rA rA' rB rB' hdiff
      have hAliceHeadZero
          (observed : Record) (hne : (rA 0).2 ≠ (rA' 0).2)
          (tailA tailA' : Fin n → Bit) (xB xB' : Fin (n + 1) → Bit) :
          ((measureAliceOperation pA F n) observed rho)
              ((pairEquiv _ _).symm
                (((fA, rA 0), tailA), (fB, xB)))
              ((pairEquiv _ _).symm
                (((fA', rA' 0), tailA'), (fB', xB'))) = 0 := by
        rw [measureAlice_operation_apply]
        exact weightedStreamStep_operation_newRecordDiagonal
          pA F n observed _ fA fA' (rA 0) (rA' 0) tailA tailA'
            (fun h => hne (congrArg Prod.snd h))
      have hBobHeadZero
          (observedA observedB : Record) (hne : (rB 0).2 ≠ (rB' 0).2)
          (tailA tailA' tailB tailB' : Fin n → Bit) :
          ((measureBobOperation pB F n) observedB
            ((measureAliceOperation pA F n) observedA rho))
              ((pairEquiv _ _).symm
                (((fA, rA 0), tailA), ((fB, rB 0), tailB)))
              ((pairEquiv _ _).symm
                (((fA', rA' 0), tailA'), ((fB', rB' 0), tailB'))) = 0 := by
        rw [measureBob_operation_apply]
        exact weightedStreamStep_operation_newRecordDiagonal
          pB F n observedB _ fB fB' (rB 0) (rB' 0) tailB tailB'
            (fun h => hne (congrArg Prod.snd h))
      have hBobAfterAliceHeadZero
          (observedA observedB : Record) (hne : (rA 0).2 ≠ (rA' 0).2)
          (tailA tailA' tailB tailB' : Fin n → Bit) :
          ((measureBobOperation pB F n) observedB
            ((measureAliceOperation pA F n) observedA rho))
              ((pairEquiv _ _).symm
                (((fA, rA 0), tailA), ((fB, rB 0), tailB)))
              ((pairEquiv _ _).symm
                (((fA', rA' 0), tailA'), ((fB', rB' 0), tailB'))) = 0 := by
        rw [measureBob_operation_apply, weightedStreamStep_operation_apply]
        have hlocal :
            ((((measureAliceOperation pA F n) observedA rho).submatrix
              (fun x => (pairEquiv _ _).symm
                (((fA, rA 0), tailA), x))
              (fun x => (pairEquiv _ _).symm
                (((fA', rA' 0), tailA'), x))).submatrix
                (fun j => (fB, Fin.cons j tailB))
                (fun j => (fB', Fin.cons j tailB'))) = 0 := by
          ext j k
          exact hAliceHeadZero observedA hne tailA tailA'
            (Fin.cons j tailB) (Fin.cons k tailB')
        have h :=
          congrArg (fun M => (weightedMeasureAndRecord pB).operation observedB M (rB 0) (rB' 0))
            hlocal
        simp only [map_zero, Matrix.zero_apply] at h
        exact h
      change ((measurementState pA pB F (n + 1)) rho)
        ((weightedScheduleOutputEquiv F (n + 1)).symm
          ((fA, rA), (fB, rB)))
        ((weightedScheduleOutputEquiv F (n + 1)).symm
          ((fA', rA'), (fB', rB'))) = 0
      rw [measurementState_succ]
      simp only [Matrix.sum_apply]
      apply Finset.sum_eq_zero
      intro observedA _
      apply Finset.sum_eq_zero
      intro observedB _
      let sigma : Op (weightedStreamSystem (F × StoredRecord) n).total :=
        (measureBobOperation pB F n) observedB
          ((measureAliceOperation pA F n) observedA rho)
      by_cases hA0 : (rA 0).2 ≠ (rA' 0).2
      · have hrec := scheduleWithMemory_preserves_accumulator_block_zero
          pA pB (F × StoredRecord) n sigma
          (fA, rA 0) (fA', rA' 0) (fB, rB 0) (fB', rB' 0)
          (hBobAfterAliceHeadZero observedA observedB hA0)
          (Fin.tail rA) (Fin.tail rA') (Fin.tail rB) (Fin.tail rB')
        exact hrec
      · by_cases hB0 : (rB 0).2 ≠ (rB' 0).2
        · have hrec := scheduleWithMemory_preserves_accumulator_block_zero
            pA pB (F × StoredRecord) n sigma
            (fA, rA 0) (fA', rA' 0) (fB, rB 0) (fB', rB' 0)
            (hBobHeadZero observedA observedB hB0)
            (Fin.tail rA) (Fin.tail rA') (Fin.tail rB) (Fin.tail rB')
          exact hrec
        · have hheadA : rA 0 = rA' 0 := by
            apply Prod.ext
            · exact Subsingleton.elim _ _
            · exact not_ne_iff.mp hA0
          have hheadB : rB 0 = rB' 0 := by
            apply Prod.ext
            · exact Subsingleton.elim _ _
            · exact not_ne_iff.mp hB0
          have htail : Fin.tail rA ≠ Fin.tail rA' ∨
              Fin.tail rB ≠ Fin.tail rB' := by
            rcases hdiff with hA | hB
            · left
              intro ht
              apply hA
              rw [← Fin.cons_self_tail rA, ← Fin.cons_self_tail rA', hheadA, ht]
            · right
              intro ht
              apply hB
              rw [← Fin.cons_self_tail rB, ← Fin.cons_self_tail rB', hheadB, ht]
          have hrec := ih (F := F × StoredRecord) (rho := sigma)
            (fA, rA 0) (fA', rA' 0) (fB, rB 0) (fB', rB' 0)
            (Fin.tail rA) (Fin.tail rA') (Fin.tail rB) (Fin.tail rB') htail
          exact hrec

end QKD.BB84.Measurement
