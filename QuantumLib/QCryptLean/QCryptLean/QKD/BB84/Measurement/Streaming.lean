import QCryptLean.LOCC.Boundary
import QCryptLean.LOCC.Boundary.DirectSum
import QCryptLean.LOCC.Instrument
import QCryptLean.LOCC.Instrument.OnFactor
import QCryptLean.LOCC.Instrument.Semantics
import QCryptLean.LOCC.LocalAction
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program
import QCryptLean.LOCC.Program.Classical
import QCryptLean.LOCC.Program.Denotation
import QCryptLean.LOCC.TwoParty
import QCryptLean.QKD.BB84.Measurement
import QCryptLean.QKD.BB84.Measurement.Classicality
import QCryptLean.QKD.BB84.Measurement.ClassicalityReference
import QCryptLean.QKD.BB84.Measurement.Records
import QCryptLean.QKD.BB84.Measurement.Schedule
import QCryptLean.QKD.BB84.Measurement.Weighted
import QCryptLean.QKD.BB84.Program
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Operators.Basic

/-! # Streaming -/


open Quantum.Operators (Op)

open Quantum.Channels (mapTensorId)

open scoped Matrix BigOperators ENNReal
open Matrix

noncomputable section

namespace QKD.BB84.Measurement.Streaming
open LOCC

open LOCC.TwoParty

attribute [local instance] storedRecordVectorDecidableEq

/-- The untouched part of one online round: both accumulators and both undelivered tails. -/
abbrev roundSpectator (F : Type) (n : ℕ) :=
  (F × F) × ((Fin n → Bit) × (Fin n → Bit))

/-- Reassociate two locally split stream heads into the physical arriving pair and one spectator. -/
def streamRoundInputRegroup (F : Type) (n : ℕ) :
    ((Bit × streamRegister F n) × (Bit × streamRegister F n)) ≃
      inputSystem.total × roundSpectator F n where
  toFun q :=
    ((TwoParty.pairEquiv Bit Bit).symm (q.1.1, q.2.1),
      ((q.1.2.1, q.2.2.1), (q.1.2.2, q.2.2.2)))
  invFun q :=
    let heads := TwoParty.pairEquiv Bit Bit q.1
    ((heads.1, (q.2.1.1, q.2.2.1)),
      (heads.2, (q.2.1.2, q.2.2.2)))
  left_inv q := by
    rcases q with ⟨⟨xA, fA, tailA⟩, ⟨xB, fB, tailB⟩⟩
    rfl
  right_inv q := by
    rcases q with ⟨active, ⟨⟨fA, fB⟩, ⟨tailA, tailB⟩⟩⟩
    apply Prod.ext
    · exact (TwoParty.pairEquiv Bit Bit).symm_apply_apply active
    · rfl

/-- Reassociate two newly recorded local outputs into the physical one-round output and the same
spectator. -/
def streamRoundOutputRegroup (F : Type) (n : ℕ) :
    ((StoredRecord × streamRegister F n) ×
      (StoredRecord × streamRegister F n)) ≃
      (Boundary.leaf outputSystem).space × roundSpectator F n where
  toFun q :=
    ((Boundary.leafSpaceEquiv outputSystem).symm
        ((TwoParty.pairEquiv StoredRecord StoredRecord).symm (q.1.1, q.2.1)),
      ((q.1.2.1, q.2.2.1), (q.1.2.2, q.2.2.2)))
  invFun q :=
    let records := TwoParty.pairEquiv StoredRecord StoredRecord
      (Boundary.leafSpaceEquiv outputSystem q.1)
    ((records.1, (q.2.1.1, q.2.2.1)),
      (records.2, (q.2.1.2, q.2.2.2)))
  left_inv q := by
    rcases q with ⟨⟨rA, fA, tailA⟩, ⟨rB, fB, tailB⟩⟩
    rfl
  right_inv q := by
    rcases q with ⟨active, ⟨⟨fA, fB⟩, ⟨tailA, tailB⟩⟩⟩
    apply Prod.ext
    · simp
    · rfl

/-- Split the physical two-party stream input into the arriving qubit pair and the untouched
accumulator/tail spectator. -/
def streamRoundInputSplit (F : Type)
    [Fintype F] [DecidableEq F] (n : ℕ) :
    (weightedStreamSystem F (n + 1)).total ≃
      inputSystem.total × roundSpectator F n :=
  (TwoParty.pairEquiv (streamRegister F (n + 1))
      (streamRegister F (n + 1))).trans
    ((Equiv.prodCongr (streamInputSplit F n) (streamInputSplit F n)).trans
      (streamRoundInputRegroup F n))

/-- Split the physical two-party stream output into the new record pair and the unchanged
accumulator/tail spectator. -/
def streamRoundOutputSplit (F : Type)
    [Fintype F] [DecidableEq F] (n : ℕ) :
    (Boundary.leaf (weightedStreamSystem (F × StoredRecord) n)).space ≃
      (Boundary.leaf outputSystem).space × roundSpectator F n :=
  (Boundary.leafSpaceEquiv (weightedStreamSystem (F × StoredRecord) n)).trans
    ((TwoParty.pairEquiv (streamRegister (F × StoredRecord) n)
      (streamRegister (F × StoredRecord) n)).trans
      ((Equiv.prodCongr (streamOutputSplit F n) (streamOutputSplit F n)).trans
        (streamRoundOutputRegroup F n)))

/-- Forward input coordinates expose the two stream heads and preserve both accumulator/tail
coordinates in Alice/Bob order. -/
@[simp] theorem streamRoundInputSplit_apply (F : Type)
    [Fintype F] [DecidableEq F] (n : ℕ)
    (fA fB : F) (xA xB : Fin (n + 1) → Bit) :
    streamRoundInputSplit F n
        ((TwoParty.pairEquiv (streamRegister F (n + 1))
          (streamRegister F (n + 1))).symm ((fA, xA), (fB, xB))) =
      ((TwoParty.pairEquiv Bit Bit).symm (xA 0, xB 0),
        ((fA, fB), (Fin.tail xA, Fin.tail xB))) := by
  rfl

/-- Inverse input coordinates rebuild each physical stream with `Fin.cons`. -/
@[simp] theorem streamRoundInputSplit_symm_apply (F : Type)
    [Fintype F] [DecidableEq F] (n : ℕ)
    (active : inputSystem.total) (fA fB : F)
    (tailA tailB : Fin n → Bit) :
    (streamRoundInputSplit F n).symm
        (active, ((fA, fB), (tailA, tailB))) =
      (TwoParty.pairEquiv (streamRegister F (n + 1))
        (streamRegister F (n + 1))).symm
        ((fA, Fin.cons (TwoParty.pairEquiv Bit Bit active).1 tailA),
          (fB, Fin.cons (TwoParty.pairEquiv Bit Bit active).2 tailB)) := by
  rfl

/-- Forward output coordinates expose the two new records and preserve both accumulator/tail
coordinates in Alice/Bob order. -/
@[simp] theorem streamRoundOutputSplit_apply (F : Type)
    [Fintype F] [DecidableEq F] (n : ℕ)
    (fA fB : F) (rA rB : StoredRecord)
    (tailA tailB : Fin n → Bit) :
    streamRoundOutputSplit F n
        ((Boundary.leafSpaceEquiv (weightedStreamSystem (F × StoredRecord) n)).symm
          ((TwoParty.pairEquiv (streamRegister (F × StoredRecord) n)
            (streamRegister (F × StoredRecord) n)).symm
              (((fA, rA), tailA), ((fB, rB), tailB)))) =
      ((Boundary.leafSpaceEquiv outputSystem).symm
          ((TwoParty.pairEquiv StoredRecord StoredRecord).symm (rA, rB)),
        ((fA, fB), (tailA, tailB))) := by
  rfl

/-- Inverse output coordinates rebuild the two stored-record accumulators without changing either
tail. -/
@[simp] theorem streamRoundOutputSplit_symm_apply (F : Type)
    [Fintype F] [DecidableEq F] (n : ℕ)
    (active : (Boundary.leaf outputSystem).space) (fA fB : F)
    (tailA tailB : Fin n → Bit) :
    (streamRoundOutputSplit F n).symm
        (active, ((fA, fB), (tailA, tailB))) =
      (Boundary.leafSpaceEquiv (weightedStreamSystem (F × StoredRecord) n)).symm
        ((TwoParty.pairEquiv (streamRegister (F × StoredRecord) n)
          (streamRegister (F × StoredRecord) n)).symm
          (((fA, (TwoParty.pairEquiv StoredRecord StoredRecord
              (Boundary.leafSpaceEquiv outputSystem active)).1), tailA),
            ((fB, (TwoParty.pairEquiv StoredRecord StoredRecord
              (Boundary.leafSpaceEquiv outputSystem active)).2), tailB))) := by
  rfl

/-- The actual one-round private program at a stream head: Alice measures first, then Bob, then
the remaining stream is exposed at the next leaf. -/
def weightedStreamRoundProgram (pA pB : PMF Basis)
    (F : Type) [Fintype F] [DecidableEq F] (n : ℕ) :
    Program (weightedStreamSystem F (n + 1)) :=
  (QKD.BB84.measureAlice pA F n).then ((QKD.BB84.measureBob pB F n).then .done)

/-- The actual Alice-then-Bob round instrument acting only on the arriving pair, reindexed onto
the full accumulator and remaining-stream registers. -/
noncomputable def onlineWeightedStreamRound (pA pB : PMF Basis)
    (F : Type) [Fintype F] [DecidableEq F] (n : ℕ) :
    Instrument (weightedStreamSystem F (n + 1)).total
      (Boundary.leaf (weightedStreamSystem (F × StoredRecord) n)).space Unit :=
  Instrument.onFactor (streamRoundInputSplit F n) (streamRoundOutputSplit F n)
    (weightedSingleQubitRoundProgram pA pB).toInstrument

/-- Entrywise arbitrary-operator identity for one arriving pair and independent spectator row and
column coordinates.  This is the explicit `K ⊗ 1` implementation identity specialized to the
actual Alice-then-Bob BB84 round. -/
theorem onlineWeightedStreamRound_operation_apply (pA pB : PMF Basis)
    (F : Type) [Fintype F] [DecidableEq F] (n : ℕ)
    (rho : Op (weightedStreamSystem F (n + 1)).total)
    (q q' : (Boundary.leaf (weightedStreamSystem (F × StoredRecord) n)).space) :
    ((onlineWeightedStreamRound pA pB F n).operation () rho) q q' =
      ((weightedSingleQubitRoundProgram pA pB).toInstrument.operation ()
        (rho.submatrix
          (fun a => (streamRoundInputSplit F n).symm
            (a, (streamRoundOutputSplit F n q).2))
          (fun a => (streamRoundInputSplit F n).symm
            (a, (streamRoundOutputSplit F n q').2))))
        (streamRoundOutputSplit F n q).1
        (streamRoundOutputSplit F n q').1 := by
  exact Instrument.onFactor_operation_apply (streamRoundInputSplit F n)
    (streamRoundOutputSplit F n) (weightedSingleQubitRoundProgram pA pB).toInstrument
    () rho q q'

/-- The denotation of the existing stream-head program equals the online arriving-pair instrument
channel for all fixed local PMFs, including biased and zero-support laws. -/
theorem weightedStreamRoundProgram_denote_eq_online
    (pA pB : PMF Basis)
    (F : Type) [Fintype F] [DecidableEq F] (n : ℕ) :
    (weightedStreamRoundProgram pA pB F n).denote =
      (onlineWeightedStreamRound pA pB F n).channel := by
  apply LinearMap.ext
  intro rho
  ext q q'
  obtain ⟨⟨⟨⟨fA, rA⟩, tailA⟩, ⟨⟨fB, rB⟩, tailB⟩⟩, rfl⟩ :=
    ((Boundary.leafSpaceEquiv (weightedStreamSystem (F × StoredRecord) n)).trans
      (pairEquiv _ _)).symm.surjective q
  obtain ⟨⟨⟨⟨fA', rA'⟩, tailA'⟩, ⟨⟨fB', rB'⟩, tailB'⟩⟩, rfl⟩ :=
    ((Boundary.leafSpaceEquiv (weightedStreamSystem (F × StoredRecord) n)).trans
      (pairEquiv _ _)).symm.surjective q'
  simp only [Instrument.channel_eq_sum, Fintype.sum_unique]
  refine Eq.trans ?_ (onlineWeightedStreamRound_operation_apply pA pB F n rho _ _).symm
  have hactive := (weightedSingleQubitRoundProgram pA pB).toInstrument_channel
  simp only [Instrument.channel_eq_sum, Fintype.sum_unique] at hactive
  have hentry := LinearMap.congr_fun hactive
    (rho.submatrix
      (fun a => (streamRoundInputSplit F n).symm (a, (fA, fB), tailA, tailB))
      (fun a => (streamRoundInputSplit F n).symm (a, (fA', fB'), tailA', tailB')))
  refine Eq.trans ?_ (congrFun (congrFun hentry
    ((Boundary.leafSpaceEquiv outputSystem).symm
      ((pairEquiv StoredRecord StoredRecord).symm (rA, rB))))
    ((Boundary.leafSpaceEquiv outputSystem).symm
      ((pairEquiv StoredRecord StoredRecord).symm (rA', rB')))).symm
  dsimp +instances only [weightedStreamRoundProgram, weightedSingleQubitRoundProgram,
    QKD.BB84.measureAlice, QKD.BB84.measureBob, weightedMeasureAlice,
    weightedMeasureAliceWithSpectator, weightedMeasureBob, PrivateAction.ofInstrument,
    PrivateAction.then]
  simp only [Program.denote_priv_eq_sum_liftedOperation,
    LinearMap.sum_apply, LinearMap.comp_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro observedA _
  apply Finset.sum_congr rfl
  intro observedB _
  change (QKD.BB84.measureBob pB F n).successorOperation observedB
    ((QKD.BB84.measureAlice pA F n).successorOperation observedA rho)
      ((pairEquiv _ _).symm (((fA, rA), tailA), ((fB, rB), tailB)))
      ((pairEquiv _ _).symm (((fA', rA'), tailA'), ((fB', rB'), tailB'))) =
    (weightedMeasureBob pB).successorOperation observedB
      ((weightedMeasureAlice pA).successorOperation observedA
        (rho.submatrix
          (fun a => (streamRoundInputSplit F n).symm (a, (fA, fB), tailA, tailB))
          (fun a => (streamRoundInputSplit F n).symm (a, (fA', fB'), tailA', tailB'))))
      ((pairEquiv StoredRecord StoredRecord).symm (rA, rB))
      ((pairEquiv StoredRecord StoredRecord).symm (rA', rB'))
  refine (PrivateAction.successorOperation_bob_apply (weightedStreamStep pB F n) observedB
    _ ((fA, rA), tailA) ((fA', rA'), tailA')
      ((fB, rB), tailB) ((fB', rB'), tailB')).trans ?_
  refine (weightedStreamStep_operation_apply pB F n observedB _ fB fB' rB rB'
    tailB tailB').trans ?_
  refine Eq.trans ?_ (PrivateAction.successorOperation_bob_apply
    (weightedMeasureAndRecord pB) observedB _ rA rA' rB rB').symm
  apply congrArg (fun sigma : Op Bit =>
    ((weightedMeasureAndRecord pB).operation observedB sigma) rB rB')
  funext j k
  refine (PrivateAction.successorOperation_alice_apply (weightedStreamStep pA F n) observedA
    rho ((fA, rA), tailA) ((fA', rA'), tailA')
      (fB, Fin.cons j tailB) (fB', Fin.cons k tailB')).trans ?_
  refine (weightedStreamStep_operation_apply pA F n observedA _ fA fA' rA rA'
    tailA tailA').trans ?_
  refine Eq.trans ?_ (PrivateAction.successorOperation_alice_apply
    (weightedMeasureAndRecord pA) observedA _ rA rA' j k).symm
  rfl

/-- The one-round implementation identity persists with an arbitrary reference register. -/
theorem weightedStreamRoundProgram_denote_eq_online_mapTensorId
    (pA pB : PMF Basis) (F : Type) [Fintype F] [DecidableEq F]
    (n : ℕ) (E : Type*) :
    mapTensorId (weightedStreamRoundProgram pA pB F n).denote E =
      mapTensorId (onlineWeightedStreamRound pA pB F n).channel E := by
  rw [weightedStreamRoundProgram_denote_eq_online]
  rfl

/-- The existing recursive schedule preserves a zero block between any fixed accumulator row and
column while processing all later stream heads. -/
def SchedulePreservesAccumulatorBlockZero
    (pA pB : PMF Basis) (F : Type)
    [Fintype F] [DecidableEq F] (N : ℕ) : Prop :=
  ∀ (rho : Op (weightedStreamSystem F N).total)
    (fA fA' fB fB' : F),
    (∀ (xA xA' xB xB' : Fin N → Bit),
      ((Matrix.reindexLinearEquiv ℂ ℂ (weightedStreamPairEquiv F N) (weightedStreamPairEquiv F
        N)).toLinearMap rho)
        ((fA, xA), (fB, xB)) ((fA', xA'), (fB', xB')) = 0) →
    ∀ (rA rA' rB rB' : Fin N → StoredRecord),
      ((Matrix.reindexLinearEquiv ℂ ℂ (weightedScheduleOutputEquiv F N) (weightedScheduleOutputEquiv
        F N)).toLinearMap
        (measurementState pA pB F N rho))
          ((fA, rA), (fB, rB)) ((fA', rA'), (fB', rB')) = 0

/-- Certificate that a concrete program begins with the actual destructive private schedule, that
each head step equals the online arriving-pair instrument, and that the accumulator zero-block
invariant holds at every remaining length.  The existential continuation begins only after all
`N` private rounds and contains no claim that its later actions are classical. -/
def StreamingMeasurementPrefix
    (pA pB : PMF Basis) (N : ℕ) {End : MultipartiteSystem Party → Type 1}
    (P : Program (weightedStreamSystem Unit N) End) : Prop :=
  ∃ continuation : Program (weightedStreamSystem (finishAcc Unit N) 0) End,
    P = measureRounds pA pB Unit N continuation ∧
    (∀ (F : Type) [Nonempty F] [Fintype F] [DecidableEq F] (n : ℕ),
      (weightedStreamRoundProgram pA pB F n).denote =
        (onlineWeightedStreamRound pA pB F n).channel) ∧
    (∀ (F : Type) [Nonempty F] [Fintype F] [DecidableEq F] (n : ℕ),
      SchedulePreservesAccumulatorBlockZero pA pB F n)

end QKD.BB84.Measurement.Streaming
