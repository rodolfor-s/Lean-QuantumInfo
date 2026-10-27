import QCryptLean.LOCC.Instrument.ClassicalTransition
import QCryptLean.LOCC.MultipartiteSystem
import QCryptLean.LOCC.Program.TwoPartyClassicalStorage
import QCryptLean.LOCC.TwoParty
import QCryptLean.QKD.BB84.Measurement.Classicality
import QCryptLean.QKD.BB84.Measurement.Records
import QCryptLean.QKD.BB84.Measurement.Schedule
import QCryptLean.QKD.BB84.Registers
import QCryptLean.Quantum.Channels.Amplification
import QCryptLean.Quantum.Channels.AmplificationAlgebra
import QCryptLean.Quantum.Channels.Basic
import QCryptLean.Quantum.Operators.Basic

/-! # Classicality Reference -/


open Quantum.Operators (Op)

open Quantum.Channels (
  mapTensorId
  mapTensorId_apply)

open scoped Matrix BigOperators
open Matrix

noncomputable section

namespace QKD.BB84.Measurement
open LOCC

open LOCC.TwoParty

attribute [local instance] storedRecordVectorDecidableEq

/-- The private measurement phase produces classical honest records for every input operator. -/
theorem weightedMeasurementSchedule_honestRegistersDiagonal
    (pA pB : PMF Basis) (N : ℕ)
    (rho : Quantum.Operators.Op (weightedStreamSystem Unit N).total) :
    (weightedStreamSystem (finishAcc Unit N) 0).HonestRegistersDiagonal
      (measurementState pA pB Unit N rho) := by
  intro q q' hqq'
  let c := weightedScheduleOutputEquiv Unit N
  have hdiff : (c q).1.2 ≠ (c q').1.2 ∨ (c q).2.2 ≠ (c q').2.2 := by
    by_contra h
    push Not at h
    have heq : q = q' := c.injective
      (Prod.ext (Prod.ext (Subsingleton.elim _ _) h.1)
        (Prod.ext (Subsingleton.elim _ _) h.2))
    rcases hqq' with hA | hB
    · exact hA (congrFun heq .alice)
    · exact hB (congrFun heq .bob)
  have hdiag := scheduleWithMemory_recordsDiagonal pA pB Unit N rho
    (c q).1.1 (c q').1.1 (c q).2.1 (c q').2.1
    (c q).1.2 (c q').1.2 (c q).2.2 (c q').2.2 hdiff
  change measurementState pA pB Unit N rho (c.symm (c q)) (c.symm (c q')) = 0 at hdiag
  simpa only [Equiv.symm_apply_apply] using hdiag

/-- Honest record diagonality persists with an arbitrary reference, including its coherences. -/
theorem weightedMeasurementSchedule_recordsDiagonal_mapTensorId
    (pA pB : PMF Basis) (N : ℕ) {E : Type*}
    (W : Op ((weightedStreamSystem Unit N).total × E))
    (rA rA' rB rB' : Fin N → StoredRecord) (s t : E)
    (hdiff : rA ≠ rA' ∨ rB ≠ rB') :
    mapTensorId (measurementState pA pB Unit N) E W
      ((weightedScheduleOutputEquiv Unit N).symm (((), rA), ((), rB)), s)
      ((weightedScheduleOutputEquiv Unit N).symm (((), rA'), ((), rB')), t) = 0 := by
  rw [mapTensorId_apply]
  exact scheduleWithMemory_recordsDiagonal pA pB Unit N
    (Matrix.of fun i j => W (i, s) (j, t)) () () () () rA rA' rB rB' hdiff

/-- The complete destructive schedule creates classical honest records against an arbitrary
finite reference from an otherwise arbitrary quantum input operator. -/
theorem weightedMeasurementSchedule_isClassicalOnFirst
    (pA pB : PMF Basis) (N : ℕ)
    {E : Type}
    (rho : Op ((weightedStreamSystem Unit N).total × E)) :
    IsClassicalOnFirst
      (Alpha := (weightedStreamSystem (finishAcc Unit N) 0).total)
      (Ref := E)
      (mapTensorId (measurementState pA pB Unit N) E rho) := by
  intro q q' e e' hxx
  rw [mapTensorId_apply]
  have hdiff : q .alice ≠ q' .alice ∨ q .bob ≠ q' .bob := by
    by_cases hAlice : q .alice = q' .alice
    · right
      intro hBob
      apply hxx
      funext i
      cases i with
      | alice => exact hAlice
      | bob => exact hBob
    · exact Or.inl hAlice
  have hdiag := weightedMeasurementSchedule_honestRegistersDiagonal pA pB N
    (Matrix.of fun i j => rho (i, e) (j, e'))
  have hentry := hdiag q q' hdiff
  exact hentry

end QKD.BB84.Measurement
